"""
Bot Scalping v20.0 — QUALITY OVER QUANTITY
============================================
AUDIT TOTAL v19.6 → v20.0
Root cause fix:
  1. TP/SL Fixed dihapus → ATR Dynamic
  2. Single TF → Multi-TF Confirmation (5M + 15M + 1H)
  3. ADX threshold dinaikkan (< 20 = no trade)
  4. EMA spread filter (chop detection)
  5. Smart Entry: anti-chase, tunggu pullback/retest
  6. Confidence Score >= 70 (bukan 45)
  7. Market Regime Detection (Sideways = NO TRADE)
  8. Adaptive Risk (3 loss beruntun → size 50%)
  9. Loss Pattern Learning (symbol/jam blocker)
 10. False breakout filter via volume + body ratio
"""

import os, time, math, threading, queue, json
from datetime import datetime, timezone
import requests
from collections import deque, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dotenv import load_dotenv
from binance.client import Client
import ta
import pandas as pd
import numpy as np

load_dotenv()
client = Client(os.getenv("API_KEY"), os.getenv("API_SECRET"))
client.FUTURES_URL = "https://testnet.binancefuture.com/fapi"

# ═══════════════════════════════════════════════════════════════════
#  CONFIG v20.0 — QUALITY OVER QUANTITY
# ═══════════════════════════════════════════════════════════════════
LEVERAGE          = 20
ORDER_USDT        = 2.0         # Base margin per posisi
MAX_POSITIONS     = 2           # Turunkan dari 3 → 2, kualitas bukan kuantitas

# ATR Dynamic TP/SL — BUKAN FIXED LAGI
ATR_SL_MULT       = 1.2         # SL = ATR × 1.2
ATR_TP_MULT       = 2.5         # TP = ATR × 2.5 → RR minimal 1:2
MIN_RR            = 2.0         # Tolak jika RR < 2.0

FUTURES_FEE_PCT   = 0.0005      # 0.05% taker fee per sisi

# Filter ketat
MIN_BASE_VOL      = 50_000_000  # Naik dari 20M → 50M (hanya liquid symbols)
ADX_MIN           = 20          # Naik dari 15 → 20 (anti-chop)
EMA_SPREAD_MIN    = 0.0015      # EMA21 vs EMA50 harus beda min 0.15% (anti-flat)
CONFIDENCE_MIN    = 70          # Naik dari 45 → 70 (hanya setup A+)
MIN_SCORE_GAP     = 15          # Naik dari 8 → 15 (harus jelas arahnya)

# Anti-overtrading
SCAN_INTERVAL     = 3           # Naik dari 1 → 3 detik
MONITOR_INT       = 0.5
SCAN_DELAY        = 0.02
BATCH_SIZE        = 10
MAX_WORKERS       = 6
COOLDOWN_SEC      = 600         # Naik dari 180 → 600 (10 menit per symbol)

# Cache TTL
TTL_5M            = 30
TTL_15M           = 60
TTL_1H            = 180

# Kill Switch
DAILY_LOSS        = -5.0        # Stop lebih cepat dari -8
CONSEC_MAX        = 3           # Stop setelah 3 loss beruntun (bukan 8)
CONSEC_PAUSE      = 300         # 5 menit pause

# Adaptive Risk
ADAPTIVE_SIZE_MULT = 0.5        # Kalikan 50% saat streak loss
ADAPTIVE_CONF_ADD  = 15         # Naikkan threshold confidence 15 poin saat streak loss
STREAK_LOSS_TRIG   = 3
STREAK_WIN_RESET   = 3

# Loss Pattern Learning
PATTERN_BLOCK_THRESHOLD = 3     # Blok symbol/jam jika loss >= 3x di kondisi sama
PATTERN_BLOCK_HOURS = 4         # Blokir selama 4 jam

# ═══════════════════════════════════════════════════════════════════
#  SYMBOLS — Hanya major/liquid
# ═══════════════════════════════════════════════════════════════════
SYMBOLS = [
    "BTCUSDT", "ETHUSDT", "BNBUSDT", "SOLUSDT", "XRPUSDT",
    "ADAUSDT", "DOGEUSDT", "AVAXUSDT", "LINKUSDT", "DOTUSDT",
    "LTCUSDT", "ATOMUSDT", "UNIUSDT", "NEARUSDT", "AAVEUSDT",
    "ARBUSDT", "OPUSDT", "INJUSDT", "SUIUSDT", "TONUSDT",
]
SYMBOLS = list(dict.fromkeys(SYMBOLS))

# ═══════════════════════════════════════════════════════════════════
#  STATE
# ═══════════════════════════════════════════════════════════════════
live_positions  = {}
trade_log       = []
_ohlcv_cache    = {}
_sym_cooldown   = {}
_ticker_cache   = {}
_ticker_ts      = 0
_lock           = threading.Lock()
_executor       = ThreadPoolExecutor(max_workers=MAX_WORKERS)
_rescan_q       = queue.Queue()
_hot_syms       = deque(maxlen=10)

_macro = {"btc": "UNKNOWN", "fng": 50, "last_fng": 0, "last_btc": 0, "regime": "UNKNOWN"}
_ks    = {"active": False, "reason": "", "resume": 0, "consec": 0, "daily": 0.0, "day_reset": 0}
_stats = {
    "trades": 0, "wins": 0, "losses": 0, "pnl": 0.0, "best": 0.0, "worst": 0.0,
    "tp_hit": 0, "sl_hit": 0, "hist": deque(maxlen=200), "start": time.time(),
    "streak_loss": 0, "streak_win": 0,
}

# Loss Pattern Learning State
_loss_patterns = {
    "by_symbol": defaultdict(list),    # {symbol: [timestamps]}
    "by_hour":   defaultdict(list),    # {hour: [timestamps]}
    "by_regime": defaultdict(list),    # {regime: [timestamps]}
    "blocked_symbols": {},              # {symbol: unblock_timestamp}
    "blocked_hours":   set(),          # {hour}
}

# ═══════════════════════════════════════════════════════════════════
#  LOSS PATTERN LEARNING
# ═══════════════════════════════════════════════════════════════════
def record_loss_pattern(sym, entry_hour, regime):
    """Catat setiap loss untuk analisis pola."""
    now = time.time()
    lp = _loss_patterns

    lp["by_symbol"][sym].append(now)
    lp["by_hour"][entry_hour].append(now)
    lp["by_regime"][regime].append(now)

    # Hanya hitung loss dalam 24 jam terakhir
    cutoff = now - 86400

    # Cek apakah symbol harus diblok
    recent_sym_losses = [t for t in lp["by_symbol"][sym] if t > cutoff]
    if len(recent_sym_losses) >= PATTERN_BLOCK_THRESHOLD:
        unblock = now + PATTERN_BLOCK_HOURS * 3600
        lp["blocked_symbols"][sym] = unblock
        print(f"  🚫 Pattern Block: {sym} diblok {PATTERN_BLOCK_HOURS}j "
              f"({len(recent_sym_losses)} loss dalam 24j)")

    # Cek apakah jam ini harus diblok
    recent_hour_losses = [t for t in lp["by_hour"][entry_hour] if t > cutoff]
    if len(recent_hour_losses) >= PATTERN_BLOCK_THRESHOLD * 2:
        lp["blocked_hours"].add(entry_hour)
        print(f"  🚫 Pattern Block: Jam {entry_hour:02d}:xx diblok "
              f"({len(recent_hour_losses)} loss dalam 24j)")

def is_pattern_blocked(sym):
    """Cek apakah symbol atau jam saat ini sedang diblok."""
    now = time.time()
    lp  = _loss_patterns
    current_hour = datetime.now().hour

    # Cek symbol block
    if sym in lp["blocked_symbols"]:
        if now < lp["blocked_symbols"][sym]:
            remaining = (lp["blocked_symbols"][sym] - now) / 60
            return True, f"symbol block ({remaining:.0f}m)"
        else:
            del lp["blocked_symbols"][sym]  # Unblock

    # Cek hour block
    if current_hour in lp["blocked_hours"]:
        return True, f"hour block (jam {current_hour:02d})"

    return False, ""

def get_loss_pattern_report():
    """Generate laporan pola loss."""
    now    = time.time()
    cutoff = now - 86400
    lp     = _loss_patterns
    lines  = ["  📊 Loss Pattern Analysis (24h):"]

    # Top loss symbols
    sym_losses = {
        s: len([t for t in ts if t > cutoff])
        for s, ts in lp["by_symbol"].items()
    }
    top_syms = sorted(sym_losses.items(), key=lambda x: x[1], reverse=True)[:5]
    if top_syms:
        lines.append("     Symbols paling sering loss:")
        for s, c in top_syms:
            if c > 0:
                lines.append(f"       {s}: {c}x")

    # Top loss hours
    hr_losses = {
        h: len([t for t in ts if t > cutoff])
        for h, ts in lp["by_hour"].items()
    }
    top_hrs = sorted(hr_losses.items(), key=lambda x: x[1], reverse=True)[:3]
    if top_hrs:
        lines.append("     Jam paling sering loss:")
        for h, c in top_hrs:
            if c > 0:
                lines.append(f"       {h:02d}:xx — {c}x")

    return "\n".join(lines)

# ═══════════════════════════════════════════════════════════════════
#  BINANCE UTILS
# ═══════════════════════════════════════════════════════════════════
_precision_cache = {}
def get_precision(symbol):
    if symbol in _precision_cache: return _precision_cache[symbol]
    try:
        info = client.futures_exchange_info()
        for s in info['symbols']:
            if s['symbol'] == symbol:
                prec = int(s['quantityPrecision'])
                _precision_cache[symbol] = prec
                return prec
    except: pass
    return 2

def effective_order_usdt():
    """Ukuran posisi adaptif berdasarkan streak loss."""
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        return ORDER_USDT * ADAPTIVE_SIZE_MULT
    return ORDER_USDT

def effective_confidence_min():
    """Threshold confidence adaptif berdasarkan streak loss."""
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        return CONFIDENCE_MIN + ADAPTIVE_CONF_ADD
    return CONFIDENCE_MIN

def qty(symbol, price):
    raw_qty = (effective_order_usdt() * LEVERAGE) / price
    prec = get_precision(symbol)
    return round(raw_qty, prec)

def price_live(symbol):
    try: return float(client.futures_symbol_ticker(symbol=symbol)["price"])
    except: return 0.0

def tickers_all():
    global _ticker_cache, _ticker_ts
    now = time.time()
    if now - _ticker_ts < 5 and _ticker_cache: return _ticker_cache
    try:
        raw = client.futures_ticker()
        _ticker_cache = {
            t["symbol"]: {
                "pct":  float(t["priceChangePercent"]),
                "vol":  float(t["quoteVolume"]),
                "last": float(t["lastPrice"])
            } for t in raw
        }
        _ticker_ts = now
        return _ticker_cache
    except: return _ticker_cache

def ok_cooldown(sym): return (time.time() - _sym_cooldown.get(sym, 0)) >= COOLDOWN_SEC
def set_cd(sym): _sym_cooldown[sym] = time.time()

def ohlcv(symbol, interval, limit=120):
    key, now = (symbol, interval), time.time()
    # TTL berdasarkan timeframe
    if interval == Client.KLINE_INTERVAL_5MINUTE:   ttl = TTL_5M
    elif interval == Client.KLINE_INTERVAL_15MINUTE: ttl = TTL_15M
    else:                                             ttl = TTL_1H

    if key in _ohlcv_cache and now - _ohlcv_cache[key][0] < ttl:
        return _ohlcv_cache[key][1]
    try:
        kl = client.futures_klines(symbol=symbol, interval=interval, limit=limit)
        df = pd.DataFrame(kl, columns=[
            "time","open","high","low","close","volume",
            "ct","qv","trades","tbbase","tbquote","ignore"
        ])
        for c in ["open","high","low","close","volume","tbbase","tbquote"]:
            df[c] = df[c].astype(float)
        _ohlcv_cache[key] = (now, df)
        return df
    except:
        return _ohlcv_cache.get(key, (None, None))[1]

def run_ta(df):
    """Hitung semua indikator teknikal."""
    c, h, l, v = df["close"], df["high"], df["low"], df["volume"]
    df["rsi"]  = ta.momentum.RSIIndicator(c, 14).rsi()
    df["mh"]   = ta.trend.MACD(c, 12, 26, 9).macd_diff()
    df["e5"]   = ta.trend.EMAIndicator(c, 5).ema_indicator()
    df["e9"]   = ta.trend.EMAIndicator(c, 9).ema_indicator()
    df["e21"]  = ta.trend.EMAIndicator(c, 21).ema_indicator()
    df["e50"]  = ta.trend.EMAIndicator(c, 50).ema_indicator()
    df["e200"] = ta.trend.EMAIndicator(c, 200).ema_indicator()
    df["atr"]  = ta.volatility.AverageTrueRange(h, l, c, 14).average_true_range()
    df["adx"]  = ta.trend.ADXIndicator(h, l, c, 14).adx()
    df["vm"]   = v.rolling(20).mean()
    df["vr"]   = v / df["vm"].replace(0, 1)
    df["br"]   = df["tbbase"] / df["volume"].replace(0, 1)
    df["body"] = abs(c - df["open"])
    df["rng"]  = h - l
    df["body_ratio"] = df["body"] / df["rng"].replace(0, 1)
    df["m5"]   = (c - c.shift(5)) / c.shift(5)
    df["m10"]  = (c - c.shift(10)) / c.shift(10)
    # Bollinger Bands untuk squeeze detection
    bb = ta.volatility.BollingerBands(c, 20, 2)
    df["bb_upper"] = bb.bollinger_hband()
    df["bb_lower"] = bb.bollinger_lband()
    df["bb_width"] = (df["bb_upper"] - df["bb_lower"]) / c
    return df

# ═══════════════════════════════════════════════════════════════════
#  MARKET REGIME DETECTION
# ═══════════════════════════════════════════════════════════════════
def detect_regime(df_1h):
    """
    Deteksi: TRENDING_BULL | TRENDING_BEAR | SIDEWAYS | VOLATILE
    Berdasarkan 1H candle untuk macro view.
    """
    if df_1h is None or len(df_1h) < 55:
        return "UNKNOWN"
    df = run_ta(df_1h.copy())
    row = df.iloc[-2]
    p, e21, e50, e200 = row["close"], row["e21"], row["e50"], row["e200"]
    adx    = row["adx"]
    atr    = row["atr"]
    bb_w   = row["bb_width"]
    m10    = row["m10"]

    # Cek spread EMA21 vs EMA50
    ema_spread = abs(e21 - e50) / e50

    # Volatile: ATR/price sangat tinggi
    atr_pct = atr / p
    if atr_pct > 0.025:
        return "VOLATILE"

    # Sideways: ADX rendah ATAU EMA sangat berdekatan
    if adx < 18 or ema_spread < 0.003:
        return "SIDEWAYS"

    # Bollinger squeeze: market akan meledak tapi belum tahu arah
    if bb_w < 0.02:
        return "SQUEEZE"

    # Trending: ADX cukup kuat
    if adx >= 25:
        if p > e21 > e50 and m10 > 0:
            return "TRENDING_BULL"
        if p < e21 < e50 and m10 < 0:
            return "TRENDING_BEAR"

    # Mild trend
    if p > e50 and m10 > -0.002:
        return "MILD_BULL"
    if p < e50 and m10 < 0.002:
        return "MILD_BEAR"

    return "SIDEWAYS"

def btc_trend():
    """Deteksi trend BTC pada 5M untuk immediate bias."""
    try:
        df = run_ta(ohlcv("BTCUSDT", Client.KLINE_INTERVAL_5MINUTE, 100).copy())
        row = df.iloc[-2]
        p, e5, e9, e21 = row["close"], row["e5"], row["e9"], row["e21"]
        m5, adx = row["m5"], row["adx"]
        if p > e5 > e9 > e21 and m5 > 0.001: return "BULL"
        if p < e5 < e9 < e21 and m5 < -0.001: return "BEAR"
        if p > e9 > e21: return "MILD_BULL"
        if p < e9 < e21: return "MILD_BEAR"
        return "SIDEWAYS"
    except: return "UNKNOWN"

def update_macro():
    """Update semua macro indicators."""
    _macro["btc"] = btc_trend()
    try:
        df_1h = ohlcv("BTCUSDT", Client.KLINE_INTERVAL_1HOUR, 60)
        _macro["regime"] = detect_regime(df_1h)
    except:
        _macro["regime"] = "UNKNOWN"

# ═══════════════════════════════════════════════════════════════════
#  MULTI-TIMEFRAME CONFIRMATION
# ═══════════════════════════════════════════════════════════════════
def get_tf_bias(symbol, interval):
    """
    Ambil bias arah dari satu timeframe.
    Return: "BULL" | "BEAR" | "NEUTRAL"
    """
    try:
        df = run_ta(ohlcv(symbol, interval, 100).copy())
        if df is None or len(df) < 55:
            return "NEUTRAL"
        row = df.iloc[-2]
        p, e9, e21, e50 = row["close"], row["e9"], row["e21"], row["e50"]
        adx = row["adx"]
        m5  = row["m5"]
        mh  = row["mh"]

        # Hanya beri bias kuat jika ADX cukup
        if adx < 18:
            return "NEUTRAL"

        bull_pts = 0
        bear_pts = 0
        if p > e9 > e21:   bull_pts += 1
        if p < e9 < e21:   bear_pts += 1
        if p > e50:        bull_pts += 1
        else:              bear_pts += 1
        if m5 > 0.002:     bull_pts += 1
        elif m5 < -0.002:  bear_pts += 1
        if mh > 0:         bull_pts += 1
        elif mh < 0:       bear_pts += 1

        if bull_pts >= 3: return "BULL"
        if bear_pts >= 3: return "BEAR"
        return "NEUTRAL"
    except:
        return "NEUTRAL"

def multi_tf_confirm(symbol, direction):
    """
    Konfirmasi multi-timeframe.
    Syarat: 15M dan 1H harus searah dengan arah entry.
    Return: (confirmed: bool, detail: str)
    """
    bias_15m = get_tf_bias(symbol, Client.KLINE_INTERVAL_15MINUTE)
    bias_1h  = get_tf_bias(symbol, Client.KLINE_INTERVAL_1HOUR)

    # Konversi direction ke bull/bear
    expected = "BULL" if direction == "LONG" else "BEAR"

    details = f"15M:{bias_15m} 1H:{bias_1h}"

    # 15M HARUS searah
    if bias_15m != expected:
        return False, f"15M berlawanan ({details})"

    # 1H boleh NEUTRAL tapi tidak boleh berlawanan
    if direction == "LONG" and bias_1h == "BEAR":
        return False, f"1H berlawanan ({details})"
    if direction == "SHORT" and bias_1h == "BULL":
        return False, f"1H berlawanan ({details})"

    return True, details

# ═══════════════════════════════════════════════════════════════════
#  ANTI-CHASE / SMART ENTRY (Pullback & Retest)
# ═══════════════════════════════════════════════════════════════════
def is_chasing(df, direction):
    """
    Deteksi apakah harga sudah terlalu jauh bergerak (chasing candle besar).
    Return True jika JANGAN masuk (sedang chase).
    """
    row  = df.iloc[-2]
    prev = df.iloc[-3]

    body_ratio = row["body_ratio"]   # Body vs Range candle terakhir
    atr        = row["atr"]
    move       = abs(row["close"] - prev["close"])

    # Jika candle terakhir body-nya > 70% range DAN move > 1.5x ATR → chase
    if body_ratio > 0.7 and move > atr * 1.5:
        return True, f"Chase: body={body_ratio:.0%} move={move/atr:.1f}xATR"

    # Cek apakah sudah jauh dari EMA9 (overextended)
    p, e9 = row["close"], row["e9"]
    dist_from_e9 = abs(p - e9) / e9

    # Lebih dari 1.5% dari EMA9 = overextended
    if dist_from_e9 > 0.015:
        return True, f"Overextended {dist_from_e9:.1%} dari EMA9"

    return False, ""

def has_pullback_retest(df, direction):
    """
    Cek apakah ada pullback/retest sebelum entry.
    LONG: harga pernah menyentuh EMA9/EMA21 dalam 3 candle terakhir lalu bounce
    SHORT: harga pernah menyentuh EMA9/EMA21 dalam 3 candle terakhir lalu reject
    Return: (True/False, detail)
    """
    recent = df.iloc[-5:-1]  # 4 candle sebelum confirmed candle

    if direction == "LONG":
        for _, r in recent.iterrows():
            # Candle menyentuh EMA9 atau EMA21 dari bawah (low dekat EMA)
            touch_e9  = r["low"] <= r["e9"]  * 1.003
            touch_e21 = r["low"] <= r["e21"] * 1.003
            if touch_e9 or touch_e21:
                return True, "Retest EMA↑"
        return False, "Belum retest EMA"

    else:  # SHORT
        for _, r in recent.iterrows():
            # Candle menyentuh EMA9 atau EMA21 dari atas (high dekat EMA)
            touch_e9  = r["high"] >= r["e9"]  * 0.997
            touch_e21 = r["high"] >= r["e21"] * 0.997
            if touch_e9 or touch_e21:
                return True, "Retest EMA↓"
        return False, "Belum retest EMA"

# ═══════════════════════════════════════════════════════════════════
#  FALSE BREAKOUT DETECTION
# ═══════════════════════════════════════════════════════════════════
def is_false_breakout(df, direction):
    """
    Deteksi false breakout via:
    1. Volume tidak mendukung breakout
    2. Candle dengan wick panjang (rejection)
    3. Breakout dari BB tapi langsung berbalik
    """
    row  = df.iloc[-2]
    prev = df.iloc[-3]

    # Volume harus >= 1.5x rata-rata untuk breakout valid
    if row["vr"] < 1.5:
        # Breakout volume rendah = suspek
        if abs(row["m5"]) > 0.005:  # Tapi gerakan besar
            return True, f"Low-vol breakout (vr={row['vr']:.1f}x)"

    # Wick rejection: wick > 2x body
    body = row["body"]
    if direction == "LONG":
        upper_wick = row["high"] - max(row["close"], row["open"])
        if upper_wick > body * 2 and body > 0:
            return True, f"Upper wick rejection ({upper_wick/body:.1f}x body)"
    else:
        lower_wick = min(row["close"], row["open"]) - row["low"]
        if lower_wick > body * 2 and body > 0:
            return True, f"Lower wick rejection ({lower_wick/body:.1f}x body)"

    # Bollinger Band false breakout
    if direction == "LONG":
        if prev["close"] > prev["bb_upper"] and row["close"] < row["bb_upper"]:
            return True, "BB false breakout ↑"
    else:
        if prev["close"] < prev["bb_lower"] and row["close"] > row["bb_lower"]:
            return True, "BB false breakout ↓"

    return False, ""

# ═══════════════════════════════════════════════════════════════════
#  ATR DYNAMIC TP/SL CALCULATOR
# ═══════════════════════════════════════════════════════════════════
def calc_tp_sl(entry_price, direction, atr):
    """
    Hitung TP dan SL berbasis ATR.
    SL = ATR × 1.2
    TP = ATR × 2.5
    RR = TP/SL = 2.08x (memenuhi MIN_RR 2.0)
    """
    sl_dist = atr * ATR_SL_MULT
    tp_dist = atr * ATR_TP_MULT

    rr = tp_dist / sl_dist if sl_dist > 0 else 0

    if direction == "LONG":
        tp = entry_price + tp_dist
        sl = entry_price - sl_dist
    else:
        tp = entry_price - tp_dist
        sl = entry_price + sl_dist

    return tp, sl, rr

# ═══════════════════════════════════════════════════════════════════
#  CONFIDENCE SCORING (0–100)
# ═══════════════════════════════════════════════════════════════════
def score_signal(df, direction, multi_tf_ok, pullback_ok, regime, btc_bias):
    """
    Hitung confidence score 0–100.
    Hanya trade jika >= 70 (atau lebih tinggi saat adaptive mode).
    """
    if df is None or len(df) < 55:
        return 0, []

    row, prev, prev2 = df.iloc[-2], df.iloc[-3], df.iloc[-4]
    p    = row["close"]
    e5, e9, e21, e50 = row["e5"], row["e9"], row["e21"], row["e50"]
    rsi  = row["rsi"]
    mh, mh_p, mh_p2 = row["mh"], prev["mh"], prev2["mh"]
    vr   = row["vr"]
    m5   = row["m5"]
    adx  = row["adx"]
    br   = row["br"]   # Buy ratio (untuk LONG, br > 0.5 bagus)
    bb_w = row["bb_width"]

    score  = 0
    sigs   = []
    long_ok  = direction == "LONG"

    # ── SECTION 1: Multi-TF Alignment (bobot tinggi) ──
    if multi_tf_ok:
        score += 20
        sigs.append("MTF✓")
    else:
        score -= 15  # Penalti besar jika TF tidak searah
        sigs.append("MTF✗")

    # ── SECTION 2: EMA Stack (trend structure) ──
    if long_ok:
        if p > e5 > e9 > e21 > e50:
            score += 25; sigs.append("EMA5stack↑")
        elif p > e9 > e21 > e50:
            score += 18; sigs.append("EMA4stack↑")
        elif p > e21 > e50:
            score += 10; sigs.append("EMA3↑")
        # Penalti jika EMA21 dan EMA50 terlalu dekat (chop)
        ema_spread = abs(e21 - e50) / e50
        if ema_spread < EMA_SPREAD_MIN:
            score -= 10; sigs.append(f"Chop({ema_spread:.3f})")
    else:
        if p < e5 < e9 < e21 < e50:
            score += 25; sigs.append("EMA5stack↓")
        elif p < e9 < e21 < e50:
            score += 18; sigs.append("EMA4stack↓")
        elif p < e21 < e50:
            score += 10; sigs.append("EMA3↓")
        ema_spread = abs(e21 - e50) / e50
        if ema_spread < EMA_SPREAD_MIN:
            score -= 10; sigs.append(f"Chop({ema_spread:.3f})")

    # ── SECTION 3: Momentum ──
    if long_ok:
        if m5 > 0.006:   score += 15; sigs.append(f"Mom+{m5*100:.1f}%")
        elif m5 > 0.003: score += 8
        elif m5 < -0.003: score -= 8  # Momentum berlawanan = penalti
    else:
        if m5 < -0.006:  score += 15; sigs.append(f"Mom{m5*100:.1f}%")
        elif m5 < -0.003: score += 8
        elif m5 > 0.003:  score -= 8

    # ── SECTION 4: MACD ──
    if long_ok:
        if mh_p <= 0 and mh > 0:            score += 18; sigs.append("MACD_X↑")
        elif mh > 0 and mh > mh_p > mh_p2:  score += 12; sigs.append("MACD↑↑")
        elif mh < 0:                          score -= 5
    else:
        if mh_p >= 0 and mh < 0:            score += 18; sigs.append("MACD_X↓")
        elif mh < 0 and mh < mh_p < mh_p2:  score += 12; sigs.append("MACD↓↓")
        elif mh > 0:                          score -= 5

    # ── SECTION 5: Volume Quality ──
    if vr >= 2.5:
        score += 12; sigs.append(f"Vol{vr:.1f}x")
    elif vr >= 1.5:
        score += 6
    elif vr < 1.0:
        score -= 8; sigs.append(f"LowVol({vr:.1f}x)")

    # Buy/Sell pressure alignment
    if long_ok and br > 0.6:   score += 8; sigs.append(f"BuyPres{br:.0%}")
    if not long_ok and br < 0.4: score += 8; sigs.append(f"SellPres{br:.0%}")

    # ── SECTION 6: RSI ──
    if long_ok:
        if 45 <= rsi <= 65:    score += 10; sigs.append(f"RSI{rsi:.0f}ok")
        elif rsi > 75:          score -= 20; sigs.append(f"RSI_OB{rsi:.0f}")
        elif rsi < 35:          score += 5;  sigs.append(f"RSI_OS{rsi:.0f}")  # Oversold bounce
    else:
        if 35 <= rsi <= 55:    score += 10; sigs.append(f"RSI{rsi:.0f}ok")
        elif rsi < 25:          score -= 20; sigs.append(f"RSI_OS{rsi:.0f}")
        elif rsi > 65:          score += 5;  sigs.append(f"RSI_OB{rsi:.0f}")

    # ── SECTION 7: ADX Strength ──
    if adx >= 35:    score += 12; sigs.append(f"ADX{adx:.0f}")
    elif adx >= 25:  score += 7
    elif adx >= 20:  score += 3
    # adx < 20 sudah di-filter di scan_one, tapi double-check
    elif adx < 20:   score -= 15; sigs.append(f"WeakADX{adx:.0f}")

    # ── SECTION 8: Pullback / Smart Entry ──
    if pullback_ok:
        score += 10; sigs.append("Pullback✓")
    else:
        score -= 5

    # ── SECTION 9: BTC Macro Alignment ──
    if long_ok and btc_bias in ("BULL", "MILD_BULL"):
        score += 8; sigs.append("BTC↑")
    elif long_ok and btc_bias in ("BEAR",):
        score -= 10; sigs.append("BTC↓!")
    elif not long_ok and btc_bias in ("BEAR", "MILD_BEAR"):
        score += 8; sigs.append("BTC↓")
    elif not long_ok and btc_bias in ("BULL",):
        score -= 10; sigs.append("BTC↑!")

    # ── SECTION 10: Market Regime Bonus/Penalty ──
    if regime in ("TRENDING_BULL", "TRENDING_BEAR"):
        score += 8  # Trending market = bonus
    elif regime == "SIDEWAYS":
        score -= 30  # Sideways = penalti besar
    elif regime == "VOLATILE":
        score -= 10  # Volatile = penalti sedang

    # ── SECTION 11: Bollinger Width (avoid squeeze breakout) ──
    if bb_w < 0.015:
        score -= 8; sigs.append("BBSqueeze")

    return max(0, min(100, score)), sigs[:5]

# ═══════════════════════════════════════════════════════════════════
#  MAIN SIGNAL FUNCTION
# ═══════════════════════════════════════════════════════════════════
def signal(df, df_5m, symbol=None):
    """
    Signal generator utama dengan semua filter.
    Return: (direction, confidence, signals, atr, tp, sl)
    """
    if df is None or len(df) < 55:
        return None, 0, [], 0.0, 0.0, 0.0

    row = df.iloc[-2]
    p, e9, e21, e50 = row["close"], row["e9"], row["e21"], row["e50"]
    rsi, adx, atr   = row["rsi"], row["adx"], row["atr"]
    vr               = row["vr"]

    # ── HARD FILTERS (langsung return None) ──

    # 1. Volume minimum
    if vr < 1.0:
        return None, 0, ["LowVol"], atr, 0, 0

    # 2. ADX minimum (market tidak trending)
    if adx < ADX_MIN:
        return None, 0, [f"ADX<{ADX_MIN}"], atr, 0, 0

    # 3. EMA spread terlalu kecil (choppy market)
    ema_spread = abs(e21 - e50) / e50
    if ema_spread < EMA_SPREAD_MIN:
        return None, 0, ["Chop/Flat"], atr, 0, 0

    # 4. Market regime filter
    regime = _macro.get("regime", "UNKNOWN")
    if regime == "SIDEWAYS":
        return None, 0, ["Sideways"], atr, 0, 0

    # 5. Pattern block check
    if symbol:
        blocked, reason = is_pattern_blocked(symbol)
        if blocked:
            return None, 0, [f"Blocked:{reason}"], atr, 0, 0

    # ── TENTUKAN ARAH BIAS ──
    bull_base = p > e9 > e21
    bear_base = p < e9 < e21

    if not bull_base and not bear_base:
        return None, 0, ["NoTrend"], atr, 0, 0

    direction = "LONG" if bull_base and not bear_base else "SHORT"
    if bull_base and bear_base:
        direction = None  # Ambigu
    if direction is None:
        return None, 0, ["Ambiguous"], atr, 0, 0

    # ── MULTI-TIMEFRAME CONFIRMATION ──
    if symbol:
        mtf_ok, mtf_detail = multi_tf_confirm(symbol, direction)
    else:
        mtf_ok, mtf_detail = False, "no_symbol"

    if not mtf_ok:
        return None, 0, [f"MTF✗:{mtf_detail}"], atr, 0, 0

    # ── ANTI-CHASE ──
    chase, chase_reason = is_chasing(df, direction)
    if chase:
        return None, 0, [f"Chase:{chase_reason}"], atr, 0, 0

    # ── FALSE BREAKOUT ──
    fbo, fbo_reason = is_false_breakout(df, direction)
    if fbo:
        return None, 0, [f"FBO:{fbo_reason}"], atr, 0, 0

    # ── PULLBACK CHECK ──
    pb_ok, pb_detail = has_pullback_retest(df, direction)

    # ── CONFIDENCE SCORING ──
    btc_bias = _macro.get("btc", "UNKNOWN")
    score, sigs = score_signal(df, direction, mtf_ok, pb_ok, regime, btc_bias)

    # ATR Dynamic TP/SL
    px_live = price_live(symbol) if symbol else p
    if px_live == 0: px_live = p
    tp, sl, rr = calc_tp_sl(px_live, direction, atr)

    # Cek RR minimum
    if rr < MIN_RR:
        return None, score, [f"RR<{MIN_RR}({rr:.1f})"], atr, 0, 0

    # Threshold confidence (adaptive)
    min_conf = effective_confidence_min()
    if score < min_conf:
        return None, score, [f"Score<{min_conf}({score})"] + sigs, atr, tp, sl

    return direction, score, sigs, atr, tp, sl

# ═══════════════════════════════════════════════════════════════════
#  KILL SWITCH
# ═══════════════════════════════════════════════════════════════════
def ks_check():
    k, now = _ks, time.time()
    if k["active"] and now >= k["resume"]:
        k["active"] = False; k["consec"] = 0
    if k["active"]: return True, k["reason"]
    day = now - (now % 86400)
    if day > k["day_reset"]: k["daily"] = 0.0; k["day_reset"] = day
    if k["daily"] <= DAILY_LOSS:
        k["active"] = True
        k["reason"]  = f"daily({k['daily']:.2f})"
        k["resume"]  = day + 86400
        return True, k["reason"]
    if k["consec"] >= CONSEC_MAX:
        k["active"] = True
        k["reason"]  = f"consec({k['consec']})"
        k["resume"]  = now + CONSEC_PAUSE
        return True, k["reason"]
    return False, ""

def ks_upd(pnl):
    _ks["daily"] += pnl
    if pnl >= 0:
        _ks["consec"] = 0
    else:
        _ks["consec"] += 1

def update_streaks(pnl):
    """Update win/loss streak untuk adaptive risk."""
    if pnl >= 0:
        _stats["streak_win"]  += 1
        _stats["streak_loss"]  = 0
        if _stats["streak_win"] >= STREAK_WIN_RESET and _stats["streak_loss"] == 0:
            pass  # sudah reset
    else:
        _stats["streak_loss"] += 1
        _stats["streak_win"]   = 0

# ═══════════════════════════════════════════════════════════════════
#  DRY RUN OPEN / CLOSE
# ═══════════════════════════════════════════════════════════════════
def live_open(sym, direction, score, sigs, price, atr, tp, sl):
    with _lock:
        if sym in live_positions or len(live_positions) >= MAX_POSITIONS:
            return
        live_positions[sym] = {"_r": True}

    try:
        q_val       = qty(sym, price)
        entry_price = price
    except Exception as e:
        print(f" ❌ Gagal Open {sym}: {e}")
        with _lock: live_positions.pop(sym, None)
        return

    pos = {
        "side":       direction,
        "entry":      entry_price,
        "qty":        q_val,
        "open_time":  time.time(),
        "score":      score,
        "sigs":       sigs,
        "tp":         tp,
        "sl":         sl,
        "atr":        atr,
        "open_hour":  datetime.now().hour,
        "regime":     _macro.get("regime", "UNKNOWN"),
    }
    with _lock: live_positions[sym] = pos

    rr = (tp - entry_price) / (entry_price - sl) if direction == "LONG" and (entry_price - sl) != 0 else \
         (entry_price - tp) / (sl - entry_price) if direction == "SHORT" and (sl - entry_price) != 0 else 0

    size_note = " [ADAPTIVE 50%]" if effective_order_usdt() < ORDER_USDT else ""
    d = "🟢" if direction == "LONG" else "🔴"
    print(f"\n  {d} [DRY] {sym} {direction} @{entry_price:.6g}{size_note}")
    print(f"      Score:{score} | RR:1:{rr:.2f}")
    print(f"      TP:{tp:.6g}(+{abs(tp-entry_price)/entry_price*100:.2f}%) "
          f"SL:{sl:.6g}(-{abs(sl-entry_price)/entry_price*100:.2f}%)")
    print(f"      Sigs: {' | '.join(sigs)}")
    _stats["trades"] += 1

def live_close(sym, reason, price=None):
    with _lock:
        pos = live_positions.pop(sym, None)
    if pos is None or pos.get("_r"): return

    if price is None: price = price_live(sym)
    side, entry, q_val = pos["side"], pos["entry"], pos["qty"]
    entry_hour = pos.get("open_hour", datetime.now().hour)
    regime     = pos.get("regime", "UNKNOWN")

    gross_pnl = (price - entry) * q_val if side == "LONG" else (entry - price) * q_val
    open_fee  = (entry * q_val) * FUTURES_FEE_PCT
    close_fee = (price * q_val) * FUTURES_FEE_PCT
    total_fee = open_fee + close_fee
    pnl       = gross_pnl - total_fee

    pct  = (price - entry) / entry * 100 if side == "LONG" else (entry - price) / entry * 100
    hold = time.time() - pos["open_time"]
    e    = "🟢" if pnl >= 0 else "🔴"

    print(f"  {e} [DRY] {sym} {side} CLOSE — {reason}")
    print(f"     {entry:.6g}→{price:.6g} ({pct:+.3f}%) hold:{hold:.0f}s")
    print(f"     PnL Net:{pnl:+.5f}U  [Kotor:{gross_pnl:+.5f}U | Fee:{total_fee:.5f}U]")

    _stats["pnl"]  += pnl
    _stats["hist"].append(pnl)
    ks_upd(pnl)
    update_streaks(pnl)

    if pnl >= 0:
        _stats["wins"] += 1
        if pnl > _stats["best"]: _stats["best"] = pnl
    else:
        _stats["losses"] += 1
        if pnl < _stats["worst"]: _stats["worst"] = pnl
        # Catat loss pattern
        record_loss_pattern(sym, entry_hour, regime)

    if "TakeProfit" in reason: _stats["tp_hit"] += 1
    elif "StopLoss" in reason: _stats["sl_hit"] += 1

    trade_log.append({
        "sym":    sym,
        "side":   side,
        "entry":  round(entry, 7),
        "exit":   round(price, 7),
        "pnl":    round(pnl, 5),
        "reason": reason,
        "hold":   int(hold),
        "score":  pos.get("score", 0),
        "regime": regime,
        "hour":   entry_hour,
    })
    set_cd(sym); _hot_syms.appendleft(sym); _rescan_q.put(1)
    print_inline()

    # Log adaptive state
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        print(f"  ⚠️  Adaptive Mode: {_stats['streak_loss']} loss beruntun — "
              f"size={effective_order_usdt():.1f}U "
              f"conf_min={effective_confidence_min()}")

# ═══════════════════════════════════════════════════════════════════
#  MONITOR — ATR DYNAMIC TP/SL
# ═══════════════════════════════════════════════════════════════════
def monitor_positions():
    for sym in list(live_positions.keys()):
        pos = live_positions.get(sym)
        if pos is None or pos.get("_r"): continue

        px = price_live(sym)
        if px == 0: continue

        side, entry = pos["side"], pos["entry"]
        tp, sl      = pos["tp"], pos["sl"]
        hold        = time.time() - pos["open_time"]
        prof_pct    = (px - entry) / entry if side == "LONG" else (entry - px) / entry

        # Cek TP
        if (side == "LONG"  and px >= tp) or \
           (side == "SHORT" and px <= tp):
            live_close(sym, "TakeProfit", px); continue

        # Cek SL
        if (side == "LONG"  and px <= sl) or \
           (side == "SHORT" and px >= sl):
            live_close(sym, "StopLoss", px); continue

        # Status print
        q_val   = pos["qty"]
        fee_est = (entry * q_val + px * q_val) * FUTURES_FEE_PCT
        pnl_now = prof_pct * entry * q_val - fee_est
        arrow   = "L" if side == "LONG" else "S"
        tp_dist = abs(tp - px) / abs(tp - entry) * 100 if abs(tp - entry) > 0 else 0
        print(f"   📌 {sym} {arrow}@{entry:.5g}→{px:.5g} "
              f"({prof_pct*100:+.2f}%) {pnl_now:+.4f}U "
              f"TP:{tp_dist:.0f}% away {hold:.0f}s [DRY]")

# ═══════════════════════════════════════════════════════════════════
#  SCANNER
# ═══════════════════════════════════════════════════════════════════
def scan_one(sym):
    try:
        time.sleep(SCAN_DELAY)
        if not ok_cooldown(sym): return None

        # Cek pattern block lebih awal
        blocked, _ = is_pattern_blocked(sym)
        if blocked: return None

        # Cek volume minimum
        tk = _ticker_cache
        if sym in tk and tk[sym]["vol"] < MIN_BASE_VOL: return None

        # Ambil dan proses 5M
        df_raw = ohlcv(sym, Client.KLINE_INTERVAL_5MINUTE, 120)
        if df_raw is None or len(df_raw) < 55: return None
        df = run_ta(df_raw.copy())

        row = df.iloc[-2]
        px  = row["close"]
        atr = row["atr"]

        # Sanity checks
        if px == 0: return None
        if atr / px > 0.03: return None   # ATR terlalu besar = terlalu volatile
        if row["adx"] < ADX_MIN: return None
        if row["vr"] < 1.0: return None

        # Run full signal (termasuk multi-TF)
        dir_, sc, sigs, atr_val, tp, sl = signal(df, df, sym)
        if dir_ is None or len(sigs) < 1: return None
        if tp == 0 or sl == 0: return None

        px_live = price_live(sym)
        if px_live == 0: return None

        # Hitung ulang TP/SL dengan harga live
        tp_live, sl_live, rr = calc_tp_sl(px_live, dir_, atr_val)
        if rr < MIN_RR: return None

        return (sym, dir_, sc, sigs, px_live, atr_val, tp_live, sl_live)
    except Exception as e:
        # print(f"  scan_one error {sym}: {e}")
        return None

def scan_batch(syms):
    res = []
    fut = {_executor.submit(scan_one, s): s for s in syms[:BATCH_SIZE]}
    try:
        for f in as_completed(fut, timeout=15):
            r = f.result(timeout=3)
            if r: res.append(r)
    except: pass
    return res

def top_movers(syms, n=15):
    tk, ss = tickers_all(), set(syms)
    mv = [
        (s, abs(d["pct"]))
        for s, d in tk.items()
        if s in ss and d["vol"] >= MIN_BASE_VOL
    ]
    return [s for s, _ in sorted(mv, key=lambda x: x[1], reverse=True)[:n]]

# ═══════════════════════════════════════════════════════════════════
#  PRINT / STATS
# ═══════════════════════════════════════════════════════════════════
def calc_stats():
    n  = _stats["wins"] + _stats["losses"]
    wr = _stats["wins"] / n * 100 if n else 0
    sh = md = 0.0
    if len(_stats["hist"]) >= 5:
        a  = np.array(list(_stats["hist"]))
        sd = float(np.std(a))
        sh = float(np.mean(a)) / sd if sd > 0 else 0.0
    if len(_stats["hist"]) >= 2:
        eq = np.cumsum(list(_stats["hist"]))
        md = float(np.min(eq - np.maximum.accumulate(eq)))
    # Profit Factor
    wins_total  = sum(p for p in _stats["hist"] if p > 0)
    loss_total  = abs(sum(p for p in _stats["hist"] if p < 0))
    pf = wins_total / loss_total if loss_total > 0 else float("inf")
    # Expectancy per trade
    avg_win  = wins_total / _stats["wins"]  if _stats["wins"]  > 0 else 0
    avg_loss = loss_total / _stats["losses"] if _stats["losses"] > 0 else 0
    exp = (wr/100) * avg_win - (1 - wr/100) * avg_loss
    return n, wr, sh, md, pf, exp

def print_inline():
    n, wr, sh, md, pf, exp = calc_stats()
    e = "💚" if _stats["pnl"] >= 0 else "🔴"
    streak_note = ""
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        streak_note = f" ⚠️ADAPT({_stats['streak_loss']}L)"
    print(f"      ┌ [v20.0] {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']} "
          f"{e}PnL:{_stats['pnl']:+.4f}U PF:{pf:.2f}{streak_note}")
    print(f"      └ TP:{_stats['tp_hit']} SL:{_stats['sl_hit']} "
          f"Sharpe:{sh:.2f} Exp:{exp:+.4f}U/T")

def print_full():
    n, wr, sh, md, pf, exp = calc_stats()
    sess = (time.time() - _stats["start"]) / 3600
    tph  = n / sess if sess > 0 else 0
    e    = "💚" if _stats["pnl"] >= 0 else "🔴"

    print(f"\n  {'─'*70}")
    print(f"   ✅ DRY RUN v20.0 [QUALITY OVER QUANTITY] — {sess*60:.0f}m | {tph:.1f}T/jam")
    print(f"   🎯 {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']}")
    print(f"   {e} PnL Net:{_stats['pnl']:+.5f}U "
          f"Best:{_stats['best']:+.5f} Worst:{_stats['worst']:+.5f}")
    print(f"   📊 Sharpe:{sh:.2f} MaxDD:{md:.5f}U ProfitFactor:{pf:.2f}")
    print(f"   💡 Expectancy:{exp:+.5f}U/trade")
    print(f"   🔔 TP Hit:{_stats['tp_hit']} SL Hit:{_stats['sl_hit']}")
    print(f"   ⚡ Streak: {_stats['streak_win']}W / {_stats['streak_loss']}L | "
          f"Adaptive: {'ON' if _stats['streak_loss'] >= STREAK_LOSS_TRIG else 'OFF'}")
    print(f"   🌍 Regime:{_macro.get('regime','?')} | BTC:{_macro.get('btc','?')}")

    if trade_log:
        print(f"   📋 Last 5 trade:")
        for t in trade_log[-5:]:
            em = "🟢" if t["pnl"] > 0 else "🔴"
            print(f"      {em} {t['sym']:<14} {t['side']} {t['pnl']:+.5f}U "
                  f"{t['hold']}s — {t['reason']} "
                  f"[Score:{t['score']} {t['regime']} H{t['hour']}]")

    # Loss Pattern Report
    if _stats["losses"] > 0:
        print(get_loss_pattern_report())

    print(f"  {'─'*70}")

def print_expectancy_math():
    """Cetak penjelasan matematika expectancy."""
    n, wr, sh, md, pf, exp = calc_stats()
    if n < 5:
        print("  [Math] Butuh minimal 5 trade untuk kalkulasi valid.")
        return

    wins_total  = sum(p for p in _stats["hist"] if p > 0)
    loss_total  = abs(sum(p for p in _stats["hist"] if p < 0))
    avg_win     = wins_total  / _stats["wins"]  if _stats["wins"]  > 0 else 0
    avg_loss    = loss_total  / _stats["losses"] if _stats["losses"] > 0 else 0

    print(f"\n  {'═'*70}")
    print(f"   💎 EXPECTANCY MATH")
    print(f"   ─────────────────────────────────────────────")
    print(f"   Win Rate      : {wr:.1f}%")
    print(f"   Avg Win       : {avg_win:+.5f}U")
    print(f"   Avg Loss      : {avg_loss:.5f}U")
    print(f"   Profit Factor : {pf:.3f}  (target >1.5)")
    print(f"   Expectancy    : {exp:+.5f}U/trade")
    print(f"   Sharpe        : {sh:.3f}    (target >0)")
    print(f"   MaxDrawdown   : {md:.5f}U")
    print(f"   ─────────────────────────────────────────────")
    print(f"   Formula: E = WR×AvgWin - (1-WR)×AvgLoss")
    print(f"          = {wr/100:.2f}×{avg_win:.5f} - {1-wr/100:.2f}×{avg_loss:.5f}")
    print(f"          = {exp:+.5f}U per trade")
    if exp > 0:
        print(f"   ✅ Expectancy POSITIF — bot menguntungkan secara matematis")
    else:
        print(f"   ❌ Expectancy NEGATIF — bot masih merugi per trade rata-rata")
    print(f"  {'═'*70}")

# ═══════════════════════════════════════════════════════════════════
#  DAEMON THREADS
# ═══════════════════════════════════════════════════════════════════
def t_monitor():
    while True:
        try:
            if live_positions: monitor_positions()
        except: pass
        time.sleep(MONITOR_INT)

def t_rescan(syms):
    while True:
        try:
            _rescan_q.get(timeout=30)
            time.sleep(1.0)  # Lebih lama dari v19
            slots = MAX_POSITIONS - len(live_positions)
            if slots <= 0 or ks_check()[0]: continue
            hot  = [s for s in _hot_syms if s not in live_positions]
            rest = [s for s in syms if s not in live_positions and s not in hot]
            res  = scan_batch((hot + rest)[:20])
            if res:
                for r in sorted(res, key=lambda x: x[2], reverse=True)[:slots]:
                    if len(live_positions) >= MAX_POSITIONS: break
                    sym, d, sc, sg, px, atr, tp, sl = r
                    live_open(sym, d, sc, sg, px, atr, tp, sl)
        except: pass

def t_macro():
    while True:
        try:
            update_macro()
        except: pass
        try:
            if time.time() - _macro["last_fng"] > 300:
                _macro["fng"] = int(requests.get(
                    "https://api.alternative.me/fng/?limit=1", timeout=5
                ).json()["data"][0]["value"])
                _macro["last_fng"] = time.time()
        except: pass
        time.sleep(10)

# ═══════════════════════════════════════════════════════════════════
#  MAIN LOOP
# ═══════════════════════════════════════════════════════════════════
def run_bot():
    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  ✅ DRY RUN v20.0 — QUALITY OVER QUANTITY                           ║")
    print("║  🎯 Multi-TF | ATR Dynamic TP/SL | Smart Entry | Loss Pattern Learn  ║")
    print("║  📊 RR ≥ 1:2 | Confidence ≥ 70 | ADX ≥ 20 | Adaptive Risk          ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")

    try:
        valid = {
            s["symbol"]
            for s in client.futures_exchange_info()["symbols"]
            if s["status"] == "TRADING"
        }
        syms = list(dict.fromkeys([s for s in SYMBOLS if s in valid]))
    except:
        syms = list(dict.fromkeys(SYMBOLS))

    threading.Thread(target=t_monitor,             daemon=True).start()
    threading.Thread(target=t_rescan, args=(syms,), daemon=True).start()
    threading.Thread(target=t_macro,               daemon=True).start()

    print("  ⏳ Warming up (5s)...")
    time.sleep(5)
    tickers_all()
    update_macro()

    cycle    = 0
    scan_idx = 0
    n_bat    = math.ceil(len(syms) / BATCH_SIZE)

    while True:
        cycle += 1
        slots  = MAX_POSITIONS - len(live_positions)
        regime = _macro.get("regime", "?")
        print(f"\n{'═'*70}")
        print(f"  #{cycle} {time.strftime('%H:%M:%S')} "
              f"Regime:{regime} BTC:{_macro['btc']} F&G:{_macro['fng']} "
              f"({len(live_positions)}/{MAX_POSITIONS}) "
              f"PnL:{_stats['pnl']:+.4f}U "
              f"Streak:{_stats['streak_loss']}L/{_stats['streak_win']}W")

        # Kill switch
        if (k := ks_check())[0]:
            print(f"  🚨 KS:{k[1]}")
            time.sleep(SCAN_INTERVAL)
            continue

        # Sideways global = no trade
        if regime == "SIDEWAYS":
            print(f"  ⏸  Market SIDEWAYS — skip scan")
            time.sleep(SCAN_INTERVAL * 2)
            continue

        if slots > 0:
            mv  = top_movers(syms, 15)
            mv  = [s for s in mv if s not in live_positions]
            bs  = scan_idx * BATCH_SIZE
            reg = [s for s in syms[bs:bs+BATCH_SIZE]
                   if s not in live_positions and s not in mv]
            scan_idx  = (scan_idx + 1) % n_bat
            scan_list = mv[:8] + reg[:5]

            try:   res = scan_batch(scan_list)
            except: res = []

            if res:
                res.sort(key=lambda x: x[2], reverse=True)
                for r in res[:slots]:
                    if len(live_positions) >= MAX_POSITIONS: break
                    sym, d, sc, sg, px, atr, tp, sl = r
                    rr = abs(tp - px) / abs(sl - px) if abs(sl - px) > 0 else 0
                    print(f"     ⭐ {sym} {d} Score:{sc} RR:1:{rr:.2f} "
                          f"ATR:{atr:.5g} {' | '.join(sg)}")
                    live_open(sym, d, sc, sg, px, atr, tp, sl)
            else:
                print(f"  🔍 Tidak ada setup A+ ditemukan — menunggu...")
        else:
            print(f"  ✅ Full ({MAX_POSITIONS}/{MAX_POSITIONS})")

        if cycle % 10 == 0: print_full()
        if cycle % 20 == 0: print_expectancy_math()
        time.sleep(SCAN_INTERVAL)

if __name__ == "__main__":
    run_bot()
