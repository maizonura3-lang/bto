"""
Bot Scalping v18.5.1 — DRY RUN LOG MODE (PAPER TRADING)
====================================================
- NORMAL MODE: Sinyal LONG dieksekusi LONG, sinyal SHORT dieksekusi SHORT.
  (INVERSE dihapus — karena inverse mode malah bikin bot kalah terus)

- ANALISIS ROOT CAUSE v18.4.0:
    * WR 27% dengan INVERSE aktif → sinyal asli sebenarnya BENAR, bot yang balik arah
    * HardSL:91 >> ExProfit:11 → entry berlawanan trend = banyak kena SL
    * TrailSL nutup di +$0.10 = SAMA dengan SL -$0.10 → expectancy = 0

- v18.5.1 PERUBAHAN KUNCI:
    ╔══════════════════════════════════════════════════════════════╗
    ║  PRINSIP: 1 PROFIT harus COVER minimal 1 SL                ║
    ║  → TrailSL worst-case net >= HardSL net                    ║
    ╚══════════════════════════════════════════════════════════════╝

    Dari log nyata:
      Net SL nyata  = $40 × 0.15% + fee = -$0.10
      Net TrailTP   = $40 × 0.342% - fee = +$0.097 ← KURANG DARI SL! bug utama

    Fix v18.5.1 (kalkulasi per notional $40, fee $0.04):
      HARD_SL_PCT    = 0.15%   → Net SL  = -$0.10
      EXTREME_TP_PCT = 0.65%   → Net TP  = +$0.22    (2.2× dari SL)
      TRAIL_ACTIVATE = 0.50%   → trail aktif pas sudah aman
      TRAIL_DISTANCE = 0.12%   → worst trail close @0.38% → net +$0.112 > SL ✅
      R:R = 2.2:1  |  Break-even WR = ~31%
      Expectancy @35%WR = +$0.012/trade ✅
      Expectancy @40%WR = +$0.028/trade ✅

    Perubahan lain:
      * INVERSE_MODE = False  ← ikuti sinyal TA asli
      * MIN_SCORE naik ke 65  ← sinyal paling kuat saja
      * MIN_VR naik ke 1.5    ← volume harus kuat
      * BR_LONG_MIN = 0.60    ← buyer dominan untuk LONG
      * BR_SHORT_MAX = 0.40   ← seller dominan untuk SHORT
      * ADX_MIN = 25          ← hanya entry saat ada trend jelas
      * Konfirmasi 15M        ← saring entry counter-trend
"""

import os, time, math, threading, queue
import requests
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from dotenv import load_dotenv
from binance.client import Client
import ta
import pandas as pd
import numpy as np

load_dotenv()
client = Client(os.getenv("API_KEY"), os.getenv("API_SECRET"))
client.FUTURES_URL = "https://testnet.binancefuture.com/fapi"

# ═══════════════════════════════════════════════════════
#  CONFIG v18.5.1
#  Prinsip: Net TrailSL worst-case >= Net HardSL
#  Kalkulasi @ notional $40 (ORDER_USDT=2, LEV=20), fee $0.04
# ═══════════════════════════════════════════════════════

INVERSE_MODE   = False   # ← NORMAL: ikuti sinyal TA asli

LEVERAGE       = 20
ORDER_USDT     = 2.0
MAX_POSITIONS  = 3

# ── TP / SL — disamakan dari cara bot LOSS ──────────────
#
#   Bot sebelumnya LOSS karena:
#     - Entry berlawanan sinyal (inverse) → sering kena SL gross 0.15%
#     - Trail nutup terlalu dini → net TrailTP < net SL
#
#   Sekarang kita BALIK logika loss itu jadi profit:
#     - Entry SEARAH sinyal → profit saat market bergerak sesuai TA
#     - SL tetap 0.15% (sesuai data nyata, tidak diubah)
#     - TP dinaikkan ke 0.65% supaya 1 TP = 2.2× dari 1 SL
#     - Trail diatur agar worst-case trail net SELALU > net SL
#
#   Net TP  (+0.65%): $40 × 0.0065 − $0.04 = +$0.22
#   Net SL  (−0.15%): $40 × 0.0015 + $0.04 = −$0.10
#   Net Trail worst : $40 × 0.0038 − $0.04 = +$0.112  ← > $0.10 ✅
# ──────────────────────────────────────────────────────
EXTREME_PROFIT_PCT = 0.0065   # +0.65% Take Profit
HARD_SL_PCT        = 0.0015   # -0.15% Hard Stop Loss (sama dengan data nyata)

# ── TRAILING STOP — dikalibrasi agar 1 trail >= 1 SL ───
#   TRAIL_ACTIVATE = 0.50%  → trail aktif setelah profit 0.50%
#   TRAIL_DISTANCE = 0.12%  → toleransi turun dari peak
#   Worst close    = 0.50% - 0.12% = 0.38%
#   Net trail min  = $40 × 0.0038 - $0.04 = +$0.112 > SL $0.10 ✅
TRAIL_ACTIVATE  = 0.0050   # Aktifkan trailing setelah profit 0.50%
TRAIL_DISTANCE  = 0.0012   # Tutup jika turun 0.12% dari peak

FUTURES_FEE_PCT = 0.0005   # Fee Taker Binance 0.05%

MIN_BASE_VOL   = 25_000_000
MIN_VR         = 1.5        # Volume harus kuat (naik dari 1.3)
BR_LONG_MIN    = 0.60       # Buyer dominan untuk LONG
BR_SHORT_MAX   = 0.40       # Seller dominan untuk SHORT
ADX_MIN        = 25         # Trend harus ada (ADX minimum)

SCAN_INTERVAL  = 1
MONITOR_INT    = 0.25
SCAN_DELAY     = 0.015
BATCH_SIZE     = 15
MAX_WORKERS    = 8

MIN_SCORE      = 65         # Sinyal paling kuat saja
MIN_GAP        = 15
COOLDOWN_SEC   = 3
TTL_5M         = 5
TTL_15M        = 30

DAILY_LOSS     = -8.0
CONSEC_MAX     = 6
CONSEC_PAUSE   = 60

# ═══════════════════════════════════════════════════════
#  SYMBOLS & STATE
# ═══════════════════════════════════════════════════════
SYMBOLS = [
    "BTCUSDT", "ETHUSDT", "BNBUSDT", "SOLUSDT", "XRPUSDT",
    "ADAUSDT", "DOGEUSDT", "AVAXUSDT", "TRXUSDT", "DOTUSDT",
    "LINKUSDT", "MATICUSDT", "LTCUSDT", "ATOMUSDT", "UNIUSDT",
    "NEARUSDT", "APTUSDT", "ARBUSDT", "OPUSDT", "INJUSDT",
    "SUIUSDT", "SEIUSDT", "FETUSDT", "WLDUSDT", "AAVEUSDT",
    "ORDIUSDT", "TONUSDT", "1000PEPEUSDT", "WIFUSDT", "JUPUSDT",
]
SYMBOLS = list(dict.fromkeys(SYMBOLS))

live_positions  = {}
trade_log       = []
_ohlcv_cache    = {}
_sym_cooldown   = {}
_ticker_cache   = {}
_ticker_ts      = 0
_lock           = threading.Lock()
_executor       = ThreadPoolExecutor(max_workers=MAX_WORKERS)
_rescan_q       = queue.Queue()
_hot_syms       = deque(maxlen=20)

_macro = {"fng": 50, "btc": "UNKNOWN", "last_fng": 0, "last_btc": 0}
_ks    = {"active": False, "reason": "", "resume": 0, "consec": 0, "daily": 0.0, "day_reset": 0}
_stats = {
    "trades": 0, "wins": 0, "losses": 0, "pnl": 0.0, "best": 0.0, "worst": 0.0,
    "extreme_tp": 0, "hard_sl": 0, "trail_sl": 0, "force": 0,
    "hist": deque(maxlen=200), "start": time.time(),
}

# ═══════════════════════════════════════════════════════
#  BINANCE UTILS
# ═══════════════════════════════════════════════════════
_precision_cache = {}
def get_precision(symbol):
    global _precision_cache
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

def qty(symbol, price):
    raw_qty = (ORDER_USDT * LEVERAGE) / price
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
                "pct": float(t["priceChangePercent"]),
                "vol": float(t["quoteVolume"]),
                "last": float(t["lastPrice"])
            } for t in raw
        }
        _ticker_ts = now
        return _ticker_cache
    except: return _ticker_cache

def ok_cooldown(sym): return (time.time() - _sym_cooldown.get(sym, 0)) >= COOLDOWN_SEC
def set_cd(sym): _sym_cooldown[sym] = time.time()

def ohlcv(symbol, interval, limit=100):
    key, now = (symbol, interval), time.time()
    ttl = TTL_5M if interval == Client.KLINE_INTERVAL_5MINUTE else TTL_15M
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
    c, h, l, v = df["close"], df["high"], df["low"], df["volume"]
    df["rsi"]  = ta.momentum.RSIIndicator(c, 14).rsi()
    df["mh"]   = ta.trend.MACD(c, 12, 26, 9).macd_diff()
    df["e5"]   = ta.trend.EMAIndicator(c, 5).ema_indicator()
    df["e9"]   = ta.trend.EMAIndicator(c, 9).ema_indicator()
    df["e21"]  = ta.trend.EMAIndicator(c, 21).ema_indicator()
    df["e50"]  = ta.trend.EMAIndicator(c, 50).ema_indicator()
    df["atr"]  = ta.volatility.AverageTrueRange(h, l, c, 14).average_true_range()
    df["adx"]  = ta.trend.ADXIndicator(h, l, c, 14).adx()
    df["vm"]   = v.rolling(20).mean()
    df["vr"]   = v / df["vm"].replace(0, 1)
    df["br"]   = df["tbbase"] / df["volume"].replace(0, 1)
    df["body"] = abs(c - df["open"])
    df["rng"]  = h - l
    df["br2"]  = df["body"] / df["rng"].replace(0, 1)
    df["m5"]   = (c - c.shift(5)) / c.shift(5)
    return df

def btc_trend():
    try:
        df = run_ta(ohlcv("BTCUSDT", Client.KLINE_INTERVAL_5MINUTE, 80).copy())
        row = df.iloc[-2]
        p, e5, e9, e21, m5 = row["close"], row["e5"], row["e9"], row["e21"], row["m5"]
        if p > e5 > e9 > e21 and m5 > 0.001: return "BULL"
        if p < e5 < e9 < e21 and m5 < -0.001: return "BEAR"
        if p > e9 > e21: return "MILD_BULL"
        if p < e9 < e21: return "MILD_BEAR"
        return "SIDEWAYS"
    except: return "UNKNOWN"

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
    _ks["consec"] = 0 if pnl >= 0 else _ks["consec"] + 1

# ═══════════════════════════════════════════════════════
#  KONFIRMASI 15M — saring entry counter-trend
# ═══════════════════════════════════════════════════════
def confirm_15m(symbol, direction):
    """
    Sinyal 5M harus dikonfirmasi searah dengan 15M.
    Mencegah entry yang melawan trend besar → penyebab utama HardSL.
    """
    try:
        df15 = run_ta(ohlcv(symbol, Client.KLINE_INTERVAL_15MINUTE, 60).copy())
        if df15 is None or len(df15) < 30:
            return True  # allow jika data tidak ada
        row = df15.iloc[-2]
        p, e9, e21, m5 = row["close"], row["e9"], row["e21"], row["m5"]
        if direction == "LONG":
            return (p > e9 and p > e21) or m5 > 0.002
        else:  # SHORT
            return (p < e9 and p < e21) or m5 < -0.002
    except:
        return True

# ═══════════════════════════════════════════════════════
#  SIGNAL — ikuti sinyal TA asli (BUKAN dibalik)
# ═══════════════════════════════════════════════════════
def signal(df, symbol=None):
    """
    v18.5.1: Sinyal TA asli, filter lebih ketat.
    Prinsip: hanya masuk saat trend kuat + volume kuat + BR mendukung + 15M searah.
    """
    if df is None or len(df) < 55: return None, 0, [], 0.0
    row, prev, prev2 = df.iloc[-2], df.iloc[-3], df.iloc[-4]
    p, e5, e9, e21, e50 = row["close"], row["e5"], row["e9"], row["e21"], row["e50"]
    rsi, mh, mh_p, mh_p2 = row["rsi"], row["mh"], prev["mh"], prev2["mh"]
    vr, br, m5, body, atr, adx = row["vr"], row["br"], row["m5"], row["br2"], row["atr"], row["adx"]

    # ── Filter volume: hanya masuk saat volume kuat ────
    if vr < MIN_VR: return None, 0, [], atr

    # ── Filter ADX: hanya entry saat ada trend jelas ───
    # Pasar choppy/sideways → skip, karena SL sering kena random
    if adx < ADX_MIN: return None, 0, [], atr

    lp = sp = 0
    sl, ss = [], []

    # ── EMA Stack ──────────────────────────────────────
    if p > e5 > e9 > e21 > e50:   lp += 35; sl.append("EMA_stack↑")
    elif p > e5 > e9 > e21:       lp += 25; sl.append("EMA↑↑")
    if p < e5 < e9 < e21 < e50:   sp += 35; ss.append("EMA_stack↓")
    elif p < e5 < e9 < e21:       sp += 25; ss.append("EMA↓↓")

    # ── Momentum ───────────────────────────────────────
    if m5 > 0.005:    lp += 28; sl.append(f"Mom+{m5*100:.1f}%")
    elif m5 > 0.003:  lp += 20; sl.append(f"Mom+{m5*100:.1f}%")
    if m5 < -0.005:   sp += 28; ss.append(f"Mom{m5*100:.1f}%")
    elif m5 < -0.003: sp += 20; ss.append(f"Mom{m5*100:.1f}%")

    # ── MACD ───────────────────────────────────────────
    if mh_p <= 0 and mh > 0:             lp += 25; sl.append("MACD_X↑")
    elif mh > 0 and mh > mh_p > mh_p2:   lp += 20; sl.append("MACD↑↑")
    if mh_p >= 0 and mh < 0:             sp += 25; ss.append("MACD_X↓")
    elif mh < 0 and mh < mh_p < mh_p2:   sp += 20; ss.append("MACD↓↓")

    # ── Volume Ratio ───────────────────────────────────
    if vr >= 3.0:   lp += 15; sp += 15; sl.append(f"Vol{vr:.1f}x"); ss.append(f"Vol{vr:.1f}x")
    elif vr >= 2.0: lp += 10; sp += 10; sl.append(f"Vol{vr:.1f}x"); ss.append(f"Vol{vr:.1f}x")

    # ── Buy/Sell Ratio — disamakan cara loss jadi profit
    #   Saat bot LOSS: entry berlawanan BR → kalah
    #   Sekarang: hanya entry SEARAH BR yang kuat
    if br > 0.65:   lp += 22; sl.append(f"Buy{br:.0%}")
    elif br > 0.60: lp += 15; sl.append(f"Buy{br:.0%}")
    if br < 0.35:   sp += 22; ss.append(f"Sell{1-br:.0%}")
    elif br < 0.40: sp += 15; ss.append(f"Sell{1-br:.0%}")

    # ── RSI Filter ─────────────────────────────────────
    if rsi > 75:   lp = int(lp * 0.3); sp += 25; ss.append(f"RSI_OB{rsi:.0f}")
    elif rsi < 25: sp = int(sp * 0.3); lp += 25; sl.append(f"RSI_OS{rsi:.0f}")

    # ── ADX bonus saat trend sangat kuat ───────────────
    if adx > 40:   lp += 12; sp += 12; sl.append(f"ADX{adx:.0f}"); ss.append(f"ADX{adx:.0f}")
    elif adx > 30: lp += 7;  sp += 7

    btc    = _macro["btc"]
    btc_sw = btc in ("SIDEWAYS", "UNKNOWN")
    thresh = 50 if btc_sw else MIN_SCORE
    gap    = abs(lp - sp)

    # ── LONG entry — semua kondisi harus terpenuhi ─────
    if lp > sp and lp >= thresh and gap >= MIN_GAP:
        if br < BR_LONG_MIN:
            return None, lp, [], atr          # BR tidak mendukung LONG
        if symbol and not confirm_15m(symbol, "LONG"):
            return None, lp, [], atr          # 15M counter-trend
        return "LONG", lp, sl[:3], atr

    # ── SHORT entry — semua kondisi harus terpenuhi ────
    if sp > lp and sp >= thresh and gap >= MIN_GAP:
        if br > BR_SHORT_MAX:
            return None, sp, [], atr          # BR tidak mendukung SHORT
        if symbol and not confirm_15m(symbol, "SHORT"):
            return None, sp, [], atr          # 15M counter-trend
        return "SHORT", sp, ss[:3], atr

    return None, max(lp, sp), [], atr


# ═══════════════════════════════════════════════════════
#  DRY RUN OPEN / CLOSE
# ═══════════════════════════════════════════════════════
def live_open(sym, direction, score, sigs, price, atr):
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
        "side":         direction,
        "entry":        entry_price,
        "qty":          q_val,
        "open_time":    time.time(),
        "score":        score,
        "sigs":         sigs,
        "atr":          atr,
        "trail_active": False,
        "peak_prof":    0.0,
    }
    with _lock: live_positions[sym] = pos

    notional = entry_price * q_val
    net_tp   = notional * EXTREME_PROFIT_PCT - notional * FUTURES_FEE_PCT * 2
    net_sl   = notional * HARD_SL_PCT        + notional * FUTURES_FEE_PCT * 2
    net_trail_worst = notional * (TRAIL_ACTIVATE - TRAIL_DISTANCE) - notional * FUTURES_FEE_PCT * 2

    d = "🟢" if direction == "LONG" else "🔴"
    print(f"\n  {d} [DRY RUN] {sym} {direction} @{entry_price:.6g}")
    print(f"      TP:+{EXTREME_PROFIT_PCT*100:.2f}%(+${net_tp:.3f}) | "
          f"SL:-{HARD_SL_PCT*100:.2f}%(-${net_sl:.3f}) | "
          f"Trail@{TRAIL_ACTIVATE*100:.1f}% dist{TRAIL_DISTANCE*100:.2f}% "
          f"worst+${net_trail_worst:.3f}")
    _stats["trades"] += 1


def live_close(sym, reason, price=None):
    with _lock:
        pos = live_positions.pop(sym, None)
    if pos is None or pos.get("_r"): return

    if price is None: price = price_live(sym)
    side, entry, q_val = pos["side"], pos["entry"], pos["qty"]

    gross_pnl = (price - entry) * q_val if side == "LONG" else (entry - price) * q_val
    open_fee  = (entry * q_val) * FUTURES_FEE_PCT
    close_fee = (price * q_val) * FUTURES_FEE_PCT
    total_fee = open_fee + close_fee
    pnl       = gross_pnl - total_fee

    pct  = (price - entry) / entry * 100 if side == "LONG" else (entry - price) / entry * 100
    hold = time.time() - pos["open_time"]
    e    = "🟢" if pnl >= 0 else "🔴"

    print(f"  {e} [DRY RUN] {sym} {side} CLOSE — {reason}")
    print(f"     {entry:.6g}→{price:.6g} ({pct:+.3f}%) hold:{hold:.0f}s | "
          f"PnL Bersih:{pnl:+.5f}U (Fee:{total_fee:.5f}U)")

    _stats["pnl"]  += pnl
    _stats["hist"].append(pnl)
    ks_upd(pnl)

    if pnl >= 0:
        _stats["wins"] += 1
        if pnl > _stats["best"]: _stats["best"] = pnl
    else:
        _stats["losses"] += 1
        if pnl < _stats["worst"]: _stats["worst"] = pnl

    if "ExtremeProfit" in reason: _stats["extreme_tp"] += 1
    elif "HardSL"      in reason: _stats["hard_sl"]    += 1
    elif "TrailSL"     in reason: _stats["trail_sl"]   += 1

    trade_log.append({
        "sym":    sym,
        "side":   side,
        "entry":  round(entry, 7),
        "exit":   round(price, 7),
        "pnl":    round(pnl, 5),
        "reason": reason,
        "hold":   int(hold),
    })
    set_cd(sym); _hot_syms.appendleft(sym); _rescan_q.put(1)
    print_inline()


# ═══════════════════════════════════════════════════════
#  MONITOR — v18.5.1 trailing stop terkalibrasi
# ═══════════════════════════════════════════════════════
def monitor_positions():
    for sym in list(live_positions.keys()):
        pos = live_positions.get(sym)
        if pos is None or pos.get("_r"): continue

        px = price_live(sym)
        if px == 0: continue

        side, entry = pos["side"], pos["entry"]
        hold        = time.time() - pos["open_time"]

        prof_pct = (px - entry) / entry if side == "LONG" else (entry - px) / entry

        # Update peak
        if prof_pct > pos["peak_prof"]:
            pos["peak_prof"] = prof_pct

        # Aktifkan trailing
        if not pos["trail_active"] and prof_pct >= TRAIL_ACTIVATE:
            pos["trail_active"] = True
            q_val   = pos["qty"]
            net_now = prof_pct * entry * q_val - (entry * q_val + px * q_val) * FUTURES_FEE_PCT
            print(f"   🔔 {sym} TRAIL AKTIF @{prof_pct*100:.2f}% net+${net_now:.4f} "
                  f"— worst close@{(TRAIL_ACTIVATE-TRAIL_DISTANCE)*100:.2f}%")

        # Cek trailing stop
        if pos["trail_active"]:
            drawdown = pos["peak_prof"] - prof_pct
            if drawdown >= TRAIL_DISTANCE:
                live_close(sym, f"TrailSL(peak:{pos['peak_prof']*100:.2f}%)", px)
                continue

        # Hard TP & SL
        if prof_pct >= EXTREME_PROFIT_PCT:
            live_close(sym, "ExtremeProfit", px); continue
        if prof_pct <= -HARD_SL_PCT:
            live_close(sym, "HardSL", px); continue

        # Status print
        q_val   = pos["qty"]
        fee_est = (entry * q_val + px * q_val) * FUTURES_FEE_PCT
        pnl_now = prof_pct * entry * q_val - fee_est
        trail_s = f" TRAIL@peak{pos['peak_prof']*100:.2f}%" if pos["trail_active"] else ""
        arrow   = "L" if side == "LONG" else "S"
        print(f"   📌 {sym} {arrow}@{entry:.5g}→{px:.5g}"
              f"({prof_pct*100:+.2f}%){trail_s} {pnl_now:+.4f}U {hold:.0f}s [DRY]")


# ═══════════════════════════════════════════════════════
#  SCANNER & THREAD ENGINE
# ═══════════════════════════════════════════════════════
def scan_one(sym):
    try:
        time.sleep(SCAN_DELAY)
        if not ok_cooldown(sym): return None
        tk = _ticker_cache
        if sym in tk and tk[sym]["vol"] < MIN_BASE_VOL: return None
        df      = run_ta(ohlcv(sym, Client.KLINE_INTERVAL_5MINUTE, 100).copy())
        px      = df["close"].iloc[-2]
        atr     = df["atr"].iloc[-2]
        if px == 0 or atr / px > 0.03: return None
        dir_, sc, sigs, atr_val = signal(df, sym)
        if dir_ is None or len(sigs) < 1: return None
        px_live = price_live(sym)
        if px_live == 0: return None
        return (sym, dir_, sc, sigs, px_live, atr_val)
    except: return None


def scan_batch(syms):
    res = []
    fut = {_executor.submit(scan_one, s): s for s in syms[:BATCH_SIZE]}
    try:
        for f in as_completed(fut, timeout=10):
            if r := f.result(timeout=2): res.append(r)
    except: pass
    return res


def top_movers(syms, n=20):
    tk, ss = tickers_all(), set(syms)
    mv = [
        (s, abs(d["pct"]))
        for s, d in tk.items()
        if s in ss and d["vol"] >= MIN_BASE_VOL
    ]
    return [s for s, _ in sorted(mv, key=lambda x: x[1], reverse=True)[:n]]


def print_inline():
    n  = _stats["wins"] + _stats["losses"]
    wr = _stats["wins"] / n * 100 if n else 0
    pnl, e = _stats["pnl"], "💚" if _stats["pnl"] >= 0 else "🔴"
    # Hitung expectancy aktual
    notional_avg = ORDER_USDT * LEVERAGE  # $40
    net_tp_est   = notional_avg * EXTREME_PROFIT_PCT - notional_avg * FUTURES_FEE_PCT * 2
    net_sl_est   = notional_avg * HARD_SL_PCT        + notional_avg * FUTURES_FEE_PCT * 2
    rr           = net_tp_est / net_sl_est
    print(f"      ┌ [v18.5.1] {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']} "
          f"{e}PnL:{pnl:+.4f}U R:R={rr:.1f}:1")
    print(f"      └ ExTP:{_stats['extreme_tp']} TrailSL:{_stats['trail_sl']} "
          f"HardSL:{_stats['hard_sl']} | TrailWorst≥SL:✅")


def print_full():
    n    = _stats["wins"] + _stats["losses"]
    wr   = _stats["wins"] / n * 100 if n else 0
    pnl  = _stats["pnl"]
    sess = (time.time() - _stats["start"]) / 3600
    tph  = n / sess if sess > 0 else 0
    e    = "💚" if pnl >= 0 else "🔴"

    notional = ORDER_USDT * LEVERAGE
    net_tp   = notional * EXTREME_PROFIT_PCT - notional * FUTURES_FEE_PCT * 2
    net_sl   = notional * HARD_SL_PCT        + notional * FUTURES_FEE_PCT * 2
    net_tr   = notional * (TRAIL_ACTIVATE - TRAIL_DISTANCE) - notional * FUTURES_FEE_PCT * 2
    rr       = net_tp / net_sl
    be_wr    = 1 / (1 + rr) * 100

    sh = md = 0.0
    if len(_stats["hist"]) >= 5:
        a  = np.array(list(_stats["hist"]))
        sd = float(np.std(a))
        sh = float(np.mean(a)) / sd if sd > 0 else 0.0
    if len(_stats["hist"]) >= 2:
        eq = np.cumsum(list(_stats["hist"]))
        md = float(np.min(eq - np.maximum.accumulate(eq)))

    print(f"\n  {'─'*66}")
    print(f"   ✅ DRY RUN v18.5.1 [NORMAL — 1 profit covers 1 SL] — "
          f"{sess*60:.0f}m | {tph:.1f}T/jam")
    print(f"   💡 Logika loss dibalik jadi profit: ikuti TA, BR searah, 15M konfirmasi")
    print(f"   📐 Net TP:+${net_tp:.3f} | Net SL:-${net_sl:.3f} | "
          f"Trail worst:+${net_tr:.3f} | R:R={rr:.1f} | BE WR={be_wr:.0f}%")
    print(f"   🎯 {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']}")
    print(f"   {e} PnL Net:{pnl:+.5f}U Best:{_stats['best']:+.5f} Worst:{_stats['worst']:+.5f}")
    print(f"   📊 Sharpe:{sh:.2f} MaxDD:{md:.5f}U")
    print(f"   🔔 ExtremeTP:{_stats['extreme_tp']} TrailSL:{_stats['trail_sl']} "
          f"HardSL:{_stats['hard_sl']}")
    print(f"   KS: consec={_ks['consec']} daily={_ks['daily']:+.4f} | BTC:{_macro['btc']}")
    if trade_log:
        print(f"   📋 Last 5 trade:")
        for t in trade_log[-5:]:
            em = "🟢" if t["pnl"] > 0 else "🔴"
            cover = "✅" if t["pnl"] > 0 or abs(t["pnl"]) <= net_sl else "—"
            print(f"      {em} {t['sym']:<14} {t['side']} "
                  f"{t['pnl']:+.5f}U {t['hold']}s — {t['reason']} {cover}")
    print(f"  {'─'*66}")


# ═══════════════════════════════════════════════════════
#  DAEMON THREADS
# ═══════════════════════════════════════════════════════
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
            time.sleep(0.3)
            slots = MAX_POSITIONS - len(live_positions)
            if slots <= 0 or ks_check()[0]: continue
            hot  = [s for s in _hot_syms if s not in live_positions]
            rest = [s for s in syms if s not in live_positions and s not in hot]
            res  = scan_batch((hot + rest)[:25])
            if res:
                for r in sorted(res, key=lambda x: x[2], reverse=True)[:slots]:
                    if len(live_positions) >= MAX_POSITIONS: break
                    sym, d, sc, sg, px, atr = r
                    live_open(sym, d, sc, sg, px, atr)
        except: pass


def t_macro():
    while True:
        try: _macro["btc"] = btc_trend()
        except: pass
        try:
            if time.time() - _macro["last_fng"] > 300:
                _macro["fng"] = int(requests.get(
                    "https://api.alternative.me/fng/?limit=1", timeout=5
                ).json()["data"][0]["value"])
                _macro["last_fng"] = time.time()
        except: pass
        time.sleep(5)


# ═══════════════════════════════════════════════════════
#  MAIN LOOP
# ═══════════════════════════════════════════════════════
def run_bot():
    notional = ORDER_USDT * LEVERAGE
    net_tp   = notional * EXTREME_PROFIT_PCT - notional * FUTURES_FEE_PCT * 2
    net_sl   = notional * HARD_SL_PCT        + notional * FUTURES_FEE_PCT * 2
    net_tr   = notional * (TRAIL_ACTIVATE - TRAIL_DISTANCE) - notional * FUTURES_FEE_PCT * 2
    rr       = net_tp / net_sl

    print("╔══════════════════════════════════════════════════════════════════╗")
    print("║  ✅ DRY RUN v18.5.1 — 1 PROFIT COVER 1 SL                      ║")
    print("║  💡 Cara bot LOSS dibalik jadi cara bot PROFIT:                 ║")
    print("║     Dulu: entry MELAWAN sinyal TA (inverse) → sering SL        ║")
    print("║     Kini: entry SEARAH sinyal TA + BR + 15M konfirmasi         ║")
    print("║  ⚠️  NO REAL ORDERS — SIMULATION LOGGING ONLY                  ║")
    print("╚══════════════════════════════════════════════════════════════════╝")
    print(f"   Net TP:+${net_tp:.3f} | Net SL:-${net_sl:.3f} | "
          f"Trail worst:+${net_tr:.3f} | R:R={rr:.1f}:1")
    print(f"   BE WR: ~{1/(1+rr)*100:.0f}% | Score≥{MIN_SCORE} | VR≥{MIN_VR}x | ADX≥{ADX_MIN}")
    print(f"   Trail aktif @{TRAIL_ACTIVATE*100:.1f}%, "
          f"worst nutup @{(TRAIL_ACTIVATE-TRAIL_DISTANCE)*100:.2f}% → net+${net_tr:.3f} > SL ✅")

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

    time.sleep(4); tickers_all()
    cycle    = scan_idx = 0
    n_bat    = math.ceil(len(syms) / BATCH_SIZE)

    while True:
        cycle += 1
        slots  = MAX_POSITIONS - len(live_positions)
        print(f"\n{'═'*64}")
        print(f"  #{cycle} {time.strftime('%H:%M:%S')} BTC:{_macro['btc']} F&G:{_macro['fng']} "
              f"({len(live_positions)}/{MAX_POSITIONS}) PnL:{_stats['pnl']:+.4f}U")

        if (k := ks_check())[0]:
            print(f"  🚨 KS:{k[1]}")
            time.sleep(SCAN_INTERVAL)
            continue

        if slots > 0:
            mv  = top_movers(syms, 20)
            mv  = [s for s in mv if s not in live_positions]
            bs  = scan_idx * BATCH_SIZE
            reg = [s for s in syms[bs:bs+BATCH_SIZE] if s not in live_positions and s not in mv]
            scan_idx  = (scan_idx + 1) % n_bat
            scan_list = mv[:15] + reg[:10]

            try:   res = scan_batch(scan_list)
            except: res = []

            if res:
                res.sort(key=lambda x: x[2], reverse=True)
                for r in res[:slots]:
                    if len(live_positions) >= MAX_POSITIONS: break
                    sym, d, sc, sg, px, atr = r
                    print(f"     ⭐ {sym} {d} Score:{sc} ATR:{atr:.5g} {' | '.join(sg)}")
                    live_open(sym, d, sc, sg, px, atr)

            elif len(live_positions) == 0:
                try:   r2 = scan_batch([s for s in syms if s not in live_positions])
                except: r2 = []
                if r2:
                    r2.sort(key=lambda x: x[2], reverse=True)
                    sym, d, sc, sg, px, atr = r2[0]
                    live_open(sym, d, sc, sg, px, atr)
        else:
            print(f"  ✅ Full ({MAX_POSITIONS}/{MAX_POSITIONS})")

        if cycle % 20 == 0: print_full()
        time.sleep(SCAN_INTERVAL)


if __name__ == "__main__":
    run_bot()
