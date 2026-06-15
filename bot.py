"""
Bot Scalping v22.0 — HIGH WIN RATE
============================================
PERBAIKAN DARI v21.0:
  1. TP/SL simetris 0.2% net (win rate >50% → profit)
  2. Entry hanya trend following di trending market
  3. Anti-chase lebih ketat + wajib pullback
  4. Threshold confidence = 65 (lebih selektif)
  5. Pattern block lebih agresif (4x loss → blok 4 jam)
  6. Daily loss limit -2U
"""

import os, time, math, threading, queue, json, requests
from datetime import datetime
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
#  CONFIG v22.0 — HIGH WIN RATE
# ═══════════════════════════════════════════════════════════════════
LEVERAGE          = 20
ORDER_USDT        = 2.0
MAX_POSITIONS     = 3

# === TP/SL simetris 0.2% net (setelah fee) ===
TARGET_NET_PROFIT_PCT = 0.002   # 0.2% dari position value → net +0.08U
TARGET_NET_LOSS_PCT   = 0.002   # 0.2% net loss → net -0.08U
FUTURES_FEE_PCT       = 0.0005  # 0.05% per side

# === ATR-based limits (longgar) ===
ATR_SL_MAX_MULT      = 2.5
ATR_TP_MIN_MULT      = 0.8

# === Entry Filters (lebih selektif) ===
MIN_BASE_VOL      = 30_000_000
ADX_MIN           = 18          # naik dari 15
EMA_SPREAD_MIN    = 0.0015
CONFIDENCE_MIN    = 65          # naik dari 55

# === Anti-Chase (diperketat) ===
MAX_BODY_RATIO    = 0.4         # turun dari 0.5
MAX_MOVE_ATR      = 1.0         # turun dari 1.2
REQUIRE_PULLBACK  = True
MAX_DIST_EMA9     = 0.005       # 0.5% (turun dari 1%)
PULLBACK_LOOKBACK = 3           # cek 3 candle terakhir

# === Entry Frequency & Pause ===
SCAN_INTERVAL_WIN    = 2
SCAN_INTERVAL_LOSS   = 5
PAUSE_AFTER_3_LOSS   = 90        # naik dari 60
SCAN_DELAY           = 0.02
BATCH_SIZE           = 10
MAX_WORKERS          = 6
COOLDOWN_SEC         = 300

# === Multi-TF (mandatory di trending market) ===
MTF_ALIGN_REQUIRED   = True      # baru: harus align
MTF_ALIGN_BONUS      = 20
MTF_MISALIGN_PENALTY = 30

# === Adaptive Risk ===
ADAPTIVE_SIZE_MULT   = 0.5
STREAK_LOSS_TRIG     = 2
STREAK_WIN_RESET     = 2

# === Loss Pattern ===
PATTERN_BLOCK_THRESHOLD = 4      # 4 loss → blok
PATTERN_BLOCK_HOURS     = 4      # blok 4 jam

# === Kill Switch ===
DAILY_LOSS           = -2.0      # stop di -2U (lebih ketat)
CONSEC_MAX           = 4
CONSEC_PAUSE         = 90

# Cache TTL
TTL_5M               = 30
TTL_15M              = 60
TTL_1H               = 180

# ═══════════════════════════════════════════════════════════════════
#  SYMBOLS
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
    "tp_hit": 0, "sl_hit": 0, "hist": deque(maxlen=500), "start": time.time(),
    "streak_loss": 0, "streak_win": 0,
    "last_trade_time": 0, "last_trade_was_win": True,
}

_loss_patterns = {
    "by_symbol": defaultdict(list),
    "by_hour":   defaultdict(list),
    "by_regime": defaultdict(list),
    "blocked_symbols": {},
    "blocked_hours":   set(),
}

# ═══════════════════════════════════════════════════════════════════
#  ADAPTIVE SCORER
# ═══════════════════════════════════════════════════════════════════
class AdaptiveScorer:
    def __init__(self, max_history=500):
        self.history = []
        self.max_history = max_history
        self.feature_winrate = defaultdict(lambda: {"wins": 0, "total": 0})
        
    def extract_features(self, df, direction, btc_bias, regime, hour):
        if df is None or len(df) < 5:
            return []
        row = df.iloc[-2]
        features = []
        
        body_ratio = row["body_ratio"]
        if body_ratio > 0.6: features.append("large_candle")
        elif body_ratio < 0.3: features.append("small_candle")
        else: features.append("mid_candle")
        
        rsi = row["rsi"]
        if rsi < 30: features.append("rsi_oversold")
        elif rsi > 70: features.append("rsi_overbought")
        else: features.append("rsi_mid")
        
        m5 = row["m5"]
        if m5 > 0.008: features.append("strong_up_momentum")
        elif m5 < -0.008: features.append("strong_down_momentum")
        else: features.append("normal_momentum")
        
        vr = row["vr"]
        if vr > 2.0: features.append("high_volume")
        elif vr < 0.7: features.append("low_volume")
        else: features.append("avg_volume")
        
        adx = row["adx"]
        if adx > 35: features.append("strong_trend")
        elif adx > 25: features.append("moderate_trend")
        else: features.append("weak_trend")
        
        if direction == "LONG" and btc_bias in ("BULL","MILD_BULL"):
            features.append("btc_aligned")
        elif direction == "SHORT" and btc_bias in ("BEAR","MILD_BEAR"):
            features.append("btc_aligned")
        else:
            features.append("btc_misaligned")
        
        if regime in ("TRENDING_BULL","TRENDING_BEAR"):
            features.append("trending_market")
        elif regime == "SIDEWAYS":
            features.append("sideways_market")
        
        return features
    
    def update(self, features, did_profit, profit_amount):
        self.history.append((tuple(features), did_profit, profit_amount))
        if len(self.history) > self.max_history:
            self.history.pop(0)
        for feat in features:
            self.feature_winrate[feat]["total"] += 1
            if did_profit:
                self.feature_winrate[feat]["wins"] += 1
    
    def predict_score(self, features):
        if len(self.history) < 30:
            return self._heuristic_score(features)
        target_set = set(features)
        similar_trades = []
        for hist_feat, did_profit, profit in self.history[-200:]:
            hist_set = set(hist_feat)
            if not hist_set: continue
            sim = len(target_set & hist_set) / len(target_set | hist_set)
            if sim > 0.4:
                similar_trades.append((did_profit, profit, sim))
        if not similar_trades:
            return self._heuristic_score(features)
        total_weight = sum(s[2] for s in similar_trades)
        if total_weight == 0: return 50
        weighted_win = sum(1.0 * s[2] for s in similar_trades if s[0]) / total_weight
        return weighted_win * 100
    
    def _heuristic_score(self, features):
        score = 50
        if "rsi_oversold" in features and "trending_market" in features: score += 15
        if "rsi_overbought" in features and "trending_market" in features: score += 15
        if "high_volume" in features: score += 10
        if "strong_trend" in features: score += 15
        if "btc_aligned" in features: score += 15
        if "btc_misaligned" in features: score -= 20
        if "sideways_market" in features: score -= 25
        return max(0, min(100, score))

_scorer = AdaptiveScorer()

# ═══════════════════════════════════════════════════════════════════
#  LOSS PATTERN (blok lebih agresif)
# ═══════════════════════════════════════════════════════════════════
def record_loss_pattern(sym, entry_hour, regime):
    now = time.time()
    lp = _loss_patterns
    lp["by_symbol"][sym].append(now)
    lp["by_hour"][entry_hour].append(now)
    lp["by_regime"][regime].append(now)
    cutoff = now - 86400

    recent_sym_losses = [t for t in lp["by_symbol"][sym] if t > cutoff]
    if len(recent_sym_losses) >= PATTERN_BLOCK_THRESHOLD:
        unblock = now + PATTERN_BLOCK_HOURS * 3600
        lp["blocked_symbols"][sym] = unblock
        print(f"  🚫 Pattern Block: {sym} diblok {PATTERN_BLOCK_HOURS}j ({len(recent_sym_losses)} loss)")

    recent_hour_losses = [t for t in lp["by_hour"][entry_hour] if t > cutoff]
    if len(recent_hour_losses) >= PATTERN_BLOCK_THRESHOLD + 1:
        lp["blocked_hours"].add(entry_hour)
        print(f"  🚫 Pattern Block: Jam {entry_hour:02d}:xx diblok ({len(recent_hour_losses)} loss)")

def is_pattern_blocked(sym):
    now = time.time()
    lp = _loss_patterns
    cur_hour = datetime.now().hour
    if sym in lp["blocked_symbols"]:
        if now < lp["blocked_symbols"][sym]:
            return True, f"symbol block ({int((lp['blocked_symbols'][sym]-now)/60)}m)"
        else:
            del lp["blocked_symbols"][sym]
    if cur_hour in lp["blocked_hours"]:
        return True, f"hour block (jam {cur_hour:02d})"
    return False, ""

def get_loss_pattern_report():
    now = time.time()
    cutoff = now - 86400
    lp = _loss_patterns
    lines = ["  📊 Loss Pattern Analysis (24h):"]
    sym_losses = {s: len([t for t in ts if t > cutoff]) for s, ts in lp["by_symbol"].items()}
    top_syms = sorted(sym_losses.items(), key=lambda x: x[1], reverse=True)[:5]
    if top_syms:
        lines.append("     Symbols paling sering loss:")
        for s, c in top_syms:
            if c > 0:
                lines.append(f"       {s}: {c}x")
    hr_losses = {h: len([t for t in ts if t > cutoff]) for h, ts in lp["by_hour"].items()}
    top_hrs = sorted(hr_losses.items(), key=lambda x: x[1], reverse=True)[:3]
    if top_hrs:
        lines.append("     Jam paling sering loss:")
        for h, c in top_hrs:
            if c > 0:
                lines.append(f"       {h:02d}:xx — {c}x")
    regime_losses = {r: len([t for t in ts if t > cutoff]) for r, ts in lp["by_regime"].items()}
    top_regimes = sorted(regime_losses.items(), key=lambda x: x[1], reverse=True)[:3]
    if top_regimes:
        lines.append("     Regime paling sering loss:")
        for r, c in top_regimes:
            if c > 0:
                lines.append(f"       {r}: {c}x")
    return "\n".join(lines)

# ═══════════════════════════════════════════════════════════════════
#  BINANCE UTILS
# ═══════════════════════════════════════════════════════════════════
_precision_cache = {}
def get_precision(symbol):
    if symbol in _precision_cache:
        return _precision_cache[symbol]
    try:
        info = client.futures_exchange_info()
        for s in info['symbols']:
            if s['symbol'] == symbol:
                prec = int(s['quantityPrecision'])
                _precision_cache[symbol] = prec
                return prec
    except:
        pass
    return 2

def get_position_value():
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        return ORDER_USDT * ADAPTIVE_SIZE_MULT * LEVERAGE
    return ORDER_USDT * LEVERAGE

def effective_order_usdt():
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        return ORDER_USDT * ADAPTIVE_SIZE_MULT
    return ORDER_USDT

def get_scan_interval():
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        return SCAN_INTERVAL_LOSS
    return SCAN_INTERVAL_WIN

def qty(symbol, price):
    raw_qty = (effective_order_usdt() * LEVERAGE) / price
    prec = get_precision(symbol)
    return round(raw_qty, prec)

def price_live(symbol):
    try:
        return float(client.futures_symbol_ticker(symbol=symbol)["price"])
    except:
        return 0.0

def tickers_all():
    global _ticker_cache, _ticker_ts
    now = time.time()
    if now - _ticker_ts < 5 and _ticker_cache:
        return _ticker_cache
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
    except:
        return _ticker_cache

def ok_cooldown(sym):
    return (time.time() - _sym_cooldown.get(sym, 0)) >= COOLDOWN_SEC

def set_cd(sym):
    _sym_cooldown[sym] = time.time()

def ohlcv(symbol, interval, limit=120):
    key, now = (symbol, interval), time.time()
    if interval == "5m":
        ttl = TTL_5M
    elif interval == "15m":
        ttl = TTL_15M
    else:
        ttl = TTL_1H
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
    df["rsi"] = ta.momentum.RSIIndicator(c, 14).rsi()
    df["mh"] = ta.trend.MACD(c, 12, 26, 9).macd_diff()
    df["e5"] = ta.trend.EMAIndicator(c, 5).ema_indicator()
    df["e9"] = ta.trend.EMAIndicator(c, 9).ema_indicator()
    df["e21"] = ta.trend.EMAIndicator(c, 21).ema_indicator()
    df["e50"] = ta.trend.EMAIndicator(c, 50).ema_indicator()
    df["e200"] = ta.trend.EMAIndicator(c, 200).ema_indicator()
    df["atr"] = ta.volatility.AverageTrueRange(h, l, c, 14).average_true_range()
    df["adx"] = ta.trend.ADXIndicator(h, l, c, 14).adx()
    df["vm"] = v.rolling(20).mean()
    df["vr"] = v / df["vm"].replace(0, 1)
    df["br"] = df["tbbase"] / df["volume"].replace(0, 1)
    df["body"] = abs(c - df["open"])
    df["rng"] = h - l
    df["body_ratio"] = df["body"] / df["rng"].replace(0, 1)
    df["m5"] = (c - c.shift(5)) / c.shift(5)
    df["m10"] = (c - c.shift(10)) / c.shift(10)
    bb = ta.volatility.BollingerBands(c, 20, 2)
    df["bb_upper"] = bb.bollinger_hband()
    df["bb_lower"] = bb.bollinger_lband()
    df["bb_width"] = (df["bb_upper"] - df["bb_lower"]) / c
    return df

# ═══════════════════════════════════════════════════════════════════
#  MARKET REGIME DETECTION
# ═══════════════════════════════════════════════════════════════════
def detect_regime(df_1h):
    if df_1h is None or len(df_1h) < 55:
        return "UNKNOWN"
    df = run_ta(df_1h.copy())
    row = df.iloc[-2]
    p, e21, e50, e200 = row["close"], row["e21"], row["e50"], row["e200"]
    adx = row["adx"]
    atr = row["atr"]
    bb_w = row["bb_width"]
    m10 = row["m10"]
    ema_spread = abs(e21 - e50) / e50
    atr_pct = atr / p
    if atr_pct > 0.025:
        return "VOLATILE"
    if adx < 16 or ema_spread < 0.002:
        return "SIDEWAYS"
    if bb_w < 0.02:
        return "SQUEEZE"
    if adx >= 22:
        if p > e21 > e50 and m10 > 0:
            return "TRENDING_BULL"
        if p < e21 < e50 and m10 < 0:
            return "TRENDING_BEAR"
    if p > e50 and m10 > -0.002:
        return "MILD_BULL"
    if p < e50 and m10 < 0.002:
        return "MILD_BEAR"
    return "SIDEWAYS"

def btc_trend():
    try:
        df = run_ta(ohlcv("BTCUSDT", "5m", 100).copy())
        row = df.iloc[-2]
        p, e5, e9, e21 = row["close"], row["e5"], row["e9"], row["e21"]
        m5, adx = row["m5"], row["adx"]
        if p > e5 > e9 > e21 and m5 > 0.001:
            return "BULL"
        if p < e5 < e9 < e21 and m5 < -0.001:
            return "BEAR"
        if p > e9 > e21:
            return "MILD_BULL"
        if p < e9 < e21:
            return "MILD_BEAR"
        return "SIDEWAYS"
    except:
        return "UNKNOWN"

def update_macro():
    _macro["btc"] = btc_trend()
    try:
        df_1h = ohlcv("BTCUSDT", "1h", 60)
        _macro["regime"] = detect_regime(df_1h)
    except:
        _macro["regime"] = "UNKNOWN"

# ═══════════════════════════════════════════════════════════════════
#  MULTI-TIMEFRAME
# ═══════════════════════════════════════════════════════════════════
def get_tf_bias(symbol, interval):
    try:
        df = run_ta(ohlcv(symbol, interval, 100).copy())
        if df is None or len(df) < 55:
            return "NEUTRAL"
        row = df.iloc[-2]
        p, e9, e21, e50 = row["close"], row["e9"], row["e21"], row["e50"]
        adx = row["adx"]
        m5 = row["m5"]
        mh = row["mh"]
        if adx < 16:
            return "NEUTRAL"
        bull_pts = 0
        bear_pts = 0
        if p > e9 > e21: bull_pts += 1
        if p < e9 < e21: bear_pts += 1
        if p > e50: bull_pts += 1
        else: bear_pts += 1
        if m5 > 0.002: bull_pts += 1
        elif m5 < -0.002: bear_pts += 1
        if mh > 0: bull_pts += 1
        elif mh < 0: bear_pts += 1
        if bull_pts >= 3: return "BULL"
        if bear_pts >= 3: return "BEAR"
        return "NEUTRAL"
    except:
        return "NEUTRAL"

# ═══════════════════════════════════════════════════════════════════
#  TP/SL simetris 0.2% net
# ═══════════════════════════════════════════════════════════════════
def calc_tp_sl_net(entry_price, direction, atr):
    position_value = get_position_value()
    fee_total = position_value * (FUTURES_FEE_PCT * 2)
    target_net_profit = position_value * TARGET_NET_PROFIT_PCT
    gross_tp_needed = target_net_profit + fee_total
    tp_pct = gross_tp_needed / position_value
    target_net_loss = position_value * TARGET_NET_LOSS_PCT
    gross_sl_allowed = target_net_loss - fee_total
    sl_pct = abs(gross_sl_allowed) / position_value
    atr_pct = atr / entry_price
    max_sl_pct = atr_pct * ATR_SL_MAX_MULT
    min_tp_pct = atr_pct * ATR_TP_MIN_MULT
    sl_pct = min(sl_pct, max_sl_pct)
    tp_pct = max(tp_pct, min_tp_pct)
    tp_pct = max(tp_pct, 0.002)
    sl_pct = max(sl_pct, 0.0015)
    if direction == "LONG":
        tp = entry_price * (1 + tp_pct)
        sl = entry_price * (1 - sl_pct)
    else:
        tp = entry_price * (1 - tp_pct)
        sl = entry_price * (1 + sl_pct)
    gross_tp_actual = abs(tp - entry_price) * (position_value / entry_price)
    net_tp_actual = gross_tp_actual - fee_total
    gross_sl_actual = abs(sl - entry_price) * (position_value / entry_price)
    net_sl_actual = gross_sl_actual - fee_total
    rr = (tp_pct / sl_pct) if sl_pct > 0 else 0
    return tp, sl, net_tp_actual, net_sl_actual, rr

# ═══════════════════════════════════════════════════════════════════
#  DETERMINE DIRECTION v3 — TREND FOLLOWING PRIORITY
# ═══════════════════════════════════════════════════════════════════
def determine_direction_v3(df, btc_bias, regime):
    if df is None or len(df) < 55:
        return None, "insufficient_data"
    row = df.iloc[-2]
    p, e9, e21, e50 = row["close"], row["e9"], row["e21"], row["e50"]
    rsi, m5, mh, vr, adx = row["rsi"], row["m5"], row["mh"], row["vr"], row["adx"]
    bb_lower, bb_upper = row["bb_lower"], row["bb_upper"]
    
    if regime in ("TRENDING_BULL", "TRENDING_BEAR"):
        if adx >= 22:
            if regime == "TRENDING_BULL" and e9 > e21 > e50 and m5 > 0:
                return "LONG", "trend_follow_bull"
            if regime == "TRENDING_BEAR" and e9 < e21 < e50 and m5 < 0:
                return "SHORT", "trend_follow_bear"
        return None, "trend_market_no_alignment"
    
    if regime in ("SIDEWAYS", "VOLATILE"):
        if p <= bb_lower * 1.001 and rsi < 35:
            return "LONG", "mean_reversion_bb_lower"
        if p >= bb_upper * 0.999 and rsi > 65:
            return "SHORT", "mean_reversion_bb_upper"
        dist_to_e21 = abs(p - e21) / e21
        if dist_to_e21 < 0.002:
            if m5 > 0.002 and mh > 0:
                return "LONG", "pullback_ema21_up"
            if m5 < -0.002 and mh < 0:
                return "SHORT", "pullback_ema21_down"
    
    if regime in ("MILD_BULL", "MILD_BEAR"):
        if p > e21 and m5 > 0.001:
            return "LONG", "mild_trend_up"
        if p < e21 and m5 < -0.001:
            return "SHORT", "mild_trend_down"
    
    return None, "no_clear_signal"

# ═══════════════════════════════════════════════════════════════════
#  ANTI-CHASE v3 (lebih ketat)
# ═══════════════════════════════════════════════════════════════════
def is_chasing_v3(df, direction):
    if len(df) < 5:
        return True, "insufficient_data"
    row = df.iloc[-2]
    prev = df.iloc[-3]
    body_ratio = row["body_ratio"]
    atr = row["atr"]
    move = abs(row["close"] - prev["close"])
    if body_ratio > MAX_BODY_RATIO:
        return True, f"large_candle_{body_ratio:.0%}"
    if move > atr * MAX_MOVE_ATR:
        return True, f"fast_move_{move/atr:.1f}xATR"
    p, e9 = row["close"], row["e9"]
    dist_from_e9 = abs(p - e9) / e9
    if dist_from_e9 > MAX_DIST_EMA9:
        return True, f"overextended_{dist_from_e9:.2%}"
    if REQUIRE_PULLBACK:
        pullback_found = False
        for i in range(-PULLBACK_LOOKBACK, 0):
            c = df.iloc[i]
            if direction == "LONG":
                if c["low"] <= c["e9"] * 1.002:
                    pullback_found = True
                    break
            else:
                if c["high"] >= c["e9"] * 0.998:
                    pullback_found = True
                    break
        if not pullback_found:
            return True, "no_pullback_to_ema9"
    return False, ""

# ═══════════════════════════════════════════════════════════════════
#  MAIN SIGNAL v22
# ═══════════════════════════════════════════════════════════════════
def signal_v22(df, symbol):
    if df is None or len(df) < 55:
        return None, 0, "insufficient_data", 0.0, 0.0, 0.0, 0.0, 0.0
    row = df.iloc[-2]
    p, atr, adx, vr = row["close"], row["atr"], row["adx"], row["vr"]
    regime = _macro.get("regime", "UNKNOWN")
    
    if vr < 0.9: return None, 0, f"low_vol_{vr:.1f}", atr, 0,0,0,0
    if adx < ADX_MIN: return None, 0, f"adx_{adx:.0f}", atr, 0,0,0,0
    e21, e50 = row["e21"], row["e50"]
    if abs(e21 - e50)/e50 < EMA_SPREAD_MIN: return None, 0, "chop", atr,0,0,0,0
    if regime == "SIDEWAYS": return None, 0, "sideways", atr,0,0,0,0
    blocked, reason = is_pattern_blocked(symbol)
    if blocked: return None, 0, f"blocked_{reason}", atr,0,0,0,0
    if atr/p > 0.025: return None, 0, f"high_atr_{atr/p:.1%}", atr,0,0,0,0
    
    direction, dir_reason = determine_direction_v3(df, _macro["btc"], regime)
    if direction is None: return None, 0, dir_reason, atr,0,0,0,0
    
    if is_chasing_v3(df, direction)[0]: return None, 0, "chase", atr,0,0,0,0
    prev = df.iloc[-3]
    if direction == "LONG" and prev["close"] > prev["bb_upper"] and row["close"] < row["bb_upper"]:
        return None, 0, "fbo_bb", atr,0,0,0,0
    if direction == "SHORT" and prev["close"] < prev["bb_lower"] and row["close"] > row["bb_lower"]:
        return None, 0, "fbo_bb", atr,0,0,0,0
    
    if regime in ("TRENDING_BULL","TRENDING_BEAR"):
        bias_15m = get_tf_bias(symbol, "15m")
        expected = "BULL" if direction == "LONG" else "BEAR"
        if bias_15m != expected:
            return None, 0, f"mtf_misalign_{bias_15m}", atr,0,0,0,0
    
    hour = datetime.now().hour
    features = _scorer.extract_features(df, direction, _macro["btc"], regime, hour)
    base_score = _scorer.predict_score(features)
    final_score = base_score
    if dir_reason.startswith("trend_follow"):
        final_score += 10
    if regime in ("TRENDING_BULL","TRENDING_BEAR"):
        final_score += 5
    final_score = max(0, min(100, final_score))
    if final_score < CONFIDENCE_MIN:
        return None, final_score, f"score_{final_score:.0f}<{CONFIDENCE_MIN}", atr,0,0,0,0
    
    px_live = price_live(symbol) or p
    tp, sl, net_tp, net_sl, rr = calc_tp_sl_net(px_live, direction, atr)
    if rr < 1.0: return None, final_score, f"rr_{rr:.1f}<1", atr,0,0,0,0
    tp_dist = abs(tp - px_live)/px_live
    sl_dist = abs(sl - px_live)/px_live
    if tp_dist > 0.015: return None, final_score, "tp_too_far", atr,0,0,0,0
    if sl_dist < 0.0015: return None, final_score, "sl_too_tight", atr,0,0,0,0
    
    return direction, final_score, dir_reason, atr, tp, sl, net_tp, net_sl

# ═══════════════════════════════════════════════════════════════════
#  KILL SWITCH
# ═══════════════════════════════════════════════════════════════════
def ks_check():
    k, now = _ks, time.time()
    if k["active"] and now >= k["resume"]:
        k["active"] = False
        k["consec"] = 0
    if k["active"]:
        return True, k["reason"]
    day = now - (now % 86400)
    if day > k["day_reset"]:
        k["daily"] = 0.0
        k["day_reset"] = day
    if k["daily"] <= DAILY_LOSS:
        k["active"] = True
        k["reason"] = f"daily_{k['daily']:.2f}"
        k["resume"] = day + 86400
        return True, k["reason"]
    if k["consec"] >= CONSEC_MAX:
        k["active"] = True
        k["reason"] = f"consec_{k['consec']}"
        k["resume"] = now + CONSEC_PAUSE
        return True, k["reason"]
    return False, ""

def ks_upd(pnl):
    _ks["daily"] += pnl
    if pnl >= 0:
        _ks["consec"] = 0
    else:
        _ks["consec"] += 1

def update_streaks(pnl):
    if pnl >= 0:
        _stats["streak_win"] += 1
        _stats["streak_loss"] = 0
        if _stats["streak_win"] >= STREAK_WIN_RESET:
            _stats["streak_loss"] = 0
    else:
        _stats["streak_loss"] += 1
        _stats["streak_win"] = 0

# ═══════════════════════════════════════════════════════════════════
#  DRY RUN OPEN / CLOSE
# ═══════════════════════════════════════════════════════════════════
def live_open(sym, direction, score, reason, price, atr, tp, sl, net_tp, net_sl):
    with _lock:
        if sym in live_positions or len(live_positions) >= MAX_POSITIONS:
            return
        live_positions[sym] = {"_r": True}
    try:
        q_val = qty(sym, price)
        entry_price = price
    except Exception as e:
        print(f" ❌ Gagal Open {sym}: {e}")
        with _lock:
            live_positions.pop(sym, None)
        return
    pos = {
        "side": direction,
        "entry": entry_price,
        "qty": q_val,
        "open_time": time.time(),
        "score": score,
        "reason": reason,
        "tp": tp,
        "sl": sl,
        "net_tp": net_tp,
        "net_sl": net_sl,
        "atr": atr,
        "open_hour": datetime.now().hour,
        "regime": _macro.get("regime", "UNKNOWN"),
    }
    with _lock:
        live_positions[sym] = pos
    rr = (tp - entry_price) / (entry_price - sl) if direction == "LONG" and (entry_price - sl) != 0 else \
         (entry_price - tp) / (sl - entry_price) if direction == "SHORT" and (sl - entry_price) != 0 else 0
    size_note = " [ADAPTIVE]" if effective_order_usdt() < ORDER_USDT else ""
    d = "🟢" if direction == "LONG" else "🔴"
    print(f"\n  {d} [DRY] {sym} {direction} @{entry_price:.6g}{size_note}")
    print(f"      Score:{score:.0f} | RR:1:{rr:.2f} | {reason}")
    print(f"      TP:{tp:.6g}(+{abs(tp-entry_price)/entry_price*100:.2f}%) → NET:+{net_tp:.4f}U")
    print(f"      SL:{sl:.6g}(-{abs(sl-entry_price)/entry_price*100:.2f}%) → NET:-{net_sl:.4f}U")
    _stats["trades"] += 1
    _stats["last_trade_time"] = time.time()

def live_close(sym, reason, price=None):
    with _lock:
        pos = live_positions.pop(sym, None)
    if pos is None or pos.get("_r"):
        return
    if price is None:
        price = price_live(sym)
    side, entry, q_val = pos["side"], pos["entry"], pos["qty"]
    entry_hour = pos.get("open_hour", datetime.now().hour)
    regime = pos.get("regime", "UNKNOWN")
    gross_pnl = (price - entry) * q_val if side == "LONG" else (entry - price) * q_val
    open_fee = (entry * q_val) * FUTURES_FEE_PCT
    close_fee = (price * q_val) * FUTURES_FEE_PCT
    total_fee = open_fee + close_fee
    pnl = gross_pnl - total_fee
    pct = (price - entry) / entry * 100 if side == "LONG" else (entry - price) / entry * 100
    hold = time.time() - pos["open_time"]
    e = "🟢" if pnl >= 0 else "🔴"
    print(f"  {e} [DRY] {sym} {side} CLOSE — {reason}")
    print(f"     {entry:.6g}→{price:.6g} ({pct:+.3f}%) hold:{hold:.0f}s")
    print(f"     PnL Net:{pnl:+.5f}U  [Kotor:{gross_pnl:+.5f}U | Fee:{total_fee:.5f}U]")
    _stats["pnl"] += pnl
    _stats["hist"].append(pnl)
    ks_upd(pnl)
    update_streaks(pnl)
    features = _scorer.extract_features(None, side, _macro.get("btc", "UNKNOWN"), regime, entry_hour)
    _scorer.update(features, pnl >= 0, pnl)
    if pnl >= 0:
        _stats["wins"] += 1
        if pnl > _stats["best"]:
            _stats["best"] = pnl
        _stats["last_trade_was_win"] = True
    else:
        _stats["losses"] += 1
        if pnl < _stats["worst"]:
            _stats["worst"] = pnl
        _stats["last_trade_was_win"] = False
        record_loss_pattern(sym, entry_hour, regime)
    if "TakeProfit" in reason:
        _stats["tp_hit"] += 1
    elif "StopLoss" in reason:
        _stats["sl_hit"] += 1
    trade_log.append({
        "sym": sym,
        "side": side,
        "entry": round(entry, 7),
        "exit": round(price, 7),
        "pnl": round(pnl, 5),
        "reason": reason,
        "hold": int(hold),
        "score": pos.get("score", 0),
        "regime": regime,
        "hour": entry_hour,
    })
    set_cd(sym)
    _hot_syms.appendleft(sym)
    _rescan_q.put(1)
    print_inline()

# ═══════════════════════════════════════════════════════════════════
#  MONITOR POSITIONS
# ═══════════════════════════════════════════════════════════════════
def monitor_positions():
    for sym in list(live_positions.keys()):
        pos = live_positions.get(sym)
        if pos is None or pos.get("_r"):
            continue
        px = price_live(sym)
        if px == 0:
            continue
        side, entry = pos["side"], pos["entry"]
        tp, sl = pos["tp"], pos["sl"]
        hold = time.time() - pos["open_time"]
        prof_pct = (px - entry) / entry if side == "LONG" else (entry - px) / entry
        if (side == "LONG" and px >= tp) or (side == "SHORT" and px <= tp):
            live_close(sym, "TakeProfit", px)
            continue
        if (side == "LONG" and px <= sl) or (side == "SHORT" and px >= sl):
            live_close(sym, "StopLoss", px)
            continue
        if int(hold) % 10 == 0 and hold > 0:
            q_val = pos["qty"]
            fee_est = (entry * q_val + px * q_val) * FUTURES_FEE_PCT
            pnl_now = prof_pct * entry * q_val - fee_est
            arrow = "L" if side == "LONG" else "S"
            tp_dist = abs(tp - px) / abs(tp - entry) * 100 if abs(tp - entry) > 0 else 0
            print(f"   📌 {sym} {arrow}@{entry:.5g}→{px:.5g} "
                  f"({prof_pct*100:+.2f}%) {pnl_now:+.4f}U "
                  f"TP:{tp_dist:.0f}% away {hold:.0f}s")

# ═══════════════════════════════════════════════════════════════════
#  SCANNER
# ═══════════════════════════════════════════════════════════════════
def scan_one(sym):
    try:
        time.sleep(SCAN_DELAY)
        if not ok_cooldown(sym):
            return None
        blocked, _ = is_pattern_blocked(sym)
        if blocked:
            return None
        tk = _ticker_cache
        if sym in tk and tk[sym]["vol"] < MIN_BASE_VOL:
            return None
        df_raw = ohlcv(sym, "5m", 120)
        if df_raw is None or len(df_raw) < 55:
            return None
        df = run_ta(df_raw.copy())
        row = df.iloc[-2]
        px = row["close"]
        atr = row["atr"]
        if px == 0: return None
        if atr / px > 0.03: return None
        if row["adx"] < ADX_MIN: return None
        if row["vr"] < 0.8: return None
        direction, score, reason, atr_val, tp, sl, net_tp, net_sl = signal_v22(df, sym)
        if direction is None: return None
        if tp == 0 or sl == 0: return None
        px_live = price_live(sym)
        if px_live == 0: return None
        tp_live, sl_live, net_tp_live, net_sl_live, rr = calc_tp_sl_net(px_live, direction, atr_val)
        return (sym, direction, score, reason, px_live, atr_val, tp_live, sl_live, net_tp_live, net_sl_live)
    except Exception as e:
        return None

def scan_batch(syms):
    res = []
    fut = {_executor.submit(scan_one, s): s for s in syms[:BATCH_SIZE]}
    try:
        for f in as_completed(fut, timeout=15):
            r = f.result(timeout=3)
            if r:
                res.append(r)
    except:
        pass
    return res

def top_movers(syms, n=15):
    tk, ss = tickers_all(), set(syms)
    mv = [(s, abs(d["pct"])) for s, d in tk.items() if s in ss and d["vol"] >= MIN_BASE_VOL]
    return [s for s, _ in sorted(mv, key=lambda x: x[1], reverse=True)[:n]]

# ═══════════════════════════════════════════════════════════════════
#  PRINT / STATS
# ═══════════════════════════════════════════════════════════════════
def calc_stats():
    n = _stats["wins"] + _stats["losses"]
    wr = _stats["wins"] / n * 100 if n else 0
    sh = md = 0.0
    if len(_stats["hist"]) >= 5:
        a = np.array(list(_stats["hist"]))
        sd = float(np.std(a))
        sh = float(np.mean(a)) / sd if sd > 0 else 0.0
    if len(_stats["hist"]) >= 2:
        eq = np.cumsum(list(_stats["hist"]))
        md = float(np.min(eq - np.maximum.accumulate(eq)))
    wins_total = sum(p for p in _stats["hist"] if p > 0)
    loss_total = abs(sum(p for p in _stats["hist"] if p < 0))
    pf = wins_total / loss_total if loss_total > 0 else float("inf")
    avg_win = wins_total / _stats["wins"] if _stats["wins"] > 0 else 0
    avg_loss = loss_total / _stats["losses"] if _stats["losses"] > 0 else 0
    exp = (wr/100) * avg_win - (1 - wr/100) * avg_loss
    return n, wr, sh, md, pf, exp, avg_win, avg_loss

def print_inline():
    n, wr, sh, md, pf, exp, avg_win, avg_loss = calc_stats()
    e = "💚" if _stats["pnl"] >= 0 else "🔴"
    streak_note = ""
    if _stats["streak_loss"] >= STREAK_LOSS_TRIG:
        streak_note = f" ⚠️ADAPT({_stats['streak_loss']}L)"
    print(f"      ┌ [v22.0] {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']} "
          f"{e}PnL:{_stats['pnl']:+.4f}U PF:{pf:.2f}{streak_note}")
    print(f"      └ TP:{_stats['tp_hit']} SL:{_stats['sl_hit']} "
          f"Sharpe:{sh:.2f} Exp:{exp:+.4f}U/T")

def print_full():
    n, wr, sh, md, pf, exp, avg_win, avg_loss = calc_stats()
    sess = (time.time() - _stats["start"]) / 3600
    tph = n / sess if sess > 0 else 0
    e = "💚" if _stats["pnl"] >= 0 else "🔴"
    print(f"\n  {'─'*70}")
    print(f"   ✅ DRY RUN v22.0 [HIGH WIN RATE] — {sess*60:.0f}m | {tph:.1f}T/jam")
    print(f"   🎯 {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']}")
    print(f"   {e} PnL Net:{_stats['pnl']:+.5f}U Best:{_stats['best']:+.5f} Worst:{_stats['worst']:+.5f}")
    print(f"   📊 Sharpe:{sh:.2f} MaxDD:{md:.5f}U ProfitFactor:{pf:.2f}")
    print(f"   💡 Expectancy:{exp:+.5f}U/trade  (AvgWin:{avg_win:+.4f}U AvgLoss:{avg_loss:.4f}U)")
    print(f"   🔔 TP Hit:{_stats['tp_hit']} SL Hit:{_stats['sl_hit']}")
    print(f"   ⚡ Streak: {_stats['streak_win']}W / {_stats['streak_loss']}L | "
          f"Adaptive: {'ON' if _stats['streak_loss'] >= STREAK_LOSS_TRIG else 'OFF'}")
    print(f"   🌍 Regime:{_macro.get('regime','?')} | BTC:{_macro.get('btc','?')}")
    if trade_log:
        print(f"   📋 Last 5 trade:")
        for t in trade_log[-5:]:
            em = "🟢" if t["pnl"] > 0 else "🔴"
            print(f"      {em} {t['sym']:<14} {t['side']} {t['pnl']:+.5f}U "
                  f"{t['hold']}s — {t['reason']} [Score:{t['score']:.0f} {t['regime']} H{t['hour']}]")
    if _stats["losses"] > 0:
        print(get_loss_pattern_report())
    print(f"  {'─'*70}")

def print_expectancy_math():
    n, wr, sh, md, pf, exp, avg_win, avg_loss = calc_stats()
    if n < 5:
        print("  [Math] Butuh minimal 5 trade untuk kalkulasi valid.")
        return
    print(f"\n  {'═'*70}")
    print(f"   💎 EXPECTANCY MATH")
    print(f"   ─────────────────────────────────────────────")
    print(f"   Win Rate      : {wr:.1f}%")
    print(f"   Avg Win       : {avg_win:+.5f}U")
    print(f"   Avg Loss      : {avg_loss:.5f}U")
    print(f"   Profit Factor : {pf:.3f}  (target >1.5)")
    print(f"   Expectancy    : {exp:+.5f}U/trade")
    print(f"   Sharpe        : {sh:.3f}    (target >0)")
    print(f"   MaxDrawdown   : {_stats['worst']:.5f}U")
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
            if live_positions:
                monitor_positions()
        except:
            pass
        time.sleep(0.5)

def t_rescan(syms):
    while True:
        try:
            _rescan_q.get(timeout=30)
            time.sleep(1.0)
            if _stats["streak_loss"] >= 3:
                last_trade = _stats["last_trade_time"]
                if time.time() - last_trade < PAUSE_AFTER_3_LOSS:
                    continue
            slots = MAX_POSITIONS - len(live_positions)
            if slots <= 0 or ks_check()[0]:
                continue
            hot = [s for s in _hot_syms if s not in live_positions]
            rest = [s for s in syms if s not in live_positions and s not in hot]
            res = scan_batch((hot + rest)[:20])
            if res:
                for r in sorted(res, key=lambda x: x[2], reverse=True)[:slots]:
                    if len(live_positions) >= MAX_POSITIONS:
                        break
                    sym, d, sc, reason, px, atr, tp, sl, net_tp, net_sl = r
                    live_open(sym, d, sc, reason, px, atr, tp, sl, net_tp, net_sl)
        except Exception as e:
            pass

def t_macro():
    while True:
        try:
            update_macro()
        except:
            pass
        try:
            if time.time() - _macro.get("last_fng", 0) > 300:
                resp = requests.get("https://api.alternative.me/fng/?limit=1", timeout=5)
                _macro["fng"] = int(resp.json()["data"][0]["value"])
                _macro["last_fng"] = time.time()
        except:
            pass
        time.sleep(10)

# ═══════════════════════════════════════════════════════════════════
#  MAIN LOOP
# ═══════════════════════════════════════════════════════════════════
def run_bot():
    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  ✅ DRY RUN v22.0 — HIGH WIN RATE (TP/SL 0.2% net)                 ║")
    print("║  🎯 Trend Following di Trending | Mean Reversion di Sideways       ║")
    print("║  📊 Anti-Chase diperketat | MTF mandatory | Confidence ≥65         ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")
    try:
        valid = {s["symbol"] for s in client.futures_exchange_info()["symbols"] if s["status"] == "TRADING"}
        syms = [s for s in SYMBOLS if s in valid]
    except:
        syms = SYMBOLS[:]
    threading.Thread(target=t_monitor, daemon=True).start()
    threading.Thread(target=t_rescan, args=(syms,), daemon=True).start()
    threading.Thread(target=t_macro, daemon=True).start()
    print("  ⏳ Warming up (5s)...")
    time.sleep(5)
    tickers_all()
    update_macro()
    cycle = 0
    scan_idx = 0
    n_bat = math.ceil(len(syms) / BATCH_SIZE)
    while True:
        cycle += 1
        slots = MAX_POSITIONS - len(live_positions)
        regime = _macro.get("regime", "?")
        interval = get_scan_interval()
        print(f"\n{'═'*70}")
        print(f"  #{cycle} {time.strftime('%H:%M:%S')} Regime:{regime} BTC:{_macro['btc']} "
              f"({len(live_positions)}/{MAX_POSITIONS}) PnL:{_stats['pnl']:+.4f}U "
              f"Streak:{_stats['streak_loss']}L/{_stats['streak_win']}W ScanInt:{interval}s")
        if ks_check()[0]:
            time.sleep(interval)
            continue
        if regime == "SIDEWAYS":
            print(f"  ⏸ Market SIDEWAYS — skip scan")
            time.sleep(interval * 2)
            continue
        if slots > 0:
            mv = top_movers(syms, 15)
            mv = [s for s in mv if s not in live_positions]
            bs = scan_idx * BATCH_SIZE
            reg = [s for s in syms[bs:bs+BATCH_SIZE] if s not in live_positions and s not in mv]
            scan_idx = (scan_idx + 1) % n_bat
            scan_list = mv[:8] + reg[:5]
            res = scan_batch(scan_list)
            if res:
                res.sort(key=lambda x: x[2], reverse=True)
                for r in res[:slots]:
                    if len(live_positions) >= MAX_POSITIONS: break
                    sym, d, sc, reason, px, atr, tp, sl, net_tp, net_sl = r
                    print(f"     ⭐ {sym} {d} Score:{sc:.0f} | {reason}")
                    live_open(sym, d, sc, reason, px, atr, tp, sl, net_tp, net_sl)
            else:
                print(f"  🔍 Tidak ada setup — menunggu...")
        else:
            print(f"  ✅ Full ({MAX_POSITIONS}/{MAX_POSITIONS})")
        if cycle % 10 == 0: print_full()
        if cycle % 20 == 0: print_expectancy_math()
        time.sleep(interval)

if __name__ == "__main__":
    run_bot()
