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
#  ADAPTIVE SCORER (sama seperti v21, hanya threshold dinaikkan)
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
        # (sama seperti v21, di-singkat agar tidak terlalu panjang)
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
    
    # ATR clamp
    atr_pct = atr / entry_price
    max_sl_pct = atr_pct * ATR_SL_MAX_MULT
    min_tp_pct = atr_pct * ATR_TP_MIN_MULT
    sl_pct = min(sl_pct, max_sl_pct)
    tp_pct = max(tp_pct, min_tp_pct)
    
    # Minimal TP 0.2%, minimal SL 0.15%
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
    
    # === TRENDING MARKET → hanya trend following ===
    if regime in ("TRENDING_BULL", "TRENDING_BEAR"):
        if adx >= 22:
            if regime == "TRENDING_BULL" and e9 > e21 > e50 and m5 > 0:
                return "LONG", "trend_follow_bull"
            if regime == "TRENDING_BEAR" and e9 < e21 < e50 and m5 < 0:
                return "SHORT", "trend_follow_bear"
        return None, "trend_market_no_alignment"
    
    # === SIDEWAYS / VOLATILE → mean reversion + pullback ===
    if regime in ("SIDEWAYS", "VOLATILE"):
        # Mean reversion di BB
        if p <= bb_lower * 1.001 and rsi < 35:
            return "LONG", "mean_reversion_bb_lower"
        if p >= bb_upper * 0.999 and rsi > 65:
            return "SHORT", "mean_reversion_bb_upper"
        # Pullback ke EMA21
        dist_to_e21 = abs(p - e21) / e21
        if dist_to_e21 < 0.002:
            if m5 > 0.002 and mh > 0:
                return "LONG", "pullback_ema21_up"
            if m5 < -0.002 and mh < 0:
                return "SHORT", "pullback_ema21_down"
    
    # === MILD TREND (ikuti, tapi hati-hati) ===
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
    
    # === HARD FILTERS ===
    if vr < 0.9: return None, 0, f"low_vol_{vr:.1f}", atr, 0,0,0,0
    if adx < ADX_MIN: return None, 0, f"adx_{adx:.0f}", atr, 0,0,0,0
    e21, e50 = row["e21"], row["e50"]
    if abs(e21 - e50)/e50 < EMA_SPREAD_MIN: return None, 0, "chop", atr,0,0,0,0
    if regime == "SIDEWAYS": return None, 0, "sideways", atr,0,0,0,0
    blocked, reason = is_pattern_blocked(symbol)
    if blocked: return None, 0, f"blocked_{reason}", atr,0,0,0,0
    if atr/p > 0.025: return None, 0, f"high_atr_{atr/p:.1%}", atr,0,0,0,0
    
    # === DIRECTION ===
    direction, dir_reason = determine_direction_v3(df, _macro["btc"], regime)
    if direction is None: return None, 0, dir_reason, atr,0,0,0,0
    
    # === ANTI-CHASE & FALSE BREAKOUT ===
    if is_chasing_v3(df, direction)[0]: return None, 0, "chase", atr,0,0,0,0
    # false breakout sederhana
    prev = df.iloc[-3]
    if direction == "LONG" and prev["close"] > prev["bb_upper"] and row["close"] < row["bb_upper"]:
        return None, 0, "fbo_bb", atr,0,0,0,0
    if direction == "SHORT" and prev["close"] < prev["bb_lower"] and row["close"] > row["bb_lower"]:
        return None, 0, "fbo_bb", atr,0,0,0,0
    
    # === MULTI-TF (mandatory di trending market) ===
    if regime in ("TRENDING_BULL","TRENDING_BEAR"):
        bias_15m = get_tf_bias(symbol, "15m")
        expected = "BULL" if direction == "LONG" else "BEAR"
        if bias_15m != expected:
            return None, 0, f"mtf_misalign_{bias_15m}", atr,0,0,0,0
    
    # === CONFIDENCE SCORE ===
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
    
    # === TP/SL ===
    px_live = price_live(symbol) or p
    tp, sl, net_tp, net_sl, rr = calc_tp_sl_net(px_live, direction, atr)
    if rr < 1.0: return None, final_score, f"rr_{rr:.1f}<1", atr,0,0,0,0
    
    tp_dist = abs(tp - px_live)/px_live
    sl_dist = abs(sl - px_live)/px_live
    if tp_dist > 0.015: return None, final_score, "tp_too_far", atr,0,0,0,0
    if sl_dist < 0.0015: return None, final_score, "sl_too_tight", atr,0,0,0,0
    
    return direction, final_score, dir_reason, atr, tp, sl, net_tp, net_sl

# ═══════════════════════════════════════════════════════════════════
#  FUNGSI PENDUKUNG (sama seperti v21, disingkat)
# ═══════════════════════════════════════════════════════════════════
def get_precision(symbol): ... # (sama)
def get_position_value(): ... # (sama)
def effective_order_usdt(): ... # (sama)
def get_scan_interval(): ... # (sama)
def qty(symbol, price): ... # (sama)
def price_live(symbol): ... # (sama)
def tickers_all(): ... # (sama)
def ok_cooldown(sym): ... # (sama)
def set_cd(sym): ... # (sama)
def ohlcv(symbol, interval, limit=120): ... # (sama)
def run_ta(df): ... # (sama)
def detect_regime(df_1h): ... # (sama)
def btc_trend(): ... # (sama)
def update_macro(): ... # (sama)
def get_tf_bias(symbol, interval): ... # (sama)
def live_open(sym, direction, score, reason, price, atr, tp, sl, net_tp, net_sl): ... # (sama, hanya update _stats)
def live_close(sym, reason, price=None): ... # (sama)
def monitor_positions(): ... # (sama)
def scan_one(sym): ... # (panggil signal_v22)
def scan_batch(syms): ... # (sama)
def top_movers(syms, n=15): ... # (sama)
def ks_check(), ks_upd(), update_streaks(): ... # (sama)
def print_inline(), print_full(), print_expectancy_math(): ... # (sama)
def t_monitor(), t_rescan(), t_macro(): ... # (sama)

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
