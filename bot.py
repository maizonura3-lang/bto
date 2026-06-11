"""
Bot Scalping v18.4.0 — DRY RUN LOG MODE (PAPER TRADING)
====================================================
- INVERSE MODE: Sinyal LONG dieksekusi SHORT, sinyal SHORT dieksekusi LONG.
- EXECUTION: LOG ONLY (Tidak melakukan order ke Binance Testnet).
- FEE CALCULATION: PnL yang ditampilkan tetap dipotong fee Taker Binance (0.05% per transaksi).

- v18.4.0 CHANGES vs v18.3.3:
    * EXTREME_PROFIT_PCT dinaikkan ke 0.5% (dari 0.3%) → net TP ~+0.40%
    * HARD_SL_PCT diturunkan ke 0.15% (dari 0.2%) → net SL ~-0.25%
    * R:R BARU: TP/SL = 0.5/0.15 = 3.33:1  ← jauh lebih sehat
    * Break-even WR baru: ~23% (dari ~60%) — margin aman sangat lebar
    * TRAILING STOP aktif setelah profit 0.3%: mengunci gain parsial
    * MIN_SCORE dinaikkan ke 58 (dari 52) → sinyal lebih selektif
    * MIN_VR dinaikkan ke 1.3 (dari 1.1) → hanya entry saat volume kuat
    * Catatan net setelah fee (posisi $40 / ORDER_USDT=2, LEV=20):
        Fee per trade  : ~$0.04 (2 × 0.05% × $40)
        Net TP (+0.5%) : $40 × 0.005 − $0.04 = +$0.16
        Net SL (−0.15%): $40 × 0.0015 + $0.04 = −$0.10
        Expectancy @60%WR: 0.6×0.16 − 0.4×0.10 = +$0.056/trade ✅

  LOGIKA BALIK (tidak berubah):
    Sinyal asli LONG  → Bot eksekusi SHORT
    Sinyal asli SHORT → Bot eksekusi LONG
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
#  CONFIG v18.4.0 — INVERSE + TP 0.5% + SL 0.15%
# ═══════════════════════════════════════════════════════

# ⚠️ INVERSE MODE PERMANEN
INVERSE_MODE   = True

LEVERAGE       = 20
ORDER_USDT     = 2.0
MAX_POSITIONS  = 3

# ── TARGET v18.4.0 ──────────────────────────────────────
# R:R = 3.33:1  |  Break-even WR = ~23%
# Net TP after fee  : ~+0.40%   ← naik dari +0.20%
# Net SL after fee  : ~-0.25%   ← turun dari -0.30%
EXTREME_PROFIT_PCT = 0.0050   # +0.5% Take Profit   ← NAIK dari 0.0030
HARD_SL_PCT        = 0.0015   # -0.15% Hard Stop Loss ← TURUN dari 0.0020

# ── TRAILING STOP v18.4.0 ───────────────────────────────
# Setelah harga menyentuh TRAIL_ACTIVATE, trailing stop aktif.
# Peak profit dilacak; jika drawdown dari peak >= TRAIL_DISTANCE, posisi ditutup.
# Ini mengunci sebagian keuntungan dan mencegah TP 0.5% terlewat karena reversal.
TRAIL_ACTIVATE  = 0.0030   # Aktifkan trailing setelah profit 0.3%
TRAIL_DISTANCE  = 0.0015   # Tutup jika profit mundur 0.15% dari peak

FUTURES_FEE_PCT = 0.0005   # Fee Taker Binance 0.05%

MIN_BASE_VOL   = 25_000_000
MIN_VR         = 1.3        # ← dinaikkan dari 1.1 (filter volume lebih ketat)
BR_LONG_MIN    = 0.48
BR_SHORT_MAX   = 0.52

SCAN_INTERVAL  = 1
MONITOR_INT    = 0.25
SCAN_DELAY     = 0.015
BATCH_SIZE     = 15
MAX_WORKERS    = 8

MIN_SCORE      = 58         # ← dinaikkan dari 52 (sinyal lebih selektif)
MIN_GAP        = 12         # ← dinaikkan dari 10
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
#  SIGNAL — menghasilkan arah RAW (sebelum inverse)
# ═══════════════════════════════════════════════════════
def signal_raw(df):
    """Menghasilkan sinyal mentah berdasarkan TA. Belum di-inverse."""
    if df is None or len(df) < 55: return None, 0, [], 0.0
    row, prev, prev2 = df.iloc[-2], df.iloc[-3], df.iloc[-4]
    p, e5, e9, e21, e50 = row["close"], row["e5"], row["e9"], row["e21"], row["e50"]
    rsi, mh, mh_p, mh_p2 = row["rsi"], row["mh"], prev["mh"], prev2["mh"]
    vr, br, m5, body, atr, adx = row["vr"], row["br"], row["m5"], row["br2"], row["atr"], row["adx"]

    # v18.4.0: MIN_VR lebih ketat, hanya masuk saat volume benar-benar kuat
    if vr < MIN_VR: return None, 0, [], atr

    lp = sp = 0
    sl, ss = [], []

    # ── EMA Stack ──────────────────────────────────────
    if p > e5 > e9 > e21 > e50:   lp += 30; sl.append("EMA_stack↑")
    elif p > e5 > e9 > e21:       lp += 22; sl.append("EMA↑↑")
    if p < e5 < e9 < e21 < e50:   sp += 30; ss.append("EMA_stack↓")
    elif p < e5 < e9 < e21:       sp += 22; ss.append("EMA↓↓")

    # ── Momentum ───────────────────────────────────────
    if m5 > 0.005:    lp += 25; sl.append(f"Mom+{m5*100:.1f}%")
    elif m5 > 0.003:  lp += 18; sl.append(f"Mom+{m5*100:.1f}%")
    if m5 < -0.005:   sp += 25; ss.append(f"Mom{m5*100:.1f}%")
    elif m5 < -0.003: sp += 18; ss.append(f"Mom{m5*100:.1f}%")

    # ── MACD ───────────────────────────────────────────
    if mh_p <= 0 and mh > 0:            lp += 22; sl.append("MACD_X↑")
    elif mh > 0 and mh > mh_p > mh_p2:  lp += 18; sl.append("MACD↑↑")
    if mh_p >= 0 and mh < 0:            sp += 22; ss.append("MACD_X↓")
    elif mh < 0 and mh < mh_p < mh_p2:  sp += 18; ss.append("MACD↓↓")

    # ── Volume Ratio ───────────────────────────────────
    if vr >= 3.0:   lp += 15; sp += 15; sl.append(f"Vol{vr:.1f}x"); ss.append(f"Vol{vr:.1f}x")
    elif vr >= 2.0: lp += 10; sp += 10; sl.append(f"Vol{vr:.1f}x"); ss.append(f"Vol{vr:.1f}x")

    # ── Buy/Sell Ratio ─────────────────────────────────
    if br > 0.65: lp += 18; sl.append(f"Buy{br:.0%}")
    if br < 0.35: sp += 18; ss.append(f"Sell{1-br:.0%}")

    # ── RSI Filter ─────────────────────────────────────
    if rsi > 75:   lp = int(lp * 0.4); sp += 20; ss.append(f"RSI_OB{rsi:.0f}")
    elif rsi < 25: sp = int(sp * 0.4); lp += 20; sl.append(f"RSI_OS{rsi:.0f}")

    # ── ADX Strength ───────────────────────────────────
    if adx > 35: lp += 8; sp += 8; sl.append(f"ADX{adx:.0f}"); ss.append(f"ADX{adx:.0f}")

    btc     = _macro["btc"]
    btc_sw  = btc in ("SIDEWAYS", "UNKNOWN")
    thresh  = 40 if btc_sw else MIN_SCORE
    gap     = abs(lp - sp)

    if lp <= sp or lp < thresh or gap < MIN_GAP:
        if sp <= lp or sp < thresh or gap < MIN_GAP:
            return None, max(lp, sp), [], atr
        if br >= BR_SHORT_MAX:
            return None, sp, [], atr
        return "SHORT", sp, ss[:3], atr

    if br <= BR_LONG_MIN:
        return None, lp, [], atr
    return "LONG", lp, sl[:3], atr


def signal(df):
    """
    Wrapper INVERSE:
      sinyal mentah LONG  → eksekusi SHORT
      sinyal mentah SHORT → eksekusi LONG
    """
    raw_dir, sc, sigs, atr = signal_raw(df)
    if raw_dir is None:
        return None, sc, sigs, atr
    inv_dir  = "SHORT" if raw_dir == "LONG" else "LONG"
    inv_sigs = sigs[:3] + [f"INV:{raw_dir}→{inv_dir}"]
    return inv_dir, sc, inv_sigs, atr


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
        "side":      direction,
        "entry":     entry_price,
        "qty":       q_val,
        "open_time": time.time(),
        "score":     score,
        "sigs":      sigs,
        "atr":       atr,
        # ── trailing stop state ──
        "trail_active": False,
        "peak_prof":    0.0,
    }
    with _lock: live_positions[sym] = pos

    d = "🟢" if direction == "LONG" else "🔴"
    print(f"\n  {d} [DRY RUN LOG] {sym} {direction} @{entry_price:.6g}  ← [INVERSE AKTIF]")
    print(f"      TP: +{EXTREME_PROFIT_PCT*100:.1f}% | SL: -{HARD_SL_PCT*100:.2f}% | "
          f"Trail aktif @+{TRAIL_ACTIVATE*100:.1f}% jarak {TRAIL_DISTANCE*100:.2f}%")
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

    print(f"  {e} [DRY RUN LOG] {sym} {side} CLOSE — {reason}")
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
#  MONITOR LOGIC — v18.4.0 dengan Trailing Stop
# ═══════════════════════════════════════════════════════
def monitor_positions():
    for sym in list(live_positions.keys()):
        pos = live_positions.get(sym)
        if pos is None or pos.get("_r"): continue

        px = price_live(sym)
        if px == 0: continue

        side, entry = pos["side"], pos["entry"]
        hold        = time.time() - pos["open_time"]

        # ── Hitung profit saat ini ─────────────────────
        prof_pct = (px - entry) / entry if side == "LONG" else (entry - px) / entry

        # ── Update peak profit (untuk trailing) ────────
        if prof_pct > pos["peak_prof"]:
            pos["peak_prof"] = prof_pct

        # ── Aktifkan trailing stop ─────────────────────
        if not pos["trail_active"] and prof_pct >= TRAIL_ACTIVATE:
            pos["trail_active"] = True
            print(f"   🔔 {sym} TRAIL AKTIF — profit mencapai {prof_pct*100:.2f}%")

        # ── Cek trailing stop ─────────────────────────
        if pos["trail_active"]:
            drawdown_from_peak = pos["peak_prof"] - prof_pct
            if drawdown_from_peak >= TRAIL_DISTANCE:
                live_close(sym, f"TrailSL(peak:{pos['peak_prof']*100:.2f}%)", px)
                continue

        # ── TP & SL tetap ─────────────────────────────
        if prof_pct >= EXTREME_PROFIT_PCT:
            live_close(sym, "ExtremeProfit", px); continue
        if prof_pct <= -HARD_SL_PCT:
            live_close(sym, "HardSL", px); continue

        # ── Status print ──────────────────────────────
        q_val   = pos["qty"]
        fee_est = ((entry * q_val) + (px * q_val)) * FUTURES_FEE_PCT
        pnl_now = (prof_pct * entry * q_val) - fee_est
        trail_s = f" TRAIL@{pos['peak_prof']*100:.2f}%" if pos["trail_active"] else ""
        arrow   = "L" if side == "LONG" else "S"
        print(f"   📌 {sym} {arrow}(INV)@{entry:.5g}→{px:.5g}"
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
        df        = run_ta(ohlcv(sym, Client.KLINE_INTERVAL_5MINUTE, 100).copy())
        px        = df["close"].iloc[-2]
        atr       = df["atr"].iloc[-2]
        if px == 0 or atr / px > 0.03: return None
        dir_, sc, sigs, atr_val = signal(df)
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
    print(f"      ┌ [v18.4.0 INVERSE] {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']} "
          f"{e}PnL Net:{pnl:+.4f}U")
    print(f"      └ Ex-Profit:{_stats['extreme_tp']} TrailSL:{_stats['trail_sl']} "
          f"HardSL:{_stats['hard_sl']}")


def print_full():
    n    = _stats["wins"] + _stats["losses"]
    wr   = _stats["wins"] / n * 100 if n else 0
    pnl  = _stats["pnl"]
    sess = (time.time() - _stats["start"]) / 3600
    tph  = n / sess if sess > 0 else 0
    e    = "💚" if pnl >= 0 else "🔴"

    sh = md = 0.0
    if len(_stats["hist"]) >= 5:
        a  = np.array(list(_stats["hist"]))
        sd = float(np.std(a))
        sh = float(np.mean(a)) / sd if sd > 0 else 0.0
    if len(_stats["hist"]) >= 2:
        eq = np.cumsum(list(_stats["hist"]))
        md = float(np.min(eq - np.maximum.accumulate(eq)))

    print(f"\n  {'─'*64}")
    print(f"   🔀 DRY RUN LOG v18.4.0 [INVERSE — TP:0.5% SL:0.15% R:R≈3.3] — "
          f"{sess*60:.0f}m | {tph:.1f}T/jam")
    print(f"   ⚠️  Sinyal LONG→SHORT | Sinyal SHORT→LONG (semua dibalik)")
    print(f"   🎯 {n}T WR:{wr:.0f}% W:{_stats['wins']} L:{_stats['losses']}")
    print(f"   {e} PnL Net:{pnl:+.5f}U Best:{_stats['best']:+.5f} Worst:{_stats['worst']:+.5f}")
    print(f"   📐 Sharpe:{sh:.2f} MaxDD:{md:.5f}U")
    print(f"   🔔 ExtremeTP:{_stats['extreme_tp']} TrailSL:{_stats['trail_sl']} "
          f"HardSL:{_stats['hard_sl']}")
    print(f"   KS: consec={_ks['consec']} daily={_ks['daily']:+.4f} | BTC:{_macro['btc']}")
    if trade_log:
        print(f"   📋 Last 5:")
        for t in trade_log[-5:]:
            em = "🟢" if t["pnl"] > 0 else "🔴"
            print(f"      {em} {t['sym']:<14} {t['side']}(INV) "
                  f"{t['pnl']:+.5f}U {t['hold']}s — {t['reason']}")
    print(f"  {'─'*64}")


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
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  🔀 DRY RUN v18.4.0 — INVERSE — TP:0.5% SL:0.15% R:R≈3.3 ║")
    print("║  🔔 Trailing Stop aktif setelah profit +0.3%               ║")
    print("║  ⚠️  Sinyal LONG→SHORT | Sinyal SHORT→LONG (semua balik)   ║")
    print("║  ⚠️  NO REAL ORDERS — SIMULATION LOGGING ONLY              ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print(f"   Net TP (+0.5%) ≈ +$0.16 | Net SL (0.15%) ≈ -$0.10 [@ $40 notional]")
    print(f"   Break-even WR  : ~23%   | Min score: {MIN_SCORE} | Min VR: {MIN_VR}x")

    try:
        valid = {
            s["symbol"]
            for s in client.futures_exchange_info()["symbols"]
            if s["status"] == "TRADING"
        }
        syms = list(dict.fromkeys([s for s in SYMBOLS if s in valid]))
    except:
        syms = list(dict.fromkeys(SYMBOLS))

    threading.Thread(target=t_monitor,          daemon=True).start()
    threading.Thread(target=t_rescan, args=(syms,), daemon=True).start()
    threading.Thread(target=t_macro,            daemon=True).start()

    time.sleep(4); tickers_all()
    cycle    = scan_idx = 0
    n_bat    = math.ceil(len(syms) / BATCH_SIZE)

    while True:
        cycle += 1
        slots  = MAX_POSITIONS - len(live_positions)
        print(f"\n{'═'*62}")
        print(f"  #{cycle} {time.strftime('%H:%M:%S')} BTC:{_macro['btc']} F&G:{_macro['fng']} "
              f"({len(live_positions)}/{MAX_POSITIONS}) PnL Net:{_stats['pnl']:+.4f}U [INVERSE]")

        if (k := ks_check())[0]:
            print(f"  🚨 KS:{k[1]}")
            time.sleep(SCAN_INTERVAL)
            continue

        if slots > 0:
            mv   = top_movers(syms, 20)
            mv   = [s for s in mv if s not in live_positions]
            bs   = scan_idx * BATCH_SIZE
            reg  = [s for s in syms[bs:bs+BATCH_SIZE] if s not in live_positions and s not in mv]
            scan_idx   = (scan_idx + 1) % n_bat
            scan_list  = mv[:15] + reg[:10]

            try:   res = scan_batch(scan_list)
            except: res = []

            if res:
                res.sort(key=lambda x: x[2], reverse=True)
                for r in res[:slots]:
                    if len(live_positions) >= MAX_POSITIONS: break
                    sym, d, sc, sg, px, atr = r
                    print(f"     ⭐ {sym} {d}(INV) Score:{sc} ATR:{atr:.5g} {' | '.join(sg)}")
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
