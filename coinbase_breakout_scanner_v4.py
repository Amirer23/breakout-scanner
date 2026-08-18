"""
Coinbase Breakout Scanner
==========================
Runs continuously (24/7, outside the browser) and scans ALL USD-quoted pairs
listed on Coinbase for resistance breakouts, using real historical candles
pulled directly from Coinbase's public REST API.

Why this works where the browser artifact couldn't:
  CORS (Cross-Origin Resource Sharing) is a BROWSER-ONLY restriction. A
  server-side script like this one has no such limitation, so it can fetch
  full historical candle data directly -- no WebSocket workaround needed.

WHAT THIS SCRIPT DOES
  1. Fetches the full list of Coinbase products (trading pairs).
  2. Filters to USD-quoted pairs that are online and tradable.
  3. For each pair, pulls recent candles and computes:
       - resistance  = highest high over the lookback window
       - volume ratio = current candle volume / average volume over lookback
       - RSI(14)
       - distance to resistance (%)
  4. Flags "breakout" (price > resistance + volume + RSI confirmation) and
     "watching" (approaching resistance) signals.
  5. Calls notify() on NEW signals only (edge-triggered, not every cycle),
     so you don't get spammed while a breakout is ongoing.
  6. Sleeps, repeats forever.

WHAT YOU STILL NEED TO DECIDE
  - Where this runs 24/7 (a small VPS, a Render/Railway background worker,
    a Raspberry Pi at home, etc.) -- anywhere that can run `python3
    coinbase_breakout_scanner.py` continuously.
  - Your notification channel -- see the notify() function below. It
    currently just logs to console + a local file (alerts_log.jsonl).
    Commented-out starter code for Telegram is included; swap in whatever
    channel you pick.

REQUIREMENTS
  pip install requests

RUN
  python3 coinbase_breakout_scanner.py
"""

import json
import math
import os
import threading
import time
import traceback
import uuid
from datetime import datetime, timezone, timedelta

import requests

# ----------------------------------------------------------------------------
# CONFIG -- tune these to taste
# ----------------------------------------------------------------------------

BASE_URL = "https://api.exchange.coinbase.com"
QUOTE_CURRENCIES = {"USD", "USDC"}  # scan BOTH: Amir's Coinbase app displays pairs as "-USDC", but on
                                     # Coinbase's Exchange API (what this script calls) only a handful of
                                     # coins (~5) actually have a distinct USDC order book -- the other
                                     # ~397 coins' real liquidity is on their "-USD" pair. Scanning USDC
                                     # alone (tried on 2026-08-17) dropped coverage from 397 coins to 5.
                                     # Scanning both catches the real liquidity everywhere AND the few
                                     # genuine USDC-native markets, at the cost of ~5 duplicate scans/cycle.
# Stablecoins are pegged to ~$1 by design -- normal peg-noise (e.g. USDS
# ticking from 0.999 to 1.001) can still clear the volume/RSI/close-strength
# bars and fire a "watching"/"breakout" signal, but it's not a real breakout,
# just the peg holding. Excluded from scanning entirely (requested 2026-08-17
# after a false USDS-USD "WATCHING" alert). Add more here if new ones show up.
STABLECOIN_BASE_SYMBOLS = {
    "USDT", "USDC", "USDS", "DAI", "PYUSD", "GUSD", "TUSD", "USDP",
    "FDUSD", "USDD", "EURC", "EURT", "LUSD", "SUSD", "USTC", "USDE",
}
GRANULARITY_SECONDS = 3600          # candle size: 60, 300, 900, 3600, 21600, 86400
LOOKBACK_CANDLES = 20               # how many candles define "resistance"
BREAKOUT_VOLUME_RATIO = float(os.environ.get("BREAKOUT_VOLUME_RATIO", "1.5"))
BREAKOUT_RSI_MIN = float(os.environ.get("BREAKOUT_RSI_MIN", "55"))
BREAKOUT_BUFFER_PCT = float(os.environ.get("BREAKOUT_BUFFER_PCT", "0.3"))       # NEW: close must clear resistance by this %
BREAKOUT_CLOSE_POSITION_MIN = float(os.environ.get("BREAKOUT_CLOSE_POSITION_MIN", "0.6"))  # NEW: close must be in top X% of candle range
WATCHING_DISTANCE_PCT = float(os.environ.get("WATCHING_DISTANCE_PCT", "1.0"))
WATCHING_VOLUME_RATIO = float(os.environ.get("WATCHING_VOLUME_RATIO", "1.5"))
WATCHING_RSI_MIN = float(os.environ.get("WATCHING_RSI_MIN", "50"))
MIN_24H_VOLUME_USD = float(os.environ.get("MIN_24H_VOLUME_USD", "2000000"))  # liquidity floor (was 5,000,000)
MEASURED_MOVE_FALLBACK_PCT = float(os.environ.get("MEASURED_MOVE_FALLBACK_PCT", "5"))  # NEW: used only if the measured-move range itself is degenerate (near-zero)

CYCLE_SLEEP_SECONDS = 300           # 5 minutes between full scan cycles
REQUEST_PACING_SECONDS = 0.35       # ~3 requests/sec, safely under Coinbase's public rate limit
MAX_RETRIES = 3

STATE_FILE = "scanner_state.json"   # tracks last signal per symbol, to avoid duplicate alerts
ALERTS_LOG_FILE = "alerts_log.jsonl"
OPEN_ORDERS_STATE_FILE = "open_orders_state.json"  # which limit order IDs were open last cycle, to detect fills

# --- Outcome tracking (win-rate stats for breakout signals) -----------------
OUTCOMES_FILE = "outcomes.json"           # pending + resolved trade outcomes
STATS_FILE = "stats.json"                 # cumulative win/loss counters
EVALUATION_HOURS = float(os.environ.get("EVALUATION_HOURS", "48"))     # how long after a breakout to check the result
# NOTE: these fallback defaults were out of sync with the documented "current
# value" of 5% in breakout-scanner-summary.md / README.md (code previously
# defaulted to 1.5%/1.0%). Aligned to 5%/5% here. This ONLY matters if the
# env vars are ever unset on Render -- if they're set there today, live
# behavior is unaffected either way.
SUCCESS_THRESHOLD_PCT = float(os.environ.get("SUCCESS_THRESHOLD_PCT", "5"))   # price up this % = win
FAILURE_THRESHOLD_PCT = float(os.environ.get("FAILURE_THRESHOLD_PCT", "5"))  # price down this % = loss

# Telegram credentials -- set these as environment variables on your server,
# never hardcode them in the file. See README.md for how to obtain them.
#   export TELEGRAM_BOT_TOKEN="123456789:AA..."
#   export TELEGRAM_CHAT_ID="123456789"
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

# --- Manual trading via Telegram (buy/sell only after an explicit /buy or
# /sell command from Amir -- nothing here trades automatically) -------------
# Requires a Coinbase Developer Platform (CDP) API key with TRADE permission.
# Create one at https://portal.cdp.coinbase.com/ -> API Keys, then set these
# as environment variables on Render (never in this file, never in chat):
#   export COINBASE_API_KEY="organizations/{org_id}/apiKeys/{key_id}"
#   export COINBASE_API_SECRET="-----BEGIN EC PRIVATE KEY----- ..."
# Also add `coinbase-advanced-py` to requirements.txt.
# If these aren't set, trading commands are simply disabled -- the scanner
# and alerts work exactly as before.

# .strip() defensively: pasting the Key ID out of the downloaded JSON file
# very easily drags along an invisible trailing newline or space, which
# silently breaks the JWT's sub/kid claim and produces a generic, useless
# "401 Unauthorized" with no other clue. Confirmed via diagnostic logging
# on 2026-08-17: COINBASE_API_KEY was landing at 37 chars instead of the
# expected 36-char UUID, with whitespace at one edge -- this was the actual
# root cause of every failed /balance attempt that day. Stripping here
# makes the script robust to that regardless of how the value gets pasted.
COINBASE_API_KEY = os.environ.get("COINBASE_API_KEY", "").strip()
COINBASE_API_SECRET = os.environ.get("COINBASE_API_SECRET", "").strip()
# Fat-finger guard: refuses any single /buy or /sell above this dollar
# amount. Raise via the MAX_ORDER_USD env var if you genuinely need to trade
# bigger size -- this is a safety net, not a real limit.
MAX_ORDER_USD = float(os.environ.get("MAX_ORDER_USD", "1000"))
TELEGRAM_OFFSET_FILE = "telegram_offset.json"  # tracks which Telegram messages were already handled

TRADING_ENABLED = bool(COINBASE_API_KEY and COINBASE_API_SECRET)
_trade_client = None
if TRADING_ENABLED:
    # Content-free diagnostic: prints ONLY lengths/shape, never the actual
    # key or secret. This exists to catch a very common failure mode --
    # stray quote marks, commas, or whitespace accidentally copy-pasted
    # along with the value when copying out of the downloaded JSON file --
    # which produces exactly a generic 401 Unauthorized with no other clue,
    # since the SDK never validates the api_key string's shape, only the
    # private key's.
    try:
        _key_has_stray_chars = any(c in COINBASE_API_KEY for c in ('"', "'", ",", "{", "}", "\n", "\r", "\t"))
        _key_has_edge_ws = COINBASE_API_KEY != COINBASE_API_KEY.strip()
        print(
            f"  [debug] COINBASE_API_KEY: length={len(COINBASE_API_KEY)} "
            f"(expect 36 for a bare Key ID UUID, longer for organizations/.../apiKeys/... format) "
            f"has_stray_chars(quotes/commas/braces/newlines)={_key_has_stray_chars} "
            f"has_leading_or_trailing_whitespace={_key_has_edge_ws}"
        )
        _secret_stripped = "".join(COINBASE_API_SECRET.split())
        _secret_has_stray_chars = any(c in COINBASE_API_SECRET for c in ('"', "'", ",", "{", "}"))
        _secret_looks_pem = COINBASE_API_SECRET.lstrip().startswith("-----BEGIN")
        print(
            f"  [debug] COINBASE_API_SECRET: raw_length={len(COINBASE_API_SECRET)} "
            f"whitespace_stripped_length={len(_secret_stripped)} "
            f"(expect 44 for a 32-byte Ed25519 seed, 88 for a 64-byte seed||pubkey, if not PEM) "
            f"looks_like_pem={_secret_looks_pem} "
            f"has_stray_chars(quotes/commas/braces)={_secret_has_stray_chars}"
        )
    except Exception:
        pass
    try:
        from coinbase.rest import RESTClient
        _trade_client = RESTClient(api_key=COINBASE_API_KEY, api_secret=COINBASE_API_SECRET)
    except Exception as e:
        print(f"  [error] Coinbase trading client failed to initialize -- trading disabled: {e}")
        TRADING_ENABLED = False

# ----------------------------------------------------------------------------
# HTTP helpers (rate-limited, with retry/backoff)
# ----------------------------------------------------------------------------

session = requests.Session()
session.headers.update({"User-Agent": "breakout-scanner/1.0"})


def get_json(path, params=None):
    url = f"{BASE_URL}{path}"
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            resp = session.get(url, params=params, timeout=10)
            if resp.status_code == 429:
                wait = 1.5 * attempt
                print(f"  [rate limited] backing off {wait:.1f}s ({path})")
                time.sleep(wait)
                continue
            resp.raise_for_status()
            return resp.json()
        except requests.RequestException as e:
            if attempt == MAX_RETRIES:
                print(f"  [error] {path} failed after {MAX_RETRIES} attempts: {e}")
                return None
            time.sleep(1.0 * attempt)
    return None


def fetch_products():
    data = get_json("/products")
    if not data:
        return []
    out = []
    for p in data:
        if p.get("quote_currency") not in QUOTE_CURRENCIES:
            continue
        if p.get("base_currency") in STABLECOIN_BASE_SYMBOLS:
            continue
        if p.get("trading_disabled"):
            continue
        if p.get("status") != "online":
            continue
        out.append(p["id"])
    return sorted(out)


def fetch_candles(product_id):
    data = get_json(f"/products/{product_id}/candles", params={"granularity": GRANULARITY_SECONDS})
    if not data or not isinstance(data, list):
        return None
    # Coinbase returns newest-first: [time, low, high, open, close, volume]
    candles = list(reversed(data))
    return candles


# ----------------------------------------------------------------------------
# Indicators
# ----------------------------------------------------------------------------

def sma(values, period):
    if len(values) < period:
        return None
    window = values[-period:]
    return sum(window) / period


def stddev(values, period, mean):
    window = values[-period:]
    variance = sum((v - mean) ** 2 for v in window) / period
    return math.sqrt(variance)


def rsi(closes, period=14):
    if len(closes) < period + 1:
        return None
    gains, losses = 0.0, 0.0
    for i in range(len(closes) - period, len(closes)):
        diff = closes[i] - closes[i - 1]
        if diff >= 0:
            gains += diff
        else:
            losses -= diff
    avg_gain, avg_loss = gains / period, losses / period
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100 - (100 / (1 + rs))


def drop_incomplete_last_candle(candles):
    """Coinbase's candle endpoint typically includes the still-forming
    current period as the last entry. Signal generation off a partial
    candle means volume ratio / RSI / close-strength are all computed from
    an incomplete bar that keeps changing -- since the scanner re-scans
    every CYCLE_SLEEP_SECONDS, this can make the SAME real breakout flicker
    in and out of the "breakout" state within one hour (e.g. it clears the
    volume/close-strength bar at minute 40 but not at minute 10), producing
    duplicate alerts and duplicate outcome-tracking entries for one event.
    Drop it so every signal is based on a fully closed candle."""
    if not candles:
        return candles
    last_start = candles[-1][0]
    if last_start + GRANULARITY_SECONDS > time.time():
        return candles[:-1]
    return candles


def find_price_target(candles, resistance, last_close):
    """Technical price target for a breakout.

    Primary method: scan further back in the already-fetched history (older
    than the lookback window used to compute `resistance`) for the next
    higher swing high -- i.e. the next real resistance level above the one
    that just broke.

    Fallback ("measured move"): if no such level exists in the fetched
    history (e.g. the coin is breaking out to a new high within our
    window -- common on strong crypto breakouts, and arguably a MORE
    bullish signal, just one with no visible ceiling to point to), project
    the height of the range that preceded the breakout on top of the
    resistance level. This is a standard technical-analysis heuristic, not
    a guarantee -- treat it as a reference point for a trailing/partial
    exit, not a promise the price will get there.

    Both methods only ever return a price ABOVE last_close (the breakout
    candle's own close): an old high found further back can sit only
    marginally above `resistance` (e.g. resistance=88.43, old high=88.44) --
    close enough that the breakout candle itself, which is what pushed the
    price past `resistance` in the first place, can already have carried
    last_close past that old high too. Returning it as-is would print a
    "target" behind the current price (a negative % move), which is useless
    as a forward objective and confusing next to an alert that just fired.
    Confirmed live on 2026-08-17 (AAVE-USD: resistance 88.43, old high
    88.44, but last_close already at 88.98 -- a target 0.6% *behind* the
    alert price). Both branches below explicitly filter/extend past
    last_close so whatever target is returned is always still ahead of it.

    Caveat: both methods are limited to whatever history Coinbase's candle
    endpoint returns for this granularity (roughly the last ~300 candles,
    i.e. ~12 days at the default 1h granularity) -- a genuinely older
    resistance level further back than that won't be seen.
    """
    highs = [c[2] for c in candles]
    lows = [c[1] for c in candles]

    older_highs = highs[: -(LOOKBACK_CANDLES + 1)]
    higher_levels = [h for h in older_highs if h > resistance and h > last_close]
    if higher_levels:
        return min(higher_levels), "next_resistance"

    window_lows = lows[-LOOKBACK_CANDLES - 1 : -1]
    range_low = min(window_lows) if window_lows else resistance
    range_height = resistance - range_low
    if range_height <= 0:
        range_height = resistance * (MEASURED_MOVE_FALLBACK_PCT / 100)
    target = resistance + range_height
    # Keep projecting the same range height forward until the target clears
    # last_close -- guards the same edge case for the measured-move branch
    # (a strong breakout candle can run past resistance + one range-height).
    # range_height is guaranteed > 0 by this point, so this always terminates.
    while target <= last_close:
        target += range_height
    return target, "measured_move"


def analyze(candles):
    if len(candles) < LOOKBACK_CANDLES + 2:
        return None

    closes = [c[4] for c in candles]
    highs = [c[2] for c in candles]
    lows = [c[1] for c in candles]
    vols = [c[5] for c in candles]

    prior_highs = highs[-LOOKBACK_CANDLES - 1 : -1]
    resistance = max(prior_highs)
    prior_vols = vols[-LOOKBACK_CANDLES - 1 : -1]
    avg_vol = sum(prior_vols) / len(prior_vols) if prior_vols else 0

    last_close = closes[-1]
    last_high = highs[-1]
    last_low = lows[-1]
    last_vol = vols[-1]
    vol_ratio = (last_vol / avg_vol) if avg_vol > 0 else None
    rsi_val = rsi(closes, 14)
    dist_pct = ((resistance - last_close) / last_close) * 100

    # Where did this candle close within its own high-low range?
    # 1.0 = closed at the high (strong buyers through the close),
    # 0.0 = closed at the low (rejected -- classic false-breakout wick).
    candle_range = last_high - last_low
    # A zero-range candle means price never even tested a range within the
    # bar -- there's no real evidence of close strength either way, so this
    # should NOT default to "passed" (1.0), which would let a signal
    # through on a technicality. Default to 0.0 (fails the strength check)
    # instead, consistent with "no confirmation = no signal".
    close_position = ((last_close - last_low) / candle_range) if candle_range > 0 else 0.0

    # Approximate 24h dollar turnover, using the last 24 hourly candles
    # (assumes GRANULARITY_SECONDS == 3600; scales proportionally otherwise).
    candles_per_day = max(1, int(round(86400 / GRANULARITY_SECONDS)))
    recent = candles[-candles_per_day:]
    daily_volume_usd = sum(c[5] * c[4] for c in recent)  # volume * close, summed

    breakout_threshold = resistance * (1 + BREAKOUT_BUFFER_PCT / 100)

    signal = "neutral"
    if daily_volume_usd < MIN_24H_VOLUME_USD:
        signal = "neutral"  # too thin/illiquid -- never signal regardless of other conditions
    elif (last_close > breakout_threshold
            and vol_ratio and vol_ratio >= BREAKOUT_VOLUME_RATIO
            and (rsi_val or 0) > BREAKOUT_RSI_MIN
            and close_position >= BREAKOUT_CLOSE_POSITION_MIN):
        signal = "breakout"
    elif (0 <= dist_pct < WATCHING_DISTANCE_PCT
          and vol_ratio and vol_ratio >= WATCHING_VOLUME_RATIO
          and (rsi_val or 0) > WATCHING_RSI_MIN):
        signal = "watching"

    target_price, target_pct, target_method = None, None, None
    if signal == "breakout":
        target_price, target_method = find_price_target(candles, resistance, last_close)
        target_pct = ((target_price - last_close) / last_close) * 100

    return {
        "last_close": last_close,
        "resistance": resistance,
        "vol_ratio": vol_ratio,
        "rsi": rsi_val,
        "dist_pct": dist_pct,
        "close_position": close_position,
        "daily_volume_usd": daily_volume_usd,
        "signal": signal,
        "target_price": target_price,
        "target_pct": target_pct,
        "target_method": target_method,
    }


# ----------------------------------------------------------------------------
# State (avoid duplicate alerts) + notification hook
# ----------------------------------------------------------------------------

def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            return {}
    return {}


def save_state(state):
    save_json_file(STATE_FILE, state)


def load_json_file(path, default):
    if os.path.exists(path):
        try:
            with open(path, "r") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            return default
    return default


def save_json_file(path, data):
    # Write to a temp file and rename over the target so a crash/restart
    # mid-write (Render can kill the process at any point) never leaves a
    # truncated/corrupt JSON file behind. A corrupt file would otherwise be
    # silently treated as "no data" on next load (see load_json_file above),
    # wiping accumulated state/outcomes/stats -- this is the actual
    # mechanism behind the "a redeploy can reset the win/loss counter" risk
    # noted in the README, not just redeploys themselves.
    tmp_path = f"{path}.tmp"
    with open(tmp_path, "w") as f:
        json.dump(data, f)
    os.replace(tmp_path, path)


def record_pending_outcome(outcomes, product_id, result, now):
    """Called when a NEW breakout alert fires. Schedules a check-back later."""
    key = f"{product_id}|{now.isoformat()}"
    outcomes[key] = {
        "product_id": product_id,
        "entry_price": result["last_close"],
        "resistance": result["resistance"],
        "target_price": result.get("target_price"),
        "target_pct": result.get("target_pct"),
        "target_method": result.get("target_method"),
        "alert_time": now.isoformat(),
        "eval_time": (now + timedelta(hours=EVALUATION_HOURS)).isoformat(),
        "resolved": False,
    }


def evaluate_pending_outcomes(outcomes, stats, now):
    """Checks any pending breakout outcomes whose evaluation time has arrived,
    fetches the current price, classifies win/loss/flat, sends a Telegram
    update, and rolls the result into cumulative stats."""
    for key, entry in outcomes.items():
        if entry.get("resolved"):
            continue
        eval_time = datetime.fromisoformat(entry["eval_time"])
        if now < eval_time:
            continue

        product_id = entry["product_id"]
        candles = fetch_candles(product_id)
        time.sleep(REQUEST_PACING_SECONDS)
        if not candles:
            continue  # try again next cycle

        current_price = candles[-1][4]
        entry_price = entry["entry_price"]
        pct_change = ((current_price - entry_price) / entry_price) * 100

        if pct_change >= SUCCESS_THRESHOLD_PCT:
            outcome = "win"
        elif pct_change <= -FAILURE_THRESHOLD_PCT:
            outcome = "loss"
        else:
            outcome = "flat"

        entry["resolved"] = True
        entry["outcome"] = outcome
        entry["exit_price"] = current_price
        entry["pct_change"] = pct_change
        entry["resolved_time"] = now.isoformat()

        stats["total"] = stats.get("total", 0) + 1
        stats[outcome] = stats.get(outcome, 0) + 1
        decided = stats.get("win", 0) + stats.get("loss", 0)
        win_rate = (stats.get("win", 0) / decided * 100) if decided > 0 else 0.0

        icon = {"win": "✅", "loss": "❌", "flat": "⚪"}[outcome]
        text = (
            f"{icon} OUTCOME: {product_id}\n"
            f"Entry: {entry_price:.6g} -> Now: {current_price:.6g} ({pct_change:+.2f}%)\n"
            f"Result: {outcome.upper()}\n"
            f"Track record: {stats.get('win',0)}W / {stats.get('loss',0)}L / {stats.get('flat',0)}F "
            f"(win rate {win_rate:.0f}% of decided trades, {stats['total']} total)"
        )
        print(f"[OUTCOME] {text}")
        if TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID:
            try:
                session.post(
                    f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                    json={"chat_id": TELEGRAM_CHAT_ID, "text": text},
                    timeout=10,
                )
            except requests.RequestException as e:
                print(f"  [error] Telegram send failed: {e}")

    # prune old resolved entries so the file doesn't grow forever
    cutoff = now - timedelta(days=30)
    to_delete = [
        k for k, v in outcomes.items()
        if v.get("resolved") and datetime.fromisoformat(v["resolved_time"]) < cutoff
    ]
    for k in to_delete:
        del outcomes[k]

    return outcomes, stats


def notify(product_id, result):
    """
    Called once when a symbol NEWLY enters 'breakout' or 'watching'.

    Sends a Telegram message. Fill in TELEGRAM_BOT_TOKEN and
    TELEGRAM_CHAT_ID below (see README.md for how to get them -- neither
    requires sharing a phone number with anyone but Telegram itself).
    Also logs every alert to alerts_log.jsonl as a backup record.
    """
    event = {
        "time": datetime.now(timezone.utc).isoformat(),
        "product_id": product_id,
        **result,
    }

    text = (
        f"{'🟢' if result['signal'] == 'breakout' else '🟡'} {product_id}: {result['signal'].upper()}\n"
        f"Price: {result['last_close']:.6g}\n"
        f"Resistance: {result['resistance']:.6g}\n"
        f"Volume ratio: {result['vol_ratio']:.2f}x\n"
        f"RSI: {result['rsi']:.0f}\n"
        f"Close strength: {result['close_position']*100:.0f}%\n"
        f"24h turnover: ${result['daily_volume_usd']:,.0f}"
    )
    if result["signal"] == "breakout" and result.get("target_price"):
        method_label = (
            "Next resistance target"
            if result["target_method"] == "next_resistance"
            else "Measured-move target (no higher resistance in range)"
        )
        text += (
            f"\n{method_label}: {result['target_price']:.6g} "
            f"({result['target_pct']:+.1f}% from here)"
        )

    print(f"[ALERT] {product_id}: {result['signal'].upper()} "
          f"price={result['last_close']:.4f} resistance={result['resistance']:.4f} "
          f"vol_ratio={result['vol_ratio']:.2f}x rsi={result['rsi']:.0f}"
          + (f" target={result['target_price']:.4f} ({result['target_pct']:+.1f}%, {result['target_method']})"
             if result.get("target_price") else ""))

    if TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID:
        try:
            session.post(
                f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                json={"chat_id": TELEGRAM_CHAT_ID, "text": text},
                timeout=10,
            )
        except requests.RequestException as e:
            print(f"  [error] Telegram send failed: {e}")
    else:
        print("  [warn] TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID not set -- skipping Telegram send.")

    with open(ALERTS_LOG_FILE, "a") as f:
        f.write(json.dumps(event) + "\n")


# ----------------------------------------------------------------------------
# Manual trading via Telegram (buy / sell / balance) -- all require an
# explicit /buy, /sell or /balance command sent by the account owner in
# Telegram. Nothing here ever executes automatically. Disabled entirely
# (TRADING_ENABLED == False) unless COINBASE_API_KEY/SECRET are set.
# ----------------------------------------------------------------------------

def _to_dict(obj):
    """Normalize a Coinbase SDK response object into a plain dict."""
    if obj is None:
        return {}
    if isinstance(obj, dict):
        return obj
    to_dict = getattr(obj, "to_dict", None)
    if callable(to_dict):
        try:
            return to_dict()
        except Exception:
            pass
    return {}


def telegram_send(text):
    """Send a plain message to the configured Telegram chat (fire-and-forget)."""
    if not (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID):
        return
    try:
        session.post(
            f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
            json={"chat_id": TELEGRAM_CHAT_ID, "text": text},
            timeout=10,
        )
    except requests.RequestException as e:
        print(f"  [error] Telegram send failed: {e}")


def get_current_price(product_id):
    """Best-effort last price for product_id, or None if it can't be fetched."""
    candles = fetch_candles(product_id)
    if not candles:
        return None
    return candles[-1][4]


def _coinbase_error_detail(e):
    """Best-effort extraction of Coinbase's actual error response body, which
    usually explains WHY a request was rejected (e.g. invalid signature,
    unknown key, clock skew) -- far more useful than the generic
    '401 Client Error: Unauthorized' text alone."""
    resp = getattr(e, "response", None)
    if resp is None:
        return ""
    try:
        return f" | body: {resp.text[:500]}"
    except Exception:
        return ""


def execute_buy(product_id, usd_amount):
    """Market-buy usd_amount worth of product_id. Reports result via Telegram."""
    order_id = str(uuid.uuid4())
    try:
        resp = _to_dict(_trade_client.market_order_buy(
            client_order_id=order_id, product_id=product_id, quote_size=str(usd_amount)))
        if resp.get("success"):
            telegram_send(f"✅ BUY executed: {product_id} for ${usd_amount}\nOrder ID: {order_id}")
        else:
            telegram_send(f"❌ BUY failed: {product_id} for ${usd_amount}\n{resp.get('error_response', resp)}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ BUY error: {product_id} for ${usd_amount}\n{e}{detail}")
        print(f"  [error] buy order failed: {e}{detail}")
        traceback.print_exc()


def execute_sell(product_id, usd_amount):
    """Market-sell ~usd_amount worth of product_id (converted to base size at
    the current price, since Coinbase's sell endpoint takes base size, not
    quote size). Reports result via Telegram."""
    order_id = str(uuid.uuid4())
    price = get_current_price(product_id)
    if not price:
        telegram_send(f"❌ SELL failed: couldn't fetch current price for {product_id}")
        return
    base_size = usd_amount / price
    try:
        resp = _to_dict(_trade_client.market_order_sell(
            client_order_id=order_id, product_id=product_id, base_size=f"{base_size:.8f}"))
        if resp.get("success"):
            telegram_send(f"✅ SELL executed: {product_id} (~${usd_amount})\nOrder ID: {order_id}")
        else:
            telegram_send(f"❌ SELL failed: {product_id} for ${usd_amount}\n{resp.get('error_response', resp)}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ SELL error: {product_id} for ${usd_amount}\n{e}{detail}")
        print(f"  [error] sell order failed: {e}{detail}")
        traceback.print_exc()


def execute_buy_limit(product_id, usd_amount, limit_price):
    """Place a GTC (good-til-cancelled) limit buy: the order sits open on
    Coinbase's book at limit_price (or better) until it fills or is
    cancelled -- unlike a market order, it does NOT execute immediately.
    usd_amount is converted to a base-currency size using limit_price
    (not the current market price), since that's the price it will
    actually transact at if/when it fills."""
    order_id = str(uuid.uuid4())
    base_size = usd_amount / limit_price
    try:
        resp = _to_dict(_trade_client.limit_order_gtc_buy(
            client_order_id=order_id, product_id=product_id,
            base_size=f"{base_size:.8f}", limit_price=str(limit_price)))
        if resp.get("success"):
            telegram_send(
                f"✅ LIMIT BUY placed: {product_id} ~${usd_amount} @ {limit_price}\n"
                f"Order ID: {order_id}\n"
                f"(Stays open until filled or cancelled -- check /orders, cancel with /cancel {order_id})"
            )
        else:
            telegram_send(f"❌ LIMIT BUY failed: {product_id} ~${usd_amount} @ {limit_price}\n{resp.get('error_response', resp)}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ LIMIT BUY error: {product_id} ~${usd_amount} @ {limit_price}\n{e}{detail}")
        print(f"  [error] limit buy order failed: {e}{detail}")
        traceback.print_exc()


def execute_sell_limit(product_id, usd_amount, limit_price):
    """Place a GTC limit sell at limit_price -- sits open until it fills or
    is cancelled, unlike a market sell. usd_amount is converted to a
    base-currency size using limit_price."""
    order_id = str(uuid.uuid4())
    base_size = usd_amount / limit_price
    try:
        resp = _to_dict(_trade_client.limit_order_gtc_sell(
            client_order_id=order_id, product_id=product_id,
            base_size=f"{base_size:.8f}", limit_price=str(limit_price)))
        if resp.get("success"):
            telegram_send(
                f"✅ LIMIT SELL placed: {product_id} ~${usd_amount} @ {limit_price}\n"
                f"Order ID: {order_id}\n"
                f"(Stays open until filled or cancelled -- check /orders, cancel with /cancel {order_id})"
            )
        else:
            telegram_send(f"❌ LIMIT SELL failed: {product_id} ~${usd_amount} @ {limit_price}\n{resp.get('error_response', resp)}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ LIMIT SELL error: {product_id} ~${usd_amount} @ {limit_price}\n{e}{detail}")
        print(f"  [error] limit sell order failed: {e}{detail}")
        traceback.print_exc()


def handle_orders_command():
    """Handle the /orders Telegram command -- lists currently open (still
    unfilled) limit orders, so the user can see what's pending and get the
    order IDs needed for /cancel."""
    if not TRADING_ENABLED:
        telegram_send("Trading is not enabled -- COINBASE_API_KEY / COINBASE_API_SECRET are not set on the server.")
        return
    try:
        resp = _to_dict(_trade_client.list_orders(order_status=["OPEN"]))
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ Failed to fetch open orders: {e}{detail}")
        print(f"  [error] list_orders failed: {e}{detail}")
        traceback.print_exc()
        return
    orders = resp.get("orders", [])
    if not orders:
        telegram_send("📋 No open orders.")
        return
    lines = ["📋 Open orders:"]
    for o in orders:
        o = o if isinstance(o, dict) else _to_dict(o)
        cfg = _to_dict(o.get("order_configuration")) or {}
        limit_cfg = _to_dict(cfg.get("limit_limit_gtc")) or {}
        price = limit_cfg.get("limit_price", "?")
        size = limit_cfg.get("base_size", "?")
        lines.append(
            f"\n{o.get('product_id', '?')} {o.get('side', '?')}\n"
            f"  size: {size}  @ {price}\n"
            f"  order id: {o.get('order_id', '?')}"
        )
    telegram_send("\n".join(lines))


def handle_cancel_command(order_id):
    """Handle the /cancel ORDER_ID Telegram command -- cancels one open
    order (get the ORDER_ID from /orders)."""
    if not TRADING_ENABLED:
        telegram_send("Trading is not enabled -- COINBASE_API_KEY / COINBASE_API_SECRET are not set on the server.")
        return
    try:
        resp = _to_dict(_trade_client.cancel_orders(order_ids=[order_id]))
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ Cancel failed: {order_id}\n{e}{detail}")
        print(f"  [error] cancel_orders failed: {e}{detail}")
        traceback.print_exc()
        return
    results = resp.get("results", [])
    result0 = _to_dict(results[0]) if results else {}
    if result0.get("success"):
        telegram_send(f"✅ Order cancelled: {order_id}")
    else:
        telegram_send(f"❌ Cancel failed: {order_id}\n{result0 or 'no such open order'}")


def check_order_fills(known_open_ids):
    """Called once per scan cycle: diffs the current set of open limit
    orders against what was open last cycle. Any order that dropped off the
    open list got resolved somehow (filled, cancelled, or expired) since we
    last checked -- fetch its final status and push a Telegram notification,
    so filling a limit order doesn't require the user to remember to check
    /orders. Returns the updated set of known-open order IDs to persist."""
    if not TRADING_ENABLED:
        return known_open_ids
    try:
        resp = _to_dict(_trade_client.list_orders(order_status=["OPEN"]))
    except Exception as e:
        print(f"  [error] check_order_fills: list_orders failed: {e}")
        return known_open_ids  # try again next cycle rather than losing track

    current_open_ids = {
        (o if isinstance(o, dict) else _to_dict(o)).get("order_id")
        for o in resp.get("orders", [])
    }
    current_open_ids.discard(None)

    resolved_ids = known_open_ids - current_open_ids
    for order_id in resolved_ids:
        try:
            order = _to_dict(_to_dict(_trade_client.get_order(order_id)).get("order", {}))
        except Exception as e:
            print(f"  [error] check_order_fills: get_order({order_id}) failed: {e}")
            continue
        status = order.get("status", "UNKNOWN")
        product_id = order.get("product_id", "?")
        side = order.get("side", "?")
        filled_size = order.get("filled_size", "?")
        avg_price = order.get("average_filled_price", "?")
        icon = {"FILLED": "✅", "CANCELLED": "🚫", "EXPIRED": "⌛"}.get(status, "ℹ️")
        telegram_send(
            f"{icon} Limit order {status}: {side} {product_id}\n"
            f"Filled: {filled_size} @ avg {avg_price}\n"
            f"Order ID: {order_id}"
        )

    return current_open_ids


def get_balances():
    """Return a list of (currency, available_amount, held_amount) for every
    account with a non-zero total (available + hold) balance, paginating
    through get_accounts().

    Coinbase reports "available" (immediately tradeable/withdrawable)
    separately from "hold" (locked in open orders, conversions, etc.) --
    an asset can have a large real position while showing near-zero
    available, which looked exactly like a missing position until we
    started including hold too. Confirmed live on 2026-08-17: a GEOD
    position worth ~$7,500 (44,307 tokens) had only ~$0.02 in
    available_balance because almost the whole thing was tied up in an
    open order -- the old available-only version silently showed it as
    dust instead of the real position it was."""
    balances = []
    cursor = None
    for _ in range(20):  # hard cap so a pagination bug can't loop forever
        kwargs = {"cursor": cursor} if cursor else {}
        resp = _to_dict(_trade_client.get_accounts(**kwargs))
        for acct in resp.get("accounts", []):
            acct = acct if isinstance(acct, dict) else _to_dict(acct)
            avail = _to_dict(acct.get("available_balance"))
            hold = _to_dict(acct.get("hold"))
            try:
                avail_value = float(avail.get("value", 0))
            except (TypeError, ValueError):
                avail_value = 0.0
            try:
                hold_value = float(hold.get("value", 0))
            except (TypeError, ValueError):
                hold_value = 0.0
            if avail_value > 0 or hold_value > 0:
                balances.append((acct.get("currency", "?"), avail_value, hold_value))
        if not resp.get("has_next"):
            break
        cursor = resp.get("cursor")
        if not cursor:
            break
    return balances


def handle_balance_command():
    """Handle the /balance Telegram command -- shows free cash (USD/USDC) and
    the estimated USD value of every other open position. Each amount is the
    TOTAL balance (available + held), with a note when part of it is on
    hold (e.g. tied up in an open order) -- available-only would understate
    or completely hide a position that's mostly on hold."""
    if not TRADING_ENABLED:
        telegram_send("Trading is not enabled -- COINBASE_API_KEY / COINBASE_API_SECRET are not set on the server.")
        return
    try:
        balances = get_balances()
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ Failed to fetch balances: {e}{detail}")
        print(f"  [error] get_balances failed: {e}{detail}")
        traceback.print_exc()
        return
    if not balances:
        telegram_send("No non-zero balances found.")
        return
    cash = [b for b in balances if b[0] in ("USD", "USDC")]
    positions = [b for b in balances if b[0] not in ("USD", "USDC")]
    lines = ["💰 Balance"]
    if cash:
        lines.append("\nFree cash:")
        for currency, avail, hold in cash:
            total = avail + hold
            extra = f"  (of which {hold:,.2f} on hold)" if hold > 0 else ""
            lines.append(f"  {currency}: {total:,.2f}{extra}")
    if positions:
        lines.append("\nOpen positions:")
        for currency, avail, hold in sorted(positions, key=lambda x: x[0]):
            total = avail + hold
            price = get_current_price(f"{currency}-USD") or get_current_price(f"{currency}-USDC")
            hold_note = f", {hold:.8g} on hold" if hold > 0 else ""
            if price:
                lines.append(f"  {currency}: {total:.8g}{hold_note}  (~${total * price:,.2f})")
            else:
                lines.append(f"  {currency}: {total:.8g}{hold_note}")
    if not cash and not positions:
        lines.append("\n(nothing to show)")
    telegram_send("\n".join(lines))


def parse_and_handle_command(text):
    """Parse one inbound Telegram message and dispatch it. Every /buy and
    /sell -- market or limit -- executes (or gets placed) directly once
    sent: Telegram itself is the confirmation step (the user must
    deliberately type/send the command), there is no additional 'are you
    sure' round-trip. /buy and /sell take an optional 4th argument, a limit
    price -- with it, the order is a GTC limit order that waits on
    Coinbase's book instead of executing immediately; without it, it's a
    market order at the current price, exactly as before."""
    parts = text.strip().split()
    if not parts:
        return
    cmd = parts[0].lower()
    if cmd in ("/buy", "/sell"):
        if len(parts) not in (3, 4):
            telegram_send(
                f"Usage: {cmd} PRODUCT_ID AMOUNT_USD [, LIMIT_PRICE]\n"
                f"Market (immediate, at current price): {cmd} BTC-USD 50\n"
                f"Limit (waits until price is reached): {cmd} BTC-USD 50, 60000\n"
                f"(the comma before the price is optional -- just there to keep the two numbers apart)"
            )
            return
        product_id = parts[1].upper()
        # Accept an optional trailing comma on the amount (e.g. "50," from
        # "/buy BTC-USD 50, 60000") purely as a readability aid for
        # separating the two numbers -- strip it before parsing either one.
        try:
            amount = float(parts[2].rstrip(","))
        except ValueError:
            telegram_send(f"Amount must be a number. Got: {parts[2]}")
            return
        limit_price = None
        if len(parts) == 4:
            try:
                limit_price = float(parts[3].rstrip(","))
            except ValueError:
                telegram_send(f"Limit price must be a number. Got: {parts[3]}")
                return
            if limit_price <= 0:
                telegram_send("Limit price must be positive.")
                return
        if amount <= 0:
            telegram_send("Amount must be positive.")
            return
        if amount > MAX_ORDER_USD:
            telegram_send(f"❌ ${amount} exceeds the MAX_ORDER_USD safety cap (${MAX_ORDER_USD}). Raise it via the Render env var if intentional.")
            return
        if not TRADING_ENABLED:
            telegram_send("Trading is not enabled -- COINBASE_API_KEY / COINBASE_API_SECRET are not set on the server.")
            return
        order_kind = f"LIMIT @ {limit_price}" if limit_price else "MARKET"
        telegram_send(f"⏳ Placing {cmd[1:].upper()} order ({order_kind}): {product_id} ${amount:.2f}...")
        if cmd == "/buy":
            execute_buy_limit(product_id, amount, limit_price) if limit_price else execute_buy(product_id, amount)
        else:
            execute_sell_limit(product_id, amount, limit_price) if limit_price else execute_sell(product_id, amount)
    elif cmd == "/balance":
        handle_balance_command()
    elif cmd == "/orders":
        handle_orders_command()
    elif cmd == "/cancel":
        if len(parts) != 2:
            telegram_send("Usage: /cancel ORDER_ID\n(get the ORDER_ID from /orders)")
            return
        handle_cancel_command(parts[1])
    elif cmd == "/help":
        telegram_send(
            "Commands:\n"
            "/buy PRODUCT_ID AMOUNT_USD -- market buy, spending AMOUNT_USD immediately at the current price\n"
            "/buy PRODUCT_ID AMOUNT_USD, LIMIT_PRICE -- limit buy, waits until price reaches LIMIT_PRICE or better\n"
            "/sell PRODUCT_ID AMOUNT_USD -- market sell, selling ~AMOUNT_USD worth immediately at the current price\n"
            "/sell PRODUCT_ID AMOUNT_USD, LIMIT_PRICE -- limit sell, waits until price reaches LIMIT_PRICE or better\n"
            "(the comma before LIMIT_PRICE is optional -- just there to keep the two numbers apart)\n"
            "/orders -- list open (unfilled) limit orders\n"
            "/cancel ORDER_ID -- cancel an open limit order (ORDER_ID from /orders)\n"
            "/balance -- show free cash and open positions\n"
            "Examples:\n"
            "  /buy BTC-USD 50\n"
            "  /buy BTC-USD 50, 60000\n"
            "Trading is " + ("ENABLED" if TRADING_ENABLED else "DISABLED (no API key set)")
        )
    else:
        telegram_send(f"Unknown command: {parts[0]}. Send /help for a list of commands.")


def telegram_polling_loop():
    """Background thread: long-polls Telegram for new messages and executes
    /buy /sell /balance /help commands. Runs independently of the main scan
    loop so commands get handled promptly regardless of where the scanner is
    in its 5-minute cycle. Only messages from TELEGRAM_CHAT_ID are honored."""
    offset = load_json_file(TELEGRAM_OFFSET_FILE, {}).get("offset", 0)
    if not (TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID):
        print("  [warn] Telegram not configured -- trading command listener disabled.")
        return
    print(f"Telegram command listener started. Trading is {'ENABLED' if TRADING_ENABLED else 'DISABLED'}.")
    while True:
        try:
            resp = session.get(
                f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/getUpdates",
                params={"offset": offset, "timeout": 30},
                timeout=35,
            )
            resp.raise_for_status()
            data = resp.json()
            for update in data.get("result", []):
                offset = update["update_id"] + 1
                message = update.get("message", {})
                chat_id = str(message.get("chat", {}).get("id", ""))
                text = message.get("text", "")
                if chat_id != str(TELEGRAM_CHAT_ID):
                    continue  # ignore anyone other than the configured owner chat
                if text:
                    print(f"[telegram] received command: {text}")
                    parse_and_handle_command(text)
            save_json_file(TELEGRAM_OFFSET_FILE, {"offset": offset})
        except requests.RequestException as e:
            print(f"  [error] Telegram polling failed: {e}")
            time.sleep(5)
        except Exception:
            print("  [error] unexpected failure in Telegram polling loop")
            traceback.print_exc()
            time.sleep(5)


# ----------------------------------------------------------------------------
# Main scan loop
# ----------------------------------------------------------------------------

def run_cycle(products, state, outcomes):
    for i, product_id in enumerate(products):
        try:
            candles = fetch_candles(product_id)
            time.sleep(REQUEST_PACING_SECONDS)  # pace requests regardless of outcome
            if not candles:
                continue
            candles = drop_incomplete_last_candle(candles)

            result = analyze(candles)
            if not result:
                continue

            prev_signal = state.get(product_id, {}).get("signal", "neutral")
            new_signal = result["signal"]

            # edge-triggered: only alert on a fresh transition INTO breakout/watching
            if new_signal in ("breakout", "watching") and new_signal != prev_signal:
                notify(product_id, result)
                if new_signal == "breakout":
                    record_pending_outcome(outcomes, product_id, result, datetime.now(timezone.utc))

            state[product_id] = {"signal": new_signal, "updated": datetime.now(timezone.utc).isoformat()}

        except Exception:
            print(f"  [error] unexpected failure on {product_id}")
            traceback.print_exc()

        if (i + 1) % 50 == 0:
            print(f"  ...scanned {i + 1}/{len(products)}")

    return state, outcomes


def main():
    print("Coinbase Breakout Scanner starting.")
    print(f"Granularity={GRANULARITY_SECONDS}s  Lookback={LOOKBACK_CANDLES}  Cycle={CYCLE_SLEEP_SECONDS}s")
    print(f"Outcome tracking: evaluate after {EVALUATION_HOURS}h, win>={SUCCESS_THRESHOLD_PCT}% loss<=-{FAILURE_THRESHOLD_PCT}%")

    state = load_state()
    outcomes = load_json_file(OUTCOMES_FILE, {})
    stats = load_json_file(STATS_FILE, {})
    known_open_order_ids = set(load_json_file(OPEN_ORDERS_STATE_FILE, []))

    # One-time reset requested 2026-08-17: today's earlier breakout alerts
    # happened during heavy debugging/redeploy activity (many restarts while
    # wiring up trading) and aren't a fair signal, so win/loss tracking
    # starts clean from this deploy onward. Guarded by a marker file so this
    # only ever fires once, no matter how many times the service redeploys
    # afterward. Does NOT touch scanner_state.json (which tracks last-signal
    # per symbol, to avoid duplicate alerts) -- only the outcome/stats
    # history is cleared.
    _RESET_MARKER_FILE = "outcomes_reset_2026-08-17.marker"
    if not os.path.exists(_RESET_MARKER_FILE):
        if outcomes or stats:
            print(f"  [info] one-time reset: clearing {len(outcomes)} pending outcome(s) and stats history (requested 2026-08-17)")
        outcomes = {}
        stats = {}
        save_json_file(OUTCOMES_FILE, outcomes)
        save_json_file(STATS_FILE, stats)
        try:
            with open(_RESET_MARKER_FILE, "w") as f:
                f.write(datetime.now(timezone.utc).isoformat())
        except Exception:
            pass

    print(f"Trading: {'ENABLED' if TRADING_ENABLED else 'DISABLED (set COINBASE_API_KEY / COINBASE_API_SECRET to enable)'}")
    if TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID:
        threading.Thread(target=telegram_polling_loop, daemon=True).start()

    while True:
        cycle_start = time.time()
        try:
            now = datetime.now(timezone.utc)
            print(f"\n=== Cycle start {now.isoformat()} ===")

            products = fetch_products()
            print(f"Scanning {len(products)} pairs on Coinbase ({'/'.join(sorted(QUOTE_CURRENCIES))})...")

            if products:
                state, outcomes = run_cycle(products, state, outcomes)
                save_state(state)

            outcomes, stats = evaluate_pending_outcomes(outcomes, stats, now)
            save_json_file(OUTCOMES_FILE, outcomes)
            save_json_file(STATS_FILE, stats)

            known_open_order_ids = check_order_fills(known_open_order_ids)
            save_json_file(OPEN_ORDERS_STATE_FILE, list(known_open_order_ids))
        except Exception:
            # Per-product errors are already caught inside run_cycle, but
            # anything outside that (fetch_products, evaluate_pending_outcomes,
            # disk I/O, etc.) used to be unhandled -- one bad response or a
            # transient error would silently kill the entire 24/7 process
            # until Render noticed and restarted it. Catch broadly here so a
            # single bad cycle can't take the whole scanner down.
            print("  [error] unexpected failure in main cycle -- scanner will keep running")
            traceback.print_exc()

        elapsed = time.time() - cycle_start
        sleep_for = max(0, CYCLE_SLEEP_SECONDS - elapsed)
        print(f"Cycle done in {elapsed:.1f}s. Sleeping {sleep_for:.1f}s.")
        time.sleep(sleep_for)


if __name__ == "__main__":
    main()
