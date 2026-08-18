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
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

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
# Confirmed live on 2026-08-18 (PUMP-USD): the nearest older high above
# resistance can sit just 0.3% away, which is technically "the next
# resistance" but not something anyone can actually trade around -- too
# close to leave room for entry/exit or normal noise. find_price_target()
# now skips any candidate level closer than this and keeps looking (or
# extends the measured-move projection) so the printed target always
# represents a real, actionable move, not just the nearest price above
# last_close.
MIN_TARGET_PCT = float(os.environ.get("MIN_TARGET_PCT", "1.5"))

# Confirmed live on 2026-08-18 (PRCL-USD: +130% in 24h, RSI 91, still fired
# a plain BREAKOUT alert with a +4.9% target and no hint that price was
# already this extended). The breakout criteria above (volume/momentum/
# close-strength) only look at the SINGLE candle that triggered the signal
# -- they say nothing about how far price has already run over the last
# day. Chasing a coin after a >100% day, at RSI 91, is a fundamentally
# different (much higher reversal-risk) situation than a fresh breakout at
# RSI 60, even though both pass the same per-candle checks. Rather than
# silently suppress these (the breakout is real, and blow-off continuations
# do happen), the alert now surfaces the missing context -- 24h price
# change is added to every alert, and an explicit warning line is appended
# when either threshold below is crossed -- so the decision to chase stays
# with the user, but is now an informed one.
EXTENDED_MOVE_24H_PCT = float(os.environ.get("EXTENDED_MOVE_24H_PCT", "50"))
EXTENDED_MOVE_RSI = float(os.environ.get("EXTENDED_MOVE_RSI", "85"))

CYCLE_SLEEP_SECONDS = 300           # 5 minutes between full scan cycles
REQUEST_PACING_SECONDS = 0.35       # ~3 requests/sec, safely under Coinbase's public rate limit
MAX_RETRIES = 3

# Persistent state directory. Render's default filesystem is EPHEMERAL --
# every file written to the plain working directory is wiped on each
# deploy. Confirmed live on 2026-08-18: trades.json (and therefore
# /history) silently reset to empty after a routine code deploy, even
# though nothing was wrong with the trades themselves on Coinbase's side.
# Fixed by attaching a persistent Disk in Render (mounted at /var/data)
# and pointing all state files at it instead. Falls back to the plain
# working directory if DATA_DIR doesn't exist -- e.g. running locally, or
# before a disk is attached -- so this doesn't break anything else.
DATA_DIR = os.environ.get("DATA_DIR", "/var/data")
if not os.path.isdir(DATA_DIR):
    DATA_DIR = "."


def _data_path(filename):
    return os.path.join(DATA_DIR, filename)


STATE_FILE = _data_path("scanner_state.json")   # tracks last signal per symbol, to avoid duplicate alerts
ALERTS_LOG_FILE = _data_path("alerts_log.jsonl")
OPEN_ORDERS_STATE_FILE = _data_path("open_orders_state.json")  # which limit order IDs were open last cycle, to detect fills
TRADES_FILE = _data_path("trades.json")         # ledger of every /buy /sell placed via the bot + limit-order resolutions (requested 2026-08-18, position tracking)

# --- Outcome tracking (win-rate stats for breakout signals) -----------------
OUTCOMES_FILE = _data_path("outcomes.json")           # pending + resolved trade outcomes
STATS_FILE = _data_path("stats.json")                 # cumulative win/loss counters
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

# All trade times are stored internally in UTC (datetime.now(timezone.utc)) --
# that never changes and is DST-safe. /history only converts to this
# timezone at DISPLAY time, so changing it doesn't require re-writing any
# stored data. Confirmed live on 2026-08-18 that showing raw UTC in /history
# was confusing next to the user's own wall clock (Amsterdam) -- defaults to
# Europe/Amsterdam; override via the DISPLAY_TIMEZONE env var if needed.
# Falls back to UTC if the configured zone name isn't recognized (e.g. the
# tzdata package is missing) rather than crashing the whole bot over a
# cosmetic display setting.
try:
    DISPLAY_TIMEZONE = ZoneInfo(os.environ.get("DISPLAY_TIMEZONE", "Europe/Amsterdam"))
except ZoneInfoNotFoundError:
    DISPLAY_TIMEZONE = timezone.utc

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
TELEGRAM_OFFSET_FILE = _data_path("telegram_offset.json")  # tracks which Telegram messages were already handled

TRADING_ENABLED = bool(COINBASE_API_KEY and COINBASE_API_SECRET)
_trade_client = None

# Order IDs for limit orders just placed by the Telegram command handler
# (which runs on its own daemon thread), not yet folded into the main
# loop's known-open-orders tracking. Needed because a marketable limit
# order (one whose price already crosses the spread) can fill within a
# second or two of being placed -- faster than the next scan cycle's
# check_order_fills() call. Without this, such an order is NEVER seen as
# "open" by list_orders() before it disappears (already filled), so it
# never triggers the fill notification at all -- confirmed live on
# 2026-08-18 with a "/sell SOL-USDC 500, 76.92" limit sell that was
# marketable at placement and filled immediately, but the user got no
# Telegram confirmation because check_order_fills() only detects orders
# that go from open -> gone between two cycles it actually observed.
# check_order_fills() folds this set into known_open_ids at the start of
# every cycle so even an instantly-filled order gets caught as "resolved"
# on the very next check.
_pending_new_order_ids = set()

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


def fetch_candles(product_id, granularity=None):
    """granularity defaults to GRANULARITY_SECONDS (the main scan's hourly
    resolution). Pass a different value -- e.g. 86400 for daily candles --
    to pull a much longer window of history for a specific one-off purpose
    (see enhance_breakout_target) without touching the main scan's
    resolution or cadence. Coinbase's candle endpoint returns roughly the
    same ~300-candle cap regardless of granularity, so daily candles cover
    ~300 days versus the ~12 days hourly candles cover for the same request."""
    if granularity is None:
        granularity = GRANULARITY_SECONDS
    data = get_json(f"/products/{product_id}/candles", params={"granularity": granularity})
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

    Beyond that, both methods also guarantee the RETURNED target clears
    last_close by at least MIN_TARGET_PCT -- a level that's technically
    ahead of price but only by a fraction of a percent (e.g. +0.3%) is just
    as unusable as one behind it as a forward OBJECTIVE; there's no real
    room for entry/exit or ordinary noise. Confirmed live on 2026-08-18
    (PUMP-USD: nearest older high only 0.3% above last_close). For
    next_resistance this means skipping past too-near old highs to the next
    one that actually clears the bar; for measured_move it means the same
    range-height projection loop already used to clear last_close also
    keeps extending until it clears this minimum too.

    IMPORTANT: skipping a too-close old high for the *objective* doesn't
    make it disappear as an *obstacle* -- price still has to get through it
    first, and a near ceiling right after a breakout is a real reason a
    trade can stall or reverse early. Silently dropping it would hide that
    risk, which is worse than an unhelpful target number (a user asked this
    directly on 2026-08-18: "how can this be a breakout if the target is
    only 0.5% away?"). So this also returns near_resistance -- the nearest
    older high above last_close REGARDLESS of the minimum, or None if there
    isn't one -- so the caller can flag it explicitly instead of hiding it.

    Caveat: both methods are limited to whatever history Coinbase's candle
    endpoint returns for this granularity (roughly the last ~300 candles,
    i.e. ~12 days at the default 1h granularity) -- a genuinely older
    resistance level further back than that won't be seen.
    """
    highs = [c[2] for c in candles]
    lows = [c[1] for c in candles]
    min_target_price = last_close * (1 + MIN_TARGET_PCT / 100)

    older_highs = highs[: -(LOOKBACK_CANDLES + 1)]
    all_higher_levels = [h for h in older_highs if h > resistance and h > last_close]
    near_resistance = min(all_higher_levels) if all_higher_levels else None

    qualifying_levels = [h for h in all_higher_levels if h >= min_target_price]
    if qualifying_levels:
        return min(qualifying_levels), "next_resistance", near_resistance

    window_lows = lows[-LOOKBACK_CANDLES - 1 : -1]
    range_low = min(window_lows) if window_lows else resistance
    range_height = resistance - range_low
    if range_height <= 0:
        range_height = resistance * (MEASURED_MOVE_FALLBACK_PCT / 100)
    target = resistance + range_height
    # Keep projecting the same range height forward until the target clears
    # BOTH last_close (a strong breakout candle can run past resistance +
    # one range-height) AND the minimum actionable distance above it.
    # range_height is guaranteed > 0 by this point, so this always terminates.
    while target <= last_close or target < min_target_price:
        target += range_height
    return target, "measured_move", near_resistance


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

    # 24h price change -- close price ~24h ago vs the current close. Missing
    # from the alert entirely until 2026-08-18 (see EXTENDED_MOVE_* above);
    # falls back to the earliest close we actually have if there's less
    # than a full day of history, same graceful-degradation approach used
    # elsewhere rather than returning None and dropping the field.
    close_24h_ago = candles[-candles_per_day - 1][4] if len(candles) > candles_per_day else candles[0][4]
    pct_change_24h = ((last_close - close_24h_ago) / close_24h_ago * 100) if close_24h_ago else None

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
    near_resistance_price, near_resistance_pct = None, None
    if signal == "breakout":
        target_price, target_method, near_resistance_price = find_price_target(
            candles, resistance, last_close)
        target_pct = ((target_price - last_close) / last_close) * 100
        if near_resistance_price is not None:
            near_resistance_pct = ((near_resistance_price - last_close) / last_close) * 100
            # Only worth flagging separately if it's NOT already the target
            # we're reporting (i.e. it was actually skipped for being too
            # close) -- if it cleared the minimum, it just IS target_price,
            # already visible, no need to repeat it as a second line.
            if near_resistance_pct >= MIN_TARGET_PCT:
                near_resistance_price, near_resistance_pct = None, None

    # Flag (never suppress) a signal that fires on top of an already very
    # extended move -- see EXTENDED_MOVE_* above. Either a large 24h price
    # change or a deeply overbought RSI is enough on its own to warrant the
    # warning; a coin can be extended on one axis without the other (e.g. a
    # huge 24h move that's already cooled off RSI-wise, or a sharp RSI spike
    # within a smaller 24h range).
    extended_move = bool(
        (pct_change_24h is not None and pct_change_24h >= EXTENDED_MOVE_24H_PCT)
        or (rsi_val is not None and rsi_val >= EXTENDED_MOVE_RSI)
    )

    return {
        "last_close": last_close,
        "resistance": resistance,
        "vol_ratio": vol_ratio,
        "rsi": rsi_val,
        "dist_pct": dist_pct,
        "close_position": close_position,
        "daily_volume_usd": daily_volume_usd,
        "pct_change_24h": pct_change_24h,
        "extended_move": extended_move,
        "signal": signal,
        "target_price": target_price,
        "target_pct": target_pct,
        "target_method": target_method,
        "near_resistance_price": near_resistance_price,
        "near_resistance_pct": near_resistance_pct,
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
    if result.get("pct_change_24h") is not None:
        text += f"\n24h change: {result['pct_change_24h']:+.1f}%"
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
    if result.get("near_resistance_price") is not None:
        # The nearest older high sits closer than MIN_TARGET_PCT, so it was
        # skipped as the reported *objective* above -- but it's still a
        # real obstacle price has to clear first. Surfacing it explicitly
        # rather than silently dropping it: a user asked directly on
        # 2026-08-18 whether skipping it made the breakout itself
        # questionable -- it doesn't (breakout = what already happened,
        # target = separate forward guess), but hiding a near ceiling
        # would have been misleading either way.
        text += (
            f"\nℹ️ Note: an older high sits just "
            f"{result['near_resistance_pct']:+.1f}% away at {result['near_resistance_price']:.6g} -- "
            "may cause an early stall/pullback before the target above."
        )
    if result.get("extended_move"):
        # Confirmed live on 2026-08-18 (PRCL-USD: +130% in 24h, RSI 91) --
        # the per-candle breakout checks above say nothing about how far
        # price already ran before this candle. Not a reason to hide the
        # alert (the breakout itself is real), but a reason to flag it
        # explicitly: entering here is chasing an already-extended move,
        # not catching a fresh one, and reversals off overbought spikes can
        # be sharp and fast.
        text += (
            "\n⚠️ Extended move -- price is already up "
            f"{result.get('pct_change_24h', 0):+.0f}% in 24h with RSI {result['rsi']:.0f}. "
            "Higher risk of a sharp pullback from here; this is a breakout "
            "continuation, not a fresh setup."
        )

    print(f"[ALERT] {product_id}: {result['signal'].upper()} "
          f"price={result['last_close']:.4f} resistance={result['resistance']:.4f} "
          f"vol_ratio={result['vol_ratio']:.2f}x rsi={result['rsi']:.0f}"
          + (f" chg24h={result['pct_change_24h']:+.1f}%" if result.get("pct_change_24h") is not None else "")
          + (f" target={result['target_price']:.4f} ({result['target_pct']:+.1f}%, {result['target_method']})"
             if result.get("target_price") else "")
          + (" EXTENDED" if result.get("extended_move") else ""))

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


def _format_display_time(iso_str):
    """Convert a stored UTC ISO timestamp (from datetime.now(timezone.utc)
    .isoformat()) to DISPLAY_TIMEZONE for /history output. Falls back to
    showing the raw stored value labeled UTC if it can't be parsed, rather
    than letting a bad/missing timestamp break the whole /history reply."""
    if not iso_str:
        return "? UTC"
    try:
        dt = datetime.fromisoformat(iso_str)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        local_dt = dt.astimezone(DISPLAY_TIMEZONE)
        tz_label = local_dt.tzname() or str(DISPLAY_TIMEZONE)
        return local_dt.strftime("%Y-%m-%d %H:%M") + f" {tz_label}"
    except (ValueError, TypeError):
        return str(iso_str)[:16].replace("T", " ") + " UTC"


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


def _floor_to_precision(value, decimals=8):
    """Floor value down to `decimals` decimal places -- used whenever a
    cash amount (usd_amount, or an entire available cash balance) is
    converted into a base-currency order size for a LIMIT order, so the
    resulting notional (base_size * limit_price) can never round UP past
    the cash amount it's meant to fit inside.

    Plain f-string formatting (f"{x:.8f}") rounds to the NEAREST 8th
    decimal, which can round up and push the order fractionally over
    budget. Confirmed live on 2026-08-18: "/buy SOL-USDC all, 76.90"
    against exactly $6,271.52 available USDC was rejected by Coinbase
    with INSUFFICIENT_FUND, because base_size = 6271.52 / 76.90 rounded
    up in its 8th decimal, making base_size * 76.90 a hair more than the
    $6,271.52 actually available. Flooring instead of rounding guarantees
    the computed size never costs more than the cash it's derived from.

    NOTE: this alone turned out not to be enough for GTC limit BUY orders
    sized off 100% of available cash -- see execute_buy_all()'s shrinking
    retry loop for the rest of the fix (Coinbase apparently reserves a
    little more than the bare notional for a resting limit order, most
    likely fee headroom in case it fills as taker)."""
    factor = 10 ** decimals
    return math.floor(value * factor) / factor


def _is_insufficient_funds_error(text):
    """True if a Coinbase error string indicates a funds/balance shortfall
    (INSUFFICIENT_FUND, or the human-readable "Insufficient balance...")
    rather than some other rejection reason. Used to decide whether it's
    worth retrying an order with a smaller amount, versus surfacing the
    error immediately."""
    upper = text.upper()
    return "INSUFFICIENT_FUND" in upper or "INSUFFICIENT BALANCE" in upper


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


def record_trade(entry):
    """Append one entry to the persisted trade/position ledger (trades.json)
    and save. This is what /history and /positions read from -- called on
    every successful market execution, limit-order placement, and eventual
    limit-order resolution (filled/cancelled/expired), so there's a full,
    durable record of everything the bot has actually done, independent of
    Telegram's own chat history. Caps the file at the most recent 500
    entries so it doesn't grow forever."""
    trades = load_json_file(TRADES_FILE, [])
    trades.append(entry)
    if len(trades) > 500:
        trades = trades[-500:]
    save_json_file(TRADES_FILE, trades)


def _try_fetch_fill_info(order_id):
    """Best-effort lookup of an order's filled_size/average_filled_price/
    total_fees immediately after placing it. Market orders on Coinbase
    typically fill within a second or two, so this usually already has
    real fill data by the time we ask -- but it's purely a nice-to-have
    for the trade log, never allowed to raise or block the calling
    function.

    total_fees is exactly what Coinbase charged for this order, in the
    pair's own quote currency (USD or USDC) -- not converted to EUR or
    any other account display currency, so it lines up with amount_usd
    and price everywhere else in the ledger (added 2026-08-18, per
    request to track real fees paid instead of estimating from the
    published fee-tier schedule)."""
    try:
        order = _to_dict(_to_dict(_trade_client.get_order(order_id)).get("order", {}))
        return order.get("filled_size"), order.get("average_filled_price"), order.get("total_fees")
    except Exception:
        return None, None, None


def execute_buy(product_id, usd_amount):
    """Market-buy usd_amount worth of product_id. Reports result via Telegram."""
    order_id = str(uuid.uuid4())
    try:
        resp = _to_dict(_trade_client.market_order_buy(
            client_order_id=order_id, product_id=product_id, quote_size=str(usd_amount)))
        if resp.get("success"):
            # Coinbase assigns its OWN order_id, separate from the
            # client_order_id we generated to send the request -- get_order,
            # list_orders and cancel_orders all key off Coinbase's order_id,
            # not ours. Using the wrong one here made every fill lookup
            # silently fail (confirmed live 2026-08-18: check_order_fills
            # got a 404 "order with this orderID was not found" trying to
            # look up our client_order_id).
            order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or order_id
            telegram_send(f"✅ BUY executed: {product_id} for ${usd_amount}\nOrder ID: {order_id}")
            filled_size, avg_price, fee = _try_fetch_fill_info(order_id)
            record_trade({
                "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                "side": "BUY", "kind": "market", "status": "executed",
                "amount_usd": usd_amount, "base_size": filled_size, "price": avg_price,
                "fee_usd": fee, "order_id": order_id,
            })
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
            # See execute_buy()'s comment -- use Coinbase's own order_id
            # from here on, not the client_order_id we generated to place
            # the order.
            order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or order_id
            telegram_send(f"✅ SELL executed: {product_id} (~${usd_amount})\nOrder ID: {order_id}")
            filled_size, avg_price, fee = _try_fetch_fill_info(order_id)
            record_trade({
                "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                "side": "SELL", "kind": "market", "status": "executed",
                "amount_usd": usd_amount, "base_size": filled_size or f"{base_size:.8f}", "price": avg_price,
                "fee_usd": fee, "order_id": order_id,
            })
        else:
            telegram_send(f"❌ SELL failed: {product_id} for ${usd_amount}\n{resp.get('error_response', resp)}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ SELL error: {product_id} for ${usd_amount}\n{e}{detail}")
        print(f"  [error] sell order failed: {e}{detail}")
        traceback.print_exc()


def execute_buy_all(product_id, limit_price=None):
    """Spend the ENTIRE available balance of product_id's QUOTE currency to
    buy -- e.g. "/buy SOL-USDC all" spends every available USDC on SOL at
    the current market price, or "/buy SOL-USDC all, 76.90" places a GTC
    limit order reserving that entire USDC balance at 76.90 (or better).
    The quote currency is read straight from product_id (the part after
    the dash) so this works correctly whether the pair is quoted in USD
    or USDC -- spending the wrong cash balance would fail with the same
    "account is not available" error seen with SOL-USD vs SOL-USDC.

    Still enforces MAX_ORDER_USD, same as every other order path -- "buy
    all" is deliberate, not a typo, but the cash balance could still have
    grown past the cap since it was set, and the cap exists precisely so
    no single command can move more than the user has explicitly allowed
    without raising it first."""
    quote_currency = product_id.split("-")[1] if "-" in product_id else None
    if quote_currency not in ("USD", "USDC"):
        telegram_send(f"❌ BUY ALL failed: {product_id} isn't quoted in USD or USDC -- can't tell which cash balance to spend.")
        return
    try:
        balances = get_balances()
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ BUY ALL failed: couldn't fetch balances for {product_id}\n{e}{detail}")
        print(f"  [error] execute_buy_all({product_id}): get_balances failed: {e}{detail}")
        traceback.print_exc()
        return
    match = next((b for b in balances if b[0] == quote_currency), None)
    if not match or match[1] <= 0:
        held_note = ""
        if match and match[2] > 0:
            held_note = f" ({match[2]:,.2f} {quote_currency} exists but is on hold, e.g. tied up in an open order -- cancel it first with /cancel)"
        telegram_send(f"❌ BUY ALL failed: no available {quote_currency} balance to spend.{held_note}")
        return
    _, available, held = match
    if available > MAX_ORDER_USD:
        telegram_send(
            f"❌ BUY ALL blocked: {available:,.2f} {quote_currency} exceeds the "
            f"MAX_ORDER_USD safety cap (${MAX_ORDER_USD:,.0f}). Raise it via the Render env var if intentional."
        )
        return
    order_id = str(uuid.uuid4())
    held_note = f"\n({held:,.2f} {quote_currency} still on hold, not included)" if held > 0 else ""

    if limit_price:
        # Limit buy: reserve the whole cash balance as base_size at
        # limit_price, exactly like execute_buy_limit() but sized from the
        # full available balance instead of a specified usd_amount.
        # _floor_to_precision() alone (rounding the notional DOWN instead
        # of to-nearest) turned out not to be enough -- confirmed live on
        # 2026-08-18 that Coinbase still rejects a GTC limit buy sized at
        # exactly 100% of available cash with INSUFFICIENT_FUND, at more
        # than one price (76.90 and 77.00), ruling out a one-off rounding
        # fluke. Coinbase appears to reserve a little more than the bare
        # notional for a resting limit order (most likely fee headroom in
        # case it fills as taker). Rather than guess a fixed safety-margin
        # percentage, retry with a slightly smaller slice of the available
        # cash each time the rejection is specifically INSUFFICIENT_FUND,
        # until it succeeds or the margin needed becomes implausibly large
        # (at which point something else is actually wrong).
        spend_fraction = 1.0
        last_error_text = None
        for attempt in range(8):
            spend = available * spend_fraction
            base_size = _floor_to_precision(spend / limit_price)
            attempt_order_id = str(uuid.uuid4())
            error_text = None
            try:
                resp = _to_dict(_trade_client.limit_order_gtc_buy(
                    client_order_id=attempt_order_id, product_id=product_id,
                    base_size=f"{base_size:.8f}", limit_price=str(limit_price)))
            except Exception as e:
                detail = _coinbase_error_detail(e)
                error_text = f"{e}{detail}"
                resp = None
            if resp is not None and resp.get("success"):
                # Use Coinbase's own order_id from here on -- see
                # execute_buy()'s comment on why attempt_order_id (our
                # client_order_id) can't be used for get_order lookups.
                attempt_order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or attempt_order_id
                margin_note = (
                    f"\n(reserved {spend:,.2f} of {available:,.2f} {quote_currency} -- "
                    f"Coinbase needed a small buffer beyond the exact notional)"
                    if spend_fraction < 1.0 else ""
                )
                telegram_send(
                    f"✅ LIMIT BUY ALL placed: {product_id} ~{spend:,.2f} {quote_currency} @ {limit_price}\n"
                    f"Order ID: {attempt_order_id}{held_note}{margin_note}\n"
                    f"(Stays open until filled or cancelled -- check /orders, cancel with /cancel {attempt_order_id})"
                )
                record_trade({
                    "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                    "side": "BUY", "kind": "limit", "status": "placed",
                    "amount_usd": spend, "base_size": f"{base_size:.8f}", "price": limit_price,
                    "order_id": attempt_order_id,
                })
                _pending_new_order_ids.add(attempt_order_id)
                return
            if error_text is None:
                error_text = str(resp.get('error_response', resp))
            if _is_insufficient_funds_error(error_text) and attempt < 7:
                last_error_text = error_text
                spend_fraction -= 0.005
                continue
            telegram_send(f"❌ LIMIT BUY ALL failed: {product_id} ~{spend:,.2f} {quote_currency} @ {limit_price}\n{error_text}")
            print(f"  [error] limit buy-all order failed: {error_text}")
            return
        telegram_send(
            f"❌ LIMIT BUY ALL failed: {product_id} -- still INSUFFICIENT_FUND after retrying down to "
            f"{spend_fraction * 100:.1f}% of available balance ({available:,.2f} {quote_currency}). "
            f"Last error: {last_error_text}"
        )
        return

    try:
        resp = _to_dict(_trade_client.market_order_buy(
            client_order_id=order_id, product_id=product_id, quote_size=str(available)))
        if resp.get("success"):
            order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or order_id
            telegram_send(
                f"✅ BUY ALL executed: {product_id} -- spent {available:,.2f} {quote_currency}"
                f"\nOrder ID: {order_id}{held_note}"
            )
            filled_size, avg_price, fee = _try_fetch_fill_info(order_id)
            record_trade({
                "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                "side": "BUY", "kind": "market", "status": "executed",
                "amount_usd": available, "base_size": filled_size, "price": avg_price,
                "fee_usd": fee, "order_id": order_id,
            })
        else:
            telegram_send(f"❌ BUY ALL failed: {product_id}\n{resp.get('error_response', resp)}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ BUY ALL error: {product_id}\n{e}{detail}")
        print(f"  [error] buy-all order failed: {e}{detail}")
        traceback.print_exc()


def execute_sell_all(product_id, limit_price=None):
    """Sell the ENTIRE available balance of product_id's base currency --
    e.g. "/sell SOL-USDC all" sells every available SOL at the current
    market price, or "/sell SOL-USDC all, 76.90" places a GTC limit order
    for that entire SOL balance at 76.90 (or better).

    Unlike execute_sell(), this does not take a usd_amount and does not
    estimate a base_size from it. It reads the real available_balance
    straight from Coinbase (via get_balances()) and sells exactly that,
    so there's no risk of a stale/rounded guess leaving dust behind or
    overshooting into an "insufficient funds" rejection. Only the
    AVAILABLE portion is sold (not held) -- balance tied up in an open
    order can't be sold until that order is filled or cancelled; the
    Telegram reply says so explicitly if any is on hold.

    Still enforces MAX_ORDER_USD, same as every other order path -- "sell
    all" is deliberate, not a typo, but the position could still have
    grown past the cap since it was set, and the cap exists precisely so
    no single command can move more than the user has explicitly allowed
    without raising it first."""
    base_currency = product_id.split("-")[0]
    try:
        balances = get_balances()
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ SELL ALL failed: couldn't fetch balances for {product_id}\n{e}{detail}")
        print(f"  [error] execute_sell_all({product_id}): get_balances failed: {e}{detail}")
        traceback.print_exc()
        return
    match = next((b for b in balances if b[0] == base_currency), None)
    if not match or match[1] <= 0:
        held_note = ""
        if match and match[2] > 0:
            held_note = f" ({match[2]:.8g} {base_currency} exists but is on hold, e.g. tied up in an open order -- cancel it first with /cancel)"
        telegram_send(f"❌ SELL ALL failed: no available {base_currency} balance to sell.{held_note}")
        return
    _, available, held = match
    if limit_price:
        # A limit sell executes at limit_price or better -- that's the
        # right number for the MAX_ORDER_USD estimate, so there's no need
        # to also fetch the live market price. Confirmed live on
        # 2026-08-18: "/sell SOL-USDC all, 77.14" failed outright because
        # Coinbase's public market-data endpoint (a separate API surface
        # from the one used to place trades) has no candles listing for
        # SOL-USDC at all (404) -- even though SOL-USDC trades fine
        # through the actual trading API. A limit order shouldn't depend
        # on an endpoint it doesn't actually need.
        usd_value = available * limit_price
    else:
        price = get_current_price(product_id)
        if not price:
            telegram_send(f"❌ SELL ALL failed: couldn't fetch current price for {product_id}")
            return
        usd_value = available * price
    if usd_value > MAX_ORDER_USD:
        telegram_send(
            f"❌ SELL ALL blocked: {available:.8g} {base_currency} (~${usd_value:,.2f}) exceeds the "
            f"MAX_ORDER_USD safety cap (${MAX_ORDER_USD:,.0f}). Raise it via the Render env var if intentional."
        )
        return
    order_id = str(uuid.uuid4())
    held_note = f"\n({held:.8g} {base_currency} still on hold, not included)" if held > 0 else ""

    if limit_price:
        # Limit sell: the whole available base_size at limit_price, exactly
        # like execute_sell_limit() but sized from the full available
        # balance instead of a specified usd_amount.
        try:
            resp = _to_dict(_trade_client.limit_order_gtc_sell(
                client_order_id=order_id, product_id=product_id,
                base_size=f"{available:.8f}", limit_price=str(limit_price)))
            if resp.get("success"):
                # Use Coinbase's own order_id from here on -- see
                # execute_buy()'s comment for why the client_order_id we
                # generated to place the order can't be used for get_order
                # lookups (confirmed live 2026-08-18: this exact order
                # type -- "/sell ... all, LIMIT" -- 404'd in
                # check_order_fills because of this mismatch).
                order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or order_id
                telegram_send(
                    f"✅ LIMIT SELL ALL placed: {product_id} {available:.8g} {base_currency} @ {limit_price}\n"
                    f"Order ID: {order_id}{held_note}\n"
                    f"(Stays open until filled or cancelled -- check /orders, cancel with /cancel {order_id})"
                )
                record_trade({
                    "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                    "side": "SELL", "kind": "limit", "status": "placed",
                    "amount_usd": usd_value, "base_size": f"{available:.8f}", "price": limit_price,
                    "order_id": order_id,
                })
                _pending_new_order_ids.add(order_id)
            else:
                telegram_send(f"❌ LIMIT SELL ALL failed: {product_id} {available:.8g} {base_currency} @ {limit_price}\n{resp.get('error_response', resp)}")
        except Exception as e:
            detail = _coinbase_error_detail(e)
            telegram_send(f"❌ LIMIT SELL ALL error: {product_id} {available:.8g} {base_currency} @ {limit_price}\n{e}{detail}")
            print(f"  [error] limit sell-all order failed: {e}{detail}")
            traceback.print_exc()
        return

    try:
        resp = _to_dict(_trade_client.market_order_sell(
            client_order_id=order_id, product_id=product_id, base_size=f"{available:.8f}"))
        if resp.get("success"):
            order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or order_id
            telegram_send(
                f"✅ SELL ALL executed: {product_id} -- sold {available:.8g} {base_currency} (~${usd_value:,.2f})"
                f"\nOrder ID: {order_id}{held_note}"
            )
            filled_size, avg_price, fee = _try_fetch_fill_info(order_id)
            record_trade({
                "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                "side": "SELL", "kind": "market", "status": "executed",
                "amount_usd": usd_value, "base_size": filled_size or f"{available:.8f}", "price": avg_price,
                "fee_usd": fee, "order_id": order_id,
            })
        else:
            telegram_send(f"❌ SELL ALL failed: {product_id}\n{resp.get('error_response', resp)}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ SELL ALL error: {product_id}\n{e}{detail}")
        print(f"  [error] sell-all order failed: {e}{detail}")
        traceback.print_exc()


def execute_buy_limit(product_id, usd_amount, limit_price):
    """Place a GTC (good-til-cancelled) limit buy: the order sits open on
    Coinbase's book at limit_price (or better) until it fills or is
    cancelled -- unlike a market order, it does NOT execute immediately.
    usd_amount is converted to a base-currency size using limit_price
    (not the current market price), since that's the price it will
    actually transact at if/when it fills."""
    order_id = str(uuid.uuid4())
    # Floor (not round) so the reserved cost never exceeds usd_amount --
    # see _floor_to_precision()'s docstring for why plain rounding can
    # push a LIMIT order's true cost fractionally over budget.
    base_size = _floor_to_precision(usd_amount / limit_price)
    try:
        resp = _to_dict(_trade_client.limit_order_gtc_buy(
            client_order_id=order_id, product_id=product_id,
            base_size=f"{base_size:.8f}", limit_price=str(limit_price)))
        if resp.get("success"):
            # Use Coinbase's own order_id from here on -- see
            # execute_buy()'s comment for why the client_order_id we
            # generated to place the order can't be used for get_order
            # lookups.
            order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or order_id
            telegram_send(
                f"✅ LIMIT BUY placed: {product_id} ~${usd_amount} @ {limit_price}\n"
                f"Order ID: {order_id}\n"
                f"(Stays open until filled or cancelled -- check /orders, cancel with /cancel {order_id})"
            )
            # status "placed", not "executed" -- this is not a fill yet, just
            # an order sitting on the book. check_order_fills() appends a
            # second ledger entry (status filled/cancelled/expired) once its
            # fate is known, so /history shows the full lifecycle.
            record_trade({
                "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                "side": "BUY", "kind": "limit", "status": "placed",
                "amount_usd": usd_amount, "base_size": f"{base_size:.8f}", "price": limit_price,
                "order_id": order_id,
            })
            _pending_new_order_ids.add(order_id)
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
    # Floor (not round) so this never asks to sell fractionally more
    # coin than usd_amount / limit_price implies -- same rounding-up
    # hazard as the buy side's _floor_to_precision().
    base_size = _floor_to_precision(usd_amount / limit_price)
    try:
        resp = _to_dict(_trade_client.limit_order_gtc_sell(
            client_order_id=order_id, product_id=product_id,
            base_size=f"{base_size:.8f}", limit_price=str(limit_price)))
        if resp.get("success"):
            # Use Coinbase's own order_id from here on -- see
            # execute_buy()'s comment for why the client_order_id we
            # generated to place the order can't be used for get_order
            # lookups.
            order_id = resp.get("order_id") or (resp.get("success_response") or {}).get("order_id") or order_id
            telegram_send(
                f"✅ LIMIT SELL placed: {product_id} ~${usd_amount} @ {limit_price}\n"
                f"Order ID: {order_id}\n"
                f"(Stays open until filled or cancelled -- check /orders, cancel with /cancel {order_id})"
            )
            record_trade({
                "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
                "side": "SELL", "kind": "limit", "status": "placed",
                "amount_usd": usd_amount, "base_size": f"{base_size:.8f}", "price": limit_price,
                "order_id": order_id,
            })
            _pending_new_order_ids.add(order_id)
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

    # Pick up any order placed since the last cycle (by the Telegram
    # command thread) even if it's not in known_open_ids yet -- see
    # _pending_new_order_ids' docstring for why this matters.
    if _pending_new_order_ids:
        known_open_ids = known_open_ids | _pending_new_order_ids
        _pending_new_order_ids.clear()

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
        fee = order.get("total_fees")
        icon = {"FILLED": "✅", "CANCELLED": "🚫", "EXPIRED": "⌛"}.get(status, "ℹ️")
        fee_note = ""
        if status == "FILLED" and fee not in (None, ""):
            try:
                quote_ccy = product_id.split("-")[1] if "-" in product_id else "USD"
                fee_note = f"\nFee: {float(fee):.2f} {quote_ccy}"
            except (TypeError, ValueError):
                pass
        telegram_send(
            f"{icon} Limit order {status}: {side} {product_id}\n"
            f"Filled: {filled_size} @ avg {avg_price}{fee_note}\n"
            f"Order ID: {order_id}"
        )
        # Second ledger entry for this order_id (the first was "placed", from
        # execute_buy_limit/execute_sell_limit) -- gives /history and
        # /positions the order's final outcome, not just its opening.
        record_trade({
            "time": datetime.now(timezone.utc).isoformat(), "product_id": product_id,
            "side": side, "kind": "limit", "status": status.lower(),
            "base_size": filled_size, "price": avg_price, "fee_usd": fee, "order_id": order_id,
        })

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


def _compute_avg_entry_prices():
    """Build a simple average-cost-basis ledger per product_id by replaying
    trades.json in order: tracks running quantity and running cost basis
    per symbol using the AVERAGE COST method (not FIFO) -- on a partial
    sell, the average entry price is unchanged, only quantity and total
    cost basis shrink proportionally. Only counts entries with status
    "executed" (market fills) or "filled" (resolved limit orders) that
    have a known numeric base_size and price -- a limit order still sitting
    at status "placed" isn't an actual transaction yet, so it's skipped.
    Returns {product_id: avg_entry_price}."""
    trades = load_json_file(TRADES_FILE, [])
    ledger = {}  # product_id -> {"qty": float, "cost": float}
    for t in trades:
        if t.get("status") not in ("executed", "filled"):
            continue
        product_id = t.get("product_id")
        side = t.get("side")
        try:
            size = float(t.get("base_size"))
            price = float(t.get("price"))
        except (TypeError, ValueError):
            continue
        if size <= 0 or price <= 0:
            continue
        pos = ledger.setdefault(product_id, {"qty": 0.0, "cost": 0.0})
        if side == "BUY":
            pos["qty"] += size
            pos["cost"] += size * price
        elif side == "SELL" and pos["qty"] > 0:
            sell_qty = min(size, pos["qty"])
            pos["cost"] *= (pos["qty"] - sell_qty) / pos["qty"]
            pos["qty"] -= sell_qty
    return {
        product_id: (pos["cost"] / pos["qty"])
        for product_id, pos in ledger.items()
        if pos["qty"] > 1e-12
    }


def handle_positions_command():
    """Handle the /positions Telegram command -- cross-references the bot's
    own trade ledger (trades.json, average-cost basis) against the REAL
    current Coinbase balances (get_balances(), always the source of truth
    for what you actually hold) to show an entry price and unrealized P&L
    for each open position.

    Important limitation: the average entry price is only known for
    quantity actually bought THROUGH this bot's /buy command. Anything
    bought outside the bot (directly in the Coinbase app, or before this
    feature existed) has no trade-log entry, so its entry price is
    genuinely unknown -- those rows say so explicitly rather than showing
    a wrong or misleading number."""
    if not TRADING_ENABLED:
        telegram_send("Trading is not enabled -- COINBASE_API_KEY / COINBASE_API_SECRET are not set on the server.")
        return
    try:
        balances = get_balances()
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ Failed to fetch balances: {e}{detail}")
        print(f"  [error] get_balances failed (in /positions): {e}{detail}")
        traceback.print_exc()
        return
    positions = [b for b in balances if b[0] not in ("USD", "USDC")]
    if not positions:
        telegram_send("📈 No open positions.")
        return
    avg_entries = _compute_avg_entry_prices()
    lines = ["📈 Open positions:"]
    for currency, avail, hold in sorted(positions, key=lambda x: x[0]):
        total = avail + hold
        current_price = get_current_price(f"{currency}-USD") or get_current_price(f"{currency}-USDC")
        entry_price = avg_entries.get(f"{currency}-USD") or avg_entries.get(f"{currency}-USDC")
        line = f"\n{currency}: {total:.8g}"
        if current_price:
            line += f"  (~${total * current_price:,.2f})"
        if entry_price and current_price:
            pnl_pct = ((current_price - entry_price) / entry_price) * 100
            pnl_usd = (current_price - entry_price) * total
            icon = "🟢" if pnl_pct >= 0 else "🔴"
            line += f"\n  entry (via bot): {entry_price:.6g}  now: {current_price:.6g}  {icon} {pnl_pct:+.1f}% ({pnl_usd:+,.2f}$)"
        elif entry_price:
            line += f"\n  entry (via bot): {entry_price:.6g}  (current price unavailable)"
        else:
            line += "\n  entry price unknown (not bought through the bot, or predates trade tracking)"
        lines.append(line)
    telegram_send("\n".join(lines))


def handle_history_command(limit=10):
    """Handle the /history [N] Telegram command -- shows the N most recent
    entries from the persisted trade ledger (trades.json): every /buy and
    /sell placed via the bot (market or limit), plus the eventual
    filled/cancelled/expired resolution of each limit order. No cap on N
    beyond what trades.json actually holds (record_trade keeps at most the
    last 500) -- these are real commands the user actually issued, not
    arbitrary data, so there's no reason to arbitrarily truncate what they
    can review. Doesn't require trading to be enabled to VIEW history --
    only to place new trades -- since this just reads a local file.

    A large N can produce more text than fits in one Telegram message
    (4096-char hard limit) -- rather than let that silently fail, this
    batches the output into multiple messages, each safely under the
    limit."""
    trades = load_json_file(TRADES_FILE, [])
    if not trades:
        telegram_send("📜 No trade history yet.")
        return
    recent = trades[-limit:][::-1]  # most recent first
    entries = []
    for t in recent:
        ts = _format_display_time(t.get("time"))
        side = t.get("side", "?")
        kind = t.get("kind", "?")
        status = t.get("status", "?")
        product_id = t.get("product_id", "?")
        price = t.get("price")
        base_size = t.get("base_size")
        amount_usd = t.get("amount_usd")
        fee_usd = t.get("fee_usd")
        price_str = f" @ {price}" if price not in (None, "?") else ""
        size_str = f" size {base_size}" if base_size not in (None, "?") else ""
        usd_str = f" (${amount_usd:.2f})" if isinstance(amount_usd, (int, float)) else ""
        fee_str = ""
        if fee_usd not in (None, ""):
            try:
                fee_str = f" fee ${float(fee_usd):.2f}"
            except (TypeError, ValueError):
                pass
        entries.append(
            f"\n{ts}\n"
            f"{side} {kind} {product_id} -- {status}{usd_str}{size_str}{price_str}{fee_str}\n"
            f"order: {t.get('order_id', '?')}"
        )

    TELEGRAM_SAFE_CHARS = 3500  # comfortably under Telegram's 4096-char message limit
    header = f"📜 Last {len(entries)} trade record(s):"
    batch = [header]
    batch_len = len(header)
    batch_num = 1
    for entry in entries:
        if batch_len + len(entry) > TELEGRAM_SAFE_CHARS and len(batch) > 1:
            telegram_send("\n".join(batch))
            batch_num += 1
            batch = [f"📜 (continued, part {batch_num}):"]
            batch_len = len(batch[0])
        batch.append(entry)
        batch_len += len(entry)
    telegram_send("\n".join(batch))


def handle_stats_command():
    """Handle the /stats Telegram command -- shows cumulative win/loss/flat
    counters for breakout ALERTS (not trades placed via the bot -- see
    /positions and /history for those). Answers "if I'd entered on every
    breakout signal and exited after EVALUATION_HOURS, how often would that
    have worked out?" -- purely informational tracking of the scanner's own
    signal quality. Reads the locally persisted stats.json, no Coinbase API
    call, so works regardless of whether trading is enabled."""
    stats = load_json_file(STATS_FILE, {})
    total = stats.get("total", 0)
    if total == 0:
        telegram_send(
            "📊 No resolved alert outcomes yet.\n"
            f"(An alert is 'resolved' {EVALUATION_HOURS:.0f}h after it fires, when price is checked again.)"
        )
        return
    win = stats.get("win", 0)
    loss = stats.get("loss", 0)
    flat = stats.get("flat", 0)
    decided = win + loss
    win_rate = (win / decided * 100) if decided > 0 else 0.0
    telegram_send(
        f"📊 Alert track record\n"
        f"Total resolved: {total}\n"
        f"Win: {win}   Loss: {loss}   Flat: {flat}\n"
        f"Win rate (of decided): {win_rate:.0f}%\n"
        f"(win = price moved +{SUCCESS_THRESHOLD_PCT:.0f}% within {EVALUATION_HOURS:.0f}h of the alert, "
        f"loss = -{FAILURE_THRESHOLD_PCT:.0f}%, flat = neither)"
    )


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
                f"(the comma before the price is optional -- just there to keep the two numbers apart)\n"
                f"{cmd} PRODUCT_ID all -- {'spend' if cmd == '/buy' else 'sell'} the entire available balance (market)\n"
                f"{cmd} PRODUCT_ID all, LIMIT_PRICE -- same, but as a limit order at LIMIT_PRICE\n"
            )
            return
        product_id = parts[1].upper()
        # "/buy PRODUCT_ID all" or "/sell PRODUCT_ID all" (optionally with
        # a trailing limit price) -- use the whole available balance (cash
        # for buy, coin for sell) instead of a specific USD amount. This
        # skips the AMOUNT_USD parsing below entirely -- there's no amount
        # to parse, and execute_buy_all()/execute_sell_all() look up the
        # real balance straight from Coinbase rather than working from an
        # estimate.
        if parts[2].rstrip(",").lower() == "all":
            if not TRADING_ENABLED:
                telegram_send("Trading is not enabled -- COINBASE_API_KEY / COINBASE_API_SECRET are not set on the server.")
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
            order_kind = f"LIMIT @ {limit_price}" if limit_price else "MARKET"
            telegram_send(f"⏳ Placing {cmd[1:].upper()} ALL order ({order_kind}): {product_id}...")
            if cmd == "/buy":
                execute_buy_all(product_id, limit_price)
            else:
                execute_sell_all(product_id, limit_price)
            return
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
    elif cmd == "/positions":
        handle_positions_command()
    elif cmd == "/history":
        n = 10
        if len(parts) == 2:
            try:
                # No upper cap (requested 2026-08-18: "these are real
                # commands I issued, no reason to limit it") -- floor of 1
                # is just to reject nonsense like /history 0 or /history -5.
                # trades.json itself caps at the most recent 500 (see
                # record_trade), and handle_history_command batches the
                # output across multiple Telegram messages if needed, so an
                # unbounded N can't silently fail or truncate.
                n = max(1, int(parts[1]))
            except ValueError:
                telegram_send(f"N must be a whole number. Got: {parts[1]}")
                return
        handle_history_command(n)
    elif cmd == "/stats":
        handle_stats_command()
    elif cmd == "/help":
        telegram_send(
            "Commands:\n"
            "/buy PRODUCT_ID AMOUNT_USD -- market buy, spending AMOUNT_USD immediately at the current price\n"
            "/buy PRODUCT_ID AMOUNT_USD, LIMIT_PRICE -- limit buy, waits until price reaches LIMIT_PRICE or better\n"
            "/buy PRODUCT_ID all -- market buy, spending the entire available cash balance (USD/USDC) for that pair\n"
            "/buy PRODUCT_ID all, LIMIT_PRICE -- limit buy, reserving the entire available cash balance at LIMIT_PRICE\n"
            "/sell PRODUCT_ID AMOUNT_USD -- market sell, selling ~AMOUNT_USD worth immediately at the current price\n"
            "/sell PRODUCT_ID AMOUNT_USD, LIMIT_PRICE -- limit sell, waits until price reaches LIMIT_PRICE or better\n"
            "/sell PRODUCT_ID all -- market sell the entire available balance of that coin\n"
            "/sell PRODUCT_ID all, LIMIT_PRICE -- limit sell, the entire available balance at LIMIT_PRICE\n"
            "(the comma before LIMIT_PRICE is optional -- just there to keep the two numbers apart)\n"
            "/orders -- list open (unfilled) limit orders\n"
            "/cancel ORDER_ID -- cancel an open limit order (ORDER_ID from /orders)\n"
            "/balance -- show free cash and open positions (real Coinbase balances)\n"
            "/positions -- open positions with entry price (via bot) and unrealized P&L\n"
            "/history [N] -- last N trades placed via the bot (default 10, no upper limit)\n"
            "/stats -- win/loss track record of breakout ALERTS (not trades)\n"
            "Examples:\n"
            "  /buy BTC-USD 50\n"
            "  /buy BTC-USD 50, 60000\n"
            "  /history 20\n"
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

def enhance_breakout_target(product_id, result):
    """Called only on a brand-new breakout event (see run_cycle) -- never on
    every cycle for every pair, and never for 'watching' signals.

    The main scan runs on hourly candles so it can catch a breakout within
    minutes of it happening (see the module docstring for why). The
    trade-off: Coinbase's candle endpoint caps out at ~300 candles per
    request, so hourly candles only cover ~12 days of history -- nowhere
    near enough to find a genuinely significant older resistance level
    (requested 2026-08-18, after a target search that only had 12 days to
    work with).

    Fix: since this only runs once per actual breakout (rare, compared to
    scanning ~400 pairs every 5 minutes), it's cheap to make one extra
    API call here -- for this one symbol only -- at DAILY granularity,
    which covers roughly the last ~300 days for the same ~300-candle cap.
    Re-run the 'next resistance' search against that much wider window; if
    it finds a real level (above both the local resistance and the current
    price), it replaces the shorter-sighted target analyze() already
    computed. If it doesn't find anything, or the extra fetch fails for any
    reason, the caller just keeps the existing, already-valid target from
    analyze() -- this is a best-effort improvement, never a requirement for
    the alert to fire."""
    try:
        daily_candles = fetch_candles(product_id, granularity=86400)
        time.sleep(REQUEST_PACING_SECONDS)
        if not daily_candles:
            return result
        resistance = result["resistance"]
        last_close = result["last_close"]
        daily_highs = [c[2] for c in daily_candles]
        higher_levels = [h for h in daily_highs if h > resistance and h > last_close]
        if higher_levels:
            target_price = min(higher_levels)
            result["target_price"] = target_price
            result["target_method"] = "next_resistance"
            result["target_pct"] = ((target_price - last_close) / last_close) * 100
    except Exception as e:
        print(f"  [error] enhance_breakout_target({product_id}) failed -- keeping short-history target: {e}")
    return result


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
                if new_signal == "breakout":
                    result = enhance_breakout_target(product_id, result)
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
    # Lives in DATA_DIR too -- now that outcomes.json/stats.json persist
    # across deploys (see DATA_DIR above), this marker must also persist,
    # or the one-time reset would fire again on every future deploy and
    # silently wipe stats that are now actually being kept.
    _RESET_MARKER_FILE = _data_path("outcomes_reset_2026-08-17.marker")
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
