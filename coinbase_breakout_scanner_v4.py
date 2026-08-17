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
import time
import traceback
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


def find_price_target(candles, resistance):
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

    Caveat: both methods are limited to whatever history Coinbase's candle
    endpoint returns for this granularity (roughly the last ~300 candles,
    i.e. ~12 days at the default 1h granularity) -- a genuinely older
    resistance level further back than that won't be seen.
    """
    highs = [c[2] for c in candles]
    lows = [c[1] for c in candles]

    older_highs = highs[: -(LOOKBACK_CANDLES + 1)]
    higher_levels = [h for h in older_highs if h > resistance]
    if higher_levels:
        return min(higher_levels), "next_resistance"

    window_lows = lows[-LOOKBACK_CANDLES - 1 : -1]
    range_low = min(window_lows) if window_lows else resistance
    range_height = resistance - range_low
    if range_height <= 0:
        range_height = resistance * (MEASURED_MOVE_FALLBACK_PCT / 100)
    return resistance + range_height, "measured_move"


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
        target_price, target_method = find_price_target(candles, resistance)
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
