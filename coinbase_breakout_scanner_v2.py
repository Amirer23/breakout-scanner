"""
Coinbase Breakout Scanner
==========================
Runs continuously (24/7, outside the browser) and scans ALL USD-quoted pairs
listed on Coinbase for resistance breakouts, using real historical candles
pulled directly from Coinbase's public REST API.
"""

import json
import math
import os
import time
import traceback
from datetime import datetime, timezone

import requests

BASE_URL = "https://api.exchange.coinbase.com"
QUOTE_CURRENCIES = {"USD"}
GRANULARITY_SECONDS = 3600
LOOKBACK_CANDLES = 20
BREAKOUT_VOLUME_RATIO = float(os.environ.get("BREAKOUT_VOLUME_RATIO", "1.5"))
BREAKOUT_RSI_MIN = float(os.environ.get("BREAKOUT_RSI_MIN", "55"))
BREAKOUT_BUFFER_PCT = float(os.environ.get("BREAKOUT_BUFFER_PCT", "0.3"))
BREAKOUT_CLOSE_POSITION_MIN = float(os.environ.get("BREAKOUT_CLOSE_POSITION_MIN", "0.6"))
WATCHING_DISTANCE_PCT = float(os.environ.get("WATCHING_DISTANCE_PCT", "1.0"))
WATCHING_VOLUME_RATIO = float(os.environ.get("WATCHING_VOLUME_RATIO", "1.5"))
WATCHING_RSI_MIN = float(os.environ.get("WATCHING_RSI_MIN", "50"))

CYCLE_SLEEP_SECONDS = 300
REQUEST_PACING_SECONDS = 0.35
MAX_RETRIES = 3

STATE_FILE = "scanner_state.json"
ALERTS_LOG_FILE = "alerts_log.jsonl"

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

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
    candles = list(reversed(data))
    return candles


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

    candle_range = last_high - last_low
    close_position = ((last_close - last_low) / candle_range) if candle_range > 0 else 1.0

    breakout_threshold = resistance * (1 + BREAKOUT_BUFFER_PCT / 100)

    signal = "neutral"
    if (last_close > breakout_threshold
            and vol_ratio and vol_ratio >= BREAKOUT_VOLUME_RATIO
            and (rsi_val or 0) > BREAKOUT_RSI_MIN
            and close_position >= BREAKOUT_CLOSE_POSITION_MIN):
        signal = "breakout"
    elif (0 <= dist_pct < WATCHING_DISTANCE_PCT
          and vol_ratio and vol_ratio >= WATCHING_VOLUME_RATIO
          and (rsi_val or 0) > WATCHING_RSI_MIN):
        signal = "watching"

    return {
        "last_close": last_close,
        "resistance": resistance,
        "vol_ratio": vol_ratio,
        "rsi": rsi_val,
        "dist_pct": dist_pct,
        "close_position": close_position,
        "signal": signal,
    }


def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            return {}
    return {}


def save_state(state):
    with open(STATE_FILE, "w") as f:
        json.dump(state, f)


def notify(product_id, result):
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
        f"Close strength: {result['close_position']*100:.0f}%"
    )
    print(f"[ALERT] {product_id}: {result['signal'].upper()} "
          f"price={result['last_close']:.4f} resistance={result['resistance']:.4f} "
          f"vol_ratio={result['vol_ratio']:.2f}x rsi={result['rsi']:.0f}")

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


def run_cycle(products, state):
    for i, product_id in enumerate(products):
        try:
            candles = fetch_candles(product_id)
            time.sleep(REQUEST_PACING_SECONDS)
            if not candles:
                continue

            result = analyze(candles)
            if not result:
                continue

            prev_signal = state.get(product_id, {}).get("signal", "neutral")
            new_signal = result["signal"]

            if new_signal in ("breakout", "watching") and new_signal != prev_signal:
                notify(product_id, result)

            state[product_id] = {"signal": new_signal, "updated": datetime.now(timezone.utc).isoformat()}

        except Exception:
            print(f"  [error] unexpected failure on {product_id}")
            traceback.print_exc()

        if (i + 1) % 50 == 0:
            print(f"  ...scanned {i + 1}/{len(products)}")

    return state


def main():
    print("Coinbase Breakout Scanner starting.")
    print(f"Granularity={GRANULARITY_SECONDS}s  Lookback={LOOKBACK_CANDLES}  Cycle={CYCLE_SLEEP_SECONDS}s")

    state = load_state()

    while True:
        cycle_start = time.time()
        print(f"\n=== Cycle start {datetime.now(timezone.utc).isoformat()} ===")

        products = fetch_products()
        print(f"Scanning {len(products)} USD pairs on Coinbase...")

        if products:
            state = run_cycle(products, state)
            save_state(state)

        elapsed = time.time() - cycle_start
        sleep_for = max(0, CYCLE_SLEEP_SECONDS - elapsed)
        print(f"Cycle done in {elapsed:.1f}s. Sleeping {sleep_for:.1f}s.")
        time.sleep(sleep_for)


if __name__ == "__main__":
    main()
