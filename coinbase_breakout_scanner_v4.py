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
  3. Every CYCLE_SLEEP_SECONDS (5 min), pulls recent HOURLY candles per pair
     and computes resistance / volume ratio / RSI(14) / distance to
     resistance, flagging "watching" (approaching resistance, OR already
     cleared it on the hourly close but not yet daily-confirmed).
  4. Once per UTC calendar day, separately pulls DAILY candles per pair and
     flags "breakout" ONLY if the full day's close clears its own daily
     resistance with the same volume/RSI/close-strength confirmation (see
     DAILY_LOOKBACK_CANDLES / analyze_daily -- added 2026-08-19 so
     "breakout" means a real daily-confirmed move, not just an hourly poke
     above a level that can fade back under it before the day ends).
  5. Calls notify() on NEW signals only (edge-triggered, not every cycle),
     so you don't get spammed while a breakout/watching state is ongoing.
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
from decimal import Decimal
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
    "USD1",  # World Liberty Financial's USD1 -- added 2026-08-21 after a false
             # USD1-USD "WATCHING" alert (Price 0.9996 vs Resistance 0.9999,
             # same peg-noise pattern as the original USDS-USD false alert above).
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
# close to leave room for entry/exit or normal noise. find_price_targets()
# now skips any candidate level closer than this and keeps looking (or
# extends the measured-move projection) so the printed target always
# represents a real, actionable move, not just the nearest price above
# last_close.
MIN_TARGET_PCT = float(os.environ.get("MIN_TARGET_PCT", "1.5"))

# How many distinct resistance levels to surface per breakout (2026-08-19,
# after Amir asked for multiple targets instead of just the nearest one --
# useful for planning a partial exit at the near level vs letting the rest
# run to a further one). TARGET_DEDUP_PCT keeps them from collapsing into
# near-duplicates: two old highs from adjacent candles often sit within a
# few cents of each other (confirmed on real LINK-USD daily data: two highs
# 10.023 and 10.024, effectively the same level) -- a candidate only counts
# as a NEW target if it's at least this far above the previously accepted
# one, so "3 targets" always means 3 meaningfully different price zones.
TARGET_LEVELS_COUNT = int(os.environ.get("TARGET_LEVELS_COUNT", "3"))
TARGET_DEDUP_PCT = float(os.environ.get("TARGET_DEDUP_PCT", "0.5"))

# "Zone tested N times" -- informational-only context added to confirmed
# BREAKOUT alerts (2026-08-20, per Amir's own SOL-USD chart read: he saw
# $84-85 as a well-tested support zone, something the bot's model never
# expressed at all -- resistance/targets are single historical price
# POINTS, not price BANDS revisited over time). This counts how many
# distinct times price has previously visited the zone around the
# breakout's own last_close (NOT around `resistance`/`new_support` -- the
# old, lower level that was just broken -- because it's the current price
# zone that matches what a chart-reader is actually looking at, and what
# produced the real finding on SOL-USD: 6 historical visits to ~$83-86,
# all within the bot's existing 300-day window). Deliberately does NOT
# feed into the breakout trigger itself (see analyze_daily/notify -- this
# is option 1 of two designs discussed with Amir on 2026-08-20; option 2,
# redefining "resistance" itself around tested zones, is a much bigger
# change and was explicitly deferred).
ZONE_TOLERANCE_PCT = float(os.environ.get("ZONE_TOLERANCE_PCT", "1"))  # how wide a band counts as "the same zone" around last_close -- tightened 2026-08-20 per Amir (wants a precise entry level, not a wide zone)
ZONE_MIN_GAP_DAYS = int(os.environ.get("ZONE_MIN_GAP_DAYS", "5"))  # touches within this many days of each other count as ONE visit, not two
ZONE_MIN_VISITS = int(os.environ.get("ZONE_MIN_VISITS", "2"))  # suppress the note entirely below this -- a single incidental touch isn't a "tested zone"

# MFI 14 and EMA9/EMA26 (added 2026-08-20, per Amir's outside consultant
# feedback). Both are informational-only context lines on WATCHING/
# BREAKOUT alerts, exactly like new_support/zone_visits above -- NEITHER
# feeds into the breakout/watching trigger logic itself. Thresholds below
# mirror the consultant's own read: MFI>80 = very high money flow /
# overbought, MFI<20 = oversold; EMA9>EMA26 = bullish trend context,
# EMA9<EMA26 = bearish.
MFI_OVERBOUGHT = float(os.environ.get("MFI_OVERBOUGHT", "80"))
MFI_OVERSOLD = float(os.environ.get("MFI_OVERSOLD", "20"))
EMA_FAST_PERIOD = int(os.environ.get("EMA_FAST_PERIOD", "9"))
EMA_SLOW_PERIOD = int(os.environ.get("EMA_SLOW_PERIOD", "26"))

# Extra 6H-timeframe context (added 2026-08-20, see fetch_6h_context() below
# for the full rationale -- fetched ONLY at alert time, never on the main
# per-cycle per-pair loop, to avoid doubling the ~400-pair API load).
SIX_HOUR_GRANULARITY_SECONDS = 21600

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

# 2026-08-19: Amir compared bot alerts against a professional daily-close
# technical read and pointed out a real gap -- "BREAKOUT" was firing on an
# HOURLY close above resistance, but proper TA convention (and the read he
# shared) only calls it confirmed once a FULL DAY closes above the level;
# an intraday poke that fades back under it before the day ends is "just an
# intraday touch", not a breakout. Concretely: NEAR-USD alerted BREAKOUT at
# an hourly close of 1.7005, while the daily-close bar for confirmation sat
# at 1.74-1.75 -- two different, both-valid standards, but conflating them
# under one label was misleading.
#
# Fix (discussed and agreed 2026-08-19): split the signal into two
# independent tracks. The hourly scan (every CYCLE_SLEEP_SECONDS, as
# before) now only ever produces "watching" as its strongest signal -- an
# hourly close that used to qualify as "breakout" is now an early
# heads-up, not a confirmation. "BREAKOUT" is reserved exclusively for
# analyze_daily(), which runs once per UTC day (see check_and_run_daily_pass
# in main()) against a FULLY CLOSED daily candle. This keeps the fast,
# real-time visibility Amir wanted (nothing is silently delayed a full day)
# while making the "BREAKOUT" label mean what it's supposed to mean.
#
# DAILY_LOOKBACK_CANDLES mirrors LOOKBACK_CANDLES (20) but in days instead
# of hours -- deliberately NOT a full year: this defines the LOCAL swing
# high that needs to break for a signal to fire, not the coin's long-term
# ceiling. A year-long lookback would often pick an all-time-high-adjacent
# level that's unreachable in any relevant timeframe for a coin that's
# down significantly from its highs (confirmed against real NEAR-USD data:
# a year back sits near its old $3 range, useless as a near-term trigger).
# The existing ~300-day daily window used for TARGETS (see
# find_price_targets/analyze_daily) already covers "how far can this run
# after breaking" -- a separate question from "what does it need to break
# in the first place", answered here.
DAILY_LOOKBACK_CANDLES = int(os.environ.get("DAILY_LOOKBACK_CANDLES", "20"))

CYCLE_SLEEP_SECONDS = 300           # 5 minutes between full scan cycles
REQUEST_PACING_SECONDS = 0.35       # ~3 requests/sec, safely under Coinbase's public rate limit
MAX_RETRIES = 3

# How often (hours) the bot proactively sends a Telegram "heartbeat" with a
# health snapshot -- added 2026-08-21 so silence itself becomes the signal
# something's wrong, instead of relying on Amir noticing the absence of
# alerts (a weak signal, easy to miss, especially since most cycles produce
# no alert at all even when everything's healthy). See send_heartbeat() /
# handle_status_command() (the on-demand /status version of the same thing).
HEARTBEAT_INTERVAL_HOURS = float(os.environ.get("HEARTBEAT_INTERVAL_HOURS", "6"))

# Populated by main()'s loop; read by handle_status_command() and
# send_heartbeat(). Module-level (not threaded through the Telegram command
# dispatch, which is zero-arg like every other handler in this file) so the
# Telegram polling thread can read live health data without main() having to
# pass anything to it.
_health = {
    "process_start": None, "cycle_count": 0, "last_cycle_seconds": None,
    "last_pairs_scanned": None, "errors_since_start": 0,
    "last_error": None, "last_error_time": None,
}

# /scan (added 2026-08-25, requested so a manual re-check doesn't mean
# waiting up to 24h for the next automatic daily pass -- see
# handle_scan_command() below). Same pattern as _health above: main()'s
# loop creates daily_state/outcomes ONCE at startup and mutates those same
# dict objects in place for the rest of the process's life (every
# `x, y = run_daily_cycle(x, y)`-style reassignment in this file hands back
# the identical object it was given) -- so stashing a reference here lets
# handle_scan_command(), running on the separate Telegram polling thread,
# operate on the SAME live state main()'s loop sees, not a stale copy.
# Populated once by main() right after daily_state/outcomes are loaded.
_shared_daily_state = None
_shared_outcomes = None

# Guards every run_daily_cycle() call -- scheduled (check_and_run_daily_pass)
# or manual (/scan) -- so the two can never run concurrently. Without this,
# a /scan firing right as the UTC day rolls over could interleave with the
# automatic pass: both would read the same pre-scan daily_state, both could
# see the same coin transition into "breakout" at once, and both would fire
# notify() + record_pending_outcome() for it -- a duplicate Telegram alert
# AND a duplicate win/loss stats entry for the same real-world signal.
_daily_scan_lock = threading.Lock()

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
# Separate signal track for the daily-confirmed breakout check (2026-08-19)
# -- deliberately its own file, not a field inside STATE_FILE's entries, so
# a coin's hourly "watching" state and its daily "breakout" state can never
# collide or overwrite each other; they're independent questions answered
# on independent schedules.
DAILY_STATE_FILE = _data_path("daily_scanner_state.json")
# Persists the last UTC calendar date the once-a-day breakout pass ran, so
# a restart/redeploy mid-day doesn't re-trigger a full 398-pair daily scan
# (see check_and_run_daily_pass in main()).
DAILY_CHECK_MARKER_FILE = _data_path("daily_check_marker.json")
ALERTS_LOG_FILE = _data_path("alerts_log.jsonl")
OPEN_ORDERS_STATE_FILE = _data_path("open_orders_state.json")  # which limit order IDs were open last cycle, to detect fills
TRADES_FILE = _data_path("trades.json")         # ledger of every /buy /sell placed via the bot + limit-order resolutions (requested 2026-08-18, position tracking)
EXIT_LEVELS_FILE = _data_path("exit_levels.json")  # structural stop/target watched per open bot position (added 2026-08-21, see compute_exit_levels())

# ALERT-ONLY exit monitoring (added 2026-08-21, per Amir's explicit choice:
# the bot never sells on its own -- it only tells him when a tracked
# position's structural stop or target is crossed, exactly like it already
# does for entries, and he decides what to do). Structural, not a fixed %:
# stop = the daily resistance level the breakout broke above (thesis is
# invalidated if price falls back below it); target = the same
# find_price_targets() level already computed and shown at entry time.

# RETURN-BASED exit alerts (added 2026-08-24, see
# claude/auto-price-alerts-feature-spec-2026-08.md in the Anki Capital
# project for the full spec/discussion). Deliberately a SEPARATE concept
# from the structural stop/target above, not a replacement or an average of
# it -- confirmed by backtest (stop-loss-and-filter-refinement-2026-08.md)
# that a fixed-% stop is a WORSE predictor of trade outcome than the
# structural one, so the structural fields are untouched by this. This pair
# answers a different question ("how much of the money currently in this
# position am I up/down, in %") and is purely a personal capital-tracking
# convenience -- always AUTO_ALERT_STOP_PCT below / AUTO_ALERT_TARGET_PCT
# above the CURRENT weighted-average entry price (avg_price from
# _compute_position_ledger()), recomputed on every additional buy into the
# position (unlike the structural levels, which lock in once and never
# move). v1 = hard-coded constants, not configurable via a command -- see
# the spec doc for why. Stored in the SAME exit_levels.json record per
# product_id as the structural fields, under separate pct_* keys, so
# /alerts and /cancelalert show/clear both together -- but the two number
# pairs must never be merged/averaged into one value.
AUTO_ALERT_STOP_PCT = 5     # alert when price falls this % below the current avg entry
AUTO_ALERT_TARGET_PCT = 10  # alert when price rises this % above the current avg entry

# --- Retest-entry tracking (added 2026-08-26, per claude/retest-entry-
# logic-spec-2026-08.md in the Anki Capital project -- full spec, backtest
# numbers (n=318 retest events out of 459 breakouts, 69.3% conversion),
# and the full decision history live there).
#
# WHAT THIS IS: a purely ADDITIVE, statistical/informational layer. It
# never buys or sells anything and never changes the existing daily
# BREAKOUT alert in any way -- Amir still decides every trade manually via
# /buy exactly as before. What it adds:
#   1. A second, separate "watch for a retest" step after a CONFIRMED daily
#      breakout: does price come back down near the broken level within
#      RETEST_MAX_WAIT_DAYS trading days and hold above it (close >=
#      resistance)? If yes, a SEPARATE "retest confirmed" Telegram alert
#      fires (see notify_retest()) -- a stronger, later-timed entry signal
#      than the original breakout alert, per the backtest (retest entries:
#      +4.54% expectancy vs. -2.38% for chasing the breakout candle).
#   2. Silent statistical tracking of what a simulated retest-entry trade
#      would have done, using two parallel fixed-% exit configs (T15/T25,
#      see RETEST_TARGET_PCTS) against REAL subsequent market prices --
#      not a backtest replay, live forward-testing, exactly like the three
#      existing frozen models (Baseline/Model A/Model B) already work.
#      Only RETEST_DISPLAYED_TRACK is ever shown to Amir (via /retest);
#      the rest accumulate silently for the biweekly comparison, same
#      reasoning as why the three frozen models aren't shown on live
#      alerts either.
#
# COST: zero extra API calls in the common case. Both the "is anything
# pending a retest?" check and the "did an open track's stop/target get
# hit today?" check reuse the SAME daily candle fetch run_daily_cycle()
# already does for every one of the ~398 pairs, every day -- see the calls
# to check_pending_retest()/update_retest_tracks() inside run_daily_cycle()
# below. The ONLY extra network call this can ever trigger is the rare
# same-day-tie 6H resolution (see resolve_same_day_tie_with_6h()), and
# even that only fires on the specific day a specific open track's stop
# AND target are both crossed in the same daily candle -- a handful of
# times total across the whole tracked population, not a per-cycle cost.
RETEST_MAX_WAIT_DAYS = int(os.environ.get("RETEST_MAX_WAIT_DAYS", "20"))            # trading days to wait for a retest before giving up
RETEST_TOUCH_TOLERANCE_PCT = float(os.environ.get("RETEST_TOUCH_TOLERANCE_PCT", "1.0"))  # "touch" = daily low within this % above the broken level
RETEST_ENTRY_BUFFER_PCT = float(os.environ.get("RETEST_ENTRY_BUFFER_PCT", "0.3"))   # simulated entry = resistance * (1 + this%) -- same buffer as BREAKOUT_BUFFER_PCT, see spec 8.1
RETEST_STOP_PCT = float(os.environ.get("RETEST_STOP_PCT", "3.0"))                   # shared stop for both tracks below (spec 8.5/8.8)
RETEST_TARGET_PCTS = {"T15": 15.0, "T25": 25.0}                                     # both tracked in parallel; only one shown live (spec 8.6)
RETEST_DISPLAYED_TRACK = "T15"                                                      # which key of RETEST_TARGET_PCTS is surfaced to Amir; the rest stay silent

RETEST_PENDING_FILE = _data_path("retest_pending.json")     # breakout events currently awaiting a retest, one open record per product_id
RETEST_TRACKING_FILE = _data_path("retest_tracking.json")   # confirmed retest events + their T15/T25 statistical tracking, list per product_id

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
    to pull a much longer window of history for a specific purpose (see
    analyze_daily/run_daily_cycle) without touching the main hourly scan's
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


def mfi(candles, period=14):
    """Money Flow Index (added 2026-08-20, per Amir's outside consultant
    feedback -- see MFI_OVERBOUGHT/MFI_OVERSOLD above). Same "volume-
    weighted RSI" concept as RSI but folds in volume, not just price: a
    move on heavy volume moves MFI more than the same move on thin volume.

    Deliberately mirrors rsi()'s exact structure/convention above -- a
    simple sum over the last `period` candles, not a continuously-smoothed
    running average -- so the two indicators behave consistently (same
    "how many candles do I need" guard, same shape of answer) and stay
    easy to reason about side by side in the same alert.

    candles are the standard [time, low, high, open, close, volume] tuples.
    Typical price = (low+high+close)/3; a day/hour's raw money flow is
    typical_price * volume. Uses ">"/"<" (not ">=") when comparing typical
    prices between periods -- a period whose typical price is EXACTLY
    unchanged from the prior one contributes to neither side, matching the
    standard MFI definition (unlike rsi() above, which folds a zero-diff
    into "gains" via >=0 -- these are different indicators with different
    conventions, this is intentional, not an inconsistency).

    Returns None if there isn't enough history, or 100.0 if there was no
    negative money flow at all in the window (mirrors rsi()'s avg_loss==0
    handling).
    """
    if len(candles) < period + 1:
        return None
    typical_prices = [(c[1] + c[2] + c[4]) / 3 for c in candles]
    money_flows = [tp * c[5] for tp, c in zip(typical_prices, candles)]
    pos_flow, neg_flow = 0.0, 0.0
    for i in range(len(candles) - period, len(candles)):
        if typical_prices[i] > typical_prices[i - 1]:
            pos_flow += money_flows[i]
        elif typical_prices[i] < typical_prices[i - 1]:
            neg_flow += money_flows[i]
    if neg_flow == 0:
        return 100.0
    money_ratio = pos_flow / neg_flow
    return 100 - (100 / (1 + money_ratio))


def ema(values, period):
    """Exponential moving average (added 2026-08-20, for EMA9/EMA26 trend
    context -- see EMA_FAST_PERIOD/EMA_SLOW_PERIOD above). Standard EMA:
    seeded with a simple average of the first `period` values, then
    exponentially weighted forward through the rest of the series.

    Uses ALL available `values` to seed and roll forward (not just the
    most recent `period`) -- unlike rsi()/mfi() above, an EMA is a
    genuinely different kind of average: every prior value still has some
    (decaying) influence on today's EMA, so truncating the input series
    early would silently bias the result low on precision. In practice
    this is called with the full daily_candles/candles list already
    fetched for this pair, which comfortably covers the ~300-day/hour
    window Coinbase's API returns.

    Returns None if there isn't enough history to seed even one EMA value.
    """
    if len(values) < period:
        return None
    k = 2 / (period + 1)
    ema_val = sum(values[:period]) / period
    for v in values[period:]:
        ema_val = v * k + ema_val * (1 - k)
    return ema_val


def drop_incomplete_last_candle(candles, granularity_seconds=None):
    """Coinbase's candle endpoint typically includes the still-forming
    current period as the last entry. Signal generation off a partial
    candle means volume ratio / RSI / close-strength are all computed from
    an incomplete bar that keeps changing -- since the scanner re-scans
    every CYCLE_SLEEP_SECONDS, this can make the SAME real breakout flicker
    in and out of the "breakout" state within one hour (e.g. it clears the
    volume/close-strength bar at minute 40 but not at minute 10), producing
    duplicate alerts and duplicate outcome-tracking entries for one event.
    Drop it so every signal is based on a fully closed candle.

    granularity_seconds defaults to GRANULARITY_SECONDS (the hourly scan's
    resolution) -- pass 86400 when checking DAILY candles (see
    analyze_daily/run_daily_cycle, added 2026-08-19), since a still-forming
    daily bar needs to be judged against a 24h window, not a 1h one."""
    if granularity_seconds is None:
        granularity_seconds = GRANULARITY_SECONDS
    if not candles:
        return candles
    last_start = candles[-1][0]
    if last_start + granularity_seconds > time.time():
        return candles[:-1]
    return candles


def _select_target_levels(qualifying_levels_sorted):
    """From an ascending list of price levels that already clear
    min_target_price, pick up to TARGET_LEVELS_COUNT of them such that each
    selected level sits at least TARGET_DEDUP_PCT above the previously
    selected one. Without this, two old highs from neighboring candles that
    happen to sit within a few cents of each other (confirmed on real
    LINK-USD daily data on 2026-08-19: highs of 10.023 and 10.024 from
    adjacent days) would count as two separate 'targets' when they're
    really the same resistance zone touched twice. This guarantees N
    reported targets always means N meaningfully distinct price zones."""
    selected = []
    for level in qualifying_levels_sorted:
        if not selected or (level - selected[-1]) / selected[-1] * 100 >= TARGET_DEDUP_PCT:
            selected.append(level)
        if len(selected) >= TARGET_LEVELS_COUNT:
            break
    return selected


def find_price_targets(candles, resistance, last_close, lookback=None):
    """Technical price target(s) for a breakout.

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
    i.e. ~12 days at the default 1h granularity, or ~300 days at daily
    granularity) -- a genuinely older resistance level further back than
    that won't be seen. (This is why "breakout" is only ever produced by
    analyze_daily(), which always calls this with daily candles -- see
    that function for the ~300-day-window reasoning.)

    Returns (targets, method, near_resistance):
      targets -- a list of up to TARGET_LEVELS_COUNT distinct price levels,
        ascending (nearest first). Length 1 for measured_move (a single
        projected level -- see TARGET_LEVELS_COUNT note on why a second/
        third synthetic projection isn't offered: it would be a multiple of
        a heuristic, not a second real historical level, and presenting it
        alongside real levels would be misleading about how grounded it is).
      method -- "next_resistance" or "measured_move".
      near_resistance -- nearest older high above last_close REGARDLESS of
        the minimum, or None if there isn't one (see IMPORTANT note above).

    lookback defaults to LOOKBACK_CANDLES (the hourly scan's resistance
    window) -- pass DAILY_LOOKBACK_CANDLES when calling this against daily
    candles (see analyze_daily, added 2026-08-19), so "older than the
    lookback window" means older than the last 20 DAYS, not the last 20
    HOURS, when it matters which candles count as "older history" to
    search for further targets.
    """
    if lookback is None:
        lookback = LOOKBACK_CANDLES
    highs = [c[2] for c in candles]
    lows = [c[1] for c in candles]
    min_target_price = last_close * (1 + MIN_TARGET_PCT / 100)

    older_highs = highs[: -(lookback + 1)]
    all_higher_levels = sorted(set(h for h in older_highs if h > resistance and h > last_close))
    near_resistance = all_higher_levels[0] if all_higher_levels else None

    qualifying_levels = [h for h in all_higher_levels if h >= min_target_price]
    targets = _select_target_levels(qualifying_levels)
    if targets:
        return targets, "next_resistance", near_resistance

    window_lows = lows[-lookback - 1 : -1]
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
    return [target], "measured_move", near_resistance


def count_zone_visits(daily_candles, level, tolerance_pct=None, min_gap_days=None):
    """Count distinct historical "visits" to the price zone around `level`
    (added 2026-08-20 -- see ZONE_TOLERANCE_PCT above for the full design
    rationale). Informational only: NOT used anywhere in the breakout
    trigger logic, and does not change resistance/target calculation.

    A day "touches" the zone if its [low, high] range overlaps the band
    [level*(1-tolerance_pct%), level*(1+tolerance_pct%)] -- i.e. price was
    physically in that band at some point during the day, same "any
    intraday touch counts" standard already used for resistance itself
    (see analyze_daily's highs = [c[2] for c in daily_candles] comment).

    Consecutive touch-days closer together than min_gap_days are treated
    as ONE visit (a multi-day stay in the zone, or a slow chop through it,
    is one "test" of the level -- not N tests for N days it happened to sit
    there). A gap of more than min_gap_days between touches starts a new
    visit.

    Deliberately does NOT exclude the most recent candles (an earlier draft
    mirrored find_price_targets()'s `older_highs = highs[: -(lookback+1)]`
    convention to avoid double-counting the breakout's own ramp-up -- but
    that convention exists there to avoid re-finding the SAME level that
    defines `resistance`. Here the zone checked is around `level`
    (last_close, the breakout price), a different and usually higher price
    than resistance, so a genuine separate touch during the recent window
    would have been silently dropped. Decided with Amir on 2026-08-20:
    simplest fix is to not exclude anything -- since consecutive touches
    already collapse into a single visit via min_gap_days, the breakout's
    own final approach into the zone counts as at most one extra visit, not
    an inflated number).

    Returns an int (0 if no history overlaps the zone at all, e.g. the
    breakout is a fresh all-time high with nothing to compare against).
    """
    if tolerance_pct is None:
        tolerance_pct = ZONE_TOLERANCE_PCT
    if min_gap_days is None:
        min_gap_days = ZONE_MIN_GAP_DAYS

    band_low = level * (1 - tolerance_pct / 100)
    band_high = level * (1 + tolerance_pct / 100)

    touch_indices = [
        i for i, c in enumerate(daily_candles)
        if c[1] <= band_high and c[2] >= band_low  # c[1]=low, c[2]=high -- day's range overlaps the band
    ]
    if not touch_indices:
        return 0

    visits = 1
    for prev_i, cur_i in zip(touch_indices, touch_indices[1:]):
        if cur_i - prev_i > min_gap_days:
            visits += 1
    return visits


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

    # MFI 14 and EMA9/EMA26 trend context (added 2026-08-20) -- informational
    # only, same treatment as new_support/zone_visits below: computed here so
    # notify() can show them, but never read by the signal/watching_reason
    # logic above or below this point.
    mfi_val = mfi(candles, 14)
    ema_fast = ema(closes, EMA_FAST_PERIOD)
    ema_slow = ema(closes, EMA_SLOW_PERIOD)
    ema_trend = None
    if ema_fast is not None and ema_slow is not None:
        ema_trend = "bullish" if ema_fast > ema_slow else ("bearish" if ema_fast < ema_slow else "flat")

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

    # 2026-08-19: "breakout" no longer fires from this (hourly) function at
    # all -- see the DAILY_LOOKBACK_CANDLES note above for why. An hourly
    # close that used to earn "breakout" here now earns "watching" instead:
    # still worth an immediate heads-up (that's the whole point of scanning
    # every 5 minutes), just not yet the confirmed label. watching_reason
    # distinguishes the two ways a coin can end up "watching" -- notify()
    # uses it to add a clarifying line rather than presenting both cases
    # identically.
    signal, watching_reason = "neutral", None
    if daily_volume_usd < MIN_24H_VOLUME_USD:
        signal = "neutral"  # too thin/illiquid -- never signal regardless of other conditions
    elif (last_close > breakout_threshold
            and vol_ratio and vol_ratio >= BREAKOUT_VOLUME_RATIO
            and (rsi_val or 0) > BREAKOUT_RSI_MIN
            and close_position >= BREAKOUT_CLOSE_POSITION_MIN):
        signal, watching_reason = "watching", "cleared_hourly"
    elif (0 <= dist_pct < WATCHING_DISTANCE_PCT
          and vol_ratio and vol_ratio >= WATCHING_VOLUME_RATIO
          and (rsi_val or 0) > WATCHING_RSI_MIN):
        signal, watching_reason = "watching", "approaching"

    # Targets/near-resistance are computed only for a CONFIRMED breakout --
    # this function can no longer produce one, so these always come back
    # empty from here now. Left in the returned dict (rather than removed)
    # so notify() and every other consumer keep working against one
    # consistent schema regardless of which function produced the result.
    targets, target_method = [], None
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
        "mfi": mfi_val,
        "ema_fast": ema_fast,
        "ema_slow": ema_slow,
        "ema_trend": ema_trend,
        "dist_pct": dist_pct,
        "close_position": close_position,
        "daily_volume_usd": daily_volume_usd,
        "pct_change_24h": pct_change_24h,
        "extended_move": extended_move,
        "signal": signal,
        "watching_reason": watching_reason,
        "targets": targets,
        "target_method": target_method,
        "near_resistance_price": near_resistance_price,
        "near_resistance_pct": near_resistance_pct,
        # This (hourly) function can never produce "breakout" -- see
        # new_support's note on analyze_daily()'s return dict for what this
        # field means. Always None here, kept in the schema so notify() and
        # every other consumer can read result.get("new_support") without
        # caring which function produced the result.
        "new_support": None,
        # Same reasoning as new_support immediately above -- zone_visits is
        # only ever computed on a confirmed daily breakout (see
        # count_zone_visits/ZONE_TOLERANCE_PCT above). Always None here.
        "zone_visits": None,
    }


def analyze_daily(daily_candles):
    """Confirmed-breakout signal on DAILY candle closes (added 2026-08-19,
    after Amir compared bot alerts against a professional daily-close-based
    technical read and found the bot's hourly-close "BREAKOUT" label too
    premature -- an intraday poke that fades back under resistance before
    the day ends shouldn't count as a breakout. Concretely: NEAR-USD
    alerted BREAKOUT at an hourly close of 1.7005, while the daily-close
    bar for confirmation in that outside read sat at 1.74-1.75 -- two
    different, both-valid standards, but conflating them under one label
    was misleading. See DAILY_LOOKBACK_CANDLES above for the full design
    discussion.

    This runs once per UTC day (see check_and_run_daily_pass in main()),
    completely independent of the hourly analyze() above, which now only
    ever produces "watching" as its strongest signal -- "breakout" is
    reserved exclusively for this function.

    Mirrors analyze()'s breakout logic exactly (same volume/RSI/close-
    strength bars -- these measure conviction, not timeframe, so the same
    thresholds apply), just on daily bars: resistance is the highest daily
    high over DAILY_LOOKBACK_CANDLES days, and the signal only fires if the
    FULL day's close clears it with confirmation. An intraday wick above
    resistance that closes back under it by the end of the UTC day --
    exactly Amir's NEAR-USD example -- does NOT fire here, because
    last_close is the daily close, not any price merely touched during the
    day.

    Since fetch_candles(granularity=86400) already returns ~300 days in one
    call, this also finds real target levels (see find_price_targets)
    directly from that SAME fetch -- no extra API call needed. This makes
    the old enhance_breakout_target() helper fully redundant: it used to
    exist specifically to re-fetch a wider daily window AFTER an hourly
    breakout fired, because the ~12 days hourly candles cover wasn't enough
    runway to find real further-out targets. Now that "breakout" only ever
    comes from this function -- which already works from a wide daily
    fetch in the first place -- that extra re-fetch has nothing left to
    add, so enhance_breakout_target() was removed 2026-08-19."""
    if len(daily_candles) < DAILY_LOOKBACK_CANDLES + 2:
        return None

    closes = [c[4] for c in daily_candles]
    highs = [c[2] for c in daily_candles]
    lows = [c[1] for c in daily_candles]

    prior_highs = highs[-DAILY_LOOKBACK_CANDLES - 1 : -1]
    resistance = max(prior_highs)
    prior_vols = [c[5] for c in daily_candles[-DAILY_LOOKBACK_CANDLES - 1 : -1]]
    avg_vol = sum(prior_vols) / len(prior_vols) if prior_vols else 0

    last_close = closes[-1]
    last_high = highs[-1]
    last_low = lows[-1]
    last_vol = daily_candles[-1][5]
    vol_ratio = (last_vol / avg_vol) if avg_vol > 0 else None
    rsi_val = rsi(closes, 14)
    dist_pct = ((resistance - last_close) / last_close) * 100

    # MFI 14 and EMA9/EMA26 trend context (added 2026-08-20) -- see the
    # matching block in analyze() above for the full rationale. Same
    # informational-only treatment: never read by the signal logic below.
    mfi_val = mfi(daily_candles, 14)
    ema_fast = ema(closes, EMA_FAST_PERIOD)
    ema_slow = ema(closes, EMA_SLOW_PERIOD)
    ema_trend = None
    if ema_fast is not None and ema_slow is not None:
        ema_trend = "bullish" if ema_fast > ema_slow else ("bearish" if ema_fast < ema_slow else "flat")

    candle_range = last_high - last_low
    close_position = ((last_close - last_low) / candle_range) if candle_range > 0 else 0.0

    # A genuine daily candle's own volume*close IS the day's turnover --
    # no need to sum multiple bars the way the hourly analyze() does to
    # approximate 24h from 24 hourly candles.
    daily_volume_usd = last_vol * last_close

    prev_close = closes[-2]
    pct_change_24h = ((last_close - prev_close) / prev_close * 100) if prev_close else None

    breakout_threshold = resistance * (1 + BREAKOUT_BUFFER_PCT / 100)

    signal = "neutral"
    if daily_volume_usd < MIN_24H_VOLUME_USD:
        signal = "neutral"
    elif (last_close > breakout_threshold
            and vol_ratio and vol_ratio >= BREAKOUT_VOLUME_RATIO
            and (rsi_val or 0) > BREAKOUT_RSI_MIN
            and close_position >= BREAKOUT_CLOSE_POSITION_MIN):
        signal = "breakout"
    # No "watching" tier here by design -- that's exclusively the hourly
    # job's role; this function only ever answers "did today's daily
    # candle confirm, yes or no".

    targets, target_method = [], None
    near_resistance_price, near_resistance_pct = None, None
    if signal == "breakout":
        target_levels, target_method, near_resistance_price = find_price_targets(
            daily_candles, resistance, last_close, lookback=DAILY_LOOKBACK_CANDLES)
        targets = [
            {"price": t, "pct": ((t - last_close) / last_close) * 100}
            for t in target_levels
        ]
        if near_resistance_price is not None:
            near_resistance_pct = ((near_resistance_price - last_close) / last_close) * 100
            if near_resistance_pct >= MIN_TARGET_PCT:
                near_resistance_price, near_resistance_pct = None, None

    extended_move = bool(
        (pct_change_24h is not None and pct_change_24h >= EXTENDED_MOVE_24H_PCT)
        or (rsi_val is not None and rsi_val >= EXTENDED_MOVE_RSI)
    )

    # "New support" (added 2026-08-20, per Amir's own chart reading of
    # SOL-USD): once a breakout is CONFIRMED, classic technical analysis
    # treats the resistance level that was just broken as the new support
    # floor on a pullback/retest -- e.g. SOL-USD broke 77.75 resistance,
    # so 77.75 becomes the level to watch as support going forward. This
    # is a genuinely different concept from `resistance` (a backward-
    # looking "what got broken" fact) and from `targets`/near_resistance
    # (forward-looking ceilings) -- it's the floor. Deliberately just the
    # bare former-resistance value, not a computed "zone" or range: the
    # rest of this bot's model is built entirely from precise historical
    # price points (real highs/lows it found in the candle data), never
    # visual round-number zones, and there's no principled way to turn a
    # single number into a defensible range without inventing a buffer
    # out of nowhere. Only meaningful once a breakout is CONFIRMED (signal
    # == "breakout") -- before that, the level hasn't actually been
    # broken yet, so calling it "support" would be premature the same way
    # calling an hourly clear a "BREAKOUT" was.
    new_support = resistance if signal == "breakout" else None

    # "Zone tested N times" (added 2026-08-20, option 1 of the two designs
    # discussed with Amir -- informational only, does NOT feed back into
    # `signal` above in any way). Checks the zone around last_close (the
    # breakout price itself), not around resistance/new_support (the old,
    # lower level just broken) -- see ZONE_TOLERANCE_PCT's comment for why.
    # Only computed on a confirmed breakout, same as new_support/targets,
    # and reuses this same already-fetched daily_candles fetch -- no extra
    # API call. No exclusion window here -- see count_zone_visits()'s
    # docstring for why that's deliberate.
    zone_visits = count_zone_visits(daily_candles, last_close) if signal == "breakout" else None

    return {
        "last_close": last_close,
        "resistance": resistance,
        "vol_ratio": vol_ratio,
        "rsi": rsi_val,
        "mfi": mfi_val,
        "ema_fast": ema_fast,
        "ema_slow": ema_slow,
        "ema_trend": ema_trend,
        "dist_pct": dist_pct,
        "close_position": close_position,
        "daily_volume_usd": daily_volume_usd,
        "pct_change_24h": pct_change_24h,
        "extended_move": extended_move,
        "signal": signal,
        "watching_reason": None,
        "targets": targets,
        "target_method": target_method,
        "near_resistance_price": near_resistance_price,
        "near_resistance_pct": near_resistance_pct,
        "new_support": new_support,
        "zone_visits": zone_visits,
    }


def fetch_6h_context(product_id):
    """Extra 6H-timeframe RSI/MFI/EMA9-26 context for a single product
    (added 2026-08-20, per Amir's outside consultant feedback -- a "4H or
    6H chart check" alongside the daily/hourly view; Amir chose 6H).

    Deliberately NOT called from run_cycle()/run_daily_cycle()'s main
    per-product loop, which already does ~400 candle fetches every 5
    minutes -- adding a second fetch per product there would double that
    load for zero benefit on the ~399 pairs that never alert. Instead this
    is called ONLY right before notify() actually fires (see the two call
    sites in run_cycle/run_daily_cycle), so in practice it runs a handful
    of times a day -- once per real WATCHING/BREAKOUT alert -- not once per
    pair per cycle. Same reasoning as new_support/zone_visits: additive
    context on an alert that's already firing, never a reason to fetch
    more for pairs that aren't alerting.

    Purely informational -- like every other addition in this section, it
    is NOT read by analyze()/analyze_daily()'s signal logic at all (it
    can't be: it's fetched and attached to `result` by the caller AFTER
    analyze()/analyze_daily() already decided the signal).

    Returns a dict {"rsi": ..., "mfi": ..., "ema_trend": ...} (any of
    which may be None if there's insufficient 6H history for that specific
    indicator), or None if the fetch itself fails or returns too few
    candles to compute anything -- notify() treats None the same as
    "omit this section", so a transient network hiccup on this SECONDARY
    fetch degrades gracefully and never blocks the underlying alert.
    """
    try:
        candles = fetch_candles(product_id, granularity=SIX_HOUR_GRANULARITY_SECONDS)
        if not candles:
            return None
        candles = drop_incomplete_last_candle(candles, granularity_seconds=SIX_HOUR_GRANULARITY_SECONDS)
        if len(candles) < 15:  # need at least period+1 for rsi/mfi to return anything
            return None
        closes = [c[4] for c in candles]
        rsi_val = rsi(closes, 14)
        mfi_val = mfi(candles, 14)
        ema_fast = ema(closes, EMA_FAST_PERIOD)
        ema_slow = ema(closes, EMA_SLOW_PERIOD)
        ema_trend = None
        if ema_fast is not None and ema_slow is not None:
            ema_trend = "bullish" if ema_fast > ema_slow else ("bearish" if ema_fast < ema_slow else "flat")
        return {"rsi": rsi_val, "mfi": mfi_val, "ema_trend": ema_trend}
    except Exception as e:
        print(f"  [warn] fetch_6h_context({product_id}) failed: {e}")
        return None


def get_btc_trend():
    """BTC-USD daily-trend snapshot (added 2026-08-21, item #6 from Amir's
    "what's missing" list -- market-regime awareness, INFORMATIONAL ONLY:
    tags alerts with the broader market backdrop, never suppresses or
    blocks an alert. Amir explicitly declined a suppression/filtering
    version of this ("just tag it, don't hide anything").

    Same treatment as fetch_6h_context() above: fetched ONLY right before
    notify() actually fires for some OTHER pair (see the two call sites in
    run_cycle/run_daily_cycle), not once per pair per cycle -- BTC itself
    rarely alerts, so in practice this runs a handful of times a day, not
    ~400 times per cycle. Reuses the exact same EMA9/EMA26 classification
    used everywhere else in this file (see analyze()/fetch_6h_context())
    for consistency -- same trend definition everywhere, just applied to
    BTC-USD's own daily candles instead of the alerting pair's.

    Returns "bullish"/"bearish"/"flat", or None if the fetch fails or
    there's insufficient BTC daily history to compute the EMAs -- notify()
    treats None as "omit this line", so a transient hiccup on this
    SECONDARY fetch never blocks the underlying alert."""
    try:
        candles = fetch_candles("BTC-USD", granularity=86400)
        if not candles:
            return None
        candles = drop_incomplete_last_candle(candles, granularity_seconds=86400)
        closes = [c[4] for c in candles]
        ema_fast = ema(closes, EMA_FAST_PERIOD)
        ema_slow = ema(closes, EMA_SLOW_PERIOD)
        if ema_fast is None or ema_slow is None:
            return None
        return "bullish" if ema_fast > ema_slow else ("bearish" if ema_fast < ema_slow else "flat")
    except Exception as e:
        print(f"  [warn] get_btc_trend() failed: {e}")
        return None


def fetch_daily_resistance(product_id):
    """The actual DAILY-timeframe resistance level a "cleared_hourly"
    watching alert is waiting on (added 2026-08-25, replacing notify()'s
    vague "typically HIGHER, 20-day resistance level" note with a real
    number -- requested after Amir watched SOL-USD clear its hourly
    resistance hard, 4x volume, RSI 80+, and still only read "watching"
    with no way to tell from the alert itself how far daily confirmation
    actually was).

    The original "cleared_hourly" note explained this number wasn't
    fetched because doing so for every pair on every 5-minute cycle
    wouldn't scale across ~400 pairs -- but exactly like
    fetch_6h_context()/get_btc_trend() above, this is only ever called
    ONCE, right before notify() fires for a coin that just cleared its
    hourly resistance (see the call site in run_cycle()), not from the
    hot per-pair loop -- so in practice this runs a handful of times a
    day, not 400x per cycle. Same non-scaling concern, same answer as
    those two: edge-triggered fetches on an alert that's already firing
    are cheap; it's only "one extra fetch for all ~400 pairs every cycle"
    that isn't.

    Mirrors analyze_daily()'s own resistance calculation exactly (highest
    daily high over the trailing DAILY_LOOKBACK_CANDLES days, excluding
    the most recent/still-forming day) so the number shown here is
    guaranteed to match what the real daily confirmation check will use
    -- not a separate approximation of it that could drift out of sync.

    Returns the resistance level (float), or None if the fetch fails or
    there isn't yet enough daily history -- notify() falls back to the
    original vague note in that case, same graceful-degradation pattern
    as fetch_6h_context()/get_btc_trend()."""
    try:
        candles = fetch_candles(product_id, granularity=86400)
        if not candles:
            return None
        candles = drop_incomplete_last_candle(candles, granularity_seconds=86400)
        if len(candles) < DAILY_LOOKBACK_CANDLES + 2:
            return None
        highs = [c[2] for c in candles]
        prior_highs = highs[-DAILY_LOOKBACK_CANDLES - 1 : -1]
        return max(prior_highs)
    except Exception as e:
        print(f"  [warn] fetch_daily_resistance({product_id}) failed: {e}")
        return None


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
    # Recorded for reference only -- the win/loss verdict itself compares
    # entry_price against SUCCESS_THRESHOLD_PCT/FAILURE_THRESHOLD_PCT below,
    # not against the target. Store the nearest of the (now possibly
    # multiple) targets, same as what used to be the single target_price.
    nearest_target = result.get("targets") or [{}]
    outcomes[key] = {
        "product_id": product_id,
        "entry_price": result["last_close"],
        "resistance": result["resistance"],
        "target_price": nearest_target[0].get("price"),
        "target_pct": nearest_target[0].get("pct"),
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
    if result.get("mfi") is not None:
        # Money Flow Index (added 2026-08-20) -- see MFI_OVERBOUGHT/
        # MFI_OVERSOLD above. Purely informational, same as RSI already
        # shown above -- doesn't affect the signal itself. Can be None on a
        # very thin/newly-listed pair with less history than the 14-period
        # window needs, hence the guard (unlike RSI, which is guaranteed
        # non-None by the time notify() runs -- see mfi()'s docstring).
        mfi_flag = ""
        if result["mfi"] >= MFI_OVERBOUGHT:
            mfi_flag = " (overbought)"
        elif result["mfi"] <= MFI_OVERSOLD:
            mfi_flag = " (oversold)"
        text += f"\nMFI: {result['mfi']:.0f}{mfi_flag}"
    if result.get("ema_trend") is not None:
        # EMA9/EMA26 trend context (added 2026-08-20) -- same informational
        # treatment. Can be None if there's less history than EMA_SLOW_PERIOD
        # (26) candles needs -- see ema()'s docstring.
        trend_icon = {"bullish": "📈", "bearish": "📉", "flat": "➡️"}.get(result["ema_trend"], "")
        text += f"\nEMA9/26 trend: {trend_icon} {result['ema_trend']}"
    ctx_6h = result.get("ctx_6h")
    if ctx_6h:
        # Extra 6H-timeframe context (added 2026-08-20) -- see
        # fetch_6h_context() for why this is attached to `result` by the
        # CALLER (run_cycle/run_daily_cycle) only at alert time, rather than
        # being computed inside analyze()/analyze_daily() like everything
        # else above. Each piece is independently optional (any of the
        # three can be None on thin 6H history), so build the line from
        # whichever parts are actually available rather than all-or-nothing.
        parts = []
        if ctx_6h.get("rsi") is not None:
            parts.append(f"RSI {ctx_6h['rsi']:.0f}")
        if ctx_6h.get("mfi") is not None:
            parts.append(f"MFI {ctx_6h['mfi']:.0f}")
        if ctx_6h.get("ema_trend") is not None:
            trend_icon = {"bullish": "📈", "bearish": "📉", "flat": "➡️"}.get(ctx_6h["ema_trend"], "")
            parts.append(f"trend {trend_icon} {ctx_6h['ema_trend']}")
        if parts:
            text += f"\n6H context: {' · '.join(parts)}"
    if result.get("btc_trend") is not None:
        # Market-regime context (added 2026-08-21, item #6) -- see
        # get_btc_trend()'s docstring. Informational only: shown for every
        # alert on every pair (bullish/bearish/flat all shown, not just
        # bad news), with an extra ⚠️ + caution note only when BTC itself
        # is trending down, since that's the case where "this pair looks
        # like a breakout" is most likely to be a coin getting dragged
        # along with a falling BTC rather than a genuine independent move.
        trend_icon = {"bullish": "📈", "bearish": "📉", "flat": "➡️"}.get(result["btc_trend"], "")
        text += f"\nBTC trend (daily): {trend_icon} {result['btc_trend']}"
        if result["btc_trend"] == "bearish":
            text += " ⚠️ market headwind -- treat this breakout with extra caution"
    if result.get("watching_reason") == "cleared_hourly":
        # Distinguishes the two ways a coin can end up "watching" (added
        # 2026-08-19, alongside the hourly/daily split -- see
        # DAILY_LOOKBACK_CANDLES above). Without this, a coin that already
        # cleared resistance on the hourly close looks identical to one
        # that's merely approaching it, even though the first is a much
        # stronger signal already awaiting confirmation.
        #
        # IMPORTANT: the "Resistance" printed above this line is the HOURLY
        # level (a 20-HOUR window) that was just cleared -- NOT the level
        # the eventual daily confirmation check will use. analyze_daily()
        # independently computes its own resistance from a 20-DAY window,
        # which is very often meaningfully higher than the hourly one (this
        # is exactly the gap that motivated this whole redesign -- see the
        # NEAR-USD example in analyze_daily()'s docstring: hourly close
        # 1.7005 vs. the real daily bar at 1.74-1.75). Found in adversarial
        # review 2026-08-19: without this line, this alert reads as "clear
        # 1.7005 on today's close = BREAKOUT", which is false and would
        # reproduce the exact confusion this redesign was meant to fix.
        # The actual daily number IS now fetched -- see fetch_daily_
        # resistance()'s docstring for why this is cheap despite the
        # concern in this comment's own history (edge-triggered, once per
        # real alert, not once per pair per cycle). Falls back to the
        # original vague note below if that fetch failed or came back None
        # (e.g. a pair too new to have DAILY_LOOKBACK_CANDLES of daily
        # history yet) -- same graceful-degradation pattern as ctx_6h/
        # btc_trend above.
        text += "\n⏳ Cleared resistance on the hourly close -- watching for a daily close confirmation before this becomes a BREAKOUT."
        daily_resistance = result.get("daily_resistance")
        if daily_resistance is not None:
            dist = ((daily_resistance - result["last_close"]) / result["last_close"]) * 100
            if dist > 0:
                text += f" Daily confirmation level: {daily_resistance:.6g} ({dist:.1f}% above the current price)."
            else:
                text += (
                    f" Daily confirmation level: {daily_resistance:.6g} -- already cleared intraday "
                    f"({-dist:.1f}% below the current price), but still needs the FULL UTC day to close above it."
                )
        else:
            text += (
                " Note: daily confirmation is checked against a separately-computed, "
                "typically HIGHER, 20-day resistance level -- not the hourly level shown above."
            )
    if result.get("new_support") is not None:
        # Classic TA reading (added 2026-08-20, per Amir's own chart read
        # of SOL-USD): the resistance level that was JUST broken becomes
        # the new support floor to watch on a pullback/retest. Deliberately
        # one plain number, not a "zone" -- see analyze_daily()'s
        # new_support comment for why. Only ever set on a real breakout
        # (never on "watching"), so this line can't appear before the
        # level has actually been confirmed broken.
        text += f"\n🧱 New support (former resistance): {result['new_support']:.6g}"
    if result.get("zone_visits") is not None and result["zone_visits"] >= ZONE_MIN_VISITS:
        # Informational-only context (added 2026-08-20, option 1 of the two
        # designs discussed with Amir) -- purely descriptive, does NOT
        # affect the breakout trigger above in any way. Suppressed entirely
        # below ZONE_MIN_VISITS so a single incidental touch doesn't read as
        # a meaningful "tested zone". See count_zone_visits()/
        # ZONE_TOLERANCE_PCT for the exact definition of a "visit".
        text += (
            f"\n📍 This price zone (~{result['last_close']:.6g} ±{ZONE_TOLERANCE_PCT:.0f}%) "
            f"was tested {result['zone_visits']} times in the available history before this breakout."
        )
    targets = result.get("targets") or []
    if result["signal"] == "breakout" and targets:
        if len(targets) == 1:
            # Single target -- either the lone next_resistance level found,
            # or the measured-move fallback (which only ever produces one
            # projected level, never several -- see find_price_targets()).
            method_label = (
                "Next resistance target"
                if result["target_method"] == "next_resistance"
                else "Measured-move target (no higher resistance in range)"
            )
            text += f"\n{method_label}: {targets[0]['price']:.6g} ({targets[0]['pct']:+.1f}% from here)"
        else:
            # Multiple distinct resistance zones found (2026-08-19, added
            # after Amir asked for more than just the nearest one) -- always
            # real historical levels here, never measured-move (that method
            # only ever returns a single synthetic projection).
            for i, t in enumerate(targets, 1):
                if i == 1:
                    label = f"Target {i} (nearest)"
                elif i == len(targets):
                    label = f"Target {i} (furthest)"
                else:
                    label = f"Target {i}"
                text += f"\n{label}: {t['price']:.6g} ({t['pct']:+.1f}% from here)"
    if result.get("near_resistance_price") is not None:
        # The nearest older high sits closer than MIN_TARGET_PCT, so it was
        # skipped as a reported *objective* above -- but it's still a real
        # obstacle price has to clear first. Surfacing it explicitly rather
        # than silently dropping it: a user asked directly on 2026-08-18
        # whether skipping it made the breakout itself questionable -- it
        # doesn't (breakout = what already happened, target = separate
        # forward guess), but hiding a near ceiling would have been
        # misleading either way.
        target_word = "target" if len(targets) <= 1 else "targets"
        text += (
            f"\nℹ️ Note: an older high sits just "
            f"{result['near_resistance_pct']:+.1f}% away at {result['near_resistance_price']:.6g} -- "
            f"may cause an early stall/pullback before the {target_word} above."
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

    targets_debug = ",".join(f"{t['price']:.4f}({t['pct']:+.1f}%)" for t in targets)
    print(f"[ALERT] {product_id}: {result['signal'].upper()} "
          f"price={result['last_close']:.4f} resistance={result['resistance']:.4f} "
          f"vol_ratio={result['vol_ratio']:.2f}x rsi={result['rsi']:.0f}"
          + (f" chg24h={result['pct_change_24h']:+.1f}%" if result.get("pct_change_24h") is not None else "")
          + (f" targets=[{targets_debug}] ({result['target_method']})" if targets else "")
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


# Set by get_base_increment() on its most recent call -- None if the last
# call succeeded, otherwise a short human-readable reason. Read by callers
# that want to tell the user WHY a precision fallback happened (e.g.
# execute_buy_all()'s limit path), instead of leaving them to guess.
# Confirmed live 2026-08-24: FET-USDC's "/buy ... all" failed twice in a
# row with INVALID_SIZE_PRECISION -- without this, there was no way to
# tell whether that meant the increment lookup itself failed (this
# fallback firing) or something else entirely was wrong.
_LAST_BASE_INCREMENT_ERROR = None


def get_base_increment(product_id):
    """Fetch this product's REAL base_increment -- the exact order-size
    step Coinbase enforces for THIS specific pair (e.g. "0.00000001" for
    SOL-USDC, but as coarse as "1" for some cheap, high-supply coins like
    ENA) -- via the same authenticated Advanced Trade client used to place
    orders (_trade_client.get_product), deliberately NOT the public
    market-data endpoint (get_json/BASE_URL, the Coinbase Exchange API).
    That's a different API surface that doesn't even know about every pair
    the trading API supports -- confirmed live 2026-08-18: SOL-USDC 404'd
    there while trading fine through _trade_client (see
    execute_sell_all()'s comment on the same issue for candles).

    Retries once (immediate, no backoff -- this only runs on a user-issued
    buy/sell, not the hot scan loop, so one extra round-trip is cheap) before
    giving up, on the theory that a single lookup failure is more likely a
    transient hiccup than a permanently-missing pair. Still returns None on
    failure so callers fall back to the old flat-8-decimal behavior instead
    of blocking the trade outright -- but now also sets
    _LAST_BASE_INCREMENT_ERROR so callers can surface the real reason
    instead of a silent, unexplained fallback."""
    global _LAST_BASE_INCREMENT_ERROR
    last_exc = None
    for attempt in range(2):
        try:
            product = _to_dict(_trade_client.get_product(product_id))
            increment = product.get("base_increment")
            if increment:
                _LAST_BASE_INCREMENT_ERROR = None
                return str(increment)
            last_exc = f"get_product({product_id}) returned no base_increment field"
            break  # a clean response with a missing field won't fix itself on retry
        except Exception as e:
            last_exc = str(e)
    print(f"  [warn] get_base_increment({product_id}) failed after retry, falling back to 8-decimal precision: {last_exc}")
    _LAST_BASE_INCREMENT_ERROR = last_exc
    return None


def _precision_fallback_note(product_id):
    """Explanatory note to append to an order-failure Telegram message when
    the failure MIGHT be explained by a base_increment lookup miss (see
    _LAST_BASE_INCREMENT_ERROR's docstring -- added 2026-08-24 after
    FET-USDC's "/buy ... all" failed twice with INVALID_SIZE_PRECISION and
    there was no way to tell whether that was caused by this fallback).

    Callers must call this immediately after get_base_increment() or
    _size_str_for_order() ran for THIS product_id -- it just reads whatever
    that call left in the global _LAST_BASE_INCREMENT_ERROR, it doesn't
    call get_base_increment() itself (that would be a second, redundant
    lookup, and could even show a misleadingly different result on a flaky
    connection). Returns "" if that lookup succeeded, since then the
    8-decimal fallback wasn't in play and there's nothing to explain."""
    if _LAST_BASE_INCREMENT_ERROR is None:
        return ""
    return (
        f"\n(note: couldn't fetch {product_id}'s real size precision from Coinbase "
        f"({_LAST_BASE_INCREMENT_ERROR}) -- fell back to 8-decimal formatting, which is "
        f"wrong for some pairs and can cause exactly this error. Retry the command; if it "
        f"keeps failing the same way, this pair likely needs its precision handled manually.)"
    )


def _floor_to_increment_str(value, increment_str):
    """Floor `value` DOWN to the nearest multiple of increment_str (a
    decimal string like "0.01" or "1", as returned by Coinbase's
    base_increment) and return it as a plain decimal string with exactly
    that many decimal places -- never more (Coinbase rejects extra
    decimals with INVALID_SIZE_PRECISION / "Too many decimals in order
    amount") and never fewer (would silently under-size the order). Uses
    Decimal throughout rather than float division, to avoid binary-float
    rounding artifacts landing just past an increment boundary."""
    increment = Decimal(increment_str)
    decimals = max(0, -increment.as_tuple().exponent)
    value_dec = Decimal(str(value))
    floored = (value_dec // increment) * increment
    return f"{floored:.{decimals}f}"


def _size_str_for_order(value, product_id):
    """Format `value` (a computed base-currency order size) as the exact
    string to send to Coinbase for product_id. FLOORS to this pair's real
    base_increment (via get_base_increment) -- never assumes 8 decimal
    places, which is only correct for some pairs. Confirmed live
    2026-08-19: "/buy ENA-USDC all, 0.0905" was rejected with
    INVALID_SIZE_PRECISION because the old code always formatted
    base_size to a flat 8 decimals (right for SOL-USDC, wrong for
    ENA-USDC, whose real base_increment allows far fewer). Falls back to
    the pre-fix flat-8-decimal floor (_floor_to_precision) only if the
    increment lookup itself fails (network hiccup) -- degrades to the old
    behavior for that one order rather than blocking the trade outright.
    Floors, never rounds, in both paths -- same reasoning as
    _floor_to_precision(): the resulting notional/balance-sold must never
    round UP past the cash or balance `value` was computed from."""
    increment = get_base_increment(product_id)
    if increment:
        return _floor_to_increment_str(value, increment)
    return f"{_floor_to_precision(value):.8f}"


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
            _maybe_init_exit_levels(product_id)
            _update_pct_levels(product_id)
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
    # See _size_str_for_order()'s docstring -- floors to product_id's REAL
    # base_increment, not a blanket 8 decimals (which fails with
    # INVALID_SIZE_PRECISION on coarser-precision pairs).
    base_size_str = _size_str_for_order(usd_amount / price, product_id)
    # See _precision_fallback_note()'s docstring -- must be read right after
    # the _size_str_for_order() call above.
    precision_note = _precision_fallback_note(product_id)
    try:
        resp = _to_dict(_trade_client.market_order_sell(
            client_order_id=order_id, product_id=product_id, base_size=base_size_str))
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
                "amount_usd": usd_amount, "base_size": filled_size or base_size_str, "price": avg_price,
                "fee_usd": fee, "order_id": order_id,
            })
            _notify_if_position_closed(product_id)
        else:
            telegram_send(f"❌ SELL failed: {product_id} for ${usd_amount}\n{resp.get('error_response', resp)}{precision_note}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ SELL error: {product_id} for ${usd_amount}\n{e}{detail}{precision_note}")
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
        # Fetch the real base_increment ONCE outside the retry loop (not
        # once per attempt -- up to 8 attempts would mean up to 8 redundant
        # lookups of the same, unchanging value). See _size_str_for_order()
        # for why 8 decimal places can't just be assumed for every pair.
        increment = get_base_increment(product_id)
        # Only relevant if every attempt below ends in failure -- lets the
        # final error message say WHY the fallback 8-decimal formatting was
        # used, instead of leaving an INVALID_SIZE_PRECISION error
        # unexplained. See _precision_fallback_note()/_LAST_BASE_INCREMENT_ERROR's
        # docstrings.
        precision_note = _precision_fallback_note(product_id)
        spend_fraction = 1.0
        last_error_text = None
        for attempt in range(8):
            spend = available * spend_fraction
            raw_size = spend / limit_price
            base_size_str = (
                _floor_to_increment_str(raw_size, increment) if increment
                else f"{_floor_to_precision(raw_size):.8f}"
            )
            attempt_order_id = str(uuid.uuid4())
            error_text = None
            try:
                resp = _to_dict(_trade_client.limit_order_gtc_buy(
                    client_order_id=attempt_order_id, product_id=product_id,
                    base_size=base_size_str, limit_price=str(limit_price)))
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
                    "amount_usd": spend, "base_size": base_size_str, "price": limit_price,
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
            telegram_send(f"❌ LIMIT BUY ALL failed: {product_id} ~{spend:,.2f} {quote_currency} @ {limit_price}\n{error_text}{precision_note}")
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
            _maybe_init_exit_levels(product_id)
            _update_pct_levels(product_id)
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
    # See _size_str_for_order()'s docstring -- floors the balance to sell
    # to product_id's REAL base_increment rather than a blanket 8
    # decimals, which fails with INVALID_SIZE_PRECISION on coarser pairs.
    # Computed once and reused below for both the limit and market
    # branches, since `available` itself doesn't change between them.
    base_size_str = _size_str_for_order(available, product_id)
    # See _precision_fallback_note()'s docstring -- must be read right after
    # the _size_str_for_order() call above, before anything else touches
    # get_base_increment() for a different product_id.
    precision_note = _precision_fallback_note(product_id)

    if limit_price:
        # Limit sell: the whole available base_size at limit_price, exactly
        # like execute_sell_limit() but sized from the full available
        # balance instead of a specified usd_amount.
        try:
            resp = _to_dict(_trade_client.limit_order_gtc_sell(
                client_order_id=order_id, product_id=product_id,
                base_size=base_size_str, limit_price=str(limit_price)))
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
                    "amount_usd": usd_value, "base_size": base_size_str, "price": limit_price,
                    "order_id": order_id,
                })
                _pending_new_order_ids.add(order_id)
            else:
                telegram_send(f"❌ LIMIT SELL ALL failed: {product_id} {available:.8g} {base_currency} @ {limit_price}\n{resp.get('error_response', resp)}{precision_note}")
        except Exception as e:
            detail = _coinbase_error_detail(e)
            telegram_send(f"❌ LIMIT SELL ALL error: {product_id} {available:.8g} {base_currency} @ {limit_price}\n{e}{detail}{precision_note}")
            print(f"  [error] limit sell-all order failed: {e}{detail}")
            traceback.print_exc()
        return

    try:
        resp = _to_dict(_trade_client.market_order_sell(
            client_order_id=order_id, product_id=product_id, base_size=base_size_str))
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
                "amount_usd": usd_value, "base_size": filled_size or base_size_str, "price": avg_price,
                "fee_usd": fee, "order_id": order_id,
            })
            _notify_if_position_closed(product_id)
        else:
            telegram_send(f"❌ SELL ALL failed: {product_id}\n{resp.get('error_response', resp)}{precision_note}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ SELL ALL error: {product_id}\n{e}{detail}{precision_note}")
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
    # see _size_str_for_order()'s docstring for why plain rounding, AND a
    # blanket 8 decimals, can both be wrong (rounding can push a LIMIT
    # order's true cost fractionally over budget; a flat 8 decimals fails
    # with INVALID_SIZE_PRECISION on pairs with a coarser real increment).
    base_size_str = _size_str_for_order(usd_amount / limit_price, product_id)
    # See _precision_fallback_note()'s docstring -- must be read right after
    # the _size_str_for_order() call above.
    precision_note = _precision_fallback_note(product_id)
    try:
        resp = _to_dict(_trade_client.limit_order_gtc_buy(
            client_order_id=order_id, product_id=product_id,
            base_size=base_size_str, limit_price=str(limit_price)))
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
                "amount_usd": usd_amount, "base_size": base_size_str, "price": limit_price,
                "order_id": order_id,
            })
            _pending_new_order_ids.add(order_id)
        else:
            telegram_send(f"❌ LIMIT BUY failed: {product_id} ~${usd_amount} @ {limit_price}\n{resp.get('error_response', resp)}{precision_note}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ LIMIT BUY error: {product_id} ~${usd_amount} @ {limit_price}\n{e}{detail}{precision_note}")
        print(f"  [error] limit buy order failed: {e}{detail}")
        traceback.print_exc()


def execute_sell_limit(product_id, usd_amount, limit_price):
    """Place a GTC limit sell at limit_price -- sits open until it fills or
    is cancelled, unlike a market sell. usd_amount is converted to a
    base-currency size using limit_price."""
    order_id = str(uuid.uuid4())
    # Floor (not round) so this never asks to sell fractionally more coin
    # than usd_amount / limit_price implies -- see _size_str_for_order()'s
    # docstring (same rounding-up hazard as the buy side, plus the
    # per-pair precision fix).
    base_size_str = _size_str_for_order(usd_amount / limit_price, product_id)
    # See _precision_fallback_note()'s docstring -- must be read right after
    # the _size_str_for_order() call above.
    precision_note = _precision_fallback_note(product_id)
    try:
        resp = _to_dict(_trade_client.limit_order_gtc_sell(
            client_order_id=order_id, product_id=product_id,
            base_size=base_size_str, limit_price=str(limit_price)))
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
                "amount_usd": usd_amount, "base_size": base_size_str, "price": limit_price,
                "order_id": order_id,
            })
            _pending_new_order_ids.add(order_id)
        else:
            telegram_send(f"❌ LIMIT SELL failed: {product_id} ~${usd_amount} @ {limit_price}\n{resp.get('error_response', resp)}{precision_note}")
    except Exception as e:
        detail = _coinbase_error_detail(e)
        telegram_send(f"❌ LIMIT SELL error: {product_id} ~${usd_amount} @ {limit_price}\n{e}{detail}{precision_note}")
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
        if side == "SELL" and status == "FILLED":
            _notify_if_position_closed(product_id)
        elif side == "BUY" and status == "FILLED":
            _maybe_init_exit_levels(product_id)
            _update_pct_levels(product_id)

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
    """Thin wrapper over _compute_position_ledger() kept for backward
    compatibility -- returns {product_id: avg_entry_price} for currently
    open (bot-tracked) positions only. See _compute_position_ledger() for
    the full picture (fee-adjusted, plus realized P&L)."""
    open_positions, _realized = _compute_position_ledger()
    return {pid: pos["avg_price"] for pid, pos in open_positions.items()}


def _compute_position_ledger():
    """Replay trades.json in order (AVERAGE COST method, fee-adjusted) to
    build two things at once:

    1. open_positions: {product_id: {"qty": float, "avg_price": float}}
       for every symbol the bot currently has an open (qty > ~0) tracked
       position in. avg_price folds BUY-side fees into the cost basis (so
       it's the true all-in cost per unit, not just the raw fill price) --
       added 2026-08-21 per Amir's own measured ~0.02%/trade fee data;
       previously fees were recorded in trades.json but never actually
       used in any P&L math.

    2. realized: {product_id: {
           "realized_pnl_usd": float,       -- cumulative, fee-adjusted,
                                                across every SELL ever
                                                executed via the bot for
                                                this product
           "total_fees_usd": float,         -- cumulative fees on those sells
           "total_cost_basis_usd": float,   -- cumulative cost basis of
                                                every unit ever sold (added
                                                2026-08-26) -- divide
                                                realized_pnl_usd by this to
                                                get the fee-adjusted %
                                                return, since the $ figure
                                                alone doesn't say whether
                                                it's a small position or a
                                                large one (see /pnl)
           "closed_lots": int,              -- how many times this symbol
                                                has gone from open -> fully
                                                flat via the bot
           "last_close": {"avg_entry":, "avg_exit":, "pnl_usd":} or None
                                             -- snapshot of the MOST RECENT
                                                full close (for the
                                                position-closed Telegram
                                                notice); None if the
                                                symbol has never fully
                                                closed via the bot
       }}
       Only ever reflects trades placed through this bot (see /positions'
       docstring for why a manually-bought-outside-the-bot chunk of the
       same coin isn't and can't be reflected here).

    Only counts entries with status "executed" (market fills) or "filled"
    (resolved limit orders) that have a known numeric base_size and price
    -- a limit order still sitting at status "placed" isn't an actual
    transaction yet, so it's skipped (and correctly so: it hasn't moved
    any real quantity)."""
    trades = load_json_file(TRADES_FILE, [])
    ledger = {}     # product_id -> {"qty": float, "cost": float}
    realized = {}   # product_id -> accumulator dict, see docstring
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
        try:
            fee = float(t.get("fee_usd") or 0)
        except (TypeError, ValueError):
            fee = 0.0
        pos = ledger.setdefault(product_id, {"qty": 0.0, "cost": 0.0})
        if side == "BUY":
            pos["qty"] += size
            pos["cost"] += size * price + fee  # fold buy-side fee into cost basis
        elif side == "SELL" and pos["qty"] > 0:
            sell_qty = min(size, pos["qty"])
            avg_cost_per_unit = pos["cost"] / pos["qty"]
            cost_of_sold = sell_qty * avg_cost_per_unit
            proceeds = sell_qty * price - fee  # sell-side fee reduces proceeds directly
            pnl = proceeds - cost_of_sold

            r = realized.setdefault(product_id, {
                "realized_pnl_usd": 0.0, "total_fees_usd": 0.0, "closed_lots": 0,
                "total_cost_basis_usd": 0.0,
                "last_close": None,
                "_pnl_at_prev_close": 0.0, "_sold_qty_since_close": 0.0,
                "_sold_proceeds_since_close": 0.0, "_last_avg_entry": None,
            })
            r["realized_pnl_usd"] += pnl
            r["total_fees_usd"] += fee
            # Cumulative cost basis of every unit ever sold for this
            # product (added 2026-08-26, requested by Amir: the $ P&L
            # alone doesn't say whether a +$200 trade is +10% on a $2,000
            # position or +0.01% on $2,000,000 -- realized_pnl_usd /
            # total_cost_basis_usd below is that %, fee-adjusted the same
            # way pnl already is (cost_of_sold folds in the BUY-side fee
            # via avg_cost_per_unit, see the cost basis comment above).
            r["total_cost_basis_usd"] += cost_of_sold
            r["_last_avg_entry"] = avg_cost_per_unit
            r["_sold_qty_since_close"] += sell_qty
            r["_sold_proceeds_since_close"] += sell_qty * price

            pos["cost"] -= cost_of_sold
            pos["qty"] -= sell_qty
            if pos["qty"] <= 1e-9:
                r["closed_lots"] += 1
                r["last_close"] = {
                    "avg_entry": r["_last_avg_entry"],
                    "avg_exit": r["_sold_proceeds_since_close"] / r["_sold_qty_since_close"],
                    "pnl_usd": r["realized_pnl_usd"] - r["_pnl_at_prev_close"],
                }
                r["_pnl_at_prev_close"] = r["realized_pnl_usd"]
                r["_sold_qty_since_close"] = 0.0
                r["_sold_proceeds_since_close"] = 0.0

    open_positions = {
        pid: {"qty": p["qty"], "avg_price": p["cost"] / p["qty"]}
        for pid, p in ledger.items() if p["qty"] > 1e-9
    }
    # Strip the internal bookkeeping keys (prefixed "_") before returning --
    # they're implementation detail, not part of the public shape.
    realized_clean = {
        pid: {k: v for k, v in r.items() if not k.startswith("_")}
        for pid, r in realized.items()
    }
    return open_positions, realized_clean


def _notify_if_position_closed(product_id):
    """Call this right after recording an executed/filled SELL. If that
    sell brought the bot-tracked position for product_id fully back to
    flat, sends a one-time Telegram notice with the realized P&L for that
    closed round-trip (fee-adjusted, via _compute_position_ledger()).
    Silent no-op if the position is still open. Never raises -- this is a
    nice-to-have notification, not allowed to block or break the actual
    sell flow it's called from."""
    try:
        open_positions, realized = _compute_position_ledger()
        if product_id in open_positions:
            return  # still open (partial sell) -- nothing to announce yet
        r = realized.get(product_id)
        close = r.get("last_close") if r else None
        if not close:
            return
        entry = close["avg_entry"]
        exitp = close["avg_exit"]
        pnl = close["pnl_usd"]
        pnl_pct = ((exitp - entry) / entry) * 100 if entry else 0.0
        icon = "🟢" if pnl >= 0 else "🔴"
        telegram_send(
            f"{icon} Position closed: {product_id}\n"
            f"Avg entry: {entry:.6g}   Avg exit: {exitp:.6g}\n"
            f"Realized P&L (after fees): {pnl:+,.2f}$ ({pnl_pct:+.1f}%)"
        )
    except Exception as e:
        print(f"  [warn] _notify_if_position_closed({product_id}) failed: {e}")
    finally:
        # Position is flat now (or the whole check above failed and we can't
        # be sure) -- either way, stop watching stale exit levels for it. A
        # future re-buy computes fresh ones via _maybe_init_exit_levels().
        try:
            _clear_exit_levels(product_id)
        except Exception as e:
            print(f"  [warn] _clear_exit_levels({product_id}) failed: {e}")


def compute_exit_levels(product_id):
    """Compute a STRUCTURAL stop and target for a newly-opened bot
    position in product_id, reusing the exact same daily resistance /
    find_price_targets() logic the breakout signal itself uses (see
    analyze_daily()) rather than an arbitrary fixed percentage:
      stop   = the current 20-day resistance level. If the daily close
               falls back below the level a breakout broke above, the
               thesis is invalidated -- that's the structural definition
               of "wrong", not a fixed distance.
      target = the first computed price target (find_price_targets()) --
               the next real historical resistance above, or a
               measured-move projection if none exists in the fetched
               window. Same target a breakout alert itself would show.

    This is used for ALERTING ONLY (see check_exit_levels()) -- it never
    places an order. Returns None if there isn't enough daily history to
    compute a resistance level (mirrors analyze_daily()'s own minimum),
    or on any fetch failure -- never raises, so it can't block the BUY
    flow it's called from."""
    try:
        daily_candles = fetch_candles(product_id, granularity=86400)
        if not daily_candles:
            return None
        daily_candles = drop_incomplete_last_candle(daily_candles, granularity_seconds=86400)
        if len(daily_candles) < DAILY_LOOKBACK_CANDLES + 2:
            return None
        highs = [c[2] for c in daily_candles]
        last_close = daily_candles[-1][4]
        prior_highs = highs[-DAILY_LOOKBACK_CANDLES - 1 : -1]
        resistance = max(prior_highs)
        target_levels, target_method, _near = find_price_targets(
            daily_candles, resistance, last_close, lookback=DAILY_LOOKBACK_CANDLES)
        target = target_levels[0] if target_levels else None
        return {"stop": resistance, "target": target, "target_method": target_method}
    except Exception as e:
        print(f"  [warn] compute_exit_levels({product_id}) failed: {e}")
        return None


def _clear_exit_levels(product_id):
    """Stop watching product_id for stop/target alerts (position closed,
    or tracking is being reset for a fresh re-buy)."""
    levels = load_json_file(EXIT_LEVELS_FILE, {})
    if product_id in levels:
        del levels[product_id]
        save_json_file(EXIT_LEVELS_FILE, levels)


def _maybe_init_exit_levels(product_id):
    """Call this right after recording an executed/filled BUY. If this
    BUY just opened a brand-new bot-tracked position (was flat before),
    compute and persist structural exit levels for it (see
    compute_exit_levels()) and send a one-time Telegram confirmation of
    what's being watched. A no-op if the position was already open before
    this BUY (an add-on buy into an existing position keeps the original
    levels rather than resetting them on every top-up) or if exit levels
    are already being tracked for it. Never raises."""
    try:
        levels = load_json_file(EXIT_LEVELS_FILE, {})
        if product_id in levels:
            return  # already tracking this position -- an add-on buy, not a fresh open
        open_positions, _realized = _compute_position_ledger()
        if product_id not in open_positions:
            return  # shouldn't happen right after a recorded BUY, but defensive
        exits = compute_exit_levels(product_id)
        if exits is None:
            print(f"  [info] no exit levels computed for {product_id} (insufficient daily history) -- /positions still works, just no stop/target alerts for this one")
            return
        levels[product_id] = {
            "stop": exits["stop"], "target": exits["target"],
            "target_method": exits["target_method"],
            "alerted_stop": False, "alerted_target": False,
            "created": datetime.now(timezone.utc).isoformat(),
        }
        save_json_file(EXIT_LEVELS_FILE, levels)
        entry_price = open_positions[product_id]["avg_price"]
        lines = [
            f"🎯 Watching exit levels for {product_id}",
            f"Entry: {entry_price:.6g}",
            f"Stop (structural, close back below = thesis invalidated): {exits['stop']:.6g}",
        ]
        if exits["target"] is not None:
            lines.append(f"Target: {exits['target']:.6g}")
        lines.append("(alert-only -- I'll ping you if either is crossed, you decide what to do)")
        telegram_send("\n".join(lines))
    except Exception as e:
        print(f"  [warn] _maybe_init_exit_levels({product_id}) failed: {e}")


def _update_pct_levels(product_id):
    """Call this right after recording an executed/filled BUY -- on EVERY
    buy into product_id, not just the first one (unlike
    _maybe_init_exit_levels() above, whose structural levels intentionally
    lock in once and never move). The return-based stop/target are defined
    as a fixed % of the CURRENT weighted-average entry price, so by
    definition they must be recomputed every time avg_price changes --
    otherwise the number shown no longer means "+AUTO_ALERT_TARGET_PCT%
    net", it's just a stale price (see the spec doc's worked example for
    why this matters). Creates the exit_levels.json record for product_id
    if it doesn't exist yet (e.g. compute_exit_levels() found insufficient
    daily history for the structural side) -- the two are independent, one
    failing to compute must never block the other. Never raises."""
    try:
        open_positions, _realized = _compute_position_ledger()
        if product_id not in open_positions:
            return  # shouldn't happen right after a recorded BUY, but defensive
        avg = open_positions[product_id]["avg_price"]
        if not avg:
            return
        new_stop = avg * (1 - AUTO_ALERT_STOP_PCT / 100)
        new_target = avg * (1 + AUTO_ALERT_TARGET_PCT / 100)
        levels = load_json_file(EXIT_LEVELS_FILE, {})
        entry = levels.get(product_id, {})
        is_fresh = "pct_avg_entry" not in entry
        entry["pct_avg_entry"] = avg
        entry["pct_stop"] = new_stop
        entry["pct_target"] = new_target
        # Re-arm both -- if this buy moved the levels, an old alert fired
        # against the PREVIOUS levels doesn't mean anything about the new
        # ones.
        entry["pct_alerted_stop"] = False
        entry["pct_alerted_target"] = False
        levels[product_id] = entry
        save_json_file(EXIT_LEVELS_FILE, levels)
        telegram_send(
            ("🎯 Watching return-based levels" if is_fresh else "🔄 Return-based levels updated (avg entry changed)")
            + f" for {product_id}\n"
            f"Avg entry: {avg:.6g}\n"
            f"Stop ({AUTO_ALERT_STOP_PCT}% below avg): {new_stop:.6g}\n"
            f"Target (+{AUTO_ALERT_TARGET_PCT}% above avg): {new_target:.6g}\n"
            "(alert-only, independent of the structural stop/target above -- I'll ping you if either is crossed, you decide what to do)"
        )
    except Exception as e:
        print(f"  [warn] _update_pct_levels({product_id}) failed: {e}")


def check_exit_levels():
    """Called once per main scan cycle: for every bot position currently
    being watched (exit_levels.json), checks the live price against its
    stored structural stop/target and fires a ONE-TIME Telegram alert the
    first time either is crossed (alerted_stop/alerted_target flags
    prevent repeat spam every cycle after that). Alert-only, exactly like
    every other signal in this bot -- never places an order on its own.

    Also self-heals: if a product_id is still listed here but the bot's
    own ledger no longer shows it as an open position (e.g. it was closed
    through a path that didn't go through _notify_if_position_closed, or
    the exit-levels file and trades.json ever drift out of sync), it's
    dropped from tracking rather than alerting forever on a position that
    doesn't exist anymore."""
    levels = load_json_file(EXIT_LEVELS_FILE, {})
    if not levels:
        return
    open_positions, _realized = _compute_position_ledger()
    changed = False
    for product_id, lv in list(levels.items()):
        if product_id not in open_positions:
            del levels[product_id]
            changed = True
            continue
        price = get_current_price(product_id)
        if price is None:
            continue
        if not lv.get("alerted_stop") and lv.get("stop") is not None and price <= lv["stop"]:
            telegram_send(
                f"🛑 STOP LEVEL HIT: {product_id}\n"
                f"Price: {price:.6g}  Stop: {lv['stop']:.6g}\n"
                f"Structural thesis invalidated (closed back below the broken resistance). Your call -- alert-only, nothing sold automatically."
            )
            lv["alerted_stop"] = True
            changed = True
        if not lv.get("alerted_target") and lv.get("target") is not None and price >= lv["target"]:
            telegram_send(
                f"🎯 TARGET HIT: {product_id}\n"
                f"Price: {price:.6g}  Target: {lv['target']:.6g}\n"
                f"Alert-only -- nothing sold automatically, your call whether to take it."
            )
            lv["alerted_target"] = True
            changed = True
        # RETURN-BASED checks (added 2026-08-24) -- separate pct_* fields on
        # the same record, same `price` already fetched above. See
        # _update_pct_levels()'s docstring for why these are independent
        # from the structural stop/target checked above, not a replacement.
        if not lv.get("pct_alerted_stop") and lv.get("pct_stop") is not None and price <= lv["pct_stop"]:
            telegram_send(
                f"🔴 PRICE ALERT: {product_id}\n"
                f"Type: STOP ({AUTO_ALERT_STOP_PCT}% below avg entry)\n"
                f"Entry: {lv.get('pct_avg_entry', float('nan')):.6g}  ->  Now: {price:.6g}\n"
                f"ℹ️ Informational only -- no order was placed automatically.\n"
                f"If you want to act: /sell {product_id} all   (or with a limit price)"
            )
            lv["pct_alerted_stop"] = True
            changed = True
        if not lv.get("pct_alerted_target") and lv.get("pct_target") is not None and price >= lv["pct_target"]:
            telegram_send(
                f"🟢 PRICE ALERT: {product_id}\n"
                f"Type: TARGET (+{AUTO_ALERT_TARGET_PCT}% above avg entry)\n"
                f"Entry: {lv.get('pct_avg_entry', float('nan')):.6g}  ->  Now: {price:.6g}\n"
                f"ℹ️ Informational only -- no order was placed automatically.\n"
                f"If you want to act: /sell {product_id} all   (or with a limit price)"
            )
            lv["pct_alerted_target"] = True
            changed = True
    if changed:
        save_json_file(EXIT_LEVELS_FILE, levels)


def send_heartbeat():
    """Send a Telegram health snapshot -- called periodically from main()'s
    loop (every HEARTBEAT_INTERVAL_HOURS) and on-demand via /status
    (handle_status_command(), a thin wrapper around this). The point isn't
    any single heartbeat message -- it's that they arrive on a predictable
    cadence, so a GAP in that cadence (no heartbeat, and no alerts either)
    is itself the alarm that something's wrong, without Amir having to
    notice the absence of alerts on his own or go check Render manually."""
    if _health["process_start"] is None:
        telegram_send("Bot is starting up -- health data not available yet.")
        return
    uptime = datetime.now(timezone.utc) - _health["process_start"]
    hours = uptime.total_seconds() / 3600
    lines = [
        "💓 Heartbeat -- bot is alive",
        f"Uptime: {hours:.1f}h",
        f"Cycles completed: {_health['cycle_count']}",
    ]
    if _health["last_cycle_seconds"] is not None:
        lines.append(f"Last cycle: {_health['last_cycle_seconds']:.1f}s, {_health['last_pairs_scanned']} pairs scanned")
    lines.append(f"Errors since start: {_health['errors_since_start']}")
    if _health["last_error"]:
        lines.append(f"Last error ({_health['last_error_time']}): {_health['last_error']}")
    lines.append(f"Trading: {'ENABLED' if TRADING_ENABLED else 'DISABLED'}")
    telegram_send("\n".join(lines))


def handle_status_command():
    """Handle the /status Telegram command -- the on-demand version of the
    periodic heartbeat (see send_heartbeat()'s docstring), for checking
    health right now instead of waiting for the next scheduled one."""
    send_heartbeat()


def handle_positions_command():
    """Handle the /positions Telegram command -- cross-references the bot's
    own trade ledger (trades.json, fee-adjusted average-cost basis via
    _compute_position_ledger()) against the REAL current Coinbase balances
    (get_balances(), always the source of truth for what you actually
    hold) to show an entry price and unrealized P&L for each open
    position.

    Important limitation: the average entry price is only known for
    quantity actually bought THROUGH this bot's /buy command. Anything
    bought outside the bot (directly in the Coinbase app, or before this
    feature existed) has no trade-log entry, so its entry price is
    genuinely unknown -- those rows say so explicitly rather than showing
    a wrong or misleading number.

    Hardened 2026-08-21: if you hold MORE of a coin than the bot's ledger
    thinks it bought (i.e. you also bought some manually, in addition to
    the bot-tracked purchase), the entry price shown is still correct
    PER UNIT for the bot-bought portion -- but it no longer silently
    applies that price (and the resulting $ P&L) to your full real
    balance, since that would overstate/understate the true $ P&L by
    blending in coins whose real cost basis this bot has no way to know.
    Instead it computes $ P&L only over the ledger-known quantity and
    flags the untracked remainder explicitly."""
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
    open_ledger, _realized = _compute_position_ledger()
    lines = ["📈 Open positions:"]
    for currency, avail, hold in sorted(positions, key=lambda x: x[0]):
        total = avail + hold
        current_price = get_current_price(f"{currency}-USD") or get_current_price(f"{currency}-USDC")
        ledger_pos = open_ledger.get(f"{currency}-USD") or open_ledger.get(f"{currency}-USDC")
        entry_price = ledger_pos["avg_price"] if ledger_pos else None
        ledger_qty = ledger_pos["qty"] if ledger_pos else 0.0
        line = f"\n{currency}: {total:.8g}"
        if current_price:
            line += f"  (~${total * current_price:,.2f})"
        if entry_price and current_price:
            pnl_pct = ((current_price - entry_price) / entry_price) * 100
            pnl_usd = (current_price - entry_price) * ledger_qty  # only the ledger-known qty, see docstring
            icon = "🟢" if pnl_pct >= 0 else "🔴"
            line += f"\n  entry (via bot): {entry_price:.6g}  now: {current_price:.6g}  {icon} {pnl_pct:+.1f}% ({pnl_usd:+,.2f}$)"
            untracked = total - ledger_qty
            if untracked > ledger_qty * 0.01 + 1e-9:  # meaningfully more held than the bot ever bought
                line += f"\n  ⚠️ {untracked:.8g} {currency} held beyond what the bot bought -- entry/P&L above covers only the bot-tracked {ledger_qty:.8g}"
        elif entry_price:
            line += f"\n  entry (via bot): {entry_price:.6g}  (current price unavailable)"
        else:
            line += "\n  entry price unknown (not bought through the bot, or predates trade tracking)"
        lines.append(line)
    telegram_send("\n".join(lines))


def handle_pnl_command():
    """Handle the /pnl Telegram command -- realized P&L (fee-adjusted)
    across every position the bot has ever fully closed, plus a grand
    total. Complements /positions (which only shows CURRENT unrealized
    P&L on OPEN positions): this is the "how have I actually done"
    number, covering trades that are already finished. Scope is the same
    as /positions -- bot-tracked trades only (see _compute_position_ledger()'s
    docstring).

    Shows a % return alongside every $ figure (added 2026-08-26, per
    Amir: "+$200 doesn't say much on its own -- is that from a $2,000
    position (10%) or a $2,000,000 one?"). % = realized_pnl_usd /
    total_cost_basis_usd, both already fee-adjusted the same way -- see
    _compute_position_ledger()'s docstring for exactly what that basis
    covers."""
    _open, realized = _compute_position_ledger()
    closed = {pid: r for pid, r in realized.items() if r["closed_lots"] > 0}
    if not closed:
        telegram_send("📊 No fully-closed bot-tracked positions yet.")
        return
    lines = ["📊 Realized P&L (bot-tracked trades, after fees):"]
    total_pnl = 0.0
    total_fees = 0.0
    total_cost_basis = 0.0
    for product_id, r in sorted(closed.items()):
        icon = "🟢" if r["realized_pnl_usd"] >= 0 else "🔴"
        basis = r.get("total_cost_basis_usd") or 0.0
        pct_s = f" ({r['realized_pnl_usd'] / basis * 100:+.1f}%)" if basis > 0 else ""
        lines.append(
            f"\n{product_id}: {icon} {r['realized_pnl_usd']:+,.2f}${pct_s} "
            f"({r['closed_lots']} closed round-trip{'s' if r['closed_lots'] != 1 else ''}, "
            f"{r['total_fees_usd']:.2f}$ fees)"
        )
        total_pnl += r["realized_pnl_usd"]
        total_fees += r["total_fees_usd"]
        total_cost_basis += basis
    icon = "🟢" if total_pnl >= 0 else "🔴"
    total_pct_s = f" ({total_pnl / total_cost_basis * 100:+.1f}%)" if total_cost_basis > 0 else ""
    lines.append(f"\n{icon} Total realized P&L: {total_pnl:+,.2f}${total_pct_s}  (total fees: {total_fees:.2f}$)")
    telegram_send("\n".join(lines))


def handle_alerts_command():
    """Handle the /alerts Telegram command (added 2026-08-24) -- lists every
    position currently being watched in exit_levels.json, showing BOTH the
    structural stop/target (added 2026-08-21, locked in at entry, never
    moves) and the return-based stop/target (added 2026-08-24, always
    AUTO_ALERT_STOP_PCT/AUTO_ALERT_TARGET_PCT off the current avg entry,
    updates on every add-on buy) side by side per product -- see the module
    comments above EXIT_LEVELS_FILE for why these are two independent
    numbers, not one. Shown for the first time here: there was previously
    no command to see what the structural side was watching either."""
    levels = load_json_file(EXIT_LEVELS_FILE, {})
    if not levels:
        telegram_send("👀 No positions being watched.")
        return
    lines = ["👀 Watched positions:"]
    for product_id, lv in sorted(levels.items()):
        lines.append(f"\n{product_id}")
        if lv.get("stop") is not None or lv.get("target") is not None:
            stop_s = f"{lv['stop']:.6g}" if lv.get("stop") is not None else "?"
            tgt_s = f"{lv['target']:.6g}" if lv.get("target") is not None else "n/a"
            done = " (hit)" if lv.get("alerted_stop") else ""
            done_t = " (hit)" if lv.get("alerted_target") else ""
            lines.append(f"  Structural: stop {stop_s}{done}  target {tgt_s}{done_t}")
        if lv.get("pct_stop") is not None:
            done = " (hit)" if lv.get("pct_alerted_stop") else ""
            done_t = " (hit)" if lv.get("pct_alerted_target") else ""
            lines.append(
                f"  Return-based (avg {lv.get('pct_avg_entry', float('nan')):.6g}): "
                f"stop {lv['pct_stop']:.6g}{done}  target {lv['pct_target']:.6g}{done_t}"
            )
    lines.append("\n(cancel any of these with /cancelalert PRODUCT_ID -- clears both structural and return-based watching for it)")
    telegram_send("\n".join(lines))


def handle_cancelalert_command(product_id):
    """Handle the /cancelalert PRODUCT_ID Telegram command (added
    2026-08-24) -- manually stop watching a position for BOTH structural
    and return-based stop/target alerts (e.g. if you've decided to hold
    longer and don't want the -5% ping). Does not touch the position
    itself or place any order -- purely stops future alerts. A future buy
    into the same product_id re-arms watching from scratch via
    _maybe_init_exit_levels()/_update_pct_levels()."""
    levels = load_json_file(EXIT_LEVELS_FILE, {})
    if product_id not in levels:
        telegram_send(f"Nothing being watched for {product_id}. Check /alerts for the exact product ID.")
        return
    _clear_exit_levels(product_id)
    telegram_send(f"🔕 Stopped watching {product_id} (structural + return-based).")


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


def handle_scan_command():
    """Handle the /scan Telegram command -- manually triggers a full
    CONFIRMED-breakout pass (the same run_daily_cycle() that check_and_run_
    daily_pass() otherwise only runs once per UTC day) across every pair,
    right now, instead of waiting for the next automatic run. Requested
    2026-08-25: "as usual, all of them" -- not scoped to one product_id,
    same full universe fetch_products() returns to the automatic pass.

    Deliberately does NOT touch DAILY_CHECK_MARKER_FILE -- that marker
    controls only the AUTOMATIC once-per-UTC-day trigger in
    check_and_run_daily_pass(). Running /scan doesn't consume or reset that
    budget, so the automatic pass still fires normally at its own next UTC
    rollover no matter how many times /scan is used in between. It reuses
    (mutates in place) the SAME daily_state/outcomes dicts the automatic
    pass uses -- see _shared_daily_state/_shared_outcomes above -- so a
    coin /scan just confirmed as breakout won't alert again when the
    automatic pass re-checks it later the same day (and vice versa).

    Runs on its own background thread, not inline on the Telegram polling
    thread that called this: a full ~400-pair pass takes several minutes
    (REQUEST_PACING_SECONDS per pair, x2 for daily+6h-context candles on
    anything that alerts), and polling is single-threaded -- every other
    command (/status, /balance, ...) would sit unanswered until it
    finished otherwise. Guarded by _daily_scan_lock so this can never run
    concurrently with the automatic pass or a second /scan (see the lock's
    own docstring for exactly what that race would otherwise cause)."""
    if _shared_daily_state is None or _shared_outcomes is None:
        telegram_send("Bot is still starting up -- try /scan again in a few seconds.")
        return
    if not _daily_scan_lock.acquire(blocking=False):
        telegram_send("⏳ A scan is already running -- hang tight, it'll post results when it's done (usually a few minutes).")
        return

    def _run():
        try:
            products = fetch_products()
            telegram_send(f"🔍 Manual scan starting: {len(products)} pairs. This can take a few minutes -- new confirmed breakouts will alert as they're found.")
            # Retest tracking (added 2026-08-26) isn't shared via a
            # module-level global like daily_state/outcomes -- it's loaded
            # fresh and saved back here, same as check_and_run_daily_pass()
            # does for the automatic pass. Fine either way since
            # handle_retest_command()/other readers always load fresh from
            # disk too; the _daily_scan_lock this function already holds
            # rules out a concurrent writer.
            retest_pending = load_json_file(RETEST_PENDING_FILE, {})
            retest_tracking = load_json_file(RETEST_TRACKING_FILE, {})
            run_daily_cycle(products, _shared_daily_state, _shared_outcomes, retest_pending, retest_tracking)
            save_json_file(DAILY_STATE_FILE, _shared_daily_state)
            save_json_file(RETEST_PENDING_FILE, retest_pending)
            save_json_file(RETEST_TRACKING_FILE, retest_tracking)
            telegram_send(f"✅ Manual scan done: {len(products)} pairs checked.")
        except Exception as e:
            print(f"  [error] manual /scan failed: {e}")
            traceback.print_exc()
            telegram_send(f"❌ Manual scan failed partway through: {e}")
        finally:
            _daily_scan_lock.release()

    threading.Thread(target=_run, daemon=True).start()


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
    elif cmd == "/pnl":
        handle_pnl_command()
    elif cmd == "/alerts":
        handle_alerts_command()
    elif cmd == "/retest":
        handle_retest_command()
    elif cmd == "/cancelalert":
        if len(parts) != 2:
            telegram_send("Usage: /cancelalert PRODUCT_ID\n(get the PRODUCT_ID from /alerts)")
            return
        handle_cancelalert_command(parts[1].upper())
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
    elif cmd == "/status":
        handle_status_command()
    elif cmd == "/scan":
        handle_scan_command()
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
            "/pnl -- realized P&L (after fees) across every position the bot has fully closed\n"
            "/alerts -- watched positions: structural stop/target AND return-based "
            f"(-{AUTO_ALERT_STOP_PCT}%/+{AUTO_ALERT_TARGET_PCT}% from avg entry) stop/target, side by side\n"
            "/retest -- retest-entry status: pairs awaiting a retest, and open T15/T25 statistical tracks "
            "(informational only, no trade is placed by this)\n"
            "/cancelalert PRODUCT_ID -- stop watching a position (both structural and return-based) -- ID from /alerts\n"
            "/history [N] -- last N trades placed via the bot (default 10, no upper limit)\n"
            "/stats -- win/loss track record of breakout ALERTS (not trades)\n"
            "/status -- bot health snapshot on demand (uptime, last cycle, errors) -- also sent automatically every "
            f"{HEARTBEAT_INTERVAL_HOURS:g}h as a heartbeat\n"
            "/scan -- manually run the full CONFIRMED-breakout pass on all pairs right now, instead of waiting for "
            "the once-per-UTC-day automatic check (takes a few minutes; doesn't affect the automatic check's own schedule)\n"
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

def run_cycle(products, state, outcomes):
    """The fast, continuous hourly pass -- runs every CYCLE_SLEEP_SECONDS
    (5 min) for all products. Since 2026-08-19, this can only ever produce
    "neutral" or "watching" -- "breakout" is exclusively decided by
    run_daily_cycle() below, once per UTC day. See DAILY_LOOKBACK_CANDLES
    above for why."""
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

            prev = state.get(product_id, {})
            prev_signal = prev.get("signal", "neutral")
            prev_reason = prev.get("watching_reason")
            new_signal = result["signal"]
            new_reason = result["watching_reason"]

            # Edge-triggered on more than just the top-level signal: a coin
            # that was already "watching" (approaching) BEFORE it clears
            # resistance would otherwise never get a fresh alert when it
            # actually clears it, because "signal" stays "watching" both
            # before and after -- only watching_reason changes, from
            # "approaching" to "cleared_hourly". That's a materially
            # stronger event (found during the pre-deploy review requested
            # 2026-08-19, before this ever hit production) and deserves its
            # own notification, not silence. Symmetric on the way down too
            # (cleared_hourly -> approaching) so a real reason-change is
            # never swallowed, while a same-reason re-check (the common
            # case, most cycles) still stays silent as before.
            if new_signal == "watching" and (new_signal != prev_signal or new_reason != prev_reason):
                # Extra 6H-timeframe context, fetched ONLY here -- i.e. only
                # for the specific product that's actually about to alert,
                # not for all ~400 products every cycle. See
                # fetch_6h_context() for the full rationale.
                result["ctx_6h"] = fetch_6h_context(product_id)
                time.sleep(REQUEST_PACING_SECONDS)
                if product_id != "BTC-USD":
                    # Skip the self-referential case: BTC-USD's own alert
                    # already shows BTC-USD's own RSI/EMA9-26 trend above --
                    # tagging it with "BTC trend" again would be redundant.
                    result["btc_trend"] = get_btc_trend()
                    time.sleep(REQUEST_PACING_SECONDS)
                if new_reason == "cleared_hourly":
                    # Only for this reason -- "approaching" alerts don't show
                    # the daily-confirmation note at all, so there's nothing
                    # for this number to feed. See fetch_daily_resistance().
                    result["daily_resistance"] = fetch_daily_resistance(product_id)
                    time.sleep(REQUEST_PACING_SECONDS)
                notify(product_id, result)

            state[product_id] = {
                "signal": new_signal,
                "watching_reason": new_reason,
                "updated": datetime.now(timezone.utc).isoformat(),
            }

        except Exception:
            print(f"  [error] unexpected failure on {product_id}")
            traceback.print_exc()

        if (i + 1) % 50 == 0:
            print(f"  ...scanned {i + 1}/{len(products)}")

    return state, outcomes


def resolve_same_day_tie_with_6h(product_id, day_ts, stop_level, target_level):
    """When a single DAILY candle shows BOTH a stop level and a target
    level crossed (low <= stop_level AND high >= target_level), the daily
    bar alone can't say which happened first -- see spec 8.8 for the full
    writeup (this was discovered running the historical backtest, where it
    materially changed the win-rate numbers: T25 25.5%->18.8% optimistic
    vs. conservative, before this fix was applied here).

    Fetches recent 6H candles (granularity=SIX_HOUR_GRANULARITY_SECONDS)
    for product_id -- the same endpoint/pattern as fetch_6h_context() --
    and filters to just the ~4 buckets covering day_ts (the UTC calendar
    day of the daily candle in question). Coinbase's candle fetch always
    returns the MOST RECENT ~300 candles, so this only works for a day
    within that recent window -- true by construction here, since this is
    only ever called live, on TODAY's daily candle, right after it closes.

    Returns "stop_first", "target_first", or None (fetch failed, too few
    6H candles for that day, or still tied even at 6H resolution -- same
    residual ambiguity the historical analysis found in ~9-13% of ties).
    Caller treats None the same as the conservative assumption (stop
    first) -- see spec 8.8's own conservative-default treatment of the
    unresolved remainder."""
    try:
        candles = fetch_candles(product_id, granularity=SIX_HOUR_GRANULARITY_SECONDS)
        if not candles:
            return None
        day_candles = [c for c in candles if day_ts <= c[0] < day_ts + 86400]
        day_candles.sort(key=lambda c: c[0])
        if not day_candles:
            return None
        stop_bucket, target_bucket = None, None
        for i, c in enumerate(day_candles):
            lo, hi = c[1], c[2]
            if stop_bucket is None and lo <= stop_level:
                stop_bucket = i
            if target_bucket is None and hi >= target_level:
                target_bucket = i
        if stop_bucket is None and target_bucket is None:
            return None  # neither actually confirms at 6H resolution -- shouldn't happen, but be defensive
        if stop_bucket is None:
            return "target_first"
        if target_bucket is None:
            return "stop_first"
        if stop_bucket < target_bucket:
            return "stop_first"
        if target_bucket < stop_bucket:
            return "target_first"
        return None  # same 6H bucket -- still tied, same residual case as spec 8.8
    except Exception as e:
        print(f"  [warn] resolve_same_day_tie_with_6h({product_id}) failed: {e}")
        return None


def open_retest_pending(pending, product_id, resistance, today_str):
    """Called from run_daily_cycle() right where a fresh BREAKOUT alert
    fires (mirrors record_pending_outcome()'s call site exactly). Opens a
    new "awaiting retest" watch for product_id. If one was already open for
    this product_id (rare -- would need a second fresh breakout while the
    first retest watch is still pending), it's simply replaced with the
    new, presumably more current, resistance level rather than trying to
    track two overlapping watches per pair -- kept deliberately simple for
    v1, see spec section 6."""
    pending[product_id] = {"resistance": resistance, "opened_date": today_str, "days_waited": 0}


def check_pending_retest(pending, tracking, product_id, daily_candles, today_str):
    """Called for EVERY product_id in run_daily_cycle()'s per-product loop
    (not just ones with a fresh breakout today) -- reuses that SAME daily
    candle fetch, no extra API call. If product_id has an open "awaiting
    retest" record, checks TODAY's already-closed daily candle (the last
    entry in daily_candles, same as analyze_daily() reads) against the
    retest condition: low within RETEST_TOUCH_TOLERANCE_PCT% above the
    broken level, AND close back at/above it (spec section 3).

    On confirmation: removes the pending record, opens the T15/T25
    statistical tracking entries (open_retest_tracks()), and returns an
    event dict for the caller to pass to notify_retest(). On no
    confirmation: increments days_waited, and drops the record (silently,
    no alert -- an expired watch isn't a notable event) once
    RETEST_MAX_WAIT_DAYS is reached without a hold. Returns None in every
    non-confirming case."""
    rec = pending.get(product_id)
    if not rec or not daily_candles:
        return None
    today_candle = daily_candles[-1]
    low, high, close = today_candle[1], today_candle[2], today_candle[4]
    resistance = rec["resistance"]
    touch_band = resistance * (1 + RETEST_TOUCH_TOLERANCE_PCT / 100)

    if low <= touch_band and close >= resistance:
        entry_price = resistance * (1 + RETEST_ENTRY_BUFFER_PCT / 100)
        del pending[product_id]
        open_retest_tracks(tracking, product_id, entry_price, resistance, today_str)
        return {"product_id": product_id, "resistance": resistance, "entry_price": entry_price}

    rec["days_waited"] += 1
    if rec["days_waited"] >= RETEST_MAX_WAIT_DAYS:
        del pending[product_id]  # expired -- no hold within the window, silently give up watching
    return None


def open_retest_tracks(tracking, product_id, entry_price, resistance, today_str):
    """Opens one statistical tracking entry per key in RETEST_TARGET_PCTS
    (currently T15 and T25) for a just-confirmed retest event. Appends to
    tracking[product_id] -- a LIST, because the same pair can produce
    multiple retest events over the bot's lifetime, each tracked
    independently (matches the historical backtest, where 74 of 147
    unique pairs had more than one retest event -- see spec 8.8)."""
    tracks = {}
    for key, target_pct in RETEST_TARGET_PCTS.items():
        tracks[key] = {
            "status": "open",
            "stop_level": entry_price * (1 - RETEST_STOP_PCT / 100),
            "target_level": entry_price * (1 + target_pct / 100),
            "days_open": 0,
        }
    tracking.setdefault(product_id, []).append({
        "opened_date": today_str,
        "entry_price": entry_price,
        "resistance": resistance,
        "tracks": tracks,
    })


def update_retest_tracks(tracking, product_id, daily_candles, today_ts, today_str):
    """Called for every product_id in run_daily_cycle()'s per-product
    loop, same reuse of that day's already-fetched daily_candles as
    check_pending_retest(). For every still-OPEN track (T15/T25) on every
    retest event recorded for this product_id, checks today's daily candle
    against that track's stop_level/target_level.

    Same-day tie handling (spec 8.8): if BOTH are crossed on today's
    candle, resolves the true order with a live 6H fetch
    (resolve_same_day_tie_with_6h()) instead of guessing -- this is the
    ONLY place this module makes an extra API call beyond the daily scan
    it's already doing, and only on the rare day this specific situation
    happens. Falls back to the conservative assumption (stop first / loss)
    if that 6H fetch can't resolve it either, exactly like the historical
    analysis in spec 8.8 does for its own small unresolved residual."""
    events = tracking.get(product_id)
    if not events or not daily_candles:
        return
    today_candle = daily_candles[-1]
    low, high = today_candle[1], today_candle[2]

    for ev in events:
        for key, tr in ev["tracks"].items():
            if tr["status"] != "open":
                continue
            stop_hit = low <= tr["stop_level"]
            target_hit = high >= tr["target_level"]
            if stop_hit and target_hit:
                order = resolve_same_day_tie_with_6h(product_id, today_ts, tr["stop_level"], tr["target_level"])
                if order == "target_first":
                    tr["status"] = "win"
                else:
                    tr["status"] = "loss"  # "stop_first" or unresolved (None) -- conservative default, see spec 8.8
                tr["resolved_date"] = today_str
                tr["resolved_via_6h_tie_break"] = True
            elif stop_hit:
                tr["status"] = "loss"
                tr["resolved_date"] = today_str
            elif target_hit:
                tr["status"] = "win"
                tr["resolved_date"] = today_str
            else:
                tr["days_open"] += 1


def notify_retest(event):
    """Sends the separate "retest confirmed" Telegram alert (spec section
    5, decision Q5) -- deliberately its own message, not a field tacked
    onto the original BREAKOUT alert, so the two remain independently
    readable/actionable. Also appends to ALERTS_LOG_FILE like notify()
    does, tagged kind="retest_confirmed" so it's distinguishable from
    ordinary breakout/watching entries in that same log."""
    product_id = event["product_id"]
    text = (
        f"🔁 {product_id}: RETEST CONFIRMED\n"
        f"Broken level held: {event['resistance']:.6g}\n"
        f"Simulated entry (level + {RETEST_ENTRY_BUFFER_PCT:g}%): {event['entry_price']:.6g}\n"
        f"Tracking {', '.join(RETEST_TARGET_PCTS.keys())} in parallel (stop ~{RETEST_STOP_PCT:g}%) -- "
        f"see /retest for status. This is a statistical/informational signal, same as the daily BREAKOUT "
        f"alert -- nothing is bought automatically."
    )
    telegram_send(text)
    log_event = {"time": datetime.now(timezone.utc).isoformat(), "kind": "retest_confirmed", **event}
    with open(ALERTS_LOG_FILE, "a") as f:
        f.write(json.dumps(log_event) + "\n")


def handle_retest_command():
    """Handle the /retest Telegram command (added 2026-08-26) -- status
    snapshot of the retest-entry statistical layer: pairs currently
    "awaiting retest" (with days remaining), and every OPEN T15/T25
    tracked event with its running stop/target. Read-only, mirrors
    /alerts' shape for the existing exit-level watching. Resolved
    (win/loss) tracks are intentionally omitted here to keep this a
    live-status view, not a report -- the biweekly comparison (spec
    section 6) covers the accumulated win-rate/expectancy numbers."""
    pending = load_json_file(RETEST_PENDING_FILE, {})
    tracking = load_json_file(RETEST_TRACKING_FILE, {})

    lines = ["🔁 Retest-entry status:"]

    if pending:
        lines.append("\nAwaiting retest:")
        for product_id, rec in sorted(pending.items()):
            days_left = max(0, RETEST_MAX_WAIT_DAYS - rec["days_waited"])
            lines.append(f"  {product_id}: level {rec['resistance']:.6g}, {days_left}d left to retest")
    else:
        lines.append("\nAwaiting retest: none.")

    open_lines = []
    for product_id, events in sorted(tracking.items()):
        for ev in events:
            open_tracks = {k: t for k, t in ev["tracks"].items() if t["status"] == "open"}
            if not open_tracks:
                continue
            parts = []
            for key, t in sorted(open_tracks.items()):
                shown = " (displayed)" if key == RETEST_DISPLAYED_TRACK else ""
                parts.append(f"{key}{shown}: stop {t['stop_level']:.6g} / target {t['target_level']:.6g}")
            open_lines.append(f"  {product_id} (entry {ev['entry_price']:.6g}): " + "  ·  ".join(parts))
    if open_lines:
        lines.append("\nOpen tracks:")
        lines.extend(open_lines)
    else:
        lines.append("\nOpen tracks: none.")

    telegram_send("\n".join(lines))


def run_daily_cycle(products, daily_state, outcomes, retest_pending, retest_tracking):
    """The CONFIRMED-breakout pass -- runs once per UTC calendar day (see
    check_and_run_daily_pass in main()), never on the regular 5-minute
    cycle, against fully-closed DAILY candles for every product.

    Uses its own daily_state dict (persisted separately at
    DAILY_STATE_FILE) rather than the hourly `state` dict passed to
    run_cycle() -- a coin's hourly "watching" status and its daily
    "breakout" status are two independent questions on two independent
    schedules, and must never be able to overwrite each other.

    This is the ONLY place "breakout" can fire (see analyze_daily) and
    therefore the only place record_pending_outcome() is called from now --
    win/loss tracking measures confirmed daily breakouts, same as before,
    just sourced from here instead of the hourly path.

    Persists daily_state (and outcomes, whenever it changes) to disk
    INCREMENTALLY, product by product, rather than only once at the end of
    the full ~400-pair loop. Found in adversarial review 2026-08-19: this
    loop can take several minutes, and Render can kill/redeploy the process
    at any point during it (documented elsewhere in this file as something
    that has actually happened). Without incremental saves, a mid-scan
    kill loses every in-memory daily_state update from that run -- so on
    the next boot, check_and_run_daily_pass() (seeing no marker file yet
    for today) reruns the ENTIRE daily scan, and every coin already
    notified as BREAKOUT earlier in the interrupted run looks "new" again
    (its daily_state update never made it to disk), causing a duplicate
    Telegram alert AND a duplicate record_pending_outcome() entry (silently
    double-counting that trade in win/loss stats later). Saving after every
    product bounds the damage from a mid-scan kill to at most the single
    product being processed at the moment of the crash. save_json_file()
    writes via temp-file+rename (see its own comment), so these frequent
    saves are already crash-safe/atomic -- no risk of a half-written file."""
    for i, product_id in enumerate(products):
        try:
            daily_candles = fetch_candles(product_id, granularity=86400)
            time.sleep(REQUEST_PACING_SECONDS)
            if not daily_candles:
                continue
            daily_candles = drop_incomplete_last_candle(daily_candles, granularity_seconds=86400)

            result = analyze_daily(daily_candles)
            if not result:
                continue

            prev_signal = daily_state.get(product_id, {}).get("signal", "neutral")
            new_signal = result["signal"]

            # edge-triggered: only alert on a fresh transition INTO breakout
            if new_signal == "breakout" and new_signal != prev_signal:
                # Extra 6H-timeframe context, fetched ONLY here -- see the
                # matching comment in run_cycle() above and
                # fetch_6h_context()'s docstring for the full rationale.
                result["ctx_6h"] = fetch_6h_context(product_id)
                time.sleep(REQUEST_PACING_SECONDS)
                if product_id != "BTC-USD":
                    result["btc_trend"] = get_btc_trend()
                    time.sleep(REQUEST_PACING_SECONDS)
                notify(product_id, result)
                record_pending_outcome(outcomes, product_id, result, datetime.now(timezone.utc))
                save_json_file(OUTCOMES_FILE, outcomes)

                # Retest-entry tracking (added 2026-08-26, spec section 5):
                # a fresh confirmed breakout opens a NEW "awaiting retest"
                # watch, independent of and in addition to the alert above.
                today_str = datetime.now(timezone.utc).date().isoformat()
                open_retest_pending(retest_pending, product_id, result["resistance"], today_str)
                save_json_file(RETEST_PENDING_FILE, retest_pending)

            daily_state[product_id] = {"signal": new_signal, "updated": datetime.now(timezone.utc).isoformat()}
            save_json_file(DAILY_STATE_FILE, daily_state)

            # Retest-entry: check every pair with an open "awaiting retest"
            # watch, and update every OPEN T15/T25 track -- for EVERY
            # product_id, not just ones with a fresh breakout today, using
            # the SAME daily_candles already fetched above (spec section
            # 5: "this covers every breakout event the scan identifies on
            # all 398 pairs, every day, regardless of whether Amir buys").
            today_str = datetime.now(timezone.utc).date().isoformat()
            today_ts = daily_candles[-1][0]
            retest_event = check_pending_retest(retest_pending, retest_tracking, product_id, daily_candles, today_str)
            if retest_event:
                notify_retest(retest_event)
                save_json_file(RETEST_PENDING_FILE, retest_pending)
                save_json_file(RETEST_TRACKING_FILE, retest_tracking)
            update_retest_tracks(retest_tracking, product_id, daily_candles, today_ts, today_str)
            save_json_file(RETEST_TRACKING_FILE, retest_tracking)

        except Exception:
            print(f"  [error] unexpected failure on {product_id} (daily)")
            traceback.print_exc()

        if (i + 1) % 50 == 0:
            print(f"  ...daily-scanned {i + 1}/{len(products)}")

    return daily_state, outcomes, retest_pending, retest_tracking


def check_and_run_daily_pass(products, daily_state, outcomes):
    """Runs run_daily_cycle() at most once per UTC calendar date. Compares
    today's UTC date against DAILY_CHECK_MARKER_FILE (persisted to disk, so
    it survives restarts/redeploys within the same day) rather than
    tracking elapsed time -- this way a redeploy mid-day never re-triggers
    a full 398-pair daily scan, but a fresh UTC day always gets exactly one
    run whenever the process next happens to check, even if it was down
    across the actual midnight rollover.

    First-ever run (no marker file yet) always triggers immediately, so a
    fresh deploy gets a real daily baseline right away instead of waiting
    up to 24h for the first confirmed-breakout check.

    Guarded by _daily_scan_lock (added 2026-08-25, see its own docstring)
    so this can never run at the same time as a manually-triggered /scan.
    If a manual scan happens to be in progress exactly when the UTC day
    rolls over, this simply skips for now -- it does NOT write
    DAILY_CHECK_MARKER_FILE in that case, so it's retried next cycle (5 min
    later) rather than the day silently going unchecked."""
    today_str = datetime.now(timezone.utc).date().isoformat()
    last_checked = load_json_file(DAILY_CHECK_MARKER_FILE, {}).get("date")
    if not products or today_str == last_checked:
        return daily_state, outcomes

    if not _daily_scan_lock.acquire(blocking=False):
        print(f"  [info] daily pass due for {today_str}, but a manual /scan is in progress -- will retry next cycle")
        return daily_state, outcomes
    try:
        print(f"\n=== New UTC day ({today_str}) -- running daily BREAKOUT check on {len(products)} pairs ===")
        retest_pending = load_json_file(RETEST_PENDING_FILE, {})
        retest_tracking = load_json_file(RETEST_TRACKING_FILE, {})
        daily_state, outcomes, retest_pending, retest_tracking = run_daily_cycle(
            products, daily_state, outcomes, retest_pending, retest_tracking)
        save_json_file(DAILY_STATE_FILE, daily_state)
        save_json_file(RETEST_PENDING_FILE, retest_pending)
        save_json_file(RETEST_TRACKING_FILE, retest_tracking)
        save_json_file(DAILY_CHECK_MARKER_FILE, {"date": today_str})
        print(f"=== Daily BREAKOUT check for {today_str} done ===")
    finally:
        _daily_scan_lock.release()
    return daily_state, outcomes


def main():
    print("Coinbase Breakout Scanner starting.")
    print(f"Granularity={GRANULARITY_SECONDS}s  Lookback={LOOKBACK_CANDLES}  Cycle={CYCLE_SLEEP_SECONDS}s")
    print(f"Daily breakout check: DAILY_LOOKBACK_CANDLES={DAILY_LOOKBACK_CANDLES}d, once per UTC day "
          f"(\"BREAKOUT\" only ever fires from this daily check now -- the hourly scan tops out at \"watching\")")
    print(f"Outcome tracking: evaluate after {EVALUATION_HOURS}h, win>={SUCCESS_THRESHOLD_PCT}% loss<=-{FAILURE_THRESHOLD_PCT}%")
    print(f"Retest-entry tracking: wait<={RETEST_MAX_WAIT_DAYS}d, touch tol={RETEST_TOUCH_TOLERANCE_PCT}%, "
          f"entry buffer={RETEST_ENTRY_BUFFER_PCT}%, stop={RETEST_STOP_PCT}%, targets={RETEST_TARGET_PCTS} "
          f"(displayed: {RETEST_DISPLAYED_TRACK}) -- statistical only, no auto-buy")

    state = load_state()
    daily_state = load_json_file(DAILY_STATE_FILE, {})
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

    # Hand handle_scan_command() (Telegram polling thread) a reference to
    # these SAME dict objects -- must happen after the one-time-reset block
    # above, which can rebind outcomes to a brand-new dict; grabbing the
    # reference any earlier would leave /scan mutating a stale, discarded
    # dict instead of the one main()'s loop actually uses. Must also happen
    # BEFORE the Telegram thread starts (right below), so /scan can never
    # see these as still None due to a startup race. See _shared_daily_state
    # /_shared_outcomes's own docstring above for why a reference is enough
    # (both are mutated in place, never reassigned, for the rest of the
    # process's life).
    global _shared_daily_state, _shared_outcomes
    _shared_daily_state = daily_state
    _shared_outcomes = outcomes

    print(f"Trading: {'ENABLED' if TRADING_ENABLED else 'DISABLED (set COINBASE_API_KEY / COINBASE_API_SECRET to enable)'}")
    if TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID:
        threading.Thread(target=telegram_polling_loop, daemon=True).start()

    _health["process_start"] = datetime.now(timezone.utc)
    print(f"Heartbeat: every {HEARTBEAT_INTERVAL_HOURS:g}h (see /status for an on-demand check)")
    last_heartbeat_sent = None

    while True:
        cycle_start = time.time()
        try:
            now = datetime.now(timezone.utc)
            print(f"\n=== Cycle start {now.isoformat()} ===")

            products = fetch_products()
            print(f"Scanning {len(products)} pairs on Coinbase ({'/'.join(sorted(QUOTE_CURRENCIES))})...")
            _health["last_pairs_scanned"] = len(products)

            if products:
                state, outcomes = run_cycle(products, state, outcomes)
                save_state(state)

                # Once-per-UTC-day confirmed BREAKOUT check (see
                # check_and_run_daily_pass) -- a no-op on every cycle except
                # the first one after the UTC date rolls over, when it runs
                # a full daily pass over all products. That one cycle will
                # take noticeably longer (an extra ~398-pair scan); this is
                # expected, not a hang.
                daily_state, outcomes = check_and_run_daily_pass(products, daily_state, outcomes)

            outcomes, stats = evaluate_pending_outcomes(outcomes, stats, now)
            save_json_file(OUTCOMES_FILE, outcomes)
            save_json_file(STATS_FILE, stats)

            known_open_order_ids = check_order_fills(known_open_order_ids)
            save_json_file(OPEN_ORDERS_STATE_FILE, list(known_open_order_ids))

            if TRADING_ENABLED:
                check_exit_levels()

            _health["cycle_count"] += 1
        except Exception as e:
            # Per-product errors are already caught inside run_cycle, but
            # anything outside that (fetch_products, evaluate_pending_outcomes,
            # disk I/O, etc.) used to be unhandled -- one bad response or a
            # transient error would silently kill the entire 24/7 process
            # until Render noticed and restarted it. Catch broadly here so a
            # single bad cycle can't take the whole scanner down.
            print("  [error] unexpected failure in main cycle -- scanner will keep running")
            traceback.print_exc()
            _health["errors_since_start"] += 1
            _health["last_error"] = str(e)
            _health["last_error_time"] = datetime.now(timezone.utc).isoformat()

        elapsed = time.time() - cycle_start
        _health["last_cycle_seconds"] = elapsed
        print(f"Cycle done in {elapsed:.1f}s. Sleeping {max(0, CYCLE_SLEEP_SECONDS - elapsed):.1f}s.")

        now_utc = datetime.now(timezone.utc)
        if last_heartbeat_sent is None or (now_utc - last_heartbeat_sent).total_seconds() >= HEARTBEAT_INTERVAL_HOURS * 3600:
            try:
                send_heartbeat()
            except Exception as e:
                print(f"  [warn] send_heartbeat failed: {e}")
            last_heartbeat_sent = now_utc

        sleep_for = max(0, CYCLE_SLEEP_SECONDS - elapsed)
        time.sleep(sleep_for)


if __name__ == "__main__":
    main()
