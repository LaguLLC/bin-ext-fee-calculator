import hashlib
import inspect
import json
import os
import re
import shutil
import tempfile
import threading
import uuid
from datetime import date, datetime, timedelta, timezone
from itertools import product

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

if not (hasattr(st, "fragment") and hasattr(st, "dialog")):
    st.set_page_config(page_title="Bin Extension Fee Calculator", page_icon="🗑️", layout="wide")
    st.error(
        f"This app needs Streamlit 1.37 or newer (found {st.__version__}). "
        "Add `streamlit>=1.37` to requirements.txt and reboot the app."
    )
    st.stop()


# ──────────────────────────────────────────────
# Constants
# ──────────────────────────────────────────────
SERVICE_RETURN = "service_return"
REPO = "repo"
SWAP = "swap"          # empty bin dropped, full bin loaded (instead of service-and-return)
DRY_RUN = "dry_run"    # truck went, nothing was loaded
HISTORY_FILE = "history.json"
HISTORY_PREV = HISTORY_FILE + ".prev"  # last good copy, kept on every write
MAX_UNDO = 50
MAX_UNDO_SAVED = 30  # how many undo/redo steps are mirrored to the browser

TYPE_DISPLAY = {
    "S/Rtn": SERVICE_RETURN,
    "S/Repo": REPO,
    "S/Swap": SWAP,
    "Dry run": DRY_RUN,
}
TYPE_FROM_CALC = {v: k for k, v in TYPE_DISPLAY.items()}

# Pick-lists. Edit these two lists to change the dropdowns; nothing else depends on them.
WASTE_TYPES = ["MSW", "Cardboard", "Metal", "Wood", "Green waste", "Mixed", "Other"]
# Per-work-order billing basis (table column "Fee basis"). Blank = use the sidebar choice.
ROW_BASIS_CHOICES = {
    "Request date": "request",
    "Paid date": "paid",
    "Loaded date": "loaded",
    "Disposal date": "disposal",
}
WEEKDAY_NAMES = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]  # index = date.weekday()

# What the "Return date is before Loaded date" setting can do.
RET_RULES = {
    "entered": "Allow: next cycle starts on the Return date (overlap days bill on both bins)",
    "loaded": "Allow: next cycle starts on the Loaded date (no overlap)",
    "block": "Don't allow (error)",
}
WAIVE_MODES = {
    "keep_free": "Waived days are not charged (free days stay calendar days)",
    "skip_days": "Waived days don't count toward the cycle (free days run on working days)",
}

# Every optional calculation setting lives here so it can be saved with a run and
# re-applied exactly. A missing key (old runs) falls back to the value shown.
DEFAULT_OPTS = {
    "dry_resets": False,       # a dry run closes the cycle and restarts the rental term
    "paid_governs": False,     # Paid date replaces Request date wherever Request would end a cycle
    "auto_bin": True,          # lock a work order to its bin when only one bin could have been on site
    "photo_on": False,         # use the Photo ID column (same ID = same bin)
    "photo_distinct": False,   # ...and different Photo IDs = different bins
    "row_basis_on": False,     # use the per-work-order Fee basis column
    "ret_rule": "entered",     # see RET_RULES
    "wk_on": False,            # waive weekend days...
    "weekend_days": [5, 6],    # ...these weekdays (0=Mon)
    "hol_on": False,           # waive the holidays listed below
    "holidays": [],            # ISO date strings
    "waive_mode": "keep_free", # see WAIVE_MODES
}

# Whole-page size. 0.70 = what the page looks like at 70% browser zoom.
# Change this one number to make everything larger or smaller.
UI_SCALE = 0.70

DATE_MIN = date(1990, 1, 1)
DATE_MAX = date(2100, 12, 31)

# Safety valve: scenarios grow as bins ** unlocked_events.
MAX_COMBOS = 250_000
MAX_TREE_LEAVES = 400

# Which event date ends an extension cycle.
#   request  = date the customer asked for service
#   loaded   = date the bin left the site (physically picked up)
#   disposal = date it was dumped (the date in the roll-off log)
BASIS_CHOICES = {
    "Request date": "request",
    "Loaded date": "loaded",
    "Disposal date": "disposal",
}
BASIS_LABEL = {v: k for k, v in BASIS_CHOICES.items()}
BASELINE_BASIS = "disposal"  # "Waived" = fee on this basis minus fee on the chosen basis
BASIS_FIELD = {"request": "request", "loaded": "loaded", "disposal": "disposal"}

DEFAULT_FILTERS = {"unused": False, "min_on": False, "min_n": 2, "bal_on": False, "bal_n": 1}

_STREAMLIT_VERSION = tuple(
    int(x) for x in re.findall(r"\d+", st.__version__)[:2]
) or (1, 0)
STRETCH = {"width": "stretch"} if _STREAMLIT_VERSION >= (1, 50) else {"use_container_width": True}
# "$3,000" needs the newer number-format presets; older Streamlit gets "$3000".
DOLLAR = "dollar" if _STREAMLIT_VERSION >= (1, 50) else "$%d"


class TooManyScenarios(ValueError):
    pass


# ──────────────────────────────────────────────
# Guam time (UTC+10, no daylight saving)
# ──────────────────────────────────────────────
# The server (e.g. Streamlit Cloud) runs on UTC, so date.today() is up to 10 hours
# behind Guam. Every "today" in this app comes from today_guam().
try:
    from zoneinfo import ZoneInfo
    GUAM_TZ = ZoneInfo("Pacific/Guam")
    datetime.now(GUAM_TZ)
except Exception:  # tzdata missing on the host: Guam has no DST, so a fixed offset is exact
    GUAM_TZ = timezone(timedelta(hours=10), "ChST")


def now_guam():
    return datetime.now(GUAM_TZ)


def today_guam():
    return now_guam().date()


# ──────────────────────────────────────────────
# Formatting helpers
# ──────────────────────────────────────────────
def fmt_fee(amount, ext_days=None, show_days=True):
    if show_days and ext_days is not None:
        return f"${amount:,.0f} ({ext_days}d)"
    return f"${amount:,.0f}"


def yymmdd(d):
    """YYMMDD display; accepts date or ISO string."""
    if d is None or d == "":
        return "—"
    if isinstance(d, str):
        try:
            d = date.fromisoformat(d[:10])
        except ValueError:
            return d
    return d.strftime("%y%m%d")


# ──────────────────────────────────────────────
# Robust date parsing for pasted / typed text
# ──────────────────────────────────────────────
# Excel copies the text it DISPLAYS ("1-Oct", "9/1", "9/1 (8/30)"), not the date
# underneath. The browser reads "9/1" as 2001-09-01, so cells are parsed here, where
# the year is inferred from context and the "(loaded)" part is kept.
_MONTHS = {m: i for i, m in enumerate(
    ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"], 1)}
_WEEKDAY = re.compile(r"^(mon|tue|wed|thu|fri|sat|sun)[a-z]*\.?,?\s+", re.I)
_TIME_TAIL = re.compile(r"[\sT]+\d{1,2}:\d{2}(:\d{2})?(\.\d+)?\s*([AaPp]\.?[Mm]\.?)?$")


def _closest_year(month, day, ref, not_after=None):
    """Pick the year that puts month/day closest to ref (and not after not_after)."""
    best = None
    for y in (ref.year - 1, ref.year, ref.year + 1):
        try:
            cand = date(y, month, day)
        except ValueError:
            continue
        if not_after is not None and cand > not_after:
            continue
        if best is None or abs((cand - ref).days) < abs((best - ref).days):
            best = cand
    if best is None:
        raise ValueError(f"'{month}/{day}' is not a valid date")
    return best


def _year(y):
    y = int(y)
    return y + 2000 if y < 100 else y


def _month_day(mon_txt, day, year_txt, ref, not_after):
    mon = _MONTHS.get(mon_txt[:3].lower())
    if mon is None:
        return None
    if year_txt:
        return date(_year(year_txt), mon, int(day))
    return _closest_year(mon, int(day), ref, not_after)


def _parse_date_core(text, ref=None, not_after=None):
    """Parse one date. Returns a date, or None for blank. Raises ValueError on junk.

    Accepted: 2026-09-01, 2026/9/1, 9/1/2026, 9/1/26, 260901, 20260901, 9/1, 1-Oct,
    1-Oct-26, Oct 1, Oct 1 2026, 1 October 2026, Thu 1-Oct, any of these with a
    time on the end, and Excel serial numbers.
    """
    if text is None:
        return None
    if isinstance(text, datetime):
        return text.date()
    if isinstance(text, date):
        return text
    s = str(text).strip().replace("\u00a0", " ")
    if s == "" or s.lower() in ("nan", "nat", "none", "—", "-"):
        return None
    s = _WEEKDAY.sub("", s)
    s = _TIME_TAIL.sub("", s).strip().rstrip(".,;")
    ref = ref or today_guam()
    out = None

    m = re.fullmatch(r"(\d{4})[-/.](\d{1,2})[-/.](\d{1,2})", s)
    if m:
        out = date(int(m[1]), int(m[2]), int(m[3]))
    if out is None:
        m = re.fullmatch(r"(\d{1,2})[-/.](\d{1,2})[-/.](\d{4}|\d{2})", s)
        if m:
            out = date(_year(m[3]), int(m[1]), int(m[2]))
    if out is None and re.fullmatch(r"\d{8}", s):
        out = date(int(s[:4]), int(s[4:6]), int(s[6:]))
    if out is None and re.fullmatch(r"\d{6}", s):  # YYMMDD (house format)
        out = date(2000 + int(s[:2]), int(s[2:4]), int(s[4:]))
    if out is None:
        m = re.fullmatch(r"(\d{1,2})[-/.](\d{1,2})", s)
        if m:
            out = _closest_year(int(m[1]), int(m[2]), ref, not_after)
    if out is None:  # 1-Oct, 1-Oct-26, 1 Oct 2026, 1 October, 01/Oct/2026
        m = re.fullmatch(r"(\d{1,2})(?:st|nd|rd|th)?[-\s/.]*([A-Za-z]{3,9})\.?(?:[-\s/.,]+(\d{4}|\d{2}))?", s)
        if m:
            out = _month_day(m[2], m[1], m[3], ref, not_after)
    if out is None:  # Oct 1, Oct-1, October 1st, Oct 1, 2026
        m = re.fullmatch(r"([A-Za-z]{3,9})\.?[-\s/.]*(\d{1,2})(?:st|nd|rd|th)?(?:[-\s/.,]+(\d{4}|\d{2}))?", s)
        if m:
            out = _month_day(m[1], m[2], m[3], ref, not_after)
    if out is None and re.fullmatch(r"\d{5}(\.\d+)?", s):  # Excel serial
        n = int(float(s))
        if 30000 <= n <= 80000:
            out = date(1899, 12, 30) + timedelta(days=n)
    if out is None:
        raise ValueError(f"Could not read '{text}' as a date")
    if not (DATE_MIN <= out <= DATE_MAX):
        raise ValueError(f"{out.isoformat()} is outside {DATE_MIN.year}-{DATE_MAX.year}")
    return out


def parse_date_text(text, ref=None, not_after=None):
    """Public wrapper: always raises ValueError with a readable message."""
    try:
        return _parse_date_core(text, ref, not_after)
    except ValueError as ex:
        msg = str(ex)
        if msg.startswith("Could not read") or "is outside" in msg:
            raise
        raise ValueError(f"Could not read '{text}' as a date") from ex


def parse_log_cell(text, ref=None):
    """Roll-off log style: '9/1' or '9/1 (8/30)' -> (disposal_date, loaded_date or None).

    The first date is the disposal (log) date; the parenthesised date is the date
    the bin was physically loaded / picked up.
    """
    if text is None:
        return None, None
    s = str(text).strip()
    m = re.fullmatch(r"(.*?)\s*[\(\[]\s*(.*?)\s*[\)\]]\s*", s)
    if m:
        disposal = parse_date_text(m[1], ref)
        if disposal is None:
            raise ValueError(f"Could not read '{s}' as a date")
        loaded = parse_date_text(m[2], disposal, not_after=disposal)
        return disposal, loaded
    return parse_date_text(s, ref), None


# ──────────────────────────────────────────────
# Core fee calculation
# ──────────────────────────────────────────────
# Event dict fields: label, idx, type, request_date, loaded_date, disposal_date, return_date
# (always all four dates; blanks are filled by effective_dates()).
#
# Timeline of one service:   request -> loaded (bin leaves site) -> disposal (dumped)
#                            -> return (bin back on site, next cycle starts)
def event_sort_key(ev):
    """Physical order: a bin can only be serviced once it is back on site, so order
    by the date it was loaded, not the date it was dumped. [#4]"""
    return (ev["loaded_date"], ev["disposal_date"], ev.get("idx", 0))


def event_end_date(ev, basis, override=True):
    """The date an extension cycle runs to for this work order.
    override=True lets a per-work-order Fee basis (ev["basis"]) replace the sidebar basis;
    the Waived baseline always passes override=False."""
    ov = ev.get("basis") if override else None
    if ov:
        basis = ov
    if basis == "request":
        # gov_date = the Paid date when "Paid date governs" is on and a Paid date was entered.
        # A per-work-order "Request date" choice is literal, so it ignores gov_date.
        return (None if ov else ev.get("gov_date")) or ev["request_date"]
    if basis == "paid":
        return ev.get("paid_date") or ev["request_date"]
    if basis == "loaded":
        return ev["loaded_date"]
    return ev["disposal_date"]


# ---- weekend / holiday waivers -------------------------------------------------
def normalize_opts(o):
    out = {k: (list(v) if isinstance(v, list) else v) for k, v in DEFAULT_OPTS.items()}
    if o:
        for k in DEFAULT_OPTS:
            if k in o and o[k] is not None:
                out[k] = o[k]
    if out["ret_rule"] not in RET_RULES:
        out["ret_rule"] = DEFAULT_OPTS["ret_rule"]
    if out["waive_mode"] not in WAIVE_MODES:
        out["waive_mode"] = DEFAULT_OPTS["waive_mode"]
    out["weekend_days"] = sorted({int(x) for x in out["weekend_days"] if str(x).isdigit() and 0 <= int(x) <= 6})
    out["holidays"] = sorted({str(x)[:10] for x in out["holidays"] if x})
    for k in ("dry_resets", "paid_governs", "auto_bin", "photo_on", "photo_distinct",
              "row_basis_on", "wk_on", "hol_on"):
        out[k] = bool(out[k])
    return out


def make_cal(opts):
    """None when no waiver is active, else the rule set used by cycle_math()."""
    o = normalize_opts(opts)
    wk = set(o["weekend_days"]) if o["wk_on"] else set()
    hol = set()
    if o["hol_on"]:
        for s in o["holidays"]:
            try:
                hol.add(date.fromisoformat(s))
            except ValueError:
                pass
    if not wk and not hol:
        return None
    return {"wk": frozenset(wk), "hol": frozenset(hol), "mode": o["waive_mode"]}


def _waived_in(a, b, cal):
    """Number of waived calendar days in [a, b] (inclusive)."""
    if b < a:
        return 0
    n = (b - a).days + 1
    cnt = 0
    for wd in cal["wk"]:
        first = (wd - a.weekday()) % 7
        if first < n:
            cnt += (n - 1 - first) // 7 + 1
    for h in cal["hol"]:
        if a <= h <= b and h.weekday() not in cal["wk"]:
            cnt += 1
    return cnt


def cycle_math(start, end, free_days, cal=None):
    """-> (cycle_days, billed_extension_days, extension_days_before_waivers).
    cal=None reproduces the original arithmetic exactly."""
    cycle_days = max(0, (end - start).days + 1)
    raw = max(0, cycle_days - free_days)
    if cal is None or cycle_days == 0:
        return cycle_days, raw, raw
    if cal["mode"] == "skip_days":
        counted = cycle_days - _waived_in(start, end, cal)
        return cycle_days, max(0, counted - free_days), raw
    if raw == 0:
        return cycle_days, 0, 0
    ext_start = start + timedelta(days=free_days)
    return cycle_days, raw - _waived_in(ext_start, end, cal), raw


def fee_for_bin(bin_events, bin_delivery_date, free_days, rate_per_day,
                end_basis=BASELINE_BASIS, cal=None):
    """Fee for one bin. Each cycle runs from cycle_start (delivery, or the previous
    return date) to the event's end date for the chosen basis. Days between the end
    date and the next return date are off-site / not billed. [#2][#3][#10]
    """
    if not bin_events:
        return 0, []
    fee = 0
    breakdown = []
    cycle_start = bin_delivery_date
    for ev in bin_events:
        end = event_end_date(ev, end_basis)
        cycle_days, ext_days, raw_ext = cycle_math(cycle_start, end, free_days, cal)
        cycle_fee = ext_days * rate_per_day
        base_end = event_end_date(ev, BASELINE_BASIS, override=False)
        _, base_ext, _ = cycle_math(cycle_start, base_end, free_days, cal)
        base_days = max(0, (base_end - cycle_start).days + 1)
        base_fee = base_ext * rate_per_day
        fee += cycle_fee
        breakdown.append({
            "idx": ev.get("idx"),
            "label": ev.get("label"),
            "cycle_start": cycle_start,
            "end_date": end,
            "disposal_date": ev["disposal_date"],
            "cycle_days": cycle_days,
            "ext_days": ext_days,
            "fee": cycle_fee,
            "base_days": base_days,
            "base_ext_days": base_ext,
            "base_fee": base_fee,
            "waived_days": base_ext - ext_days,
            "waived_fee": base_fee - cycle_fee,
            "cal_days": raw_ext - ext_days,           # days a weekend/holiday waiver removed
            "cal_fee": (raw_ext - ext_days) * rate_per_day,
        })
        if ev["type"] == REPO:
            break
        cycle_start = ev["return_date"]
    return fee, breakdown


def _events_by_bin(events, assignment):
    bins = {}
    for i, ev in enumerate(events):
        bins.setdefault(assignment[i], []).append(ev)
    for b in bins:
        bins[b] = sorted(bins[b], key=event_sort_key)
    return bins


def is_valid_assignment(events, assignment, delivery_dates, distinct_links=False, exempt=None):
    """exempt = event idx values the user locked to a bin by hand: the delivery-date
    check is skipped for them (an explicit exception); every other rule still applies."""
    exempt = exempt or ()
    bins = _events_by_bin(events, assignment)
    for b, bin_events in bins.items():
        repo_idx = [i for i, e in enumerate(bin_events) if e["type"] == REPO]
        if len(repo_idx) > 1:
            return False
        if repo_idx and repo_idx[0] != len(bin_events) - 1:
            return False
        bin_start = delivery_dates.get(b)
        if bin_start is None:
            return False
        prev = None
        for e in bin_events:
            # The bin was physically on site until it was loaded.
            if e["loaded_date"] < bin_start and e.get("idx") not in exempt:
                return False
            # [#4] A bin cannot be loaded again before it is back on site.
            if prev is not None and e["loaded_date"] < prev["return_date"]:
                return False
            prev = e
    # Photo IDs: the same ID is the same bin; optionally different IDs are different bins.
    by_link = {}
    for i, e in enumerate(events):
        lk = e.get("link")
        if lk:
            by_link.setdefault(lk, set()).add(assignment[i])
    if any(len(s) > 1 for s in by_link.values()):
        return False
    if distinct_links:
        used = [next(iter(s)) for s in by_link.values()]
        if len(set(used)) != len(used):
            return False
    return True


# ---- Photo IDs, auto-assignment, dry runs: everything that prepares events for the maths ----
def _norm_link(s):
    s = re.sub(r"\s+", " ", str(s or "").strip()).casefold()
    return s


def propagate_links(events, fixed):
    """Work orders sharing a Photo ID are one bin: if any is locked, lock them all.
    -> (fixed, conflicts) where conflicts = [(link, [bins...])] for IDs locked to two bins."""
    fixed = dict(fixed)
    groups, conflicts = {}, []
    for i, e in enumerate(events):
        lk = e.get("link")
        if lk:
            groups.setdefault(lk, []).append(i)
    for lk, idxs in groups.items():
        locked = {fixed[i] for i in idxs if i in fixed}
        if len(locked) > 1:
            conflicts.append((lk, sorted(locked)))
        elif len(locked) == 1:
            b = next(iter(locked))
            for i in idxs:
                fixed[i] = b
    return fixed, conflicts


def free_decision_groups(events, fixed):
    """The unlocked events, grouped so that work orders sharing a Photo ID form ONE
    decision (which bin?). Every other work order is its own group."""
    seen, groups = {}, []
    for i, e in enumerate(events):
        if i in fixed:
            continue
        lk = e.get("link")
        if lk:
            if lk in seen:
                seen[lk].append(i)
                continue
            seen[lk] = [i]
            groups.append(seen[lk])
        else:
            groups.append([i])
    return [tuple(g) for g in groups]


def possible_bins_map(events, fixed, delivery_dates, num_bins):
    """idx -> bins that CAN host the event. Only conditions that every valid scenario must
    satisfy are used (delivered by the loaded date; pairwise order/return/repo rules against
    work orders already locked to that bin), so a bin dropped here is truly impossible."""
    out = {}
    for i, e in enumerate(events):
        ok = []                                   # computed for locked events too (ignoring their own lock)
        for b in range(1, int(num_bins) + 1):
            ds = delivery_dates.get(b)
            if ds is None or e["loaded_date"] < ds:
                continue
            bad = False
            for j, fb in fixed.items():
                if j == i or fb != b:
                    continue
                o = events[j]
                a, c = (o, e) if event_sort_key(o) <= event_sort_key(e) else (e, o)
                if a["type"] == REPO or c["loaded_date"] < a["return_date"]:
                    bad = True
                    break
            if not bad:
                ok.append(b)
        out[i] = ok
    return out


def prepare_calc(events, fixed, delivery_dates, num_bins, opts=None):
    """Turn the events typed into the table into the events the maths runs on.
    Applies, in order: dry-run handling, Paid-date / per-work-order basis, the Return-before-
    Loaded rule, Photo IDs, then auto-assigns work orders that only one bin could have served.
    Nothing here changes the typed rows or what is saved as the run's inputs."""
    o = normalize_opts(opts)
    keep, remap, inert = [], {}, []
    for i, e in enumerate(events):
        src = e.get("idx", i)
        if e["type"] == DRY_RUN and not o["dry_resets"]:
            inert.append(e)          # a dry run that does not reset the term never touches the fees
            continue
        remap[src] = len(keep)
        keep.append(e)
    out = []
    for new_i, e in enumerate(keep):
        c = dict(e, idx=new_i, src=e.get("idx", new_i))
        pd_ = e.get("paid_date")
        c["gov_date"] = pd_ if (o["paid_governs"] and pd_) else None
        c["basis"] = e.get("basis") if o["row_basis_on"] else ""
        c["link"] = _norm_link(e.get("link")) if o["photo_on"] else ""
        c["link_text"] = (e.get("link") or "") if o["photo_on"] else ""
        if o["ret_rule"] == "loaded" and c["type"] != REPO and c["return_date"] < c["loaded_date"]:
            c["return_date"] = c["loaded_date"]
        out.append(c)
    user_fixed = {remap[i]: b for i, b in fixed.items() if i in remap}
    exempt = set(user_fixed)
    new_fixed, conflicts = propagate_links(out, user_fixed)
    auto = set()
    if o["auto_bin"]:
        for _ in range(len(out) + 1):
            pm = possible_bins_map(out, new_fixed, delivery_dates, num_bins)
            add = {i: bl[0] for i, bl in pm.items() if i not in new_fixed and len(bl) == 1}
            if not add:
                break
            # keep Photo-ID groups together
            add, _c = propagate_links(out, {**new_fixed, **add})
            auto |= {i for i in add if i not in new_fixed}
            new_fixed = add
    return {"events": out, "fixed": new_fixed, "exempt": exempt, "conflicts": conflicts,
            "inert": inert, "auto": auto, "opts": o, "cal": make_cal(o)}


def deduplicate_scenarios(results):
    seen = {}
    for r in results:
        bin_sets = []
        for b in sorted(r["assignment"].keys()):
            event_tuple = tuple(sorted(r["assignment"][b]))
            bin_sets.append(event_tuple)
        canonical_events = tuple(sorted(bin_sets))
        fee_tuple = tuple(sorted(r["fees"].values()))
        canonical = (canonical_events, fee_tuple)
        if canonical not in seen:
            seen[canonical] = r
    deduped = sorted(seen.values(), key=lambda x: x["total"])
    removed = len(results) - len(deduped)
    return deduped, removed



# ──────────────────────────────────────────────
# Scenario generation and filters
# ──────────────────────────────────────────────
def calculate_allocations(delivery_dates, free_days, rate_per_day, events,
                          fixed_assignments=None, num_bins=2,
                          end_basis=BASELINE_BASIS, cal=None, exempt=None,
                          distinct_links=False):
    """Every valid way to assign the events to bins, cheapest first.

    Nothing is filtered here: filters are applied afterwards by filter_scenarios(),
    so toggling a filter never needs a recalculation and can report what it hid.
    Events that share a Photo ID are decided together (one choice of bin for the group).
    """
    fixed_assignments = fixed_assignments or {}
    events = [dict(e, idx=i) for i, e in enumerate(events)]
    fixed_assignments, conflicts = propagate_links(events, fixed_assignments)
    if conflicts:
        return []
    groups = free_decision_groups(events, fixed_assignments)
    combos = int(num_bins) ** len(groups)
    if combos > MAX_COMBOS:
        raise TooManyScenarios(
            f"{combos:,} bin assignments to test ({num_bins} bins ^ "
            f"{len(groups)} unlocked decisions) is more than the {MAX_COMBOS:,} limit. "
            "Lock more events to a known bin, link work orders with a Photo ID, "
            "or reduce the number of bins."
        )
    results = []
    for combo in product(range(1, num_bins + 1), repeat=len(groups)):
        assignment = dict(fixed_assignments)
        for grp, bin_num in zip(groups, combo):
            for idx in grp:
                assignment[idx] = bin_num
        if not is_valid_assignment(events, assignment, delivery_dates, distinct_links, exempt):
            continue
        bins = _events_by_bin(events, assignment)
        for b in range(1, num_bins + 1):
            bins.setdefault(b, [])
        fees = {}
        breakdowns = {}
        for b in bins:
            fees[b], breakdowns[b] = fee_for_bin(
                bins[b], delivery_dates.get(b), free_days, rate_per_day, end_basis, cal
            )
        total = sum(fees.values())
        total_ext_days = sum(c["ext_days"] for bd in breakdowns.values() for c in bd)
        waived = sum(c["waived_fee"] for bd in breakdowns.values() for c in bd)
        waived_days = sum(c["waived_days"] for bd in breakdowns.values() for c in bd)
        cal_waived = sum(c["cal_fee"] for bd in breakdowns.values() for c in bd)
        cal_waived_days = sum(c["cal_days"] for bd in breakdowns.values() for c in bd)
        results.append({
            "combo": combo,
            "assignment": {b: [e["label"] for e in bins[b]] for b in bins},
            "counts": {b: len(bins[b]) for b in bins},
            "fees": fees,
            "breakdowns": breakdowns,
            "total": total,
            "total_ext_days": total_ext_days,
            "waived": waived,
            "waived_days": waived_days,
            "cal_waived": cal_waived,
            "cal_waived_days": cal_waived_days,
        })
    results.sort(key=lambda r: (r["total"], r["total_ext_days"], r["combo"]))
    return results


def run_engine(delivery_dates, free_days, rate_per_day, events, fixed, num_bins,
               end_basis, opts=None):
    """Prepare the typed events (prepare_calc) and calculate. -> (all_results, prep).
    The ONE place the maths is started from, so the Calculator, History, re-runs and
    reloads can never disagree about how the options are applied."""
    prep = prepare_calc(events, fixed, delivery_dates, num_bins, opts)
    results = calculate_allocations(
        delivery_dates, free_days, rate_per_day, prep["events"], prep["fixed"], num_bins,
        end_basis=end_basis, cal=prep["cal"], exempt=prep["exempt"],
        distinct_links=prep["opts"]["photo_distinct"] and prep["opts"]["photo_on"],
    )
    return results, prep


def normalize_filters(f):
    out = dict(DEFAULT_FILTERS)
    if f:
        out.update({k: f[k] for k in DEFAULT_FILTERS if k in f})
    out["min_n"] = max(1, int(out["min_n"]))
    out["bal_n"] = max(0, int(out["bal_n"]))
    return out


def scenario_passes(r, f, num_bins):
    counts = [r["counts"].get(b, 0) for b in range(1, int(num_bins) + 1)]
    if f["unused"] and min(counts) == 0:
        return False
    if f["min_on"] and min(counts) < f["min_n"]:
        return False
    if f["bal_on"] and (max(counts) - min(counts)) > f["bal_n"]:
        return False
    return True


def filter_scenarios(results, filters, num_bins):
    """-> (kept, number_hidden)."""
    f = normalize_filters(filters)
    if not (f["unused"] or f["min_on"] or f["bal_on"]):
        return results, 0
    kept = [r for r in results if scenario_passes(r, f, num_bins)]
    return kept, len(results) - len(kept)


def describe_filters(filters):
    f = normalize_filters(filters)
    parts = []
    if f["unused"]:
        parts.append("a bin has no work orders")
    if f["min_on"]:
        parts.append(f"a bin has fewer than {f['min_n']} work orders")
    if f["bal_on"]:
        parts.append(f"bins differ by more than {f['bal_n']} work order(s)")
    return "; ".join(parts)


# ──────────────────────────────────────────────
# Decision tree (days-only) and per-bin timeline
# ──────────────────────────────────────────────
def compute_edge_ext_days(events, partial_assignment, target_idx, bin_num,
                          delivery_dates, free_days, end_basis=BASELINE_BASIS, cal=None):
    target = events[target_idx]
    tkey = event_sort_key(target)
    bin_events = [
        ev for i, ev in enumerate(events)
        if i in partial_assignment and partial_assignment[i] == bin_num
        and event_sort_key(ev) <= tkey
    ]
    bin_events.sort(key=event_sort_key)
    cycle_start = delivery_dates.get(bin_num)
    if cycle_start is None:
        return 0
    for ev in bin_events:
        end = event_end_date(ev, end_basis)
        if ev["idx"] == target_idx:
            return cycle_math(cycle_start, end, free_days, cal)[1]
        if ev["type"] == REPO:
            return 0
        cycle_start = ev["return_date"]
    return 0


def build_decision_tree_dot(events, fixed_assignments, num_bins, delivery_dates,
                            free_days, rate_per_day, highlight_combo=None,
                            hide_invalid=False, end_basis=BASELINE_BASIS,
                            cal=None, exempt=None, distinct_links=False):
    # One decision per group: work orders sharing a Photo ID are drawn as a single step.
    groups = free_decision_groups(events, fixed_assignments)
    if not groups:
        return None

    def group_label(g):
        return " + ".join(events[i]["label"] for i in g)

    lines = []
    lines.append("digraph DT {")
    lines.append("  rankdir=TB;")
    lines.append('  node [shape=box, style="rounded,filled", fillcolor=white, fontname="Arial"];')
    lines.append('  edge [fontname="Arial", fontsize=10];')

    start_parts = []
    for b in sorted(delivery_dates.keys()):
        d = delivery_dates[b]
        start_parts.append(f"Bin {b} delivered {d}")
    if fixed_assignments:
        for idx, b in fixed_assignments.items():
            lbl = events[idx]["label"]
            start_parts.append(f"{lbl} locked to Bin {b}")
    start_text = "\\n".join(start_parts) if start_parts else "no fixed events"
    first_service_label = group_label(groups[0])
    root_label = (
        f"Start\\n{start_text}\\n\\n"
        f"First decision: which bin handled {first_service_label}?"
    )
    lines.append(f'  root [label="{root_label}", shape=ellipse, fillcolor="#cfe2ff"];')

    node_counter = [0]

    def new_id():
        node_counter[0] += 1
        return f"n{node_counter[0]}"

    frontier = {(): "root"}
    for depth, grp in enumerate(groups):
        ev_label = group_label(grp)
        is_last = (depth == len(groups) - 1)
        next_frontier = {}
        for partial, parent_id in frontier.items():
            for bin_num in range(1, num_bins + 1):
                new_partial = partial + (bin_num,)
                edge_assignment = dict(fixed_assignments)
                for gi, bn in zip(groups[:depth + 1], new_partial):
                    for fi in gi:
                        edge_assignment[fi] = bn
                edge_ext = sum(
                    compute_edge_ext_days(events, edge_assignment, idx, bin_num, delivery_dates,
                                          free_days, end_basis, cal)
                    for idx in grp
                )
                on_highlight_path = False
                if highlight_combo is not None and len(highlight_combo) >= depth + 1:
                    on_highlight_path = all(
                        new_partial[i] == highlight_combo[i] for i in range(depth + 1)
                    )
                skip_branch = False
                node_lines = []
                nid = None
                if is_last:
                    full_assignment = dict(fixed_assignments)
                    for gi, bn in zip(groups, new_partial):
                        for fi in gi:
                            full_assignment[fi] = bn
                    if is_valid_assignment(events, full_assignment, delivery_dates,
                                           distinct_links, exempt):
                        bins_map = _events_by_bin(events, full_assignment)
                        for b in range(1, num_bins + 1):
                            bins_map.setdefault(b, [])
                        per_bin_ext = {}
                        total_ext = 0
                        for b in bins_map:
                            _, bd = fee_for_bin(
                                bins_map[b], delivery_dates.get(b), free_days,
                                rate_per_day, end_basis, cal
                            )
                            ext_sum = sum(c["ext_days"] for c in bd)
                            per_bin_ext[b] = ext_sum
                            total_ext += ext_sum
                        leaf_lines = [f"Total: {total_ext}d"]
                        for b in sorted(bins_map.keys()):
                            leaf_lines.append(f"B{b}: {per_bin_ext[b]}d")
                        leaf_label = "\\n".join(leaf_lines)
                        if on_highlight_path:
                            fill = "#28a745"
                            node_extras = ', fontcolor="white", penwidth=3'
                        else:
                            fill = "#d1e7dd"
                            node_extras = ""
                        nid = new_id()
                        node_lines.append(f'  {nid} [label="{leaf_label}", fillcolor="{fill}"{node_extras}];')
                    else:
                        if hide_invalid:
                            skip_branch = True
                        else:
                            nid = new_id()
                            node_lines.append(f'  {nid} [label="(invalid)", fillcolor="#f8d7da"];')
                else:
                    next_lbl = group_label(groups[depth + 1])
                    node_label = f"Which bin handled\\n{next_lbl}?"
                    nid = new_id()
                    if on_highlight_path:
                        node_lines.append(f'  {nid} [label="{node_label}", fillcolor="#fff3cd", penwidth=2];')
                    else:
                        node_lines.append(f'  {nid} [label="{node_label}"];')
                if skip_branch:
                    continue
                lines.extend(node_lines)
                if edge_ext > 0:
                    edge_label = f"{ev_label} -> Bin {bin_num}\\n+{edge_ext}d"
                else:
                    edge_label = f"{ev_label} -> Bin {bin_num}"
                if on_highlight_path:
                    edge_extras = ', color="#28a745", penwidth=3, fontcolor="#28a745"'
                else:
                    edge_extras = ""
                lines.append(f'  {parent_id} -> {nid} [label="  {edge_label}  "{edge_extras}];')
                next_frontier[new_partial] = nid
        frontier = next_frontier
    lines.append("}")
    return "\n".join(lines)


def build_timeline_view(scenario, num_bins, delivery_dates, free_days):
    lines = []
    lines.append("digraph Timeline {")
    lines.append("  rankdir=LR;")
    lines.append('  node [shape=box, style="rounded,filled", fontname="Arial", fontsize=11];')
    lines.append('  edge [fontname="Arial", fontsize=9];')
    for b in range(1, int(num_bins) + 1):
        bin_breakdown = scenario["breakdowns"][b]
        bin_total = scenario["fees"][b]
        bin_ext = sum(c["ext_days"] for c in bin_breakdown)
        bin_delivery = delivery_dates.get(b)
        lines.append(f'  subgraph cluster_bin{b} {{')
        lines.append(f'    label="Bin {b}: ${bin_total:,.0f} ({bin_ext}d ext)";')
        lines.append('    style="rounded,filled";')
        lines.append('    fillcolor="#f8f9fa";')
        lines.append('    fontname="Arial";')
        lines.append('    fontsize=12;')
        del_id = f"d{b}"
        lines.append(f'    {del_id} [label="Delivered\\n{bin_delivery}", fillcolor="#cfe2ff", shape=ellipse];')
        prev_id = del_id
        if not bin_breakdown:
            empty_id = f"e{b}"
            lines.append(f'    {empty_id} [label="(no services)", fillcolor="white", style="dashed,filled"];')
            lines.append(f'    {prev_id} -> {empty_id} [style=invis];')
        else:
            for i, c in enumerate(bin_breakdown):
                evt_id = f"b{b}c{i}"
                cycle_days = c["cycle_days"]
                ext_days = c["ext_days"]
                fee = c["fee"]
                if ext_days > 0:
                    fill = "#fff3cd"
                    extras = f"\\n+{ext_days}d ext = ${fee:,.0f}"
                else:
                    fill = "#d1e7dd"
                    extras = ""
                waived = f"\\n(waived {c['waived_days']}d)" if c["waived_days"] > 0 else ""
                evt_label = f"Service\\n{c['end_date']}\\n{cycle_days}d cycle{extras}{waived}"
                lines.append(f'    {evt_id} [label="{evt_label}", fillcolor="{fill}"];')
                edge_label = f"{cycle_days}d"
                edge_extras = ', color="#dc3545", penwidth=2' if ext_days > 0 else ""
                lines.append(f'    {prev_id} -> {evt_id} [label="{edge_label}"{edge_extras}];')
                prev_id = evt_id
        lines.append("  }")
    lines.append("}")
    return "\n".join(lines)



# ──────────────────────────────────────────────
# History storage
# ──────────────────────────────────────────────
# Each calculation that has a customer name is saved as one "run".
# (The JSON key is still called "version" so existing history.json files keep working.)
def make_version_name(run_date, range_dates, num_bins):
    """'Run 261015 · Range 260901–260930 · 2 bins'.
    Run = the day (Guam) the calculation was run. Range = first–last event date."""
    ds = [d for d in range_dates if isinstance(d, date)]
    if ds:
        rng = yymmdd(min(ds)) if min(ds) == max(ds) else f"{yymmdd(min(ds))}–{yymmdd(max(ds))}"
    else:
        rng = "no dates"
    return f"Run {yymmdd(run_date)} · Range {rng} · {int(num_bins)} bin{'s' if int(num_bins) != 1 else ''}"


def event_range_dates(events, basis):
    key = {"request": "request_date", "loaded": "loaded_date"}.get(basis, "disposal_date")
    return [e[key] for e in events]


def _record_disposal_dates(rec):
    out = []
    for e in rec.get("events", []):
        raw = e.get("disposal_date") or e.get("haul_date")
        try:
            out.append(date.fromisoformat(raw))
        except (TypeError, ValueError):
            pass
    return out


def _migrate_history(entries):
    """Give old records an id and a run name (in memory; saved on next write)."""
    changed = False
    used = {r.get("id") for r in entries if r.get("id")}
    for rec in entries:
        if not rec.get("id"):
            # Deterministic (content hash), so the id is the same on every reload
            # even before the migrated file has been written back.
            base = "h" + hashlib.md5(
                json.dumps(rec, sort_keys=True, default=str).encode()).hexdigest()[:11]
            rid, n = base, 1
            while rid in used:
                n += 1
                rid = f"{base}-{n}"
            rec["id"] = rid
            used.add(rid)
            changed = True
        if not rec.get("version"):
            try:
                run = date.fromisoformat(str(rec.get("logged_at", ""))[:10])
            except ValueError:
                run = today_guam()
            rec["version"] = make_version_name(
                run, _record_disposal_dates(rec),
                rec.get("num_bins", len(rec.get("delivery_dates", {})) or 1),
            )
            changed = True
    return entries, changed


@st.cache_resource
def _history_lock():
    return threading.RLock()  # one per server process: serialises read-modify-write


def _read_history_file(path):
    with open(path, "r") as f:
        data = json.load(f)
    if not isinstance(data, list):
        raise ValueError(f"{path} is not a list")
    return data


def load_history():
    data = None
    if os.path.exists(HISTORY_FILE):
        try:
            data = _read_history_file(HISTORY_FILE)
        except Exception:
            # Keep the bad file under its own name so it is never silently overwritten.
            try:
                os.replace(HISTORY_FILE, f"{HISTORY_FILE}.corrupt-{now_guam():%y%m%d-%H%M%S}")
            except OSError:
                pass
    if data is None and os.path.exists(HISTORY_PREV):
        try:
            data = _read_history_file(HISTORY_PREV)  # fall back to the last good copy
        except Exception:
            data = None
    if data is None:
        return []
    data, _ = _migrate_history(data)
    return data


def save_history(entries):
    """Write to a temp file, force it to disk, keep the previous good file, then swap.
    A crash or power cut leaves either the old file or the new one, never half of one."""
    with _history_lock():
        tmp = HISTORY_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(entries, f, indent=2, default=str)
            f.flush()
            os.fsync(f.fileno())
        if os.path.exists(HISTORY_FILE):
            try:
                shutil.copyfile(HISTORY_FILE, HISTORY_PREV)
            except OSError:
                pass
        os.replace(tmp, HISTORY_FILE)  # atomic
        try:  # make the rename itself durable
            dfd = os.open(os.path.dirname(os.path.abspath(HISTORY_FILE)), os.O_RDONLY)
            try:
                os.fsync(dfd)
            finally:
                os.close(dfd)
        except (OSError, AttributeError):
            pass


def _history_sig():
    try:
        st_ = os.stat(HISTORY_FILE)
        return (st_.st_mtime_ns, st_.st_size)
    except OSError:
        return None


def unique_version_name(history, customer, name):
    taken = {h.get("version") for h in history if h.get("customer") == customer}
    if name not in taken:
        return name
    n = 2
    while f"{name} ({n})" in taken:
        n += 1
    return f"{name} ({n})"


def add_to_history(customer, version, delivery_dates, events, results,
                   free_days, rate, num_bins, fixed_assignments,
                   end_basis=BASELINE_BASIS, filters=None, blanks=None, opts=None):
    with _history_lock():
        return _add_to_history_locked(customer, version, delivery_dates, events, results,
                                      free_days, rate, num_bins, fixed_assignments,
                                      end_basis, filters, blanks, opts)


def _add_to_history_locked(customer, version, delivery_dates, events, results,
                           free_days, rate, num_bins, fixed_assignments,
                           end_basis, filters, blanks, opts=None):
    history = load_history()
    min_ext = results[0].get("total_ext_days", 0) if results else 0
    max_ext = results[-1].get("total_ext_days", 0) if results else 0
    fixed_serialized = {str(k): int(v) for k, v in fixed_assignments.items()}
    now = now_guam()
    version = unique_version_name(
        history, customer,
        version or make_version_name(now.date(), event_range_dates(events, end_basis), num_bins),
    )
    blanks = blanks or {}
    rec = {
        "id": uuid.uuid4().hex[:12],
        "customer": customer,
        "version": version,
        "delivery_dates": {str(b): str(d) for b, d in delivery_dates.items()},
        "free_days": int(free_days),
        "rate": float(rate),
        "num_bins": int(num_bins),
        "end_basis": end_basis,
        "filters": normalize_filters(filters),
        "options": normalize_opts(opts),
        "fixed_assignments": fixed_serialized,
        "events": [
            {
                "label": e["label"],
                "disposal_date": str(e["disposal_date"]),
                "request_date": str(e["request_date"]),
                "loaded_date": str(e["loaded_date"]),
                "return_date": str(e["return_date"]),
                "type": e["type"],
                "paid_date": str(e["paid_date"]) if e.get("paid_date") else "",
                "waste": e.get("waste", ""),
                "remarks": e.get("remarks", ""),
                "link": e.get("link", ""),
                "basis": e.get("basis", ""),
                "blank": list(blanks.get(i, [])),  # cells the user left empty
            } for i, e in enumerate(events)
        ],
        "min_total": results[0]["total"] if results else 0,
        "max_total": results[-1]["total"] if results else 0,
        "min_ext_days": min_ext,
        "max_ext_days": max_ext,
        "scenario_count": len(results),
        "logged_at": str(now.date()),                    # Guam date
        "logged_ts": now.isoformat(timespec="seconds"),  # Guam time stamp
    }
    history.append(rec)
    save_history(history)
    return rec


def delete_history_records(ids):
    """Delete the runs with these ids. Returns how many were removed."""
    ids = set(ids or [])
    with _history_lock():
        history = load_history()
        keep = [h for h in history if h.get("id") not in ids]
        save_history(keep)
    return len(history) - len(keep)


def parse_record_to_calc_inputs(rec):
    """Convert a stored history record back into dict of calc inputs.
    Older records (no request/loaded dates) fall back to the disposal date."""
    events, blanks = [], {}
    for i, e in enumerate(rec["events"]):
        disposal = date.fromisoformat(e.get("disposal_date") or e["haul_date"])
        loaded = date.fromisoformat(e["loaded_date"]) if e.get("loaded_date") else disposal
        request = date.fromisoformat(e["request_date"]) if e.get("request_date") else loaded
        return_d = date.fromisoformat(e["return_date"]) if e.get("return_date") else disposal
        events.append({
            "label": e["label"],
            "idx": i,
            "disposal_date": disposal,
            "loaded_date": loaded,
            "request_date": request,
            "return_date": return_d,
            "type": e["type"],
            "paid_date": date.fromisoformat(e["paid_date"]) if e.get("paid_date") else None,
            "waste": e.get("waste", "") or "",
            "remarks": e.get("remarks", "") or "",
            "link": e.get("link", "") or "",
            "basis": e.get("basis", "") or "",
        })
        blanks[i] = list(e.get("blank", []))
    if "delivery_dates" in rec:
        delivery_dates = {
            int(k): date.fromisoformat(v)
            for k, v in rec["delivery_dates"].items()
        }
    else:
        single = date.fromisoformat(rec.get("delivery_date", str(today_guam())))
        delivery_dates = {1: single, 2: single}
    free_days = rec.get("free_days", 10)
    rate = rec.get("rate", 50.0)
    num_bins = rec.get("num_bins", len(delivery_dates))
    fixed_raw = rec.get("fixed_assignments", {})
    fixed = {int(k): int(v) for k, v in fixed_raw.items()} if fixed_raw else {}
    filters = normalize_filters(rec.get("filters") or {"unused": rec.get("require_all_bins", False)})
    return {
        "events": events,
        "blanks": blanks,
        "delivery_dates": delivery_dates,
        "free_days": free_days,
        "rate": rate,
        "num_bins": num_bins,
        "fixed_assignments": fixed,
        # Legacy records were calculated on the single (disposal/haul) date.
        "end_basis": rec.get("end_basis", BASELINE_BASIS),
        "filters": filters,
        "opts": normalize_opts(rec.get("options")),  # old runs: defaults = old behaviour
    }


def _run_parsed(parsed, free_days=None, rate=None):
    """All valid scenarios for a parsed record, filtered the way it was saved."""
    results, _prep = run_engine(
        parsed["delivery_dates"],
        parsed["free_days"] if free_days is None else free_days,
        parsed["rate"] if rate is None else rate,
        parsed["events"],
        parsed["fixed_assignments"],
        parsed["num_bins"],
        parsed["end_basis"],
        parsed["opts"],
    )
    kept, _ = filter_scenarios(results, parsed["filters"], parsed["num_bins"])
    return kept


@st.cache_data(show_spinner=False, max_entries=64)
def _cached_recompute(rec_json):
    """Cached so the History page does not recompute on every unrelated rerun."""
    rec = json.loads(rec_json)
    parsed = parse_record_to_calc_inputs(rec)
    return _run_parsed(parsed), parsed


def recompute_from_record(rec):
    """Recompute allocation results from a stored history record."""
    return _cached_recompute(json.dumps(rec, sort_keys=True, default=str))


# ──────────────────────────────────────────────
# Single source of truth (SSOT) for the events
# ──────────────────────────────────────────────
# st.session_state["rows"] is the ONE copy of the events. The table and the pickers
# are only views of it: each view edits SSOT through a callback, and a view that did
# not make the last change re-seeds itself from SSOT the next time it is shown.
#
# Date cells (Request / Loaded / Disposal / Return) may be blank. What a blank means:
#   * Only the date for the chosen billing basis is required to calculate.
#   * When the FIRST date is entered in an empty row, the other blank date cells in
#     that row are pre-filled from it (so a plain log date just works). Those cells
#     are remembered as "auto" (r["auto"]).
#   * An auto cell FOLLOWS the dates you typed: change one and the auto cells are
#     re-derived (refresh_auto). The moment you type into a cell yourself it becomes
#     yours and is never overwritten by editing a different cell.
#   * Clear a cell to leave it blank; blanks are treated as "same as the nearest
#     filled date" (see effective_dates).
#   * Return defaults to the LOADED date (not disposal): when a bin is swapped (empty
#     dropped, full one loaded, dumped on another day) the customer has a bin on site
#     from the loaded date. Type a later Return date if the bin was really off site.
S = st.session_state

TABLE_MODE = "📋 Table (paste from Excel)"
PICKER_MODE = "🎯 Individual pickers"
NAV_CALC = "Calculator"
NAV_HIST = "History"

COL_NO = "No"
COL_TYPE = "Type"
COL_REQUEST = "Request date"
COL_LOADED = "Loaded date"
COL_DISPOSAL = "Disposal date"
COL_RETURN = "Return date"
COL_BIN = "Bin (if known)"
COL_PAID = "Paid date"
COL_POSS = "Possible bins"
COL_PHOTO = "Photo ID"
COL_BASIS = "Fee basis"
COL_WASTE = "Waste type"
COL_REMARKS = "Remarks"
# Chronological left to right; Type first because it decides whether Return exists.
# TBL_COLS is every column the table holds. Which ones are SHOWN, and in what order, is
# decided by visible_cols(); a hidden column keeps its data (it is only left out of column_order).
TBL_COLS = [COL_NO, COL_TYPE, COL_REQUEST, COL_PAID, COL_LOADED, COL_DISPOSAL, COL_RETURN,
            COL_BIN, COL_POSS, COL_PHOTO, COL_BASIS, COL_WASTE, COL_REMARKS]
EDIT_COLS = [c for c in TBL_COLS if c not in (COL_NO, COL_POSS)]   # COL_POSS is computed
_DATE_FIELD = {COL_REQUEST: "request", COL_LOADED: "loaded", COL_DISPOSAL: "disposal", COL_RETURN: "ret"}
DATE_FIELDS = ("request", "loaded", "disposal", "ret")   # Paid is deliberately NOT here: it is never auto-filled
FIELD_COL = {v: k for k, v in _DATE_FIELD.items()}
BASIS_NEED_LABEL = {"request": COL_REQUEST, "loaded": COL_LOADED, "disposal": COL_DISPOSAL,
                    "paid": COL_PAID}
ROW_BASIS_LABEL = {v: k for k, v in ROW_BASIS_CHOICES.items()}


def has_return(rtype):
    """Every type except S/Repo has a Return date (the next cycle's start)."""
    return rtype != "S/Repo"


def _next_uid():
    S["_uid"] = S.get("_uid", 0) + 1
    return S["_uid"]


def seed_row(r):
    """Pre-fill the blank date cells of a row from the dates it already has."""
    d, l, q = r["disposal"], r["loaded"], r["request"]
    if d is None and l is None and q is None:
        return
    before = {f: r[f] for f in DATE_FIELDS}
    if l is None:
        l = d or q
    if q is None:
        q = l
    if d is None:
        d = l or q
    r["disposal"], r["loaded"], r["request"] = d, l, q
    if has_return(r["type"]) and r["ret"] is None:
        r["ret"] = l  # bin is back on site from the loaded date (swap); see header notes
    if not has_return(r["type"]):
        r["ret"] = None
    auto = r.setdefault("auto", set())
    for f in DATE_FIELDS:
        if before[f] is None and r[f] is not None:
            auto.add(f)


def refresh_auto(r):
    """Re-derive the auto-filled cells from the cells the user typed."""
    auto = r.setdefault("auto", set())
    if not auto:
        return
    for f in auto:
        r[f] = None
    if all(r[f] is None for f in DATE_FIELDS):
        auto.clear()
        return
    e = effective_dates(r)
    for f in list(auto):
        if f == "ret" and not has_return(r["type"]):
            r[f] = None
            auto.discard(f)
        else:
            r[f] = e[f]


def new_row(disposal=None, rtype="S/Rtn", binsel="Unknown", placeholder=False):
    r = {
        "uid": _next_uid(),
        "disposal": disposal, "loaded": None, "request": None, "ret": None,
        "type": rtype, "bin": binsel,
        "paid": None, "waste": "", "remarks": "", "link": "", "basis": "",   # see COL_* above
        "err": {}, "raw": {},   # unreadable text typed into a cell
        "ph": placeholder,      # untouched demo row: the first date edit replaces the whole row
        "auto": set(),          # date cells pre-filled for the user; they follow the typed ones
    }
    seed_row(r)
    return r


def row_is_empty(r):
    return all(r[f] is None for f in DATE_FIELDS) and not r["raw"]


def effective_dates(r):
    """All four dates with blanks filled from the nearest filled date."""
    d, l, q, t = r["disposal"], r["loaded"], r["request"], r["ret"]
    e_l = l or d or q
    e_d = d or l or q
    e_q = q or l or d
    e_r = (t or e_l) if has_return(r["type"]) else e_d  # blank return = back on site at loading
    return {"request": e_q, "loaded": e_l, "disposal": e_d, "ret": e_r}


def default_rows(anchor):
    return [new_row(anchor + timedelta(days=10 * (i + 1)), placeholder=True) for i in range(3)]


def _anchor():
    dl = S.get("delivery_last") or {}
    return min(dl.values()) if dl else today_guam() - timedelta(days=30)


def _ref_for_row(rows, pos):
    """Reference date for inferring a missing year: nearest earlier event, else delivery."""
    for j in range(pos - 1, -1, -1):
        for f in ("disposal", "loaded", "request"):
            if rows[j][f]:
                return rows[j][f]
    return _anchor()


def _row_snap(r):
    out = {f: (r[f].isoformat() if isinstance(r[f], date) else None) for f in DATE_FIELDS}
    out.update(uid=r["uid"], type=r["type"], bin=r["bin"], err=dict(r.get("err", {})),
               raw=dict(r.get("raw", {})), ph=bool(r.get("ph")), auto=sorted(r.get("auto", ())),
               paid=r["paid"].isoformat() if isinstance(r.get("paid"), date) else None,
               waste=r.get("waste", ""), remarks=r.get("remarks", ""),
               link=r.get("link", ""), basis=r.get("basis", ""))
    return out


def _row_from_snap(x):
    r = {"uid": int(x["uid"]), "type": x.get("type", "S/Rtn"), "bin": x.get("bin", "Unknown"),
         "err": dict(x.get("err", {})), "raw": dict(x.get("raw", {})),
         "ph": bool(x.get("ph")), "auto": set(x.get("auto", [])),
         "waste": x.get("waste", "") or "", "remarks": x.get("remarks", "") or "",
         "link": x.get("link", "") or "", "basis": x.get("basis", "") or ""}
    for f in DATE_FIELDS + ("paid",):
        try:
            r[f] = date.fromisoformat(x[f]) if x.get(f) else None
        except (TypeError, ValueError):
            r[f] = None
    return r


def state_snap():
    """JSON-safe copy of everything undo/redo covers (the event rows)."""
    return {"rows": [_row_snap(r) for r in S["rows"]], "default": bool(S.get("rows_default", False))}


def touch(source, record=True):
    """Call after ANY change to SSOT. source: 'table' | 'picker' | 'other'.
    record=False: a housekeeping change that must not become an undo step."""
    S["rev"] += 1
    if source == "table":
        S["tbl_rev"] = S["rev"]
    elif source == "picker":
        S["pick_rev"] = S["rev"]
    cur, last = state_snap(), S.get("_last_snap")
    if record and last is not None and cur != last:
        S["undo"] = (S.get("undo", []) + [last])[-MAX_UNDO:]
        S["redo"] = []
    S["_last_snap"] = cur


def _apply_snap(snap):
    S["_last_snap"] = snap
    S["rows"] = [_row_from_snap(x) for x in snap["rows"]]
    S["rows_default"] = bool(snap.get("default", False))
    S["_uid"] = max([S.get("_uid", 0)] + [r["uid"] for r in S["rows"]])
    touch("other", record=False)  # bumps rev so the table / pickers re-seed


def undo_cb():
    if S.get("undo"):
        S["redo"] = (S.get("redo", []) + [S["_last_snap"]])[-MAX_UNDO:]
        _apply_snap(S["undo"].pop())


def redo_cb():
    if S.get("redo"):
        S["undo"] = (S.get("undo", []) + [S["_last_snap"]])[-MAX_UNDO:]
        _apply_snap(S["redo"].pop())


def sanitize_rows(rows, num_bins):
    """Never let SSOT hold anything the UI cannot render. Returns notices."""
    notices = []
    for i, r in enumerate(rows, 1):
        for f in DATE_FIELDS + ("paid",):
            v = r.get(f)
            if v is not None and (not isinstance(v, date) or not (DATE_MIN <= v <= DATE_MAX)):
                r[f] = None
        if r["type"] not in TYPE_DISPLAY:
            r["type"] = "S/Rtn"
        if not has_return(r["type"]):
            r["ret"] = None
        if r.get("basis") and r["basis"] not in ROW_BASIS_CHOICES:
            r["basis"] = ""
        for k in ("waste", "remarks", "link"):
            if not isinstance(r.get(k), str):
                r[k] = ""
        b = r.get("bin", "Unknown")
        if b != "Unknown":
            try:
                n = int(str(b).split()[-1])
            except ValueError:
                n = 0
            if not (1 <= n <= num_bins):
                notices.append(f"Row {i} was locked to {b} but only {num_bins} bin(s) are on site — reset to Unknown.")
                r["bin"] = "Unknown"
    return notices


def validate_rows(rows, num_bins, basis, opts=None, delivery_dates=None):
    """Only the date for the billing basis is required; any others are checked when filled."""
    o = normalize_opts(opts)
    errors, warns = [], []
    anchor = _anchor()
    link_bins = {}
    for i, r in enumerate(rows, 1):
        for col, msg in r.get("err", {}).items():
            errors.append(f"Row {i} ({col}): {msg}")
        d, l, q, ret = r["disposal"], r["loaded"], r["request"], r["ret"]
        paid = r.get("paid")
        # Which date ends this row's cycle: its own Fee basis (if that feature is on), else the sidebar's.
        row_b = ROW_BASIS_CHOICES.get(r.get("basis") or "") if o["row_basis_on"] else None
        eff_b = row_b or basis
        inert = r["type"] == "Dry run" and not o["dry_resets"]
        need_field = "request" if eff_b == "paid" else BASIS_FIELD[eff_b]
        need_label = BASIS_NEED_LABEL[eff_b]
        if row_is_empty(r):
            errors.append(f"Row {i} is empty — fill it in, or select the row and press Delete.")
        elif inert:
            pass                       # a dry run that does not reset the term only needs *a* date
        elif eff_b == "paid":
            if paid is None and COL_PAID not in r.get("err", {}):
                errors.append(f"Row {i}: {COL_PAID} is required (the billing basis for this work order is {COL_PAID}).")
        elif r[need_field] is None and not (eff_b == "request" and not row_b and o["paid_governs"] and paid):
            if FIELD_COL[need_field] not in r.get("err", {}):
                errors.append(f"Row {i}: {need_label} is required (the billing basis is {need_label}).")
        if eff_b == "request" and not row_b and o["paid_governs"] and paid is None and not inert \
                and not row_is_empty(r):
            warns.append(f"Row {i}: no {COL_PAID} entered — the Request date is used for this work order.")
        if l and d and l > d:
            errors.append(f"Row {i}: Loaded date ({l}) is after the Disposal date ({d}).")
        if q and l and q > l:
            errors.append(
                f"Row {i}: Request date ({q}) must be the same as or earlier than the Loaded date ({l}).")
        elif q and d and not l and q > d:
            errors.append(
                f"Row {i}: Request date ({q}) must be the same as or earlier than the Disposal date ({d}).")
        if has_return(r["type"]) and ret:
            floor = q if q else (l or d)
            if floor and ret < floor:
                if q:
                    errors.append(f"Row {i}: Return date ({ret}) is before the Request date ({q}).")
                else:
                    errors.append(
                        f"Row {i}: Return date ({ret}) is before the Loaded date ({floor}). To allow a "
                        "return before loading, enter a Request date on or before the Return date.")
            elif l and ret < l:
                if o["ret_rule"] == "block":
                    errors.append(
                        f"Row {i}: Return date ({ret}) is before the Loaded date ({l}); the sidebar "
                        "setting \"Return before Loaded\" is set to Don't allow.")
                elif r["type"] == "S/Rtn":
                    warns.append(
                        f"Row {i}: Return date ({ret}) is before the Loaded date ({l}). If an empty bin "
                        "was dropped first, set Type to S/Swap.")
        ref = r["paid"] if (eff_b == "paid" and paid) else r[need_field]
        if ref and abs((ref - anchor).days) > 730:
            warns.append(f"Row {i}: {need_label} {ref} is more than 2 years from the delivery date — check the year.")
        if o["photo_on"] and r.get("link") and r.get("bin", "Unknown") != "Unknown":
            link_bins.setdefault(_norm_link(r["link"]), {}).setdefault(r["bin"], []).append(i)
        if delivery_dates and r.get("bin", "Unknown") != "Unknown" and (l or d or q):
            try:
                b = int(str(r["bin"]).split()[-1])
            except ValueError:
                b = 0
            ds = delivery_dates.get(b)
            loaded_eff = l or d or q
            if ds and loaded_eff < ds:
                warns.append(
                    f"Row {i}: locked to Bin {b}, which was delivered {ds} — after this work order's Loaded "
                    "date. Accepted as an exception; that bin's first cycle starts on its delivery date.")
    for lk, per_bin in link_bins.items():
        if len(per_bin) > 1:
            parts = "; ".join(f"{b}: rows {', '.join(map(str, rs))}" for b, rs in per_bin.items())
            errors.append(f"Photo ID \"{lk}\" is locked to different bins ({parts}). "
                          "Work orders with the same Photo ID must be the same bin.")
    return errors, warns


def rows_to_events(rows):
    """SSOT rows -> calc events (all four dates filled), locked bins, blank cells per row."""
    eff = [effective_dates(r) for r in rows]
    base_labels = []
    for r, e in zip(rows, eff):
        d = e["disposal"]
        lab = d.strftime("%b %d")
        if e["loaded"] != d:
            lab += f" ({e['loaded'].strftime('%b %d')})"
        if r["type"] == "Dry run":
            lab = "DR " + lab
        elif r["type"] == "S/Swap":
            lab = "SW " + lab
        base_labels.append(lab)
    seen, events, fixed, blanks = {}, [], {}, {}
    for i, (r, lab, e) in enumerate(zip(rows, base_labels, eff)):
        seen[lab] = seen.get(lab, 0) + 1
        label = lab if base_labels.count(lab) == 1 else f"{lab} #{seen[lab]}"
        events.append({
            "label": label,
            "idx": i,
            "disposal_date": e["disposal"],
            "loaded_date": e["loaded"],
            "request_date": e["request"],
            "return_date": e["ret"],
            "type": TYPE_DISPLAY.get(r["type"], SERVICE_RETURN),
            "paid_date": r.get("paid"),
            "waste": r.get("waste", ""),
            "remarks": r.get("remarks", ""),
            "link": r.get("link", ""),
            "basis": ROW_BASIS_CHOICES.get(r.get("basis") or "", ""),
        })
        blanks[i] = [f for f in DATE_FIELDS if r[f] is None and not (f == "ret" and not has_return(r["type"]))]
        if r["bin"] != "Unknown":
            fixed[i] = int(str(r["bin"]).split()[-1])
    return events, fixed, blanks


def rows_from_record_inputs(parsed):
    """History record -> SSOT rows (keeps the cells that were left blank)."""
    rows = []
    for i, e in enumerate(parsed["events"]):
        rtype = TYPE_FROM_CALC.get(e["type"], "S/Rtn")
        r = new_row(None, rtype)
        r["disposal"], r["loaded"] = e["disposal_date"], e["loaded_date"]
        r["request"] = e["request_date"]
        r["ret"] = e["return_date"] if has_return(rtype) else None
        r["paid"] = e.get("paid_date")
        r["waste"], r["remarks"], r["link"] = e.get("waste", ""), e.get("remarks", ""), e.get("link", "")
        r["basis"] = ROW_BASIS_LABEL.get(e.get("basis") or "", "")
        for f in parsed["blanks"].get(i, []):
            r[f] = None
        if i in parsed["fixed_assignments"]:
            r["bin"] = f"Bin {parsed['fixed_assignments'][i]}"
        rows.append(r)
    return rows


def _norm_cell(x):
    if x is None:
        return ""
    try:
        if pd.isna(x):
            return ""
    except (TypeError, ValueError):
        pass
    if hasattr(x, "item"):
        try:
            x = x.item()
        except Exception:
            pass
    return x.strip() if isinstance(x, str) else x


def apply_cell_edit(r, col, val, ref):
    """Apply one edited cell to an SSOT row."""
    s = "" if val is None else str(val).strip()
    if col == COL_TYPE:
        if s in TYPE_DISPLAY:
            r["type"] = s
            if not has_return(s):
                r["ret"] = None
                r["auto"].discard("ret")
                r["err"].pop(COL_RETURN, None)
                r["raw"].pop(COL_RETURN, None)
            elif r["ret"] is None:  # S/Repo -> any type with a return: return follows the loaded date
                r["ret"] = r["loaded"] or r["disposal"] or r["request"]
                if r["ret"] is not None:
                    r["auto"].add("ret")
        return
    if col == COL_BIN:
        r["bin"] = s or "Unknown"
        return
    if col == COL_BASIS:
        r["basis"] = s if s in ROW_BASIS_CHOICES else ""
        return
    if col == COL_WASTE:
        r["waste"] = s
        return
    if col == COL_REMARKS:
        r["remarks"] = s
        return
    if col == COL_PHOTO:
        r["link"] = s
        return
    if col == COL_PAID:  # never auto-filled and never changes the other dates
        r["err"].pop(col, None)
        r["raw"].pop(col, None)
        if s == "":
            r["paid"] = None
            return
        try:
            r["paid"] = parse_date_text(s, r["request"] or r["disposal"] or r["loaded"] or ref)
        except ValueError as ex:
            r["err"][col] = str(ex)
            r["raw"][col] = s
        return
    if col == COL_RETURN and not has_return(r["type"]):
        return  # S/Repo has no return date; any entry is discarded
    r["err"].pop(col, None)
    r["raw"].pop(col, None)
    field = _DATE_FIELD[col]
    r["auto"].discard(field)  # typed (or cleared) by the user: no longer auto-filled
    if s == "":
        r[field] = None
        return
    try:
        if col == COL_DISPOSAL:
            d, l = parse_log_cell(s, ref)
            r["disposal"] = d
            if l is not None:
                r["loaded"] = l  # "9/1 (8/30)": the part in brackets is the loaded date
                r["auto"].discard("loaded")
        else:
            r[field] = parse_date_text(s, r["disposal"] or r["loaded"] or r["request"] or ref)
    except ValueError as ex:
        r["err"][col] = str(ex)
        r["raw"][col] = s


def edit_row(r, edits, ref):
    """Apply a batch of (column, value) edits to one row, then pre-fill if it was empty
    and let previously pre-filled cells follow the change.

    An empty row, or an untouched demo row, is treated as new: the first date entered
    replaces whatever the other date cells held, so pasting a column of dates over the
    demo rows cannot leave stale Request/Loaded dates behind."""
    touched = any(c in _DATE_FIELD for c, _ in edits)
    entered = any(c in _DATE_FIELD and str(v if v is not None else "").strip() != "" for c, v in edits)
    fresh = row_is_empty(r) or r.get("ph", False)
    if entered and r.get("ph"):
        for f in DATE_FIELDS:
            r[f] = None
        r["err"], r["raw"] = {}, {}
        r["auto"] = set()
    for col, val in edits:
        apply_cell_edit(r, col, val, ref)
    if touched:
        r["ph"] = False
    if entered and fresh:
        seed_row(r)
    refresh_auto(r)  # auto-filled cells follow whatever the user just changed


def _cell_txt(r, col, field):
    if col in r["raw"]:
        return r["raw"][col]
    v = r[field]
    return v.isoformat() if isinstance(v, date) else ""


def possible_info(rows):
    """Per row: (bins that could have served it | None, tag). Tags: locked / auto / photo / only /
    free / none / inert (a dry run that does not reset the term). Uses only conditions every
    valid scenario must meet, so a bin left out is truly impossible."""
    out = [(None, "", None)] * len(rows)
    try:
        dd = S.get("delivery_last") or {}
        nb = int(S.get("num_bins_input", 2))
        if not dd or not rows:
            return out
        idxs = [i for i, r in enumerate(rows) if any(r[f] for f in DATE_FIELDS)]
        events, fixed, _ = rows_to_events([rows[i] for i in idxs])
        prep = prepare_calc(events, fixed, dd, nb, current_opts())
        pm = possible_bins_map(prep["events"], prep["fixed"], dd, nb)
        newidx = {ev["src"]: ev["idx"] for ev in prep["events"]}
        out = list(out)
        for k, i in enumerate(idxs):
            if k not in newidx:
                out[i] = (None, "inert", None)
                continue
            ni = newidx[k]
            bl = pm[ni]
            if ni in prep["exempt"]:
                tag = "locked"
            elif ni in prep["auto"]:
                tag = "auto"
            elif ni in prep["fixed"]:
                tag = "photo"
            elif not bl:
                tag = "none"
            elif len(bl) == 1:
                tag = "only"
            else:
                tag = "free"
            out[i] = (bl, tag, prep["fixed"].get(ni))
    except Exception:  # a helper must never break the table
        pass
    return out


def possible_bin_texts(rows):
    """One short text per row for the read-only 'Possible bins' column."""
    texts = []
    for bl, tag, fb in possible_info(rows):
        if tag == "inert":
            texts.append("— (dry run: no effect)")
        elif tag == "none":
            texts.append("⚠ none")
        elif tag == "locked":
            texts.append(f"Bin {fb} (locked)")
        elif tag == "auto":
            texts.append(f"Bin {fb} (auto)")
        elif tag == "photo":
            texts.append(f"Bin {fb} (Photo ID)")
        elif not bl:
            texts.append("")
        elif tag == "only":
            texts.append(f"Bin {bl[0]} only")
        else:
            texts.append(", ".join(f"Bin {b}" for b in bl))
    return texts


def build_view_df(rows):
    def col(values):
        return pd.Series(values, dtype=object)
    return pd.DataFrame({
        COL_NO: col([str(i) for i in range(1, len(rows) + 1)]),
        COL_TYPE: col([r["type"] for r in rows]),
        COL_REQUEST: col([_cell_txt(r, COL_REQUEST, "request") for r in rows]),
        COL_PAID: col([_cell_txt(r, COL_PAID, "paid") for r in rows]),
        COL_LOADED: col([_cell_txt(r, COL_LOADED, "loaded") for r in rows]),
        COL_DISPOSAL: col([_cell_txt(r, COL_DISPOSAL, "disposal") for r in rows]),
        COL_RETURN: col([_cell_txt(r, COL_RETURN, "ret") if has_return(r["type"]) else "" for r in rows]),
        COL_BIN: col([r["bin"] for r in rows]),
        COL_POSS: col(possible_bin_texts(rows)),
        COL_PHOTO: col([r.get("link", "") for r in rows]),
        COL_BASIS: col([r.get("basis", "") for r in rows]),
        COL_WASTE: col([r.get("waste", "") for r in rows]),
        COL_REMARKS: col([r.get("remarks", "") for r in rows]),
    })[TBL_COLS]


def _same_view(a, b):
    if len(a) != len(b):
        return False
    for c in TBL_COLS:
        for x, y in zip(a[c].tolist(), b[c].tolist()):
            if _norm_cell(x) != _norm_cell(y):
                return False
    return True


def table_rebuild():
    S["tbl_base"] = build_view_df(S["rows"])
    S["tbl_seen"] = S["tbl_base"].copy()
    S["tbl_ver"] += 1
    S["tbl_rev"] = S["rev"]


def _editor_delta():
    d = S.get(f"tbl_{S['tbl_ver']}")
    return d if isinstance(d, dict) else {}


def on_table_edit():
    """data_editor callback: fold the grid's edits, row additions (paste / +) and row
    deletions (select row + Delete key) into SSOT."""
    base, seen, rows = S.get("tbl_base"), S.get("tbl_seen"), S["rows"]
    if base is None or seen is None or len(base) != len(rows):
        table_rebuild()
        return
    delta = _editor_delta()
    deleted = {int(x) for x in (delta.get("deleted_rows") or [])}
    added = delta.get("added_rows") or []

    # What the grid shows now = base + cell edits (same rule Streamlit uses).
    eff = base.copy()
    for pos_s, changes in (delta.get("edited_rows") or {}).items():
        pos = int(pos_s)
        if 0 <= pos < len(eff):
            for col, val in changes.items():
                if col in EDIT_COLS:
                    eff.at[pos, col] = "" if val is None else str(val)

    # 1. cells changed since the last time this callback ran
    changed = {}
    for pos in range(len(rows)):
        if pos in deleted:
            continue
        for col in EDIT_COLS:
            if _norm_cell(eff.at[pos, col]) != _norm_cell(seen.at[pos, col]):
                changed.setdefault(pos, []).append(col)
    data_edit = False
    cleared = False
    for pos, cols in changed.items():
        edit_row(rows[pos], [(c, eff.at[pos, c]) for c in cols], _ref_for_row(rows, pos))
        data_edit = True
        cleared = cleared or any(_norm_cell(eff.at[pos, c]) == "" for c in cols)

    # 2. rows added by pasting past the end / the + row
    new_rows = []
    for item in added:
        r = new_row()
        ref = new_rows[-1]["disposal"] if new_rows and new_rows[-1]["disposal"] else (
            _ref_for_row(rows + new_rows, len(rows) + len(new_rows)))
        edit_row(r, [(c, item[c]) for c in EDIT_COLS if c in item], ref)
        new_rows.append(r)

    # 3. rows deleted with the Delete key
    if deleted:
        rows[:] = [r for i, r in enumerate(rows) if i not in deleted]
    rows.extend(new_rows)
    structural = bool(deleted or new_rows)
    if data_edit or structural:
        S["rows_default"] = False

    view = build_view_df(rows)
    if structural or cleared or not _same_view(view, eff):
        S["tbl_base"] = view           # renumber / pre-fill / normalise: re-seed the grid once
        S["tbl_seen"] = view.copy()
        S["tbl_ver"] += 1
    else:
        S["tbl_seen"] = eff            # nothing to change: keep the grid (and its selection) as is
    touch("table")


def ensure_table_fresh():
    sig = table_ctx_sig()
    if (S.get("tbl_base") is None or S["tbl_rev"] != S["rev"] or len(S["tbl_base"]) != len(S["rows"])
            or S.get("tbl_ctx") != sig):
        S["tbl_ctx"] = sig
        table_rebuild()


def ensure_picker_fresh():
    if S["pick_rev"] != S["rev"]:
        S["pick_ver"] += 1
        S["pick_rev"] = S["rev"]


# ---- sidebar options -> engine options, and the column layout ----
def parse_holidays(text, ref=None):
    """Free text (one date per line or comma separated) -> (sorted ISO dates, unreadable items)."""
    good, bad = set(), []
    for part in re.split(r"[,;\n]+", text or ""):
        p = part.strip()
        if not p:
            continue
        try:
            d = parse_date_text(p, ref)
            if d:
                good.add(d.isoformat())
        except ValueError:
            bad.append(p)
    return sorted(good), bad


def current_opts():
    """The calculation options as currently set in the sidebar (normalised)."""
    hol, _bad = parse_holidays(S.get("opt_holidays", ""), _anchor())
    return normalize_opts({
        "dry_resets": S.get("opt_dry_resets"), "paid_governs": S.get("opt_paid_governs"),
        "auto_bin": S.get("opt_auto_bin"), "photo_on": S.get("opt_photo_on"),
        "photo_distinct": S.get("opt_photo_distinct"), "row_basis_on": S.get("opt_row_basis"),
        "ret_rule": S.get("opt_ret_rule"), "wk_on": S.get("opt_wk_on"),
        "weekend_days": S.get("opt_weekend_days"), "hol_on": S.get("opt_hol_on"),
        "holidays": hol, "waive_mode": S.get("opt_waive_mode"),
    })


def visible_cols():
    """Columns shown in the table, in order. A column that is switched off keeps its data
    (it is only left out of column_order), so it comes back with its values when switched on."""
    o = current_opts()
    hidden = set()
    if not o["paid_governs"]:
        hidden.add(COL_PAID)
    if not o["photo_on"]:
        hidden.add(COL_PHOTO)
    if not o["row_basis_on"]:
        hidden.add(COL_BASIS)
    if not S.get("col_waste", True):
        hidden.add(COL_WASTE)
    if not S.get("col_remarks", True):
        hidden.add(COL_REMARKS)
    if not S.get("col_poss", True):
        hidden.add(COL_POSS)
    order = [c for c in S.get("col_order", TBL_COLS) if c in TBL_COLS and c != COL_NO]
    order += [c for c in TBL_COLS if c != COL_NO and c not in order]
    return [COL_NO] + [c for c in order if c not in hidden]


def set_opts_widgets(o):
    """Push saved calculation options into the sidebar widgets (callbacks / restore only,
    i.e. before those widgets are drawn)."""
    o = normalize_opts(o)
    S["opt_dry_resets"], S["opt_paid_governs"], S["opt_auto_bin"] = o["dry_resets"], o["paid_governs"], o["auto_bin"]
    S["opt_photo_on"], S["opt_photo_distinct"], S["opt_row_basis"] = o["photo_on"], o["photo_distinct"], o["row_basis_on"]
    S["opt_ret_rule"], S["opt_waive_mode"] = o["ret_rule"], o["waive_mode"]
    S["opt_wk_on"], S["opt_weekend_days"] = o["wk_on"], list(o["weekend_days"])
    S["opt_hol_on"], S["opt_holidays"] = o["hol_on"], "\n".join(o["holidays"])


def table_ctx_sig():
    """Everything outside the rows that changes what the table shows. When it changes the
    grid is re-drawn (a data_editor cannot change its columns without losing edits)."""
    dd = S.get("delivery_last") or {}
    return json.dumps([sorted((int(b), str(d)) for b, d in dd.items()), S.get("num_bins_input"),
                       current_opts(), visible_cols()], sort_keys=True, default=str)


def apply_row_order(uids):
    """Put the rows in the order of these uids (ignored unless it is the same set of rows)."""
    rows = S["rows"]
    by = {str(r["uid"]): r for r in rows}
    if sorted(uids) != sorted(by) or [str(r["uid"]) for r in rows] == list(uids):
        return False
    rows[:] = [by[u] for u in uids]
    S["rows_default"] = False
    touch("other")
    return True


# ---- row tools (sort / insert / move) ----
def _sort_value(r, col, poss):
    if col == COL_TYPE:
        names = list(TYPE_DISPLAY)
        return names.index(r["type"]) if r["type"] in names else None
    if col in _DATE_FIELD:
        if col == COL_RETURN and not has_return(r["type"]):
            return None
        return r[_DATE_FIELD[col]]
    if col == COL_PAID:
        return r.get("paid")
    if col == COL_BIN:
        return None if r["bin"] == "Unknown" else int(str(r["bin"]).split()[-1])
    if col == COL_POSS:
        return poss or None
    key = {COL_PHOTO: "link", COL_BASIS: "basis", COL_WASTE: "waste", COL_REMARKS: "remarks"}.get(col)
    v = (r.get(key) or "").strip().casefold() if key else ""
    return v or None


def sort_rows_cb():
    """Reorder the rows by one column. Blank cells always go last. Undoable."""
    col, desc = S.get("sort_col", COL_REQUEST), S.get("sort_dir") == "Descending"
    rows = S["rows"]
    if col == COL_NO:
        if desc:
            rows.reverse()
    else:
        poss = possible_bin_texts(rows) if col == COL_POSS else [""] * len(rows)
        keyed = [(_sort_value(r, col, p), r) for r, p in zip(rows, poss)]
        have = sorted([kr for kr in keyed if kr[0] is not None], key=lambda kr: kr[0], reverse=desc)
        rows[:] = [r for _, r in have] + [r for v, r in keyed if v is None]
    S["rows_default"] = False
    touch("other")


def insert_rows_cb(where):
    """Insert blank rows above / below row # (1-based) instead of only at the end."""
    rows = S["rows"]
    n = len(rows)
    pos = min(max(int(S.get("ins_pos", 1)), 1), max(n, 1))
    k = max(1, int(S.get("ins_n", 1)))
    at = 0 if n == 0 else (pos - 1 if where == "above" else pos)
    rows[at:at] = [new_row() for _ in range(k)]
    S["rows_default"] = False
    touch("other")


def move_row_cb():
    rows = S["rows"]
    n = len(rows)
    if n < 2:
        return
    a = min(max(int(S.get("mv_from", 1)), 1), n) - 1
    b = min(max(int(S.get("mv_to", 1)), 1), n) - 1
    if a != b:
        rows.insert(b, rows.pop(a))
        S["rows_default"] = False
        touch("other")


def apply_col_order(ids):
    cur = [c for c in S.get("col_order", TBL_COLS) if c != COL_NO]
    vis = [c for c in visible_cols() if c != COL_NO]
    if sorted(ids) != sorted(vis) or list(ids) == [c for c in cur if c in vis]:
        return False
    # keep hidden columns where they were; re-slot the visible ones in the dragged order
    it = iter(ids)
    S["col_order"] = [next(it) if c in vis else c for c in cur] if cur else list(ids)
    return True


_SORTER_HTML = """<!doctype html><html><head><meta charset="utf-8"><style>
html,body{margin:0;padding:0;font:13px/1.25 "Source Sans Pro",Arial,sans-serif;background:transparent}
#list{display:flex;flex-direction:column;gap:4px;overflow-y:auto;padding:2px}
#list.h{flex-direction:row;flex-wrap:wrap}
.item{display:flex;align-items:center;gap:6px;padding:4px 8px;border:1px solid var(--bd);border-radius:6px;
  background:var(--bg);color:var(--fg);cursor:grab;user-select:none;white-space:nowrap}
.item.over{outline:2px solid #ff4b4b}
.item.drag{opacity:.4}
.grip{opacity:.55}
.lbl{flex:1 1 auto;overflow:hidden;text-overflow:ellipsis}
.btn{border:1px solid var(--bd);background:transparent;color:var(--fg);border-radius:4px;cursor:pointer;
  padding:0 5px;font-size:11px;line-height:16px}
.btn:hover{background:rgba(255,75,75,.2)}
</style></head><body><div id="list"></div><script>
(function () {
  var list = document.getElementById("list"), items = [], horizontal = false, maxh = 240, dragEl = null;
  function post(type, data) {
    window.parent.postMessage(Object.assign({isStreamlitMessage: true, type: type}, data || {}), "*");
  }
  function fit() {
    post("streamlit:setFrameHeight", {height: Math.min(Math.max(list.scrollHeight + 6, 28), maxh)});
  }
  function send() {
    var ids = Array.prototype.map.call(list.children, function (c) { return c.getAttribute("data-id"); });
    post("streamlit:setComponentValue", {
      value: {token: Math.random().toString(36).slice(2) + Date.now(), order: ids}, dataType: "json"});
  }
  function move(el, delta) {
    var sib = delta < 0 ? el.previousElementSibling : el.nextElementSibling;
    if (!sib) return;
    if (delta < 0) list.insertBefore(el, sib); else list.insertBefore(sib, el);
    send();
  }
  function render() {
    list.className = horizontal ? "h" : "";
    list.style.maxHeight = (maxh - 6) + "px";
    list.innerHTML = "";
    items.forEach(function (it) {
      var d = document.createElement("div");
      d.className = "item"; d.draggable = true; d.setAttribute("data-id", it.id);
      d.innerHTML = '<span class="grip">⠿</span><span class="lbl"></span>' +
        '<button class="btn up" title="Move earlier">' + (horizontal ? "◀" : "▲") + '</button>' +
        '<button class="btn dn" title="Move later">' + (horizontal ? "▶" : "▼") + '</button>';
      d.querySelector(".lbl").textContent = it.label;
      d.querySelector(".up").onclick = function () { move(d, -1); };
      d.querySelector(".dn").onclick = function () { move(d, 1); };
      d.addEventListener("dragstart", function (e) {
        dragEl = d; d.classList.add("drag"); e.dataTransfer.effectAllowed = "move";
        try { e.dataTransfer.setData("text/plain", it.id); } catch (x) {}
      });
      d.addEventListener("dragend", function () {
        d.classList.remove("drag"); dragEl = null;
        Array.prototype.forEach.call(list.children, function (c) { c.classList.remove("over"); });
      });
      d.addEventListener("dragover", function (e) {
        e.preventDefault(); if (!dragEl || dragEl === d) return;
        Array.prototype.forEach.call(list.children, function (c) { c.classList.remove("over"); });
        d.classList.add("over");
      });
      d.addEventListener("drop", function (e) {
        e.preventDefault(); if (!dragEl || dragEl === d) return;
        var kids = Array.prototype.slice.call(list.children);
        if (kids.indexOf(dragEl) < kids.indexOf(d)) list.insertBefore(dragEl, d.nextSibling);
        else list.insertBefore(dragEl, d);
        send();
      });
      list.appendChild(d);
    });
    fit();
  }
  // Ctrl+Z / Ctrl+Y while a drag-list button has the focus: forward to the header's Undo / Redo.
  document.addEventListener("keydown", function (e) {
    if (!(e.ctrlKey || e.metaKey) || e.altKey) return;
    var k = (e.key || "").toLowerCase();
    var redo = (k === "y") || (k === "z" && e.shiftKey), undo = (k === "z" && !e.shiftKey);
    if (!undo && !redo) return;
    try {
      var b = window.parent.document.querySelector(redo ? ".st-key-redo_btn button" : ".st-key-undo_btn button");
      if (b) { e.preventDefault(); if (!b.disabled) b.click(); }
    } catch (x) {}
  });
  window.addEventListener("resize", fit);
  if (window.ResizeObserver) new ResizeObserver(fit).observe(list);
  window.addEventListener("message", function (ev) {
    var m = ev.data || {};
    if (m.type !== "streamlit:render") return;
    var a = m.args || {};
    var dark = !!a.dark;
    document.documentElement.style.setProperty("--fg", dark ? "#fafafa" : "#31333f");
    document.documentElement.style.setProperty("--bg", dark ? "#262730" : "#f0f2f6");
    document.documentElement.style.setProperty("--bd", dark ? "#4a4c5a" : "#c9ccd6");
    items = a.items || []; horizontal = !!a.horizontal; maxh = a.maxh || 240;
    render();
  });
  post("streamlit:componentReady", {apiVersion: 1});
})();
</script></body></html>"""


@st.cache_resource
def _sorter_component():
    d = os.path.join(tempfile.gettempdir(), "bin_calc_sorter")
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "index.html"), "w") as f:
        f.write(_SORTER_HTML)
    return components.declare_component("bin_calc_sorter", path=d)


def drag_sorter(key, items, apply_fn, horizontal=False, max_height=240):
    """A drag-to-reorder list (with ▲▼ buttons for touch screens). items = [{"id","label"}].
    Each drop reports a fresh token; a report is applied once, so reruns never re-apply it."""
    try:
        dark = st.context.theme.type == "dark"
    except Exception:
        dark = False
    try:
        val = _sorter_component()(items=items, horizontal=horizontal, dark=dark,
                                  maxh=max_height, key=key, default=None)
    except Exception:
        st.caption("Drag list unavailable on this Streamlit build; use the Sort / Move controls.")
        return
    if isinstance(val, dict) and val.get("token") and val["token"] != S.get(f"{key}_tok"):
        S[f"{key}_tok"] = val["token"]
        apply_fn([str(x) for x in (val.get("order") or [])])


# ---- structure changes ----
def _next_event_date():
    for r in reversed(S["rows"]):
        for f in ("disposal", "loaded", "request"):
            if r[f]:
                return r[f] + timedelta(days=10)
    return _anchor() + timedelta(days=10)


def set_event_count(n):
    n = max(0, int(n))
    rows = S["rows"]
    while len(rows) < n:
        rows.append(new_row(_next_event_date()))
    del rows[n:]
    S["rows_default"] = False
    touch("other")


def reset_events_cb():
    """Hard reset of the event inputs without a browser refresh."""
    S["rows"] = default_rows(_anchor())
    S["rows_anchor"] = _anchor()
    S["rows_default"] = True
    S["_flash_notices"] = []
    S.pop("last_results", None)
    touch("other")


# ---- picker callbacks ----
PICK_FIELD = {"req": "request", "load": "loaded", "disp": "disposal", "ret": "ret"}
PICK_TEXT = {"waste": COL_WASTE, "remarks": COL_REMARKS, "link": COL_PHOTO, "basis": COL_BASIS}


def _row_by_uid(uid):
    for r in S["rows"]:
        if r["uid"] == uid:
            return r
    return None


def on_picker_resize(v):
    set_event_count(S[f"p{v}_n"])
    S["pick_rev"] = S["rev"]  # the picker already shows the right number of rows
    S["pick_ver"] += 1        # ...but new rows need fresh widget keys


def on_picker_change(uid, field, v):
    r = _row_by_uid(uid)
    if r is None:
        return
    val = S.get(f"p{v}_{uid}_{field}")
    r["err"], r["raw"] = {}, {}
    if field in PICK_FIELD:
        col = FIELD_COL[PICK_FIELD[field]]
        edit_row(r, [(col, val.isoformat() if isinstance(val, date) else "")], r["disposal"])
    elif field == "type" and val in TYPE_DISPLAY:
        edit_row(r, [(COL_TYPE, val)], None)
        S.pop(f"p{v}_{uid}_ret", None)
    elif field == "bin":
        r["bin"] = val or "Unknown"
    elif field == "paid":
        edit_row(r, [(COL_PAID, val.isoformat() if isinstance(val, date) else "")], r["disposal"])
    elif field in PICK_TEXT:
        edit_row(r, [(PICK_TEXT[field], val or "")], None)
    S["rows_default"] = False
    # push pre-filled values into the sibling widgets so they show them
    for f, name in PICK_FIELD.items():
        k = f"p{v}_{uid}_{f}"
        if k in S:
            S[k] = r[name]
    touch("picker")


# ──────────────────────────────────────────────
# Column-config helper (works across Streamlit versions)
# ──────────────────────────────────────────────
def _cc(kind, label, align=None, **kw):
    """st.column_config.<kind>(label, **kw), dropping options this Streamlit does
    not know. `align` ('center'/'right') is added as a raw key; older versions ignore it."""
    cls = getattr(st.column_config, kind)
    ok = inspect.signature(cls).parameters
    cfg = cls(label, **{k: v for k, v in kw.items() if k in ok})
    if align:
        cfg["alignment"] = align
    return cfg


def fmt_range(lo, hi, dlo=None, dhi=None, show_days=True):
    """'$0 – $100 (0–2d)', or a single value when lo == hi."""
    money = f"${lo:,.0f}" if lo == hi else f"${lo:,.0f} – ${hi:,.0f}"
    if show_days and dlo is not None:
        days = f"{dlo}d" if dlo == dhi else f"{dlo}–{dhi}d"
        return f"{money} ({days})"
    return money


# ──────────────────────────────────────────────
# Rendering helpers: scenario table
# ──────────────────────────────────────────────
def build_scenario_table(results, num_bins, show_days, show_cal=False):
    """Numeric columns (so sorting by Total puts $250 before $300 before $3,000)
    plus the column_config that formats them."""
    nb = int(num_bins)
    rows = []
    for i, r in enumerate(results, 1):
        row = {"No": str(i)}
        for b in range(1, nb + 1):
            row[f"Bin {b}"] = ", ".join(r["assignment"][b]) if r["assignment"][b] else "(none)"
        for b in range(1, nb + 1):
            row[f"Bin {b} Fee"] = float(r["fees"][b])
            if show_days:
                row[f"Bin {b} Days"] = int(sum(c["ext_days"] for c in r["breakdowns"][b]))
        row["Total"] = float(r["total"])
        if show_days:
            row["Total Days"] = int(r.get("total_ext_days", 0))
        row["Waived"] = float(r.get("waived", 0))
        if show_days:
            row["Waived Days"] = int(r.get("waived_days", 0))
        if show_cal:
            row["Weekend/holiday waived"] = float(r.get("cal_waived", 0))
            if show_days:
                row["Weekend/holiday Days"] = int(r.get("cal_waived_days", 0))
        rows.append(row)
    cfg = {"No": _cc("TextColumn", "No", align="center", width="small", pinned=True)}
    for b in range(1, nb + 1):
        cfg[f"Bin {b}"] = _cc("TextColumn", f"Bin {b}", width="medium")
        cfg[f"Bin {b} Fee"] = _cc("NumberColumn", f"Bin {b} Fee", format=DOLLAR, width="small")
        if show_days:
            cfg[f"Bin {b} Days"] = _cc("NumberColumn", f"Bin {b} Days", format="%d d", width="small")
    cfg["Total"] = _cc("NumberColumn", "Total", format=DOLLAR, width="small")
    if show_days:
        cfg["Total Days"] = _cc("NumberColumn", "Total Days", format="%d d", width="small")
    cfg["Waived"] = _cc("NumberColumn", "Waived", format=DOLLAR, width="small")
    if show_days:
        cfg["Waived Days"] = _cc("NumberColumn", "Waived Days", format="%d d", width="small")
    if show_cal:
        cfg["Weekend/holiday waived"] = _cc("NumberColumn", "Weekend/holiday waived", format=DOLLAR, width="small")
        if show_days:
            cfg["Weekend/holiday Days"] = _cc("NumberColumn", "Weekend/holiday Days", format="%d d", width="small")
    df = pd.DataFrame(rows)
    for c in [c for c in df.columns if c.endswith("Fee") or c in ("Total", "Waived", "Weekend/holiday waived")]:
        if (df[c] % 1 == 0).all():      # whole dollars: show $3,000, not $3,000.00
            df[c] = df[c].astype(int)
    return df, cfg


def show_scenario_table(results, num_bins, show_days, show_cal=False):
    df, cfg = build_scenario_table(results, num_bins, show_days, show_cal)
    st.dataframe(df, hide_index=True, column_config=cfg, **STRETCH)


def options_summary(opts, n_dry=0):
    """Plain-language list of the options that change the numbers (for the results and the audit)."""
    o = normalize_opts(opts)
    out = []
    if n_dry:
        out.append("dry runs reset the rental term" if o["dry_resets"]
                   else f"{n_dry} dry run(s) listed but not billed (they do not reset the term)")
    if o["paid_governs"]:
        out.append("Paid date governs instead of Request date (Request date is the fallback)")
    if o["row_basis_on"]:
        out.append("per-work-order Fee basis is on")
    if o["photo_on"]:
        out.append("Photo IDs link work orders to the same bin"
                   + (" and different IDs must be different bins" if o["photo_distinct"] else ""))
    if o["ret_rule"] != DEFAULT_OPTS["ret_rule"]:
        out.append("Return before Loaded — " + RET_RULES[o["ret_rule"]])
    cal = make_cal(o)
    if cal:
        wk = ", ".join(WEEKDAY_NAMES[d] for d in sorted(cal["wk"]))
        bits = ([f"weekends ({wk})"] if cal["wk"] else []) + ([f"{len(cal['hol'])} holiday(s)"] if cal["hol"] else [])
        out.append("waived: " + " + ".join(bits) + " — " + WAIVE_MODES[cal["mode"]].lower())
    if not o["auto_bin"]:
        out.append("auto-assign of single-bin work orders is off")
    return out


def audit_table(events, fixed, exempt, auto, end_basis):
    """One row per work order as the maths saw it (dates, which date ends the cycle, bin, notes)."""
    rows = []
    for e in events:
        i = e["idx"]
        eff = e.get("basis") or end_basis
        if eff == "request" and not e.get("basis") and e.get("gov_date"):
            ends = f"Paid date {yymmdd(event_end_date(e, end_basis))}"
        else:
            ends = f"{ROW_BASIS_LABEL.get(eff, eff)} {yymmdd(event_end_date(e, end_basis))}"
        if i in fixed:
            how = "locked" if i in exempt else ("auto" if i in auto else "Photo ID")
            bin_txt = f"Bin {fixed[i]} ({how})"
        else:
            bin_txt = "unknown"
        rows.append({
            "No": int(e.get("src", i)) + 1, "Work order": e["label"],
            "Type": TYPE_FROM_CALC.get(e["type"], e["type"]),
            "Request": yymmdd(e["request_date"]), "Paid": yymmdd(e.get("paid_date")),
            "Loaded": yymmdd(e["loaded_date"]), "Disposal": yymmdd(e["disposal_date"]),
            "Return": yymmdd(e["return_date"]) if e["type"] != REPO else "—",
            "Cycle ends on": ends, "Bin": bin_txt,
            "Photo ID": e.get("link_text", e.get("link", "")) or "",
            "Waste type": e.get("waste", "") or "", "Remarks": e.get("remarks", "") or "",
        })
    return pd.DataFrame(rows)


def basis_caption(end_basis):
    label = BASIS_LABEL.get(end_basis, end_basis)
    if end_basis == BASELINE_BASIS:
        return f"Extension days run to the **{label}** (nothing waived)."
    return (
        f"Extension days run to the **{label}**. **Waived** = fee if billed to the "
        f"Disposal date − fee on the {label}."
    )


# ──────────────────────────────────────────────
# Render: full results (for calculator)
# ──────────────────────────────────────────────
def render_results(cached, filters, show_tree, show_days, show_timeline, interchangeable,
                   hide_invalid_leaves):
    all_results = cached["all_results"]
    events = cached["events"]
    num_bins = cached["num_bins"]
    delivery_dates = cached["delivery_dates"]
    fixed_assignments = cached["fixed"]
    free_days = cached["free_days"]
    rate_per_day = cached["rate"]
    end_basis = cached["end_basis"]

    if not all_results:
        st.error(
            "No valid scenarios found. Check that each bin has at most one "
            "S/Repo (and it's the last event for that bin), that no event was "
            "loaded before its bin's delivery date (unless you locked it to that bin as an "
            "exception), that no bin is loaded again before its Return date, and that Photo IDs "
            "do not contradict locked bins."
        )
        return
    results, hidden_by_filters = filter_scenarios(all_results, filters, num_bins)
    if not results:
        st.warning(
            f"All {len(all_results):,} valid scenario(s) are hidden by the filters "
            f"({describe_filters(filters)}). Loosen or turn off a filter in the sidebar."
        )
        return
    has_unknown_bins = len(events) > len(fixed_assignments)
    if (not interchangeable) and has_unknown_bins:
        st.warning(
            "⚠️ You have rows with unknown bin assignments and "
            "**Hide equivalent permutations** is off. You'll see "
            "all possible bin assignments — including ones with the "
            "same figures and event groupings. Consider turning on "
            "**Hide equivalent permutations** if you only need "
            "distinct outcomes."
        )
    removed_count = 0
    if interchangeable:
        results, removed_count = deduplicate_scenarios(results)
    lines = [
        f"Showing **{len(results):,}** of **{len(all_results):,}** valid scenario(s) across "
        f"**{len(events):,}** event(s) · billing basis: **{BASIS_LABEL.get(end_basis, end_basis)}**."
    ]
    if hidden_by_filters:
        lines.append(f"Hid **{hidden_by_filters:,}** by the filters (a scenario is hidden when {describe_filters(filters)}).")
    if removed_count > 0:
        lines.append(
            f"Hid **{removed_count:,}** equivalent permutation(s) "
            "(same figures and event groupings — only bin labels differ)."
        )
    st.success("\n\n".join(lines))
    st.caption(basis_caption(end_basis))
    cal = cached.get("cal")
    summary = options_summary(cached.get("opts"), len(cached.get("inert") or []) +
                              sum(1 for e in events if e["type"] == DRY_RUN))
    if summary:
        st.caption("⚙️ Options in effect: " + "; ".join(summary) + ".")
    if cached.get("auto"):
        st.caption("🔒 Auto-assigned (only one bin could have been on site): " + ", ".join(
            f"row {events[i].get('src', i) + 1} → Bin {fixed_assignments[i]}" for i in sorted(cached["auto"])) + ".")
    with st.expander("🧾 Inputs used for this calculation (audit)"):
        st.dataframe(audit_table(events, fixed_assignments, cached.get("exempt") or set(),
                                 cached.get("auto") or set(), end_basis), hide_index=True, **STRETCH)
        if cached.get("inert"):
            st.caption("Not in the table above: " + ", ".join(e["label"] for e in cached["inert"]) +
                       " (dry run, not billed because it does not reset the rental term).")

    lowest, highest = results[0]["total"], results[-1]["total"]
    lowest_ext = results[0].get("total_ext_days", 0)
    highest_ext = results[-1].get("total_ext_days", 0)
    w_vals = [r.get("waived", 0) for r in results]
    wd_vals = [r.get("waived_days", 0) for r in results]
    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Lowest total fee", fmt_fee(lowest, lowest_ext, show_days))
    m2.metric("Highest total fee", fmt_fee(highest, highest_ext, show_days))
    m3.metric("Range", f"${highest - lowest:,.0f}")
    m4.metric("Waived (min – max)", fmt_range(min(w_vals), max(w_vals), min(wd_vals), max(wd_vals), show_days))

    show_scenario_table(results, num_bins, show_days, cal is not None)

    st.subheader("📋 Scenario breakdown")
    choice = st.selectbox(
        "View detailed cycle math for scenario No:",
        list(range(1, len(results) + 1)),
    )
    selected_scenario = results[choice - 1]

    if show_tree:
        st.subheader("🌳 Decision tree")
        n_free = len(free_decision_groups(events, fixed_assignments))
        if int(num_bins) ** n_free > MAX_TREE_LEAVES:
            st.info(
                f"Tree skipped: {int(num_bins) ** n_free:,} branches is too many to draw "
                f"(limit {MAX_TREE_LEAVES}). Lock more events to a bin to shrink it."
            )
        else:
            dot = build_decision_tree_dot(
                events, fixed_assignments, num_bins, delivery_dates,
                free_days, rate_per_day,
                highlight_combo=selected_scenario.get("combo"),
                hide_invalid=hide_invalid_leaves,
                end_basis=end_basis, cal=cal, exempt=cached.get("exempt"),
                distinct_links=bool((cached.get("opts") or {}).get("photo_distinct")
                                    and (cached.get("opts") or {}).get("photo_on")),
            )
            if dot is None:
                st.info("No decisions to display — all events are locked to specific bins.")
            else:
                try:
                    st.graphviz_chart(dot, **STRETCH)
                    legend_text = """
**🗺️ Tree legend**
- 🔵 **Blue oval** = Start (shows delivery dates + locked bins)
- ⬜ **White boxes** = "Which bin?" decision points
- 🟢 **Light green boxes** = valid leaf (total + per-bin extension days)
- 🟩 **Bright green path** = the scenario currently selected above
- **Arrow labels:** "Service date → Bin N" with **+Nd** showing extension days added
- Tree shows **days only** (dollars in scenario table + breakdown below)
"""
                    if not hide_invalid_leaves:
                        legend_text = legend_text.replace(
                            "- 🟩 **Bright green path**",
                            "- 🔴 **Pink boxes** = invalid (event predates bin's delivery, duplicate repo, or loaded before the bin was back)\n- 🟩 **Bright green path**",
                        )
                    st.markdown(legend_text)
                except Exception as ex:
                    st.warning(f"Could not render decision tree: {ex}")

    if show_timeline:
        st.subheader("📅 Per-bin timeline (for selected scenario)")
        st.caption(
            "Each bin as a horizontal sequence: Delivery → Service → Service. "
            "Yellow = cycles with extension days. Green = within free days. "
            "Red arrows = cycles that ran over."
        )
        timeline_dot = build_timeline_view(
            selected_scenario, num_bins, delivery_dates, free_days
        )
        try:
            st.graphviz_chart(timeline_dot, **STRETCH)
        except Exception as ex:
            st.warning(f"Could not render timeline: {ex}")

    for b in range(1, int(num_bins) + 1):
        bin_fee = selected_scenario["fees"][b]
        bin_breakdown = selected_scenario["breakdowns"][b]
        bin_ext_total = sum(c["ext_days"] for c in bin_breakdown)
        header = f"Bin {b} — {fmt_fee(bin_fee, bin_ext_total, show_days)}"
        with st.expander(header):
            if not bin_breakdown:
                st.write("_No events on this bin._")
            for c in bin_breakdown:
                # "\\$" because two bare $ in one markdown line render as LaTeX
                line = (
                    f"• {c['cycle_start']} → {c['end_date']}: "
                    f"{c['cycle_days']} days, {c['ext_days']} over → "
                    f"**\\${c['fee']:,.0f}**"
                )
                if c.get("cal_days", 0) > 0:
                    line += f" · weekend/holiday waiver removed {c['cal_days']}d (\\${c['cal_fee']:,.0f})"
                if c["waived_days"] > 0:
                    line += (
                        f" · waived {c['waived_days']}d (\\${c['waived_fee']:,.0f}) vs. "
                        f"disposal date {c['disposal_date']}"
                    )
                st.write(line)

    info = cached.get("saved_msg")
    if info:
        st.info(info)
    elif not cached.get("customer", "").strip():
        st.caption("ℹ️ Customer name was blank — not saved to history.")


# ──────────────────────────────────────────────
# Render: static view of a history run
# ──────────────────────────────────────────────
def record_events_df(parsed):
    """The inputs of a saved run as typed (before any option was applied)."""
    rows = []
    for i, e in enumerate(parsed["events"]):
        fb = parsed["fixed_assignments"].get(i)
        rows.append({
            "No": i + 1, "Type": TYPE_FROM_CALC.get(e["type"], e["type"]),
            "Request": yymmdd(e["request_date"]), "Paid": yymmdd(e.get("paid_date")),
            "Loaded": yymmdd(e["loaded_date"]), "Disposal": yymmdd(e["disposal_date"]),
            "Return": yymmdd(e["return_date"]) if e["type"] != REPO else "—",
            "Fee basis": ROW_BASIS_LABEL.get(e.get("basis") or "", ""),
            "Bin (locked)": f"Bin {fb}" if fb else "",
            "Photo ID": e.get("link", ""), "Waste type": e.get("waste", ""), "Remarks": e.get("remarks", ""),
        })
    return pd.DataFrame(rows)


def render_static_view_of_record(rec, show_days):
    """Read-only display of a saved run's results."""
    try:
        results, parsed = recompute_from_record(rec)
    except TooManyScenarios as ex:
        st.warning(str(ex))
        return
    except Exception as ex:
        st.warning(f"Could not parse run: {ex}")
        return
    if not results:
        st.warning("No scenarios to show — the run has invalid data, or its filters hide every scenario.")
        return
    deliv_text = ", ".join(sorted(set(str(d) for d in parsed["delivery_dates"].values())))
    st.caption(
        f"📅 Delivery: {deliv_text} | "
        f"⏱️ Free days: {parsed['free_days']} | "
        f"💰 Rate: ${parsed['rate']:.2f}/day | "
        f"🗑️ Bins: {parsed['num_bins']} | "
        f"📋 Events: {len(parsed['events'])} | "
        f"🧮 Basis: {BASIS_LABEL.get(parsed['end_basis'], parsed['end_basis'])}"
    )
    flt = describe_filters(parsed["filters"])
    if flt:
        st.caption(f"🔎 Filters: hid scenarios where {flt}.")
    n_dry = sum(1 for e in parsed["events"] if e["type"] == DRY_RUN)
    summary = options_summary(parsed["opts"], n_dry)
    if summary:
        st.caption("⚙️ Options in effect: " + "; ".join(summary) + ".")
    m1, m2, m3 = st.columns(3)
    m1.metric("Lowest fee", fmt_fee(results[0]["total"], results[0].get("total_ext_days", 0), show_days))
    m2.metric("Highest fee", fmt_fee(results[-1]["total"], results[-1].get("total_ext_days", 0), show_days))
    m3.metric("Scenarios", f"{len(results):,}")
    show_scenario_table(results, parsed["num_bins"], show_days, make_cal(parsed["opts"]) is not None)
    with st.expander("🧾 Work orders in this run (audit)"):
        st.dataframe(record_events_df(parsed), hide_index=True, **STRETCH)


# ──────────────────────────────────────────────
# Render: compare two runs
# ──────────────────────────────────────────────
def render_record_comparison(rec_a, rec_b, show_days):
    """Side-by-side comparison of two runs."""
    try:
        results_a, parsed_a = recompute_from_record(rec_a)
        results_b, parsed_b = recompute_from_record(rec_b)
    except Exception as ex:
        st.warning(f"Could not parse runs: {ex}")
        return
    col_a, col_b = st.columns(2)
    for col, rec, results, parsed, icon in (
        (col_a, rec_a, results_a, parsed_a, "🅰️"),
        (col_b, rec_b, results_b, parsed_b, "🅱️"),
    ):
        with col:
            st.markdown(f"### {icon} {rec['customer']}")
            st.caption(f"{rec.get('version', '')}")
            if results:
                st.metric("Lowest", fmt_fee(results[0]["total"], results[0].get("total_ext_days", 0), show_days))
                st.metric("Highest", fmt_fee(results[-1]["total"], results[-1].get("total_ext_days", 0), show_days))
                st.metric("Scenarios", f"{len(results):,}")
                st.write(f"📋 Events: {len(parsed['events'])}")
                st.write(f"⏱️ Free days: {parsed['free_days']}")
                st.write(f"💰 Rate: \\${parsed['rate']:.2f}/day")
                st.write(f"🧮 Basis: {BASIS_LABEL.get(parsed['end_basis'], parsed['end_basis'])}")
            else:
                st.warning("No valid scenarios")
    st.divider()
    st.markdown("**🔍 Differences (B minus A)**")
    if results_a and results_b:
        d1, d2 = st.columns(2)
        d1.metric("Lowest", f"${results_b[0]['total'] - results_a[0]['total']:+,.0f}")
        d2.metric("Highest", f"${results_b[-1]['total'] - results_a[-1]['total']:+,.0f}")


# ──────────────────────────────────────────────
# Render: re-run a run with new terms
# ──────────────────────────────────────────────
def render_rerun_results(rec, new_free_days, new_rate, show_days):
    """Re-run a saved run with new free days / rate."""
    try:
        parsed = parse_record_to_calc_inputs(rec)
        results = _run_parsed(parsed, new_free_days, new_rate)
    except TooManyScenarios as ex:
        st.warning(str(ex))
        return
    except Exception as ex:
        st.warning(f"Could not parse run: {ex}")
        return
    if not results:
        st.warning("No valid scenarios with these new terms.")
        return
    lowest, highest = results[0]["total"], results[-1]["total"]
    orig_min, orig_max = rec.get("min_total", 0), rec.get("max_total", 0)
    st.markdown(
        f"**Original:** {parsed['free_days']} free days @ "
        f"\\${parsed['rate']:.2f}/day → \\${orig_min:,.0f} – \\${orig_max:,.0f}"
    )
    st.markdown(f"**New:** {new_free_days} free days @ \\${new_rate:.2f}/day")
    m1, m2 = st.columns(2)
    m1.metric("Lowest fee (new)", fmt_fee(lowest, results[0].get("total_ext_days", 0), show_days),
              delta=f"${lowest - orig_min:+,.0f}")
    m2.metric("Highest fee (new)", fmt_fee(highest, results[-1].get("total_ext_days", 0), show_days),
              delta=f"${highest - orig_max:+,.0f}")
    show_scenario_table(results, parsed["num_bins"], show_days, make_cal(parsed["opts"]) is not None)


# ──────────────────────────────────────────────
# Reload a run into the Calculator
# ──────────────────────────────────────────────
def calc_is_pristine():
    """True when the Calculator holds nothing worth protecting from an overwrite."""
    if S.get("last_results"):
        return False
    if (S.get("customer_name") or "").strip() or (S.get("version_name") or "").strip():
        return False
    return bool(S.get("rows_default", True))


def reload_record_to_calculator(rec):
    """Load a run's inputs AND results into the Calculator and switch to it. Must run
    inside a callback (before widgets are created) so it may set widget state."""
    parsed = parse_record_to_calc_inputs(rec)
    nb = int(parsed["num_bins"])
    fd = int(parsed["free_days"])
    S["rental_type"] = (
        "Roll-off (10 free days)" if fd == 10
        else "Short-term (3 free days)" if fd == 3 else "Custom"
    )
    if fd not in (10, 3):
        S["_custom_free_days"] = fd
    S["rate_input"] = float(parsed["rate"])
    S["num_bins_input"] = nb
    S["basis_choice"] = BASIS_LABEL.get(parsed["end_basis"], "Request date")
    flt = parsed["filters"]
    S["f_unused"], S["f_min_on"], S["f_min_n"] = flt["unused"], flt["min_on"], flt["min_n"]
    S["f_bal_on"], S["f_bal_n"] = flt["bal_on"], flt["bal_n"]
    set_opts_widgets(parsed["opts"])
    S["customer_name"] = rec.get("customer", "")
    S["version_name"] = rec.get("version", "")
    dd = {b: parsed["delivery_dates"].get(b) or min(parsed["delivery_dates"].values())
          for b in range(1, nb + 1)}
    S["staggered"] = len(set(dd.values())) > 1
    S["delivery_single"] = min(dd.values())
    for b in range(1, 6):
        S.pop(f"delivery_bin_{b}", None)
    for b, d in dd.items():
        S[f"delivery_bin_{b}"] = d
    S["delivery_last"] = dict(dd)
    rows = rows_from_record_inputs(parsed)
    sanitize_rows(rows, nb)
    S["rows"] = rows
    S["rows_default"] = False
    touch("other")
    all_results, prep = run_engine(
        dd, parsed["free_days"], parsed["rate"], parsed["events"],
        parsed["fixed_assignments"], nb, parsed["end_basis"], parsed["opts"])
    S["last_results"] = snapshot_from_run(
        prep, all_results, dd, parsed["free_days"], parsed["rate"], nb, parsed["end_basis"],
        rec.get("customer", ""),
        f"📌 Loaded from history: **{rec.get('customer', '')}** — {rec.get('version', '')}")
    S["nav"] = NAV_CALC  # the page switch happens in Python, no browser scripting involved


def do_reload_cb(rec_id):
    rec = next((h for h in load_history() if h.get("id") == rec_id), None)
    if rec is None:
        S["_flash"] = ("error", "That run no longer exists.")
        return
    try:
        reload_record_to_calculator(rec)
        S["_flash"] = ("success", f"Loaded **{rec['customer']}** — {rec['version']} into the Calculator.")
    except Exception as ex:
        S["_flash"] = ("error", f"Could not load that run: {ex}")


def request_reload_cb(rec_id):
    """'Load' button: reload straight away unless the Calculator has content."""
    if calc_is_pristine():
        do_reload_cb(rec_id)
    else:
        S["_pending_reload"] = rec_id


@st.dialog("Overwrite the Calculator?")
def confirm_reload_dialog(rec_id):
    rec = next((h for h in load_history() if h.get("id") == rec_id), None)
    name = f"**{rec['customer']}** — {rec['version']}" if rec else "this run"
    st.write(
        f"The Calculator already has inputs or results. Loading {name} will "
        "replace them (customer, run name, dates, events, terms, filters and results)."
    )
    c1, c2 = st.columns(2)
    if c1.button("Overwrite", type="primary", on_click=do_reload_cb, args=(rec_id,), **STRETCH):
        st.rerun()
    if c2.button("Cancel", **STRETCH):
        st.rerun()


@st.dialog("Confirm delete")
def confirm_delete_dialog(ids, label):
    st.write(f"Delete {label}? This cannot be undone.")
    c1, c2 = st.columns(2)
    if c1.button("Delete", type="primary", **STRETCH):
        n = delete_history_records(ids)
        S["_flash"] = ("success", f"Deleted {n} run(s).")
        st.rerun()
    if c2.button("Cancel", **STRETCH):
        st.rerun()


# ──────────────────────────────────────────────
# Events panel (table + pickers over one SSOT).
# Deliberately NOT an @st.fragment: with a fragment, clicking Calculate right after editing
# a field (which commits on blur) sent two updates from different scopes in one batch and
# Streamlit dropped the click, so the first click did nothing.
# ──────────────────────────────────────────────
def _seed(key, value):
    if key not in S:
        S[key] = value


def render_table_mode(num_bins):
    ensure_table_fresh()
    bin_options = ["Unknown"] + [f"Bin {b + 1}" for b in range(int(num_bins))]
    type_options = list(TYPE_DISPLAY.keys())

    st.info(
        "💡 **Table tips:** paste a block of dates straight from Excel — rows are added "
        "automatically. **Delete** clears the selected cell(s); with a row's checkbox ticked "
        "(it shows when you hover at the left of a row; the one in the header selects all) it "
        "deletes the row(s) instead. Dates can be "
        "`9/1`, `1-Oct`, `9/1/2026`, `2026-09-01`, `260901` or the log style `9/1 (8/30)` — the "
        "part in brackets fills **Loaded date**. **Ctrl+Enter** runs Calculate."
    )
    st.caption(
        "🔄 Entering the first date in an empty row pre-fills that row's other blank dates. "
        "Pre-filled cells follow if you change a date you typed; a cell you typed yourself is never "
        "overwritten. A blank **Return** means the bin was on site again from the **Loaded** date "
        "(a swap) — type an earlier Return date (not before Request) if the empty bin was dropped first, "
        "or a later one if the bin really was off site. Only the date for the "
        "billing basis (sidebar) is required — clear any cell you don't need."
    )

    def _editor():
        return st.data_editor(
            S["tbl_base"],
            key=f"tbl_{S['tbl_ver']}",
            on_change=on_table_edit,
            num_rows="dynamic",
            hide_index=True,
            column_order=visible_cols(),
            disabled=[COL_NO, COL_POSS],
            column_config={
                COL_NO: _cc("TextColumn", "No", align="center", width="small"),
                COL_TYPE: _cc("SelectboxColumn", COL_TYPE,
                              help="S/Rtn = service & return (bin comes back) · S/Repo = rental ends (no return "
                                   "date) · S/Swap = empty bin dropped, full bin loaded · Dry run = truck went, "
                                   "nothing loaded (see the sidebar for whether it resets the rental term)",
                              options=type_options, required=True, default="S/Rtn", width="small"),
                COL_REQUEST: _cc("TextColumn", COL_REQUEST,
                                 help="Date the customer asked for service. Same as or earlier than Loaded."),
                COL_PAID: _cc("TextColumn", COL_PAID,
                              help="Date the request was paid. Governs instead of the Request date when "
                                   "'Paid date governs' is on (sidebar). Never auto-filled."),
                COL_LOADED: _cc("TextColumn", COL_LOADED,
                                help="Date the bin left the site (for a Dry run: the date of the trip)."),
                COL_DISPOSAL: _cc("TextColumn", COL_DISPOSAL,
                                  help="Date the bin was dumped (the roll-off log date). "
                                       "Accepts 9/1, 1-Oct, 2026-09-01, 260901 or 9/1 (8/30)."),
                COL_RETURN: _cc("TextColumn", COL_RETURN,
                                help="Date the bin was back on site (starts the next cycle). Blank = the "
                                     "Loaded date. May be EARLIER than Loaded (empty bin dropped first) but not "
                                     "before the Request date; or later if the bin was off site. Blank for S/Repo."),
                COL_BIN: _cc("SelectboxColumn", COL_BIN,
                             help="Lock event to a specific bin, or leave Unknown (Delete resets it)",
                             options=bin_options, required=False, default="Unknown"),
                COL_POSS: _cc("TextColumn", COL_POSS,
                              help="Read-only. Bins that could have served this work order given the delivery "
                                   "dates and the bins already locked. A bin not listed can still be chosen "
                                   "in the Bin column as an exception (you get a warning)."),
                COL_PHOTO: _cc("TextColumn", COL_PHOTO,
                               help="Optional. Work orders with the same Photo ID are the same bin "
                                    "(e.g. the same bin seen in two driver photos) without saying which bin. "
                                    "Leave blank when unsure."),
                COL_BASIS: _cc("SelectboxColumn", COL_BASIS,
                               help="Optional. Use a different date to end THIS work order's cycle. "
                                    "Blank = the sidebar billing basis.",
                               options=list(ROW_BASIS_CHOICES), required=False),
                COL_WASTE: _cc("SelectboxColumn", COL_WASTE, help="For the audit trail only; not used in the fee maths.",
                               options=WASTE_TYPES, required=False, width="small"),
                COL_REMARKS: _cc("TextColumn", COL_REMARKS, help="For the audit trail only; not used in the fee maths.",
                                 width="medium"),
            },
            **STRETCH,
        )

    try:
        _editor()
    except Exception as ex:  # never leave the grid stuck on a bad state
        table_rebuild()
        try:
            _editor()
            st.warning(f"The table state hit an error and was rebuilt from your inputs ({type(ex).__name__}).")
        except Exception as ex2:
            st.error(f"The table could not be displayed: {ex2}. Use **Reset events**.")


def render_picker_mode(num_bins):
    ensure_picker_fresh()
    rows = S["rows"]
    v = S["pick_ver"]
    nkey = f"p{v}_n"
    _seed(nkey, len(rows))
    st.number_input("Number of events", min_value=0, max_value=60, key=nkey,
                    on_change=on_picker_resize, args=(v,),
                    help="Adds or removes events at the end of the list (use Row tools to insert in the middle).")
    all_bins = ["Unknown"] + [f"Bin {b + 1}" for b in range(int(num_bins))]
    type_options = list(TYPE_DISPLAY.keys())
    opts = current_opts()
    info = possible_info(rows)
    dkw = dict(value=None, min_value=DATE_MIN, max_value=DATE_MAX)  # value=None -> may be left blank
    for i, r in enumerate(rows):
        uid = r["uid"]

        def k(f, uid=uid):
            return f"p{v}_{uid}_{f}"
        for f, name in PICK_FIELD.items():
            if f != "ret" or has_return(r["type"]):
                _seed(k(f), r[name])
        if opts["paid_governs"]:
            _seed(k("paid"), r.get("paid"))
        _seed(k("type"), r["type"])
        _seed(k("bin"), r["bin"] if r["bin"] in all_bins else "Unknown")
        _seed(k("waste"), r.get("waste") or None)
        _seed(k("remarks"), r.get("remarks", ""))
        _seed(k("link"), r.get("link", ""))
        _seed(k("basis"), r.get("basis") or None)
        if S.get(k("waste")) not in WASTE_TYPES:   # a pick-list can never hold a value it does not offer
            S[k("waste")] = None
        if S.get(k("basis")) not in ROW_BASIS_CHOICES:
            S[k("basis")] = None
        # Bin choices: the bins that could have served this work order first; the rest stay
        # selectable (marked) so an exception can still be entered.
        poss = (info[i][0] or []) if i < len(info) else []
        if i < len(info) and info[i][2]:   # an auto / Photo-ID assigned bin is on site by definition
            poss = sorted(set(poss) | {info[i][2]}) if info[i][1] != "locked" else poss
        bin_opts = ["Unknown"] + [f"Bin {b}" for b in poss] + [b for b in all_bins[1:] if b not in {f"Bin {x}" for x in poss}]
        if S.get(k("bin")) not in bin_opts:
            S[k("bin")] = "Unknown"

        def bin_label(b, poss=poss):
            if b == "Unknown" or int(b.split()[-1]) in poss:
                return b
            return f"{b} (not on site — exception)"
        st.markdown(f"**Event {i + 1}**")
        c = st.columns([1, 1.3, 1.3, 1.3, 1.3, 1.3, 1.1])
        with c[0]:
            st.selectbox("Type", type_options, key=k("type"), on_change=on_picker_change,
                         args=(uid, "type", v))
        with c[1]:
            st.date_input("Request date", key=k("req"), on_change=on_picker_change,
                          args=(uid, "req", v), help="Same as or earlier than Loaded.", **dkw)
        with c[2]:
            if opts["paid_governs"]:
                st.date_input("Paid date", key=k("paid"), on_change=on_picker_change,
                              args=(uid, "paid", v), help="Governs instead of the Request date.", **dkw)
            else:
                st.markdown("&nbsp;", unsafe_allow_html=True)
        with c[3]:
            st.date_input("Loaded date", key=k("load"), on_change=on_picker_change,
                          args=(uid, "load", v), help="Date the bin left the site.", **dkw)
        with c[4]:
            st.date_input("Disposal date", key=k("disp"), on_change=on_picker_change,
                          args=(uid, "disp", v), help="Date the bin was dumped (roll-off log date).", **dkw)
        with c[5]:
            if has_return(r["type"]):
                st.date_input("Return date", key=k("ret"), on_change=on_picker_change,
                              args=(uid, "ret", v),
                              help="Date the bin was back on site. Blank = Loaded date. May be earlier than "
                                   "Loaded (not before Request) or later than Disposal.", **dkw)
            else:
                st.markdown("_(rental ends — no return date)_")
        with c[6]:
            st.selectbox("Bin (if known)", bin_opts, key=k("bin"), format_func=bin_label,
                         on_change=on_picker_change, args=(uid, "bin", v))
        c2 = st.columns([1.3, 2.4, 1.3, 1.3])
        with c2[0]:
            st.selectbox("Waste type", WASTE_TYPES, index=None, key=k("waste"), placeholder="—",
                         on_change=on_picker_change, args=(uid, "waste", v))
        with c2[1]:
            st.text_input("Remarks", key=k("remarks"), on_change=on_picker_change, args=(uid, "remarks", v))
        with c2[2]:
            if opts["photo_on"]:
                st.text_input("Photo ID", key=k("link"), on_change=on_picker_change, args=(uid, "link", v),
                              help="Same Photo ID = same bin.")
        with c2[3]:
            if opts["row_basis_on"]:
                st.selectbox("Fee basis", list(ROW_BASIS_CHOICES), index=None, key=k("basis"), placeholder="(sidebar)",
                             on_change=on_picker_change, args=(uid, "basis", v))
        st.divider()
    if not rows:
        st.caption("No events yet — raise **Number of events**.")


def _row_drag_label(i, r):
    e = effective_dates(r) if any(r[f] for f in DATE_FIELDS) else None
    if e is None:
        return f"{i + 1}. (empty)"
    bits = [f"{i + 1}.", r["type"], f"req {yymmdd(e['request'])}", f"loaded {yymmdd(e['loaded'])}",
            f"disp {yymmdd(e['disposal'])}"]
    if r["bin"] != "Unknown":
        bits.append(r["bin"])
    if r.get("link"):
        bits.append(f"ID {r['link']}")
    return " · ".join(bits)


def row_tools_panel(mode):
    """Sort / insert / move / drag-reorder. All of these only reorder or add rows (undoable)."""
    with st.expander("🧰 Row & column tools — sort, insert, move, drag to reorder"):
        n = len(S["rows"])
        st.markdown("**Sort rows** (blank cells go last; undoable)")
        sc = st.columns([2, 1.5, 1])
        if S.get("sort_col") not in TBL_COLS:
            S["sort_col"] = COL_REQUEST
        sc[0].selectbox("Sort by", TBL_COLS, key="sort_col")
        sc[1].radio("Order", ["Ascending", "Descending"], key="sort_dir", horizontal=True)
        sc[2].button("Sort rows", key="sort_go", on_click=sort_rows_cb, disabled=n < 2, **STRETCH)
        st.markdown("**Insert rows**")
        ic = st.columns([1, 1, 1, 1])
        for _k, _hi in (("ins_pos", max(n, 1)), ("mv_from", max(n, 1)), ("mv_to", max(n, 1)), ("ins_n", 20)):
            S[_k] = min(max(int(S.get(_k, 1)), 1), _hi)      # keep the stored value inside the current range
        ic[0].number_input("At row #", min_value=1, max_value=max(n, 1), key="ins_pos")
        ic[1].number_input("How many", min_value=1, max_value=20, key="ins_n")
        ic[2].button("⬆ Insert above", key="ins_above", on_click=insert_rows_cb, args=("above",), **STRETCH)
        ic[3].button("⬇ Insert below", key="ins_below", on_click=insert_rows_cb, args=("below",), **STRETCH)
        st.markdown("**Move a row**")
        mc = st.columns([1, 1, 1, 1])
        mc[0].number_input("Move row #", min_value=1, max_value=max(n, 1), key="mv_from")
        mc[1].number_input("To position #", min_value=1, max_value=max(n, 1), key="mv_to")
        mc[2].button("Move", key="mv_go", on_click=move_row_cb, disabled=n < 2, **STRETCH)
        if n > 1:
            st.markdown("**Drag rows** into a new order (▲▼ work on touch screens)")
            drag_sorter("row_sorter", [{"id": str(r["uid"]), "label": _row_drag_label(i, r)}
                                       for i, r in enumerate(S["rows"])],
                        apply_row_order, max_height=230)
        if mode == TABLE_MODE:
            st.markdown("**Drag columns** into a new order (switch columns on/off in the sidebar)")
            drag_sorter("col_sorter", [{"id": c, "label": c} for c in visible_cols() if c != COL_NO],
                        apply_col_order, horizontal=True, max_height=90)
        st.caption("Tip: you can also drag a column header in the table itself, but that only lasts until the "
                   "table is next re-drawn — use the list above to keep the order.")


def events_panel(num_bins, end_basis):
    st.subheader("Events")
    st.caption("**S/Rtn** = service & return (bin comes back) | **S/Repo** = service & repo (rental ends) | "
               "**S/Swap** = empty bin dropped, full bin loaded | **Dry run** = truck went, nothing loaded")
    mode = st.radio(
        "Input mode", [TABLE_MODE, PICKER_MODE], horizontal=True, key="input_mode",
        help="Both views edit the same list of events, so switching keeps your entries.",
    )
    # While the rows are still the untouched placeholders, keep them in step with
    # the delivery date.
    anchor = _anchor()
    if S["rows_default"] and S.get("rows_anchor") != anchor:
        S["rows"] = default_rows(anchor)
        S["rows_anchor"] = anchor
        touch("other", record=False)
    notices = sanitize_rows(S["rows"], int(num_bins))
    if notices:
        S["_flash_notices"] = S.get("_flash_notices", []) + notices
        touch("other", record=False)

    row_tools_panel(mode)   # before the table, so a reorder is already in SSOT when the grid is drawn
    if mode == TABLE_MODE:
        render_table_mode(num_bins)
    else:
        render_picker_mode(num_bins)

    for msg in S.pop("_flash_notices", []):
        st.info(msg)
    opts = current_opts()
    errors, warns = validate_rows(S["rows"], int(num_bins), end_basis, opts, S.get("delivery_last"))
    if errors:
        st.error("⚠️ Fix before calculating:\n\n" + "\n".join(f"- {e}" for e in errors))
    for w in warns:
        st.warning(w)
    pool = [effective_dates(r) for r in S["rows"] if any(r[f] for f in DATE_FIELDS)]
    key = {"request": "request", "loaded": "loaded"}.get(end_basis, "disposal")
    st.caption(
        "💾 Saved as (if the run name is blank): "
        f"**{make_version_name(today_guam(), [e[key] for e in pool], num_bins)}**"
    )


# ──────────────────────────────────────────────
# Calculation + results fragment
# ──────────────────────────────────────────────
def snapshot_from_run(prep, all_results, delivery_dates, free_days, rate, num_bins,
                      end_basis, customer, saved_msg=None):
    """What the results panel needs, kept in session_state. 'events' / 'fixed' are the PREPARED
    ones (the maths ran on these); the typed rows and saved inputs are never altered."""
    return {
        "all_results": all_results, "events": prep["events"], "num_bins": num_bins,
        "customer": customer, "delivery_dates": dict(delivery_dates),
        "fixed": dict(prep["fixed"]), "exempt": set(prep["exempt"]), "auto": set(prep["auto"]),
        "inert": list(prep["inert"]), "opts": prep["opts"], "cal": prep["cal"],
        "free_days": free_days, "rate": rate,
        "end_basis": end_basis, "saved_msg": saved_msg,
    }


def _recalc_cached(cached, end_basis):
    o = cached.get("opts") or normalize_opts(None)
    return calculate_allocations(
        cached["delivery_dates"], cached["free_days"], cached["rate"], cached["events"],
        cached["fixed"], cached["num_bins"], end_basis=end_basis, cal=cached.get("cal"),
        exempt=cached.get("exempt"), distinct_links=o["photo_distinct"] and o["photo_on"],
    )


def run_calculation(delivery_dates, free_days, rate, num_bins, end_basis, filters):
    rows = S["rows"]
    sanitize_rows(rows, num_bins)
    opts = current_opts()
    errors, _ = validate_rows(rows, num_bins, end_basis, opts, delivery_dates)
    if errors:
        st.error("⚠️ Fix before calculating:\n\n" + "\n".join(f"- {e}" for e in errors))
        return
    if not rows:
        st.warning("Please add at least one event before calculating.")
        return
    events, fixed, blanks = rows_to_events(rows)
    try:
        all_results, prep = run_engine(
            delivery_dates, free_days, rate, events, fixed, num_bins, end_basis, opts)
    except TooManyScenarios as ex:
        st.error(str(ex))
        return
    kept, _hidden = filter_scenarios(all_results, filters, num_bins)
    customer = (S.get("customer_name") or "").strip()
    snapshot = snapshot_from_run(prep, all_results, delivery_dates, free_days, rate,
                                 num_bins, end_basis, customer)
    if customer and all_results:
        rec = add_to_history(
            customer, (S.get("version_name") or "").strip(), delivery_dates, events,
            kept, free_days, rate, num_bins, fixed, end_basis, filters, blanks, opts,
        )
        snapshot["saved_msg"] = f"✅ Saved to history under **{customer}** as _{rec['version']}_"
    S["last_results"] = snapshot


def results_panel(show_tree, show_days, show_timeline, interchangeable,
                  hide_invalid_leaves, end_basis, filters, free_days=None, rate=None):
    cached = S.get("last_results")
    if not cached:
        return
    # The billing basis applies live to the last calculation (filters never need a recalculation).
    if cached["end_basis"] != end_basis:
        try:
            cached["all_results"] = _recalc_cached(cached, end_basis)
            cached["end_basis"] = end_basis
        except TooManyScenarios as ex:
            st.error(str(ex))
            return
    stale = []
    if free_days is not None and cached["free_days"] != free_days:
        stale.append("free days")
    if rate is not None and cached["rate"] != rate:
        stale.append("extension rate")
    if cached.get("opts") is not None and cached["opts"] != current_opts():
        stale.append("calculation options")
    if stale:
        st.warning(f"The {', '.join(stale)} changed since this calculation — press **Calculate** to refresh the results.")
    render_results(cached, filters, show_tree, show_days, show_timeline, interchangeable, hide_invalid_leaves)


# ──────────────────────────────────────────────
# History page
# ──────────────────────────────────────────────
def _run_label(h):
    return f"{h['customer']} · {h['version']}"


def _md5_short(txt):
    return hashlib.md5(txt.encode()).hexdigest()[:8]


def history_table(filtered, show_days):
    rows = []
    for h in filtered:
        dts = _record_disposal_dates(h)
        if "delivery_dates" in h:
            deliveries = sorted(set(h["delivery_dates"].values()))
            delivery_display = deliveries[0] if len(deliveries) == 1 else f"{deliveries[0]} → {deliveries[-1]}"
        else:
            delivery_display = h.get("delivery_date", "—")
        row = {
            "Customer": h["customer"],
            "Run": h["version"],
            "Delivery": delivery_display,
            "Event date range": f"{min(dts)} → {max(dts)}" if dts else "—",
            "Events": len(h["events"]),
            "Scenarios": int(h.get("scenario_count", 0)),
            "Min fee": float(h["min_total"]),
        }
        if show_days:
            row["Min days"] = int(h.get("min_ext_days") or 0)
        row["Max fee"] = float(h["max_total"])
        if show_days:
            row["Max days"] = int(h.get("max_ext_days") or 0)
        row["Logged"] = h.get("logged_at", "—")
        rows.append(row)
    cfg = {
        "Events": _cc("NumberColumn", "Events", format="%d", width="small"),
        "Scenarios": _cc("NumberColumn", "Scenarios", format="%d", width="small"),
        "Min fee": _cc("NumberColumn", "Min fee", format=DOLLAR, width="small"),
        "Max fee": _cc("NumberColumn", "Max fee", format=DOLLAR, width="small"),
        "Min days": _cc("NumberColumn", "Min days", format="%d d", width="small"),
        "Max days": _cc("NumberColumn", "Max days", format="%d d", width="small"),
    }
    df = pd.DataFrame(rows)
    for c in ("Min fee", "Max fee"):
        if (df[c] % 1 == 0).all():
            df[c] = df[c].astype(int)
    st.dataframe(df, hide_index=True, column_config=cfg, **STRETCH)


def render_backup_panel(history):
    with st.expander("💾 Backup & restore"):
        extra = S.get("_browser_extra") or []
        st.caption(
            f"Runs on the server: **{len(history):,}** · runs only this device remembers: **{len(extra):,}**. "
            "Every run is also copied into this browser, so it survives the app sleeping, a server restart "
            "or the device being switched off. A downloaded file also survives clearing the browser.")
        if extra:
            st.warning(f"{len(extra)} run(s) are in this device's backup but not on the server "
                       "(the server's file may have been reset, or another device deleted them).")
            st.button(f"Restore {len(extra)} run(s) from this device", key="restore_device",
                      on_click=restore_device_runs_cb)
        st.download_button("⬇ Download all runs (.json)", data=json.dumps(history, indent=2, default=str),
                           file_name=f"bin_calc_history_{yymmdd(today_guam())}.json", mime="application/json",
                           key="hist_download")
        up = st.file_uploader("Import a downloaded backup (adds runs that are missing)", type="json",
                              key="hist_import")
        if up is not None and S.get("_imported_id") != up.file_id:
            S["_imported_id"] = up.file_id
            try:
                added = import_runs(json.loads(up.getvalue().decode("utf-8")))
                S["_flash"] = ("success", f"Imported {added} run(s) from {up.name}.")
            except Exception as ex:
                S["_flash"] = ("error", f"Could not import that file: {ex}")
            st.rerun()


def render_history(show_days):
    st.subheader("📚 Customer history")
    history = load_history()
    if not history:
        st.info("No history yet. Run a calculation with a customer name filled in to start logging.")
        render_backup_panel(history)
        return
    customers = sorted(set(h["customer"] for h in history))
    col_pick, col_recent = st.columns([2, 1])
    with col_pick:
        selected_customer = st.selectbox("Customer", ["(all customers)"] + customers, key="hist_customer")
    with col_recent:
        recent_n = st.number_input(
            "Show last N runs", min_value=1, max_value=200, value=10, key="hist_n",
            help="Limit how many runs to show.",
        )
    if selected_customer == "(all customers)" or selected_customer not in customers:
        filtered = history
    else:
        filtered = [h for h in history if h["customer"] == selected_customer]
    filtered = list(reversed(filtered))[:int(recent_n)]  # newest first
    st.caption(f"Showing **{len(filtered):,}** run(s), newest first. Click a column header to sort.")
    history_table(filtered, show_days)

    st.subheader("🔍 View a run")
    labels = {h["id"]: _run_label(h) for h in filtered}
    sel_id = st.selectbox(
        "Run", list(labels), format_func=lambda i: labels[i],
        help="Pick a run from the table above.",
    )
    rec = next(h for h in filtered if h["id"] == sel_id)
    render_static_view_of_record(rec, show_days)

    with st.expander("🔁 Load into Calculator"):
        st.write("Fills the Calculator with this run's customer, run name, dates, events, terms, "
                 "filters and results, then switches to it.")
        st.button("Load into Calculator", type="primary", key=f"reload_{sel_id}",
                  on_click=request_reload_cb, args=(sel_id,))

    with st.expander("🔄 Re-run with new rental terms"):
        st.write("Try different free-day allowances or rates without changing the saved run.")
        rc1, rc2 = st.columns(2)
        with rc1:
            new_free_days = st.number_input(
                "New free rental days", min_value=1, value=int(rec.get("free_days", 10)),
                key=f"new_fd_{sel_id}")
        with rc2:
            new_rate = st.number_input(
                "New extension rate ($)", min_value=0.0, value=float(rec.get("rate", 50.0)),
                key=f"new_rate_{sel_id}")
        if st.button("Re-run with new terms", key=f"rerun_{sel_id}"):
            render_rerun_results(rec, new_free_days, new_rate, show_days)

    with st.expander("⚖️ Compare with another run"):
        other_ids = [i for i in labels if i != sel_id]
        if not other_ids:
            st.info("Need at least 2 runs in this list to compare.")
        else:
            other_id = st.selectbox("Compare with which run?", other_ids,
                                    format_func=lambda i: labels[i], key=f"compare_{sel_id}")
            if st.button("Show comparison", key=f"comp_btn_{sel_id}"):
                render_record_comparison(rec, next(h for h in filtered if h["id"] == other_id), show_days)

    with st.expander("📄 Raw JSON"):
        st.json(rec)

    with st.expander("🗑️ Delete runs"):
        st.caption("Nothing is deleted until you pick runs. To clear everything, choose "
                   "**(all customers)** and **(all runs)**.")
        dc1, dc2 = st.columns([1, 2])
        sel_c = dc1.multiselect("Customers", ["(all customers)"] + customers, key="del_customers",
                                placeholder="Choose customers")
        chosen = customers if "(all customers)" in sel_c else sel_c
        pool = [h for h in history if h["customer"] in chosen]
        multi = len(chosen) > 1
        run_label = {h["id"]: (_run_label(h) if multi else h["version"]) for h in pool}
        sel_r = dc2.multiselect(
            "Runs", ["(all runs)"] + list(run_label),
            format_func=lambda i: "(all runs)" if i == "(all runs)" else run_label[i],
            key="del_runs_" + _md5_short("|".join(sorted(chosen))),
            placeholder="Choose runs", disabled=not chosen)
        ids = [h["id"] for h in pool] if "(all runs)" in sel_r else [i for i in sel_r if i in run_label]
        who = "all customers" if "(all customers)" in sel_c else (
            ", ".join(chosen) if len(chosen) <= 3 else f"{len(chosen)} customers")
        if st.button(f"🗑️ Delete {len(ids):,} run(s)", disabled=not ids, key="del_go"):
            confirm_delete_dialog(ids, f"{len(ids):,} run(s) of {who}")

    render_backup_panel(history)

    pending = S.pop("_pending_reload", None)
    if pending:
        confirm_reload_dialog(pending)


# ──────────────────────────────────────────────
# Streamlit UI
# ──────────────────────────────────────────────
st.set_page_config(page_title="Bin Extension Fee Calculator", page_icon="🗑️", layout="wide")


def init_state():
    d = S.setdefault
    d("rev", 0)
    d("tbl_rev", -1)
    d("pick_rev", -1)
    d("tbl_ver", 0)
    d("pick_ver", 0)
    d("tbl_base", None)
    d("tbl_seen", None)
    d("nav", NAV_CALC)
    d("rental_type", "Roll-off (10 free days)")
    d("rate_input", 50.0)
    d("num_bins_input", 2)
    d("basis_choice", "Request date")
    d("f_unused", False)
    d("f_min_on", False)
    d("f_min_n", 2)
    d("f_bal_on", False)
    d("f_bal_n", 1)
    d("customer_name", "")
    d("version_name", "")
    d("staggered", False)
    d("input_mode", TABLE_MODE)
    d("undo", [])
    d("redo", [])
    for k, v in (("opt_dry_resets", False), ("opt_paid_governs", False), ("opt_auto_bin", True),
                 ("opt_photo_on", False), ("opt_photo_distinct", False), ("opt_row_basis", False),
                 ("opt_ret_rule", DEFAULT_OPTS["ret_rule"]), ("opt_wk_on", False),
                 ("opt_weekend_days", [5, 6]), ("opt_hol_on", False), ("opt_holidays", ""),
                 ("opt_waive_mode", DEFAULT_OPTS["waive_mode"]),
                 ("col_waste", True), ("col_remarks", True), ("col_poss", True)):
        d(k, v)
    d("col_order", [c for c in TBL_COLS if c != COL_NO])
    if "rows" not in S:
        S["rows"] = default_rows(_anchor())
        S["rows_default"] = True
        S["rows_anchor"] = _anchor()
    if S.get("_last_snap") is None:
        S["_last_snap"] = state_snap()


def inject_css():
    try:
        dark = st.context.theme.type == "dark"
    except Exception:
        dark = False
    bg = "#0e1117" if dark else "#ffffff"
    edge = "rgba(128,128,128,.35)"
    st.markdown(
        f"""<style>
        html {{ font-size: {UI_SCALE * 100:.0f}% !important; }}
        .stMainBlockContainer {{ padding-top: 3.75rem !important; }}
        /* the sticky element is the wrapper Streamlit puts around the keyed container */
        [data-testid="stLayoutWrapper"]:has(> .st-key-app_header), .st-key-app_header {{
            position: sticky; top: 3.75rem; z-index: 990; background: {bg};
        }}
        .st-key-app_header {{
            padding: .25rem 0 .35rem 0; gap: .35rem; border-bottom: 1px solid {edge};
        }}
        .st-key-app_header .app-title {{ font-size: 1.7rem; font-weight: 700; line-height: 1.35; padding-bottom: .35rem; }}
/* page switch: radio drawn as tabs */
        .st-key-app_header [data-testid="stRadio"] [role="radiogroup"] {{ gap: .3rem; }}
        .st-key-app_header [data-testid="stRadio"] label {{
            border: 1px solid {edge}; border-radius: .45rem; padding: .15rem .9rem; margin: 0;
            cursor: pointer;
        }}
        .st-key-app_header [data-testid="stRadio"] label > div:first-child {{ display: none; }}
        .st-key-app_header [data-testid="stRadio"] label:has(input:checked) {{
            background: #ff4b4b; border-color: #ff4b4b;
        }}
        .st-key-app_header [data-testid="stRadio"] label:has(input:checked) p {{ color: #fff; font-weight: 600; }}
        [data-testid="stTooltipContent"] {{ max-width: min(22rem, 88vw) !important; }}
        </style>""",
        unsafe_allow_html=True,
    )


# ──────────────────────────────────────────────
# Browser backup: saved runs + working events + undo/redo history are mirrored into this
# browser's localStorage, so they come back after the server hibernates or restarts (its
# disk may be wiped), the device is powered off, or the page is reloaded.
# ──────────────────────────────────────────────
_STORE_HTML = """<!doctype html><html><body><script>
(function () {
  var KH = "bin_calc_history_v1", KW = "bin_calc_work_v1", reported = false;
  function post(type, data) {
    window.parent.postMessage(Object.assign({isStreamlitMessage: true, type: type}, data || {}), "*");
  }
  function get(k) { try { return window.localStorage.getItem(k); } catch (e) { return null; } }
  function put(k, v) { try { window.localStorage.setItem(k, v); } catch (e) {} }
  window.addEventListener("message", function (ev) {
    var m = ev.data || {};
    if (m.type !== "streamlit:render") return;
    var a = m.args || {};
    if (typeof a.hist === "string") put(KH, a.hist);
    if (typeof a.work === "string") put(KW, a.work);
    if (!reported) {
      reported = true;
      post("streamlit:setComponentValue", {value: {ok: true, hist: get(KH), work: get(KW)}, dataType: "json"});
    }
  });
  post("streamlit:componentReady", {apiVersion: 1});
  post("streamlit:setFrameHeight", {height: 0});
})();
</script></body></html>"""


@st.cache_resource
def _store_component():
    d = os.path.join(tempfile.gettempdir(), "bin_calc_store")
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "index.html"), "w") as f:
        f.write(_STORE_HTML)
    return components.declare_component("bin_calc_store", path=d)


# Sidebar / page settings that are mirrored to the browser with the events, so a device that was
# switched off (or a session the server dropped) comes back with the same terms, dates and options.
def _ok_choice(allowed):
    return lambda v: v in allowed


def _ok_bool(v):
    return isinstance(v, bool)


def _ok_int(lo, hi):
    return lambda v: isinstance(v, int) and not isinstance(v, bool) and lo <= v <= hi


_SETTING_CHECKS = {
    "rental_type": _ok_choice(["Roll-off (10 free days)", "Short-term (3 free days)", "Custom"]),
    "rate_input": lambda v: isinstance(v, (int, float)) and not isinstance(v, bool) and v >= 0,
    "num_bins_input": _ok_int(1, 5),
    "basis_choice": _ok_choice(list(BASIS_CHOICES)),
    "f_unused": _ok_bool, "f_min_on": _ok_bool, "f_bal_on": _ok_bool,
    "f_min_n": _ok_int(1, 50), "f_bal_n": _ok_int(0, 50),
    "customer_name": lambda v: isinstance(v, str), "version_name": lambda v: isinstance(v, str),
    "staggered": _ok_bool,
    "delivery_single": lambda v: isinstance(v, date),
    "input_mode": _ok_choice([TABLE_MODE, PICKER_MODE]),
    "opt_dry_resets": _ok_bool, "opt_paid_governs": _ok_bool, "opt_auto_bin": _ok_bool,
    "opt_photo_on": _ok_bool, "opt_photo_distinct": _ok_bool, "opt_row_basis": _ok_bool,
    "opt_ret_rule": _ok_choice(list(RET_RULES)), "opt_waive_mode": _ok_choice(list(WAIVE_MODES)),
    "opt_wk_on": _ok_bool, "opt_hol_on": _ok_bool, "opt_holidays": lambda v: isinstance(v, str),
    "opt_weekend_days": lambda v: isinstance(v, list) and all(isinstance(x, int) and 0 <= x <= 6 for x in v),
    "col_waste": _ok_bool, "col_remarks": _ok_bool, "col_poss": _ok_bool,
}
for _b in range(1, 6):
    _SETTING_CHECKS[f"delivery_bin_{_b}"] = lambda v: isinstance(v, date)


def settings_snap():
    out = {}
    for k in _SETTING_CHECKS:
        if k in S:
            v = S[k]
            out[k] = {"d": v.isoformat()} if isinstance(v, date) else v
    out["_free_days"] = S.get("_free_days_now")
    out["_col_order"] = list(S.get("col_order", []))
    return out


def settings_restore(d):
    """Apply a saved settings dict. Every value is checked first: a stale or hand-edited backup
    can never put a widget into a state it cannot display."""
    n = 0
    for k, v in (d or {}).items():
        try:
            if k == "_free_days":
                if isinstance(v, int) and v >= 1:
                    S["_custom_free_days"] = v
                continue
            if k == "_col_order":
                if isinstance(v, list) and all(c in TBL_COLS for c in v):
                    S["col_order"] = [c for c in v if c != COL_NO]
                continue
            if k not in _SETTING_CHECKS:
                continue
            if isinstance(v, dict) and "d" in v:
                v = date.fromisoformat(v["d"])
            if _SETTING_CHECKS[k](v):
                S[k] = v
                n += 1
        except Exception:
            continue
    return n


def _browser_history(blob):
    try:
        h = json.loads((blob or {}).get("hist") or "null")
        return [x for x in h if isinstance(x, dict) and x.get("id")] if isinstance(h, list) else []
    except Exception:
        return []


def restore_device_runs_cb():
    """History page button: add the runs this browser remembers but the server no longer has."""
    extra = S.get("_browser_extra") or []
    with _history_lock():
        history = load_history()
        have = {h.get("id") for h in history}
        add = [x for x in extra if x.get("id") not in have]
        if add:
            save_history(history + add)
    S["_browser_extra"] = []
    S["_flash"] = ("success", f"Restored {len(add)} run(s) from this device's backup.")


def import_runs(records):
    """Merge runs from a backup file by id. -> number added."""
    records = [x for x in records if isinstance(x, dict) and x.get("id") and isinstance(x.get("events"), list)]
    with _history_lock():
        history = load_history()
        have = {h.get("id") for h in history}
        add = [x for x in records if x["id"] not in have]
        if add:
            add, _ = _migrate_history(add)
            save_history(history + add)
    return len(add)


def restore_from_browser():
    """Once per session, as soon as the browser has reported what it holds."""
    blob = S.get("bin_store")
    if S.get("_browser_ready") or not isinstance(blob, dict):
        return
    S["_browser_ready"] = True
    notes = []
    try:  # saved runs: automatic only when the server's own file came back empty
        hist = _browser_history(blob)
        server = load_history()
        if hist and not server:
            save_history(hist)
            server = hist
            notes.append(f"Restored {len(hist)} saved run(s) from this device's backup copy "
                         "(the server's history file was empty).")
        # Runs only this device remembers (server older / reset / other device wrote since): kept in the
        # backup and offered on the History page; never merged silently, so a deliberate delete stays deleted.
        have = {h.get("id") for h in server}
        S["_browser_extra"] = [x for x in hist if x["id"] not in have]
        if S["_browser_extra"]:
            notes.append(f"This device remembers {len(S['_browser_extra'])} run(s) the server does not have. "
                         "See **History → Backup**.")
    except Exception:
        pass
    try:  # working events + undo/redo + settings, only into an untouched session
        w = json.loads(blob.get("work") or "null")
        if (isinstance(w, dict) and w.get("rows") and S.get("rows_default")
                and not S.get("undo") and not S.get("redo") and not S.get("last_results")):
            def _ok(lst):
                return [x for x in (lst or []) if isinstance(x, dict) and isinstance(x.get("rows"), list)]
            S["rows"] = [_row_from_snap(x) for x in w["rows"]]
            S["rows_default"] = bool(w.get("default", False))
            S["undo"] = _ok(w.get("undo"))[-MAX_UNDO:]
            S["redo"] = _ok(w.get("redo"))[-MAX_UNDO:]
            S["_uid"] = max([S.get("_uid", 0)] + [r["uid"] for r in S["rows"]])
            if isinstance(w.get("settings"), dict):
                settings_restore(w["settings"])
            touch("other", record=False)
            if not S["rows_default"]:
                notes.append("Restored your last events, settings and undo history. Use **Reset events** to start fresh.")
    except Exception:
        pass
    if notes:
        S["_flash_notices"] = S.get("_flash_notices", []) + notes


def persist_to_browser():
    """Mount the (invisible) store; once it has reported, keep it up to date."""
    args = {}
    if S.get("_browser_ready"):
        args["work"] = json.dumps({
            "rows": state_snap()["rows"], "default": bool(S.get("rows_default")),
            "undo": S.get("undo", [])[-MAX_UNDO_SAVED:], "redo": S.get("redo", [])[-MAX_UNDO_SAVED:],
            "settings": settings_snap(),
            "saved": now_guam().isoformat(timespec="seconds"),
        }, separators=(",", ":"), default=str)
        extra = S.get("_browser_extra") or []
        sig = (_history_sig(), len(extra))
        if sig != S.get("_hist_sig_sent"):
            # The server's runs PLUS any run only this device holds: the backup never shrinks behind your back.
            args["hist"] = json.dumps(load_history() + extra, default=str, separators=(",", ":"))
            S["_hist_sig_sent"] = sig
    try:
        _store_component()(key="bin_store", default=None, **args)
    except Exception:
        pass  # the backup is a safety net; never break the app for it


init_state()
restore_from_browser()
inject_css()

with st.container(key="app_header"):
    st.markdown('<div class="app-title">🗑️ Bin Extension Fee Calculator</div>', unsafe_allow_html=True)

    # A horizontal radio styled as tabs: its value lives in session_state, so any button
    # can switch pages from Python (no browser scripting).
    _hc = st.columns([7, 1.25, 1.25], vertical_alignment="center")
    _hc[0].radio("Page", [NAV_CALC, NAV_HIST], key="nav", horizontal=True, label_visibility="collapsed")
    # Undo / redo for the events (also Ctrl+Z / Ctrl+Y, wired up by the script at the bottom of the page).
    _on_calc = (S.get("nav") or NAV_CALC) == NAV_CALC
    _hc[1].button("↶ Undo", key="undo_btn", on_click=undo_cb, disabled=not (S.get("undo") and _on_calc),
                  help=(f"Undo the last change to the events — Ctrl+Z ({len(S.get('undo', []))} step(s) available)."
                        if _on_calc else "Undo applies to the Calculator's events."), **STRETCH)
    _hc[2].button("↷ Redo", key="redo_btn", on_click=redo_cb, disabled=not (S.get("redo") and _on_calc),
                  help=(f"Redo — Ctrl+Y or Ctrl+Shift+Z ({len(S.get('redo', []))} step(s) available)."
                        if _on_calc else "Redo applies to the Calculator's events."), **STRETCH)

page = S.get("nav") or NAV_CALC
page_changed = S.get("_prev_page") != page
if page_changed:  # coming back to a page: re-seed its grids from SSOT
    S["tbl_rev"] = -1
    S["pick_rev"] = -1
    S["_prev_page"] = page

# Streamlit forgets a widget's value when the widget is not drawn in a run, and the
# browser blanks it. Only one page is drawn at a time, so re-assert the keyed widgets'
# values: every run for the page that is hidden, and once more on the run that brings a
# page back (that run is what makes the browser show the value again).
_KEEP = {
    NAV_CALC: ["customer_name", "version_name", "staggered", "delivery_single", "input_mode"]
    + [f"delivery_bin_{b}" for b in range(1, 6)],
    NAV_HIST: ["hist_customer", "hist_n"],
}
for _page, _keys in _KEEP.items():
    if _page != page or page_changed:
        for _k in _keys:
            if _k in S:
                S[_k] = S[_k]

# One-shot messages (set by callbacks / dialogs before a rerun).
_flash = S.pop("_flash", None)
if _flash:
    (st.success if _flash[0] == "success" else st.error)(_flash[1])

with st.sidebar:
    st.header("Rental Terms")
    rental_type = st.radio(
        "Rental type",
        ["Roll-off (10 free days)", "Short-term (3 free days)", "Custom"],
        key="rental_type",
        help="Pick a preset to auto-fill free days, or choose Custom to set manually.",
    )
    if rental_type == "Roll-off (10 free days)":
        default_free_days = 10
    elif rental_type == "Short-term (3 free days)":
        default_free_days = 3
    else:
        default_free_days = int(S.get("_custom_free_days", 10))
    free_days = st.number_input(
        "Free rental days per cycle",
        value=default_free_days,
        min_value=1,
        disabled=(rental_type != "Custom"),
        help="Locked unless you select Custom above.",
    )
    S["_free_days_now"] = int(free_days)   # what the browser backup remembers for Custom
    rate = st.number_input("Extension fee per day ($)", min_value=0.0, key="rate_input")
    num_bins = int(st.number_input("Number of bins on site", min_value=1, max_value=5, key="num_bins_input"))
    st.caption("Off-site days (between Loaded date and Return date) are not billed.")
    st.divider()

    st.subheader("Billing basis")
    basis_label = st.radio(
        "Extension days run to the…",
        list(BASIS_CHOICES.keys()),
        key="basis_choice",
        help="Which date ends each rental cycle. Only that date is required in the events table.",
    )
    end_basis = BASIS_CHOICES[basis_label]
    st.caption({
        "request": "Billed up to the day the customer asked for service; the wait after that is not billed.",
        "loaded": "Billed up to the day the bin left the site.",
        "disposal": "Billed up to the roll-off log (dump) date.",
    }[end_basis])
    if S.get("opt_paid_governs") and end_basis == "request":
        st.caption("💳 **Paid date governs:** the Paid date replaces the Request date here "
                   "(a work order with no Paid date falls back to its Request date).")
    st.divider()

    st.subheader("Date rules & options")
    st.caption("Options that change the numbers are saved with each run. After changing one, press Calculate.")
    st.selectbox(
        "Return date before Loaded date", list(RET_RULES), key="opt_ret_rule",
        format_func=lambda k: RET_RULES[k],
        help="Sometimes the empty bin is dropped (Return) a day before the full bin is picked up (Loaded). "
             "A Return date is never allowed before the Request date. Overlap days are the days both "
             "cycles cover; they are billed on both bins unless you start the next cycle on the Loaded date.",
    )
    st.checkbox("🔒 Auto-assign a bin when only one was on site", key="opt_auto_bin",
                help="Locks a work order to its bin when every other bin was not yet delivered (or conflicts "
                     "with a locked work order). The results are identical — it only removes impossible "
                     "choices and speeds up large batches.")
    st.checkbox("🚚 Dry run resets the rental term", key="opt_dry_resets",
                help="On: a Dry run closes the current cycle on its date and the next cycle (and free days) "
                     "starts that day, like a service. Off: a Dry run is listed but has no effect on fees.")
    st.checkbox("💳 Paid date governs (instead of Request date)", key="opt_paid_governs",
                help="Adds a Paid date column right of Request date. Where the Request date would end a "
                     "cycle, the Paid date does (Request date if no Paid date was entered). Turning this off "
                     "hides the column but keeps every date you typed.")
    st.checkbox("🧾 Choose the billing date per work order", key="opt_row_basis",
                help="Adds a Fee basis column so one work order can end on its Request date, another on its "
                     "Paid date, another on its Loaded date... in the same batch. Blank = the sidebar choice. "
                     "Turning this off ignores (but keeps) the choices.")
    st.checkbox("📷 Photo IDs link work orders to the same bin", key="opt_photo_on",
                help="Adds a Photo ID column. Work orders with the same Photo ID are treated as the same bin "
                     "(you need not know which). Leave the ID blank where you cannot tell. Turning this off "
                     "ignores (but keeps) the IDs.")
    st.checkbox("…and different Photo IDs are different bins", key="opt_photo_distinct",
                disabled=not S["opt_photo_on"],
                help="Only if the IDs identify the physical bin (e.g. a painted number). Otherwise leave off.")
    with st.expander("📆 Weekend & holiday waivers"):
        st.checkbox("Waive weekends", key="opt_wk_on")
        st.multiselect("Weekend days", list(range(7)), key="opt_weekend_days",
                       format_func=lambda i: WEEKDAY_NAMES[i], disabled=not S["opt_wk_on"])
        st.checkbox("Waive holidays", key="opt_hol_on")
        st.text_area("Holidays (one date per line, or comma-separated)", key="opt_holidays", height=90,
                     disabled=not S["opt_hol_on"],
                     help="Include the year, e.g. 261126 or 2026-11-26. A date without a year takes the year "
                          "nearest the delivery date.")
        _hol, _bad = parse_holidays(S.get("opt_holidays", ""), _anchor())
        if S["opt_hol_on"]:
            st.caption(f"{len(_hol)} holiday date(s) read.")
            if _bad:
                st.warning("Could not read: " + ", ".join(_bad))
        st.selectbox("How waived days work", list(WAIVE_MODES), key="opt_waive_mode",
                     format_func=lambda k: WAIVE_MODES[k],
                     disabled=not (S["opt_wk_on"] or S["opt_hol_on"]))
    with st.expander("🗂️ Table columns"):
        st.checkbox("Waste type", key="col_waste")
        st.checkbox("Remarks", key="col_remarks")
        st.checkbox("Possible bins", key="col_poss")
        st.caption("Paid date, Photo ID and Fee basis show up when their option above is on. "
                   "Hidden columns keep their data. Reorder columns under *Row & column tools*.")
    st.divider()

    st.subheader("Scenario filters")
    st.checkbox("🚫 Hide scenarios with an unused bin", key="f_unused",
                help="Hide any scenario in which a bin on site has no work orders.")
    st.checkbox("📉 Hide bins with too few work orders", key="f_min_on",
                help="Hide scenarios where any bin has fewer than N work orders.")
    if S["f_min_on"]:
        st.number_input("Minimum work orders per bin", min_value=1, max_value=50, key="f_min_n")
    st.checkbox("⚖️ Keep bins balanced", key="f_bal_on",
                help="Hide scenarios where the busiest and quietest bin differ by more than N work orders.")
    if S["f_bal_on"]:
        st.number_input("Max gap between busiest and quietest bin", min_value=0, max_value=50, key="f_bal_n")
    filters = normalize_filters({
        "unused": S["f_unused"], "min_on": S["f_min_on"], "min_n": S["f_min_n"],
        "bal_on": S["f_bal_on"], "bal_n": S["f_bal_n"],
    })
    st.divider()

    st.subheader("Display options")
    show_tree = st.checkbox(
        "🌳 Show decision tree",
        value=False,
        help="Tree showing all allocation possibilities (days-only labels).",
    )
    hide_invalid_leaves = st.checkbox(
        "🚫 Hide invalid leaves from tree",
        value=True,
        help="Skip branches that lead to impossible scenarios.",
        disabled=not show_tree,
    )
    show_timeline = st.checkbox(
        "📅 Show per-bin timeline",
        value=False,
        help="Alternative view: each bin as a horizontal swim lane.",
    )
    show_days = st.checkbox(
        "📊 Show days alongside dollars",
        value=True,
        help="Adds extension day counts next to dollar amounts.",
    )
    interchangeable = st.checkbox(
        "🔁 Hide equivalent permutations",
        value=True,
        help=(
            "Collapse scenarios where only the bin labels differ. "
            "Turn off if the bins are not interchangeable (e.g. different sizes)."
        ),
    )
    st.divider()
    with st.expander("⌨️ Keyboard tips"):
        st.markdown(
            """
**In the events table:**
- **Arrow keys** = move between cells
- **Enter** or just **typing** = edit the selected cell
- **Ctrl+V** = paste (adds rows as needed)
- **Delete** = clear the selected cell(s); with a row checkbox ticked it deletes the row(s)
- **Esc** = exit a cell editor

**Global shortcuts:** **Ctrl + Enter** = run Calculate · **Ctrl + Z** = undo · **Ctrl + Y** (or Ctrl + Shift + Z) = redo
"""
        )

# ──────────────────────────────────────────────
# Page: Calculator
# ──────────────────────────────────────────────
if page == NAV_CALC:
    col_a, col_b = st.columns([1, 1])
    with col_a:
        st.text_input("Customer name (leave blank to skip saving to history)", key="customer_name")
        st.text_input(
            "Run name (optional)", key="version_name",
            placeholder="Blank = auto: Run YYMMDD · Range YYMMDD–YYMMDD · N bins",
            help="Run = the day (Guam) you calculate. Range = first–last event date. "
                 "If the name already exists for this customer, (2), (3)… is added.",
        )
        bc1, bc2 = st.columns(2)
        if "last_results" in S:
            bc1.button("🗑️ Clear results", key="clear_results",
                       on_click=lambda: S.pop("last_results", None),
                       help="Remove the results below (inputs are kept)", **STRETCH)
        bc2.button("🧹 Reset events", key="reset_events", on_click=reset_events_cb,
                   help="Put the events back to the 3 placeholder rows and clear results.", **STRETCH)
    with col_b:
        staggered_delivery = st.checkbox(
            "Bins delivered on different dates?", key="staggered",
            help="Check if bins were dropped off on separate days.",
        )

    last_delivery = S.get("delivery_last") or {}
    fallback_delivery = (min(last_delivery.values()) if last_delivery
                         else today_guam() - timedelta(days=30))
    delivery_dates = {}
    if staggered_delivery:
        st.markdown("**Per-bin delivery dates:**")
        cols = st.columns(num_bins)
        for b in range(1, num_bins + 1):
            key = f"delivery_bin_{b}"
            if key not in S:
                S[key] = last_delivery.get(b, fallback_delivery)
            with cols[b - 1]:
                delivery_dates[b] = st.date_input(
                    f"Bin {b} delivery", key=key, min_value=DATE_MIN, max_value=DATE_MAX)
    else:
        if "delivery_single" not in S:
            S["delivery_single"] = fallback_delivery
        single_delivery = st.date_input(
            "Delivery date (all bins)", key="delivery_single",
            min_value=DATE_MIN, max_value=DATE_MAX)
        for b in range(1, num_bins + 1):
            delivery_dates[b] = single_delivery
    S["delivery_last"] = dict(delivery_dates)

    events_panel(num_bins, end_basis)

    calc_clicked = st.button(
        "🧮 Calculate all scenarios (or press Ctrl+Enter)",
        type="primary",
        key="calc_btn",
    )
    if calc_clicked:
        run_calculation(delivery_dates, free_days, rate, num_bins, end_basis, filters)

    results_panel(show_tree, show_days, show_timeline, interchangeable,
                  hide_invalid_leaves, end_basis, filters, free_days, rate)

    # Ctrl+Enter shortcut, plus: keep the table's scroll position when it is re-drawn
    components.html(
        """
        <script>
        (function() {
            const doc = window.parent.document;
            if (doc._gridScrollKeeper) return;
            doc._gridScrollKeeper = true;
            // Editing a date can re-seed the table, which makes Streamlit draw a fresh grid
            // that starts at the top-left. Remember the offsets and put them back.
            const saved = {gl: 0, gt: 0, pl: 0, pt: 0};
            let frozen = false, tracked = null, token = 0, queued = false;
            const grid = () => {
                const g = doc.querySelector('[data-testid="stDataFrame"]');
                return g ? g.querySelector('.dvn-scroller') : null;
            };
            const main = () => doc.querySelector('[data-testid="stMain"]')
                || doc.querySelector('section.main')
                || doc.querySelector('[data-testid="stAppViewContainer"]');
            doc.addEventListener('scroll', function(e) {
                if (frozen) return;
                const t = e.target;
                if (!t || t === doc || !t.classList) return;
                if (t.classList.contains('dvn-scroller')) {
                    if (t === grid()) { saved.gl = t.scrollLeft; saved.gt = t.scrollTop; tracked = t; }
                } else if (t === main()) {
                    saved.pl = t.scrollLeft; saved.pt = t.scrollTop;
                }
            }, true);
            const userEvents = ['wheel', 'touchstart', 'pointerdown', 'keydown'];
            function restore() {
                frozen = true;
                const my = ++token, t0 = Date.now();
                let stable = 0;
                function finish() {
                    userEvents.forEach(ev => doc.removeEventListener(ev, takeOver, true));
                    if (token === my) { frozen = false; tracked = grid(); }
                }
                function takeOver() { token++; finish(); frozen = false; tracked = grid(); }
                userEvents.forEach(ev => doc.addEventListener(ev, takeOver, {capture: true, passive: true}));
                (function step() {
                    if (token !== my) return;
                    const g = grid();
                    if (g) {
                        if (Math.abs(g.scrollLeft - saved.gl) > 1) g.scrollLeft = saved.gl;
                        if (Math.abs(g.scrollTop - saved.gt) > 1) g.scrollTop = saved.gt;
                        const m = main();
                        if (m) {
                            if (Math.abs(m.scrollTop - saved.pt) > 1) m.scrollTop = saved.pt;
                            if (Math.abs(m.scrollLeft - saved.pl) > 1) m.scrollLeft = saved.pl;
                        }
                        const ok = Math.abs(g.scrollLeft - saved.gl) <= 1 && Math.abs(g.scrollTop - saved.gt) <= 1;
                        stable = ok ? stable + 1 : 0;
                        if (stable >= 15) return finish();
                    }
                    if (Date.now() - t0 > 2500) return finish();  // no grid came back (other page): leave alone
                    requestAnimationFrame(step);
                })();
            }
            new MutationObserver(function() {
                if (queued || frozen) return;
                queued = true;
                requestAnimationFrame(function() {
                    queued = false;
                    if (tracked && !tracked.isConnected) restore();
                    else if (!tracked) tracked = grid();
                });
            }).observe(doc.body, {childList: true, subtree: true});
        })();
        (function() {
            // Ctrl+Z / Ctrl+Y (Cmd on Mac, Ctrl+Shift+Z too) press the header's Undo / Redo buttons.
            // Left alone while typing in a text box, a cell editor or a dropdown so their own undo works.
            const doc = window.parent.document;
            if (doc._undoKeysAttached) return;
            doc._undoKeysAttached = true;
            doc.addEventListener('keydown', function(e) {
                if (!(e.ctrlKey || e.metaKey) || e.altKey) return;
                const k = (e.key || '').toLowerCase();
                const redo = (k === 'y') || (k === 'z' && e.shiftKey);
                const undo = (k === 'z' && !e.shiftKey);
                if (!undo && !redo) return;
                const t = e.target;
                if (t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT' ||
                          t.isContentEditable)) return;
                const btn = doc.querySelector(redo ? '.st-key-redo_btn button' : '.st-key-undo_btn button');
                if (!btn) return;
                e.preventDefault();
                if (!btn.disabled) btn.click();
            }, true);
        })();
        (function() {
            const doc = window.parent.document;
            if (doc._ctrlEnterAttached) return;
            doc._ctrlEnterAttached = true;
            doc.addEventListener('keydown', function(e) {
                if (e.ctrlKey && e.key === 'Enter') {
                    const buttons = doc.querySelectorAll('button');
                    for (const btn of buttons) {
                        if (btn.innerText && btn.innerText.includes('Calculate all scenarios')) {
                            btn.click();
                            e.preventDefault();
                            return;
                        }
                    }
                }
            });
        })();
        </script>
        """,
        height=0,
    )
else:
    # ──────────────────────────────────────────
    # Page: History
    # ──────────────────────────────────────────
    render_history(show_days)

# Keep the browser backup current (runs on every page, after everything else).
persist_to_browser()
