import hashlib
import inspect
import json
import os
import re
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
HISTORY_FILE = "history.json"

TYPE_DISPLAY = {
    "S/Rtn": SERVICE_RETURN,
    "S/Repo": REPO,
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


def event_end_date(ev, basis):
    if basis == "request":
        return ev["request_date"]
    if basis == "loaded":
        return ev["loaded_date"]
    return ev["disposal_date"]


def fee_for_bin(bin_events, bin_delivery_date, free_days, rate_per_day,
                end_basis=BASELINE_BASIS):
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
        cycle_days = max(0, (end - cycle_start).days + 1)
        ext_days = max(0, cycle_days - free_days)
        cycle_fee = ext_days * rate_per_day

        base_end = event_end_date(ev, BASELINE_BASIS)
        base_days = max(0, (base_end - cycle_start).days + 1)
        base_ext = max(0, base_days - free_days)
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


def is_valid_assignment(events, assignment, delivery_dates):
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
            if e["loaded_date"] < bin_start:
                return False
            # [#4] A bin cannot be loaded again before it is back on site.
            if prev is not None and e["loaded_date"] < prev["return_date"]:
                return False
            prev = e
    return True


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
                          end_basis=BASELINE_BASIS):
    """Every valid way to assign the events to bins, cheapest first.

    Nothing is filtered here: filters are applied afterwards by filter_scenarios(),
    so toggling a filter never needs a recalculation and can report what it hid.
    """
    fixed_assignments = fixed_assignments or {}
    events = [dict(e, idx=i) for i, e in enumerate(events)]
    n = len(events)
    free_indices = [i for i in range(n) if i not in fixed_assignments]
    combos = int(num_bins) ** len(free_indices)
    if combos > MAX_COMBOS:
        raise TooManyScenarios(
            f"{combos:,} bin assignments to test ({num_bins} bins ^ "
            f"{len(free_indices)} unlocked events) is more than the {MAX_COMBOS:,} limit. "
            "Lock more events to a known bin or reduce the number of bins."
        )
    results = []
    for combo in product(range(1, num_bins + 1), repeat=len(free_indices)):
        assignment = dict(fixed_assignments)
        for idx, bin_num in zip(free_indices, combo):
            assignment[idx] = bin_num
        if not is_valid_assignment(events, assignment, delivery_dates):
            continue
        bins = _events_by_bin(events, assignment)
        for b in range(1, num_bins + 1):
            bins.setdefault(b, [])
        fees = {}
        breakdowns = {}
        for b in bins:
            fees[b], breakdowns[b] = fee_for_bin(
                bins[b], delivery_dates.get(b), free_days, rate_per_day, end_basis
            )
        total = sum(fees.values())
        total_ext_days = sum(c["ext_days"] for bd in breakdowns.values() for c in bd)
        waived = sum(c["waived_fee"] for bd in breakdowns.values() for c in bd)
        waived_days = sum(c["waived_days"] for bd in breakdowns.values() for c in bd)
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
        })
    results.sort(key=lambda r: (r["total"], r["total_ext_days"], r["combo"]))
    return results


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
                          delivery_dates, free_days, end_basis=BASELINE_BASIS):
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
        cycle_days = max(0, (end - cycle_start).days + 1)
        if ev["idx"] == target_idx:
            return max(0, cycle_days - free_days)
        if ev["type"] == REPO:
            return 0
        cycle_start = ev["return_date"]
    return 0


def build_decision_tree_dot(events, fixed_assignments, num_bins, delivery_dates,
                            free_days, rate_per_day, highlight_combo=None,
                            hide_invalid=False, end_basis=BASELINE_BASIS):
    free_indices = [i for i in range(len(events)) if i not in fixed_assignments]
    if not free_indices:
        return None
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
    first_service_label = events[free_indices[0]]["label"]
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
    for depth, idx in enumerate(free_indices):
        ev_label = events[idx]["label"]
        is_last = (depth == len(free_indices) - 1)
        next_frontier = {}
        for partial, parent_id in frontier.items():
            for bin_num in range(1, num_bins + 1):
                new_partial = partial + (bin_num,)
                edge_assignment = dict(fixed_assignments)
                for fi, bn in zip(free_indices[:depth + 1], new_partial):
                    edge_assignment[fi] = bn
                edge_ext = compute_edge_ext_days(
                    events, edge_assignment, idx, bin_num, delivery_dates,
                    free_days, end_basis
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
                    for fi, bn in zip(free_indices, new_partial):
                        full_assignment[fi] = bn
                    if is_valid_assignment(events, full_assignment, delivery_dates):
                        bins_map = _events_by_bin(events, full_assignment)
                        for b in range(1, num_bins + 1):
                            bins_map.setdefault(b, [])
                        per_bin_ext = {}
                        total_ext = 0
                        for b in bins_map:
                            _, bd = fee_for_bin(
                                bins_map[b], delivery_dates.get(b), free_days,
                                rate_per_day, end_basis
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
                    next_idx = free_indices[depth + 1]
                    next_lbl = events[next_idx]["label"]
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


def load_history():
    if not os.path.exists(HISTORY_FILE):
        return []
    try:
        with open(HISTORY_FILE, "r") as f:
            data = json.load(f)
        if not isinstance(data, list):
            raise ValueError("history.json is not a list")
    except Exception:
        # Keep a copy so a bad file is never silently overwritten.
        try:
            os.replace(HISTORY_FILE, HISTORY_FILE + ".bak")
        except OSError:
            pass
        return []
    data, _ = _migrate_history(data)
    return data


def save_history(entries):
    tmp = HISTORY_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump(entries, f, indent=2, default=str)
    os.replace(tmp, HISTORY_FILE)  # atomic: never leaves a half-written file


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
                   end_basis=BASELINE_BASIS, filters=None, blanks=None):
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
        "fixed_assignments": fixed_serialized,
        "events": [
            {
                "label": e["label"],
                "disposal_date": str(e["disposal_date"]),
                "request_date": str(e["request_date"]),
                "loaded_date": str(e["loaded_date"]),
                "return_date": str(e["return_date"]),
                "type": e["type"],
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
    }


def _run_parsed(parsed, free_days=None, rate=None):
    """All valid scenarios for a parsed record, filtered the way it was saved."""
    results = calculate_allocations(
        parsed["delivery_dates"],
        parsed["free_days"] if free_days is None else free_days,
        parsed["rate"] if rate is None else rate,
        parsed["events"],
        parsed["fixed_assignments"],
        parsed["num_bins"],
        end_basis=parsed["end_basis"],
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
#     that row are pre-filled from it (so a plain log date just works).
#   * After that nothing is ever overwritten by editing a different cell. Clear a
#     cell to leave it blank; blanks are treated as "same as the nearest filled date"
#     (see effective_dates).
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
# Chronological left to right; Type first because it decides whether Return exists.
TBL_COLS = [COL_NO, COL_TYPE, COL_REQUEST, COL_LOADED, COL_DISPOSAL, COL_RETURN, COL_BIN]
EDIT_COLS = [COL_TYPE, COL_REQUEST, COL_LOADED, COL_DISPOSAL, COL_RETURN, COL_BIN]
_DATE_FIELD = {COL_REQUEST: "request", COL_LOADED: "loaded", COL_DISPOSAL: "disposal", COL_RETURN: "ret"}
DATE_FIELDS = ("request", "loaded", "disposal", "ret")
FIELD_COL = {v: k for k, v in _DATE_FIELD.items()}
BASIS_NEED_LABEL = {"request": COL_REQUEST, "loaded": COL_LOADED, "disposal": COL_DISPOSAL}


def _next_uid():
    S["_uid"] = S.get("_uid", 0) + 1
    return S["_uid"]


def seed_row(r):
    """Pre-fill the blank date cells of a row from the dates it already has."""
    d, l, q = r["disposal"], r["loaded"], r["request"]
    if d is None and l is None and q is None:
        return
    if l is None:
        l = d or q
    if q is None:
        q = l
    if d is None:
        d = l or q
    r["disposal"], r["loaded"], r["request"] = d, l, q
    if r["type"] == "S/Rtn" and r["ret"] is None:
        r["ret"] = d
    if r["type"] == "S/Repo":
        r["ret"] = None


def new_row(disposal=None, rtype="S/Rtn", binsel="Unknown", placeholder=False):
    r = {
        "uid": _next_uid(),
        "disposal": disposal, "loaded": None, "request": None, "ret": None,
        "type": rtype, "bin": binsel,
        "err": {}, "raw": {},   # unreadable text typed into a cell
        "ph": placeholder,      # untouched demo row: the first date edit replaces the whole row
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
    e_r = (t or e_d) if r["type"] == "S/Rtn" else e_d
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


def touch(source):
    """Call after ANY change to SSOT. source: 'table' | 'picker' | 'other'."""
    S["rev"] += 1
    if source == "table":
        S["tbl_rev"] = S["rev"]
    elif source == "picker":
        S["pick_rev"] = S["rev"]


def sanitize_rows(rows, num_bins):
    """Never let SSOT hold anything the UI cannot render. Returns notices."""
    notices = []
    for i, r in enumerate(rows, 1):
        for f in DATE_FIELDS:
            v = r.get(f)
            if v is not None and (not isinstance(v, date) or not (DATE_MIN <= v <= DATE_MAX)):
                r[f] = None
        if r["type"] not in TYPE_DISPLAY:
            r["type"] = "S/Rtn"
        if r["type"] == "S/Repo":
            r["ret"] = None
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


def validate_rows(rows, num_bins, basis):
    """Only the date for the billing basis is required; any others are checked when filled."""
    errors, warns = [], []
    anchor = _anchor()
    need_field = BASIS_FIELD[basis]
    need_label = BASIS_NEED_LABEL[basis]
    for i, r in enumerate(rows, 1):
        for col, msg in r.get("err", {}).items():
            errors.append(f"Row {i} ({col}): {msg}")
        d, l, q, ret = r["disposal"], r["loaded"], r["request"], r["ret"]
        if r[need_field] is None:
            if row_is_empty(r):
                errors.append(f"Row {i} is empty — fill it in, or select the row and press Delete.")
            elif FIELD_COL[need_field] not in r.get("err", {}):
                errors.append(f"Row {i}: {need_label} is required (the billing basis is {need_label}).")
        if l and d and l > d:
            errors.append(f"Row {i}: Loaded date ({l}) is after the Disposal date ({d}).")
        if q and l and q > l:
            errors.append(
                f"Row {i}: Request date ({q}) must be the same as or earlier than the Loaded date ({l}).")
        elif q and d and not l and q > d:
            errors.append(
                f"Row {i}: Request date ({q}) must be the same as or earlier than the Disposal date ({d}).")
        if r["type"] == "S/Rtn" and ret:
            floor = l or q
            if floor and ret < floor:
                errors.append(f"Row {i}: Return date ({ret}) is before the Loaded date ({floor}).")
        ref = r[need_field]
        if ref and abs((ref - anchor).days) > 730:
            warns.append(f"Row {i}: {need_label} {ref} is more than 2 years from the delivery date — check the year.")
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
        })
        blanks[i] = [f for f in DATE_FIELDS if r[f] is None and not (f == "ret" and r["type"] == "S/Repo")]
        if r["bin"] != "Unknown":
            fixed[i] = int(str(r["bin"]).split()[-1])
    return events, fixed, blanks


def rows_from_record_inputs(parsed):
    """History record -> SSOT rows (keeps the cells that were left blank)."""
    rows = []
    for i, e in enumerate(parsed["events"]):
        rtype = "S/Repo" if e["type"] == REPO else "S/Rtn"
        r = new_row(None, rtype)
        r["disposal"], r["loaded"] = e["disposal_date"], e["loaded_date"]
        r["request"] = e["request_date"]
        r["ret"] = e["return_date"] if rtype == "S/Rtn" else None
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
            if s == "S/Repo":
                r["ret"] = None
                r["err"].pop(COL_RETURN, None)
                r["raw"].pop(COL_RETURN, None)
            elif r["ret"] is None:  # S/Repo -> S/Rtn: return follows the service date
                r["ret"] = r["disposal"] or r["loaded"] or r["request"]
        return
    if col == COL_BIN:
        r["bin"] = s or "Unknown"
        return
    if col == COL_RETURN and r["type"] == "S/Repo":
        return  # S/Repo has no return date; any entry is discarded
    r["err"].pop(col, None)
    r["raw"].pop(col, None)
    field = _DATE_FIELD[col]
    if s == "":
        r[field] = None
        return
    try:
        if col == COL_DISPOSAL:
            d, l = parse_log_cell(s, ref)
            r["disposal"] = d
            if l is not None:
                r["loaded"] = l  # "9/1 (8/30)": the part in brackets is the loaded date
        else:
            r[field] = parse_date_text(s, r["disposal"] or r["loaded"] or r["request"] or ref)
    except ValueError as ex:
        r["err"][col] = str(ex)
        r["raw"][col] = s


def edit_row(r, edits, ref):
    """Apply a batch of (column, value) edits to one row, then pre-fill if it was empty.

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
    for col, val in edits:
        apply_cell_edit(r, col, val, ref)
    if touched:
        r["ph"] = False
    if entered and fresh:
        seed_row(r)


def _cell_txt(r, col, field):
    if col in r["raw"]:
        return r["raw"][col]
    v = r[field]
    return v.isoformat() if isinstance(v, date) else ""


def build_view_df(rows):
    def col(values):
        return pd.Series(values, dtype=object)
    return pd.DataFrame({
        COL_NO: col([str(i) for i in range(1, len(rows) + 1)]),
        COL_TYPE: col([r["type"] for r in rows]),
        COL_REQUEST: col([_cell_txt(r, COL_REQUEST, "request") for r in rows]),
        COL_LOADED: col([_cell_txt(r, COL_LOADED, "loaded") for r in rows]),
        COL_DISPOSAL: col([_cell_txt(r, COL_DISPOSAL, "disposal") for r in rows]),
        COL_RETURN: col([_cell_txt(r, COL_RETURN, "ret") if r["type"] == "S/Rtn" else "" for r in rows]),
        COL_BIN: col([r["bin"] for r in rows]),
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
    if S.get("tbl_base") is None or S["tbl_rev"] != S["rev"] or len(S["tbl_base"]) != len(S["rows"]):
        table_rebuild()


def ensure_picker_fresh():
    if S["pick_rev"] != S["rev"]:
        S["pick_ver"] += 1
        S["pick_rev"] = S["rev"]


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
def build_scenario_table(results, num_bins, show_days):
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
    df = pd.DataFrame(rows)
    for c in [c for c in df.columns if c.endswith("Fee") or c in ("Total", "Waived")]:
        if (df[c] % 1 == 0).all():      # whole dollars: show $3,000, not $3,000.00
            df[c] = df[c].astype(int)
    return df, cfg


def show_scenario_table(results, num_bins, show_days):
    df, cfg = build_scenario_table(results, num_bins, show_days)
    st.dataframe(df, hide_index=True, column_config=cfg, **STRETCH)


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
            "loaded before its bin's delivery date, and that no bin is loaded "
            "again before its Return date."
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

    show_scenario_table(results, num_bins, show_days)

    st.subheader("📋 Scenario breakdown")
    choice = st.selectbox(
        "View detailed cycle math for scenario No:",
        list(range(1, len(results) + 1)),
    )
    selected_scenario = results[choice - 1]

    if show_tree:
        st.subheader("🌳 Decision tree")
        n_free = len([i for i in range(len(events)) if i not in fixed_assignments])
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
                end_basis=end_basis,
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
    m1, m2, m3 = st.columns(3)
    m1.metric("Lowest fee", fmt_fee(results[0]["total"], results[0].get("total_ext_days", 0), show_days))
    m2.metric("Highest fee", fmt_fee(results[-1]["total"], results[-1].get("total_ext_days", 0), show_days))
    m3.metric("Scenarios", f"{len(results):,}")
    show_scenario_table(results, parsed["num_bins"], show_days)


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
    show_scenario_table(results, parsed["num_bins"], show_days)


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
    all_results = calculate_allocations(
        dd, parsed["free_days"], parsed["rate"], parsed["events"],
        parsed["fixed_assignments"], nb, end_basis=parsed["end_basis"])
    S["last_results"] = {
        "all_results": all_results, "events": parsed["events"], "num_bins": nb,
        "customer": rec.get("customer", ""), "delivery_dates": dd,
        "fixed": parsed["fixed_assignments"], "free_days": parsed["free_days"],
        "rate": parsed["rate"], "end_basis": parsed["end_basis"],
        "saved_msg": f"📌 Loaded from history: **{rec.get('customer', '')}** — {rec.get('version', '')}",
    }
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
        "automatically. To remove rows, select them (the checkbox at the left of a row shows "
        "when you hover; the one in the header selects all) and press **Delete**. Dates can be "
        "`9/1`, `1-Oct`, `9/1/2026`, `2026-09-01`, `260901` or the log style `9/1 (8/30)` — the "
        "part in brackets fills **Loaded date**. **Ctrl+Enter** runs Calculate."
    )
    st.caption(
        "🔄 Entering the first date in an empty row pre-fills that row's other blank dates; "
        "after that nothing is ever overwritten by editing a different cell. Only the date for "
        "the billing basis (sidebar) is required — clear any cell you don't need."
    )

    def _editor():
        return st.data_editor(
            S["tbl_base"],
            key=f"tbl_{S['tbl_ver']}",
            on_change=on_table_edit,
            num_rows="dynamic",
            hide_index=True,
            column_order=TBL_COLS,
            disabled=[COL_NO],
            column_config={
                COL_NO: _cc("TextColumn", "No", align="center", width="small"),
                COL_TYPE: _cc("SelectboxColumn", COL_TYPE,
                              help="S/Rtn = bin returns; S/Repo = rental ends (no return date)",
                              options=type_options, required=True, default="S/Rtn", width="small"),
                COL_REQUEST: _cc("TextColumn", COL_REQUEST,
                                 help="Date the customer asked for service. Same as or earlier than Loaded."),
                COL_LOADED: _cc("TextColumn", COL_LOADED,
                                help="Date the bin left the site."),
                COL_DISPOSAL: _cc("TextColumn", COL_DISPOSAL,
                                  help="Date the bin was dumped (the roll-off log date). "
                                       "Accepts 9/1, 1-Oct, 2026-09-01, 260901 or 9/1 (8/30)."),
                COL_RETURN: _cc("TextColumn", COL_RETURN,
                                help="Date the bin was back on site (starts the next cycle). "
                                     "May be later than Disposal. Blank for S/Repo."),
                COL_BIN: _cc("SelectboxColumn", COL_BIN,
                             help="Lock event to a specific bin, or leave Unknown",
                             options=bin_options, required=True, default="Unknown"),
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
                    help="Adds or removes events at the end of the list.")
    bin_options = ["Unknown"] + [f"Bin {b + 1}" for b in range(int(num_bins))]
    type_options = list(TYPE_DISPLAY.keys())
    dkw = dict(value=None, min_value=DATE_MIN, max_value=DATE_MAX)  # value=None -> may be left blank
    for i, r in enumerate(rows):
        uid = r["uid"]

        def k(f, uid=uid):
            return f"p{v}_{uid}_{f}"
        for f, name in PICK_FIELD.items():
            if f != "ret" or r["type"] == "S/Rtn":
                _seed(k(f), r[name])
        _seed(k("type"), r["type"])
        _seed(k("bin"), r["bin"] if r["bin"] in bin_options else "Unknown")
        st.markdown(f"**Event {i + 1}**")
        c = st.columns([1, 1.3, 1.3, 1.3, 1.3, 1])
        with c[0]:
            st.selectbox("Type", type_options, key=k("type"), on_change=on_picker_change,
                         args=(uid, "type", v))
        with c[1]:
            st.date_input("Request date", key=k("req"), on_change=on_picker_change,
                          args=(uid, "req", v), help="Same as or earlier than Loaded.", **dkw)
        with c[2]:
            st.date_input("Loaded date", key=k("load"), on_change=on_picker_change,
                          args=(uid, "load", v), help="Date the bin left the site.", **dkw)
        with c[3]:
            st.date_input("Disposal date", key=k("disp"), on_change=on_picker_change,
                          args=(uid, "disp", v), help="Date the bin was dumped (roll-off log date).", **dkw)
        with c[4]:
            if r["type"] == "S/Rtn":
                st.date_input("Return date", key=k("ret"), on_change=on_picker_change,
                              args=(uid, "ret", v),
                              help="Date the bin was back on site. May be later than Disposal.", **dkw)
            else:
                st.markdown("_(rental ends — no return date)_")
        with c[5]:
            st.selectbox("Bin (if known)", bin_options, key=k("bin"),
                         on_change=on_picker_change, args=(uid, "bin", v))
        st.divider()
    if not rows:
        st.caption("No events yet — raise **Number of events**.")


def events_panel(num_bins, end_basis):
    st.subheader("Events")
    st.caption("**S/Rtn** = Service & return (bin comes back) | **S/Repo** = Service & repo (rental ends)")
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
        touch("other")
    notices = sanitize_rows(S["rows"], int(num_bins))
    if notices:
        S["_flash_notices"] = S.get("_flash_notices", []) + notices
        touch("other")

    if mode == TABLE_MODE:
        render_table_mode(num_bins)
    else:
        render_picker_mode(num_bins)

    for msg in S.pop("_flash_notices", []):
        st.info(msg)
    errors, warns = validate_rows(S["rows"], int(num_bins), end_basis)
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
def run_calculation(delivery_dates, free_days, rate, num_bins, end_basis, filters):
    rows = S["rows"]
    sanitize_rows(rows, num_bins)
    errors, _ = validate_rows(rows, num_bins, end_basis)
    if errors:
        st.error("⚠️ Fix before calculating:\n\n" + "\n".join(f"- {e}" for e in errors))
        return
    if not rows:
        st.warning("Please add at least one event before calculating.")
        return
    events, fixed, blanks = rows_to_events(rows)
    try:
        all_results = calculate_allocations(
            delivery_dates, free_days, rate, events, fixed, num_bins, end_basis=end_basis)
    except TooManyScenarios as ex:
        st.error(str(ex))
        return
    kept, _hidden = filter_scenarios(all_results, filters, num_bins)
    customer = (S.get("customer_name") or "").strip()
    snapshot = {
        "all_results": all_results, "events": events, "num_bins": num_bins,
        "customer": customer, "delivery_dates": dict(delivery_dates),
        "fixed": dict(fixed), "free_days": free_days, "rate": rate,
        "end_basis": end_basis, "saved_msg": None,
    }
    if customer and all_results:
        rec = add_to_history(
            customer, (S.get("version_name") or "").strip(), delivery_dates, events,
            kept, free_days, rate, num_bins, fixed, end_basis, filters, blanks,
        )
        snapshot["saved_msg"] = f"✅ Saved to history under **{customer}** as _{rec['version']}_"
    S["last_results"] = snapshot


def results_panel(show_tree, show_days, show_timeline, interchangeable,
                  hide_invalid_leaves, end_basis, filters):
    cached = S.get("last_results")
    if not cached:
        return
    # The billing basis applies live to the last calculation (filters never need a recalculation).
    if cached["end_basis"] != end_basis:
        try:
            cached["all_results"] = calculate_allocations(
                cached["delivery_dates"], cached["free_days"], cached["rate"], cached["events"],
                cached["fixed"], cached["num_bins"], end_basis=end_basis,
            )
            cached["end_basis"] = end_basis
        except TooManyScenarios as ex:
            st.error(str(ex))
            return
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


def render_history(show_days):
    st.subheader("📚 Customer history")
    history = load_history()
    if not history:
        st.info("No history yet. Run a calculation with a customer name filled in to start logging.")
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
    if "rows" not in S:
        S["rows"] = default_rows(_anchor())
        S["rows_default"] = True
        S["rows_anchor"] = _anchor()


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


init_state()
inject_css()

with st.container(key="app_header"):
    st.markdown('<div class="app-title">🗑️ Bin Extension Fee Calculator</div>', unsafe_allow_html=True)

    # A horizontal radio styled as tabs: its value lives in session_state, so any button
    # can switch pages from Python (no browser scripting).
    st.radio("Page", [NAV_CALC, NAV_HIST], key="nav", horizontal=True, label_visibility="collapsed")

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
- **Delete** = clear a cell, or delete the selected rows
- **Esc** = exit a cell editor

**Global shortcut:** **Ctrl + Enter** = run Calculate
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
                  hide_invalid_leaves, end_basis, filters)

    # Ctrl+Enter shortcut
    components.html(
        """
        <script>
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
