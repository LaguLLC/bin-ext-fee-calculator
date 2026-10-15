import streamlit as st
import pandas as pd
import hashlib
import json
import os
import re
import uuid
from datetime import date, datetime, timedelta
from itertools import product
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

# [#8] Explicit, wide date window. The old "range" error came from Streamlit's
# st.date_input default of today +/- 10 years, not from the fee logic.
DATE_MIN = date(1990, 1, 1)
DATE_MAX = date(2100, 12, 31)

# Safety valve: scenarios grow as bins ** unlocked_events.
MAX_COMBOS = 250_000
MAX_TREE_LEAVES = 400

# [#2][#4] Which event date ends an extension cycle.
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

_STREAMLIT_VERSION = tuple(
    int(x) for x in re.findall(r"\d+", st.__version__)[:2]
) or (1, 0)
STRETCH = {"width": "stretch"} if _STREAMLIT_VERSION >= (1, 50) else {"use_container_width": True}


class TooManyScenarios(ValueError):
    pass


# ──────────────────────────────────────────────
# Formatting helpers
# ──────────────────────────────────────────────
def fmt_fee(amount, ext_days=None, show_days=True):
    if show_days and ext_days is not None:
        return f"${amount:,.0f} ({ext_days}d)"
    return f"${amount:,.0f}"


def yymmdd(d):
    """[#1] YYMMDD display; accepts date or ISO string."""
    if d is None or d == "":
        return "—"
    if isinstance(d, str):
        try:
            d = date.fromisoformat(d[:10])
        except ValueError:
            return d
    return d.strftime("%y%m%d")


def iso_or_blank(d):
    return d.isoformat() if isinstance(d, date) else ""


# ──────────────────────────────────────────────
# [#4][#8] Robust date parsing for pasted / typed text
# ──────────────────────────────────────────────
# Why: the browser's date parser reads "9/1" as 2001-09-01 and silently drops the
# "(8/30)" in "9/1 (8/30)". Text cells are parsed here instead, where the year is
# inferred from context and the "(loaded)" part is kept.
_MONTHS = {m: i for i, m in enumerate(
    ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"], 1)}


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


def _parse_date_core(text, ref=None, not_after=None):
    """Parse one date. Returns a date, or None for blank. Raises ValueError on junk.

    Accepted: 2026-09-01, 2026/9/1, 9/1/2026, 9/1/26, 260901, 20260901, 9/1, Sep 1,
    Sep 1 2026, Excel serial numbers.
    """
    if text is None:
        return None
    if isinstance(text, datetime):
        return text.date()
    if isinstance(text, date):
        return text
    s = str(text).strip()
    if s == "" or s.lower() in ("nan", "nat", "none", "—", "-"):
        return None
    ref = ref or date.today()
    out = None

    m = re.fullmatch(r"(\d{4})[-/.](\d{1,2})[-/.](\d{1,2})(?:[ T].*)?", s)
    if m:
        out = date(int(m[1]), int(m[2]), int(m[3]))
    if out is None:
        m = re.fullmatch(r"(\d{1,2})[-/.](\d{1,2})[-/.](\d{4}|\d{2})", s)
        if m:
            y = int(m[3])
            y = y + 2000 if y < 100 else y
            out = date(y, int(m[1]), int(m[2]))
    if out is None and re.fullmatch(r"\d{8}", s):
        out = date(int(s[:4]), int(s[4:6]), int(s[6:]))
    if out is None and re.fullmatch(r"\d{6}", s):  # YYMMDD (house format)
        out = date(2000 + int(s[:2]), int(s[2:4]), int(s[4:]))
    if out is None:
        m = re.fullmatch(r"(\d{1,2})[-/.](\d{1,2})", s)
        if m:
            out = _closest_year(int(m[1]), int(m[2]), ref, not_after)
    if out is None:
        m = re.fullmatch(r"([A-Za-z]{3,9})\.?\s+(\d{1,2})(?:,?\s+(\d{4}))?", s)
        if m and m[1][:3].lower() in _MONTHS:
            mon = _MONTHS[m[1][:3].lower()]
            out = date(int(m[3]), mon, int(m[2])) if m[3] else _closest_year(mon, int(m[2]), ref, not_after)
    if out is None:
        m = re.fullmatch(r"(\d{1,2})\s+([A-Za-z]{3,9})\.?(?:,?\s+(\d{4}))?", s)
        if m and m[2][:3].lower() in _MONTHS:
            mon = _MONTHS[m[2][:3].lower()]
            out = date(int(m[3]), mon, int(m[1])) if m[3] else _closest_year(mon, int(m[1]), ref, not_after)
    if out is None and re.fullmatch(r"\d{5}(\.\d+)?", s):  # Excel serial
        n = int(float(s))
        if 30000 <= n <= 80000:
            out = date(1899, 12, 30) + timedelta(days=n)
    if out is None:
        raise ValueError(f"Could not read '{s}' as a date")
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
# Event dict fields (built by rows_to_events / parse_record_to_calc_inputs):
#   label, idx, type, request_date, loaded_date, disposal_date, return_date
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


def calculate_allocations(delivery_dates, free_days, rate_per_day, events,
                          fixed_assignments=None, num_bins=2,
                          end_basis=BASELINE_BASIS, require_all_bins=False):
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
        # [#9] optional filter: every bin on site must have at least one work order.
        if require_all_bins and any(not bins[b] for b in range(1, num_bins + 1)):
            continue
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
            "fees": fees,
            "breakdowns": breakdowns,
            "total": total,
            "total_ext_days": total_ext_days,
            "waived": waived,
            "waived_days": waived_days,
        })
    results.sort(key=lambda r: r["total"])
    return results


# ──────────────────────────────────────────────
# Decision tree (days-only)
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
def make_version_name(run_date, disposal_dates, num_bins):
    """[#1] Short, self-describing default: 'Run 261015 · Range 260901–260930 · 2 bins'.
    Run = the day the calculation was run. Range = first–last disposal date."""
    ds = [d for d in disposal_dates if isinstance(d, date)]
    if ds:
        rng = yymmdd(min(ds)) if min(ds) == max(ds) else f"{yymmdd(min(ds))}–{yymmdd(max(ds))}"
    else:
        rng = "no dates"
    return f"Run {yymmdd(run_date)} · Range {rng} · {int(num_bins)} bin{'s' if int(num_bins) != 1 else ''}"


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
    """Give old records an id and a version name (in memory; saved on next write)."""
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
                run = date.today()
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
    while f"{name} (v{n})" in taken:
        n += 1
    return f"{name} (v{n})"


def add_to_history(customer, version, delivery_dates, events, results,
                   free_days, rate, num_bins, fixed_assignments,
                   end_basis=BASELINE_BASIS, require_all_bins=False):
    history = load_history()
    min_ext = results[0].get("total_ext_days", 0) if results else 0
    max_ext = results[-1].get("total_ext_days", 0) if results else 0
    fixed_serialized = {str(k): int(v) for k, v in fixed_assignments.items()}
    version = unique_version_name(
        history, customer,
        version or make_version_name(date.today(), [e["disposal_date"] for e in events], num_bins),
    )
    rec = {
        "id": uuid.uuid4().hex[:12],
        "customer": customer,
        "version": version,
        "delivery_dates": {str(b): str(d) for b, d in delivery_dates.items()},
        "free_days": int(free_days),
        "rate": float(rate),
        "num_bins": int(num_bins),
        "end_basis": end_basis,
        "require_all_bins": bool(require_all_bins),
        "fixed_assignments": fixed_serialized,
        "events": [
            {
                "label": e["label"],
                "disposal_date": str(e["disposal_date"]),
                "request_date": str(e["request_date"]),
                "loaded_date": str(e["loaded_date"]),
                "return_date": str(e["return_date"]),
                "type": e["type"],
            } for e in events
        ],
        "min_total": results[0]["total"] if results else 0,
        "max_total": results[-1]["total"] if results else 0,
        "min_ext_days": min_ext,
        "max_ext_days": max_ext,
        "scenario_count": len(results),
        "logged_at": str(date.today()),
    }
    history.append(rec)
    save_history(history)
    return rec


def delete_history_records(ids=None, customer=None):
    """[#5] Delete by record ids (versions) and/or every record of a customer."""
    ids = set(ids or [])
    history = load_history()
    keep = [
        h for h in history
        if h.get("id") not in ids and not (customer is not None and h.get("customer") == customer)
    ]
    save_history(keep)
    return len(history) - len(keep)


def parse_record_to_calc_inputs(rec):
    """Convert a stored history record back into dict of calc inputs.
    Older records (no request/loaded dates) fall back to the disposal date."""
    events = []
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
    if "delivery_dates" in rec:
        delivery_dates = {
            int(k): date.fromisoformat(v)
            for k, v in rec["delivery_dates"].items()
        }
    else:
        single = date.fromisoformat(rec.get("delivery_date", str(date.today())))
        delivery_dates = {1: single, 2: single}
    free_days = rec.get("free_days", 10)
    rate = rec.get("rate", 50.0)
    num_bins = rec.get("num_bins", len(delivery_dates))
    fixed_raw = rec.get("fixed_assignments", {})
    fixed = {int(k): int(v) for k, v in fixed_raw.items()} if fixed_raw else {}
    return {
        "events": events,
        "delivery_dates": delivery_dates,
        "free_days": free_days,
        "rate": rate,
        "num_bins": num_bins,
        "fixed_assignments": fixed,
        # Legacy records were calculated on the single (disposal/haul) date.
        "end_basis": rec.get("end_basis", BASELINE_BASIS),
        "require_all_bins": bool(rec.get("require_all_bins", False)),
    }


def _run_parsed(parsed, free_days=None, rate=None):
    return calculate_allocations(
        parsed["delivery_dates"],
        parsed["free_days"] if free_days is None else free_days,
        parsed["rate"] if rate is None else rate,
        parsed["events"],
        parsed["fixed_assignments"],
        parsed["num_bins"],
        end_basis=parsed["end_basis"],
        require_all_bins=parsed["require_all_bins"],
    )


@st.cache_data(show_spinner=False, max_entries=64)
def _cached_recompute(rec_json):
    """Cached so the History tab does not recompute on every unrelated rerun."""
    rec = json.loads(rec_json)
    parsed = parse_record_to_calc_inputs(rec)
    return _run_parsed(parsed), parsed


def recompute_from_record(rec):
    """Recompute allocation results from a stored history record."""
    return _cached_recompute(json.dumps(rec, sort_keys=True, default=str))


# ──────────────────────────────────────────────
# [#7][#8] Single source of truth (SSOT) for the events
# ──────────────────────────────────────────────
# st.session_state["rows"] is the ONE copy of the events. The table and the pickers
# are only views of it: each view edits SSOT through a callback, and a view that did
# not make the last change re-seeds itself from SSOT the next time it is shown.
#
# Why the old table flickered / needed double clicks / threw errors:
#   st.data_editor's identity includes the data it is given. The old code fed the
#   edited result back in as the next input on EVERY run, so the grid was rebuilt on
#   every edit (selection lost, flicker) and stale widget state could be replayed
#   against a different table (StreamlitAPIException that survived until a hard
#   refresh). Here the grid input only changes when something has to be
#   auto-filled or normalised.
S = st.session_state

TABLE_MODE = "📋 Table (paste from Excel)"
PICKER_MODE = "🎯 Individual pickers"

COL_DEL = "Del"
COL_NO = "No"
COL_DISPOSAL = "Disposal date"
COL_REQUEST = "Request date"
COL_LOADED = "Loaded date"
COL_TYPE = "Type"
COL_RETURN = "Return date"
COL_BIN = "Bin (if known)"
TBL_COLS = [COL_DEL, COL_NO, COL_DISPOSAL, COL_REQUEST, COL_LOADED, COL_TYPE, COL_RETURN, COL_BIN]
EDIT_COLS = [COL_DISPOSAL, COL_REQUEST, COL_LOADED, COL_TYPE, COL_RETURN, COL_BIN, COL_DEL]
_DATE_FIELD = {COL_DISPOSAL: "disposal", COL_REQUEST: "request", COL_LOADED: "loaded", COL_RETURN: "ret"}


def _next_uid():
    S["_uid"] = S.get("_uid", 0) + 1
    return S["_uid"]


def new_row(disposal=None, rtype="S/Rtn", binsel="Unknown"):
    return {
        "uid": _next_uid(),
        "disposal": disposal,
        "loaded": disposal,      # default = disposal date; overwrite when it differs
        "request": disposal,     # default = loaded date; overwrite when it differs
        "type": rtype,
        "ret": disposal if rtype == "S/Rtn" else None,
        "bin": binsel,
        "load_ovr": False, "req_ovr": False, "ret_ovr": False,
        "sel": False,            # UI only: "Del" checkbox
        "err": {}, "raw": {},    # unreadable text typed into a cell
    }


def sync_row(r):
    """Apply the default-fill chain: disposal -> loaded -> request, disposal -> return."""
    if r["type"] == "S/Repo":
        r["ret"] = None
        r["ret_ovr"] = False
    elif not r["ret_ovr"]:
        r["ret"] = r["disposal"]
    if not r["load_ovr"]:
        r["loaded"] = r["disposal"]
    if not r["req_ovr"]:
        r["request"] = r["loaded"]


def default_rows(anchor):
    rows = []
    for i in range(3):
        rows.append(new_row(anchor + timedelta(days=10 * (i + 1))))
    return rows


def _anchor():
    dl = S.get("delivery_last") or {}
    return min(dl.values()) if dl else date.today() - timedelta(days=30)


def _ref_for_row(rows, pos):
    """Reference date for inferring a missing year: previous event, else delivery."""
    for j in range(pos - 1, -1, -1):
        if rows[j]["disposal"]:
            return rows[j]["disposal"]
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
    if not rows:  # the grid and pickers always need at least one event
        rows.append(new_row(_anchor() + timedelta(days=10)))
    for i, r in enumerate(rows, 1):
        for f in ("disposal", "loaded", "request", "ret"):
            v = r.get(f)
            if v is not None and (not isinstance(v, date) or not (DATE_MIN <= v <= DATE_MAX)):
                r[f] = None
        if r["type"] not in TYPE_DISPLAY:
            r["type"] = "S/Rtn"
        b = r.get("bin", "Unknown")
        if b != "Unknown":
            try:
                n = int(str(b).split()[-1])
            except ValueError:
                n = 0
            if not (1 <= n <= num_bins):
                notices.append(f"Row {i} was locked to {b} but only {num_bins} bin(s) are on site — reset to Unknown.")
                r["bin"] = "Unknown"
        sync_row(r)
    return notices


def validate_rows(rows, num_bins):
    errors, warns = [], []
    anchor = _anchor()
    for i, r in enumerate(rows, 1):
        for col, msg in r.get("err", {}).items():
            errors.append(f"Row {i} ({col}): {msg}")
        d, l, q, ret = r["disposal"], r["loaded"], r["request"], r["ret"]
        if d is None:
            if COL_DISPOSAL not in r.get("err", {}):
                errors.append(f"Row {i}: Disposal date is missing.")
            continue
        if l and l > d:
            errors.append(f"Row {i}: Loaded date ({l}) is after the Disposal date ({d}).")
        if q and l and q > l:
            errors.append(
                f"Row {i}: Request date ({q}) must be the same as or earlier than the "
                f"Loaded date ({l})."
            )
        if r["type"] == "S/Rtn" and ret and l and ret < l:
            errors.append(f"Row {i}: Return date ({ret}) is before the Loaded date ({l}).")
        if abs((d - anchor).days) > 730:
            warns.append(f"Row {i}: Disposal date {d} is more than 2 years from the delivery date — check the year.")
    return errors, warns


def rows_to_events(rows):
    """SSOT rows -> calc events (+ locked bins). Labels are made unique."""
    base_labels = []
    for r in rows:
        d, l = r["disposal"], r["loaded"]
        lab = d.strftime("%b %d")
        if l and l != d:
            lab += f" ({l.strftime('%b %d')})"
        base_labels.append(lab)
    seen, events, fixed = {}, [], {}
    for i, (r, lab) in enumerate(zip(rows, base_labels)):
        seen[lab] = seen.get(lab, 0) + 1
        label = lab if base_labels.count(lab) == 1 else f"{lab} #{seen[lab]}"
        d = r["disposal"]
        events.append({
            "label": label,
            "idx": i,
            "disposal_date": d,
            "loaded_date": r["loaded"] or d,
            "request_date": r["request"] or r["loaded"] or d,
            "return_date": (r["ret"] or d) if r["type"] == "S/Rtn" else d,
            "type": TYPE_DISPLAY.get(r["type"], SERVICE_RETURN),
        })
        if r["bin"] != "Unknown":
            fixed[i] = int(str(r["bin"]).split()[-1])
    return events, fixed


def rows_from_record_inputs(parsed):
    """History record -> SSOT rows (keeps request/loaded/return overrides)."""
    rows = []
    for i, e in enumerate(parsed["events"]):
        rtype = "S/Repo" if e["type"] == REPO else "S/Rtn"
        r = new_row(e["disposal_date"], rtype)
        r["loaded"] = e["loaded_date"]
        r["load_ovr"] = e["loaded_date"] != e["disposal_date"]
        r["request"] = e["request_date"]
        r["req_ovr"] = e["request_date"] != e["loaded_date"]
        if rtype == "S/Rtn":
            r["ret"] = e["return_date"]
            r["ret_ovr"] = e["return_date"] != e["disposal_date"]
        if i in parsed["fixed_assignments"]:
            r["bin"] = f"Bin {parsed['fixed_assignments'][i]}"
        sync_row(r)
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
    if isinstance(x, (bool,)):
        return x
    if hasattr(x, "item"):
        try:
            x = x.item()
        except Exception:
            pass
    return x.strip() if isinstance(x, str) else x


def apply_cell_edit(r, col, val, ref):
    """Apply one edited cell to an SSOT row. Returns True if it was a data edit
    (False for the UI-only Del checkbox)."""
    if col == COL_DEL:
        r["sel"] = bool(val)
        return False
    s = "" if val is None else str(val).strip()
    if col == COL_TYPE:
        if s in TYPE_DISPLAY:
            r["type"] = s
        sync_row(r)
        return True
    if col == COL_BIN:
        r["bin"] = s or "Unknown"
        return True
    r["err"].pop(col, None)
    r["raw"].pop(col, None)
    if col == COL_RETURN and r["type"] == "S/Repo":
        sync_row(r)  # S/Repo has no return date; any entry is discarded
        return True
    key = _DATE_FIELD[col]
    try:
        if col == COL_DISPOSAL:
            d, l = parse_log_cell(s, ref) if s else (None, None)
            r["disposal"] = d
            if l is not None:
                r["loaded"], r["load_ovr"] = l, (l != d)
            elif r["load_ovr"] and d and r["loaded"] and r["loaded"] > d:
                r["load_ovr"] = False  # a fresh log date replaces an older "(loaded)" part
        else:
            d = parse_date_text(s, r["disposal"] or ref) if s else None
            ovr = {"request": "req_ovr", "loaded": "load_ovr", "ret": "ret_ovr"}[key]
            if d is None:
                r[ovr] = False  # blank = back to the default
            else:
                r[key] = d
                default = {"request": r["loaded"], "loaded": r["disposal"], "ret": r["disposal"]}[key]
                r[ovr] = (d != default)
    except ValueError as ex:
        r["err"][col] = str(ex)
        r["raw"][col] = s
    sync_row(r)
    return True


def _cell_txt(r, col, field):
    if col in r["raw"]:
        return r["raw"][col]
    v = r[field]
    return v.isoformat() if isinstance(v, date) else ""


def build_view_df(rows):
    return pd.DataFrame({
        COL_DEL: pd.Series([bool(r["sel"]) for r in rows], dtype=bool),
        COL_NO: pd.Series(list(range(1, len(rows) + 1)), dtype="int64"),
        COL_DISPOSAL: pd.Series([_cell_txt(r, COL_DISPOSAL, "disposal") for r in rows], dtype=object),
        COL_REQUEST: pd.Series([_cell_txt(r, COL_REQUEST, "request") for r in rows], dtype=object),
        COL_LOADED: pd.Series([_cell_txt(r, COL_LOADED, "loaded") for r in rows], dtype=object),
        COL_TYPE: pd.Series([r["type"] for r in rows], dtype=object),
        COL_RETURN: pd.Series([_cell_txt(r, COL_RETURN, "ret") if r["type"] == "S/Rtn" else "" for r in rows], dtype=object),
        COL_BIN: pd.Series([r["bin"] for r in rows], dtype=object),
    })[TBL_COLS]


def _same_view(a, b):
    if len(a) != len(b):
        return False
    for col in TBL_COLS:
        for x, y in zip(a[col].tolist(), b[col].tolist()):
            if _norm_cell(x) != _norm_cell(y):
                return False
    return True


def table_rebuild():
    S["tbl_base"] = build_view_df(S["rows"])
    S["tbl_seen"] = S["tbl_base"].copy()
    S["tbl_ver"] += 1
    S["tbl_rev"] = S["rev"]


def on_table_edit():
    """data_editor callback: fold the grid's edits into SSOT."""
    base, seen, rows = S.get("tbl_base"), S.get("tbl_seen"), S["rows"]
    if base is None or seen is None or len(base) != len(rows):
        table_rebuild()
        return
    delta = S.get(f"tbl_{S['tbl_ver']}") or {}
    edits = delta.get("edited_rows", {}) if isinstance(delta, dict) else {}
    eff = base.copy()
    for pos_s, changes in edits.items():
        pos = int(pos_s)
        if not (0 <= pos < len(eff)):
            continue
        for col, val in changes.items():
            if col in eff.columns and col != COL_NO:
                if col == COL_DEL:
                    eff.at[pos, col] = bool(val)
                else:
                    eff.at[pos, col] = "" if val is None else str(val)
    data_edit = False
    for pos in range(len(rows)):
        for col in EDIT_COLS:
            new, old = _norm_cell(eff.at[pos, col]), _norm_cell(seen.at[pos, col])
            if new != old:
                if apply_cell_edit(rows[pos], col, new, _ref_for_row(rows, pos)):
                    data_edit = True
    if data_edit:
        S["rows_default"] = False
    view = build_view_df(rows)
    if _same_view(view, eff):
        S["tbl_seen"] = eff          # nothing to auto-fill: keep the grid as is
    else:
        S["tbl_base"] = view         # auto-fill / normalise: re-seed the grid once
        S["tbl_seen"] = view.copy()
        S["tbl_ver"] += 1
    touch("table")


def ensure_table_fresh():
    if S.get("tbl_base") is None or S["tbl_rev"] != S["rev"] or len(S["tbl_base"]) != len(S["rows"]):
        table_rebuild()


def ensure_picker_fresh():
    if S["pick_rev"] != S["rev"]:
        S["pick_ver"] += 1
        S["pick_rev"] = S["rev"]


# ---- structure changes (shared by both views) ----
def _next_event_date():
    rows = S["rows"]
    for r in reversed(rows):
        if r["disposal"]:
            return r["disposal"] + timedelta(days=10)
    return _anchor() + timedelta(days=10)


def set_event_count(n):
    n = max(1, int(n))
    rows = S["rows"]
    while len(rows) < n:
        rows.append(new_row(_next_event_date()))
    del rows[n:]
    S["rows_default"] = False
    touch("other")


def add_row_cb():
    set_event_count(len(S["rows"]) + 1)


def delete_selected_cb():
    S["rows"] = [r for r in S["rows"] if not r["sel"]] or [new_row(_anchor() + timedelta(days=10))]
    S["rows_default"] = False
    touch("other")


def clear_selection_cb():
    for r in S["rows"]:
        r["sel"] = False
    touch("other")


def reset_events_cb():
    """[#8] Hard reset of the event inputs without a browser refresh."""
    S["rows"] = default_rows(_anchor())
    S["rows_anchor"] = _anchor()
    S["rows_default"] = True
    S["_flash_notices"] = []
    S.pop("last_results", None)
    touch("other")


def add_pasted_rows_cb():
    """Append rows from text pasted out of the roll-off log (one date per line;
    only the first tab-separated column is read)."""
    text = S.get("paste_box", "")
    rows, problems, added = S["rows"], [], 0
    if S.get("rows_default"):
        rows.clear()  # replace the untouched placeholder rows
    for ln, line in enumerate(text.splitlines(), 1):
        cell = line.split("\t")[0].strip()
        if not cell:
            continue
        try:
            ref = rows[-1]["disposal"] if rows and rows[-1]["disposal"] else _anchor()
            d, l = parse_log_cell(cell, ref)
        except ValueError as ex:
            problems.append(f"Pasted line {ln}: {ex}")
            continue
        if d is None:
            continue
        r = new_row(d)
        if l is not None:
            r["loaded"], r["load_ovr"] = l, (l != d)
        sync_row(r)
        rows.append(r)
        added += 1
    if not rows:
        rows.append(new_row(_anchor() + timedelta(days=10)))
    S["rows_default"] = False
    S["paste_box"] = ""
    S["_flash_notices"] = problems + ([f"Added {added} row(s) from the pasted text."] if added else [])
    touch("other")


# ---- picker callbacks ----
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
    if field == "disp" and isinstance(val, date):
        r["disposal"] = val
        if r["load_ovr"] and r["loaded"] and r["loaded"] > val:
            r["load_ovr"] = False
    elif field == "load" and isinstance(val, date):
        r["loaded"], r["load_ovr"] = val, (val != r["disposal"])
    elif field == "req" and isinstance(val, date):
        r["request"], r["req_ovr"] = val, (val != r["loaded"])
    elif field == "ret" and isinstance(val, date):
        r["ret"], r["ret_ovr"] = val, (val != r["disposal"])
    elif field == "type" and val in TYPE_DISPLAY:
        r["type"] = val
        S.pop(f"p{v}_{uid}_ret", None)
    elif field == "bin":
        r["bin"] = val or "Unknown"
    sync_row(r)
    S["rows_default"] = False
    # push auto-filled values into the sibling widgets so they show the new defaults
    for f, v_ in (("load", r["loaded"]), ("req", r["request"]), ("ret", r["ret"])):
        k = f"p{v}_{uid}_{f}"
        if k in S and v_ is not None:
            S[k] = v_
    touch("picker")


# ──────────────────────────────────────────────
# Rendering helpers: scenario table
# ──────────────────────────────────────────────
def build_scenario_rows(results, num_bins, show_days, include_waived=True):
    table_rows = []
    for i, r in enumerate(results, 1):
        row = {"#": i}
        for b in range(1, int(num_bins) + 1):
            services_list = r["assignment"][b]
            row[f"Bin {b}"] = ", ".join(services_list) if services_list else "(none)"
        for b in range(1, int(num_bins) + 1):
            bin_fee = r["fees"][b]
            bin_ext = sum(c["ext_days"] for c in r["breakdowns"][b])
            row[f"Bin {b} Fee"] = fmt_fee(bin_fee, bin_ext, show_days)
        row["Total"] = fmt_fee(r["total"], r.get("total_ext_days", 0), show_days)
        if include_waived:
            # [#10] how much the chosen date basis removes vs. billing to the disposal date
            row["Waived"] = fmt_fee(r.get("waived", 0), r.get("waived_days", 0), show_days)
        table_rows.append(row)
    return table_rows


def basis_caption(end_basis):
    label = BASIS_LABEL.get(end_basis, end_basis)
    if end_basis == BASELINE_BASIS:
        return f"Extension days run to the **{label}** (no waiver applied)."
    return (
        f"Extension days run to the **{label}**. **Waived** = fee if billed to the "
        f"Disposal date − fee on the {label}."
    )


# ──────────────────────────────────────────────
# Render: full results (for calculator)
# ──────────────────────────────────────────────
def render_results(cached, show_tree, show_days, show_timeline, interchangeable,
                   hide_invalid_leaves):
    results = cached["results"]
    events = cached["events"]
    num_bins = cached["num_bins"]
    delivery_dates = cached["delivery_dates"]
    fixed_assignments = cached["fixed"]
    free_days = cached["free_days"]
    rate_per_day = cached["rate"]
    end_basis = cached["end_basis"]

    if not results:
        if cached.get("require_all_bins"):
            st.error(
                "No scenarios left: every scenario leaves at least one bin without a "
                "work order. Turn off **Hide scenarios with an empty bin** in the sidebar to see them."
            )
        else:
            st.error(
                "No valid scenarios found. Check that each bin has at most one "
                "S/Repo (and it's the last event for that bin), that no event was "
                "loaded before its bin's delivery date, and that no bin is loaded "
                "again before its Return date."
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
    msg = f"Found {len(results)} valid scenario(s) across {len(events)} event(s)."
    if removed_count > 0:
        msg += (
            f" Hid {removed_count} equivalent permutation(s) "
            "(same figures and event groupings — only bin labels differ)."
        )
    st.success(msg)
    st.caption(basis_caption(end_basis))

    lowest = results[0]["total"]
    highest = results[-1]["total"]
    spread = highest - lowest
    lowest_ext = results[0].get("total_ext_days", 0)
    highest_ext = results[-1].get("total_ext_days", 0)
    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Lowest total fee", fmt_fee(lowest, lowest_ext, show_days))
    m2.metric("Highest total fee", fmt_fee(highest, highest_ext, show_days))
    m3.metric("Range", f"${spread:,.0f}")
    m4.metric("Waived (lowest scenario)",
              fmt_fee(results[0].get("waived", 0), results[0].get("waived_days", 0), show_days))

    st.dataframe(build_scenario_rows(results, num_bins, show_days), **STRETCH)

    st.subheader("📋 Scenario breakdown")
    choice = st.selectbox(
        "View detailed cycle math for scenario:",
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
# Render: static view of a history record
# ──────────────────────────────────────────────
def render_static_view_of_record(rec, show_days):
    """Read-only display of a saved history record's results."""
    try:
        results, parsed = recompute_from_record(rec)
    except TooManyScenarios as ex:
        st.warning(str(ex))
        return
    except Exception as ex:
        st.warning(f"Could not parse record: {ex}")
        return
    if not results:
        st.warning("Could not recompute results — original record may have invalid data.")
        return
    deliv_strs = sorted(set(str(d) for d in parsed["delivery_dates"].values()))
    deliv_text = ", ".join(deliv_strs)
    st.caption(
        f"📅 Delivery: {deliv_text} | "
        f"⏱️ Free days: {parsed['free_days']} | "
        f"💰 Rate: ${parsed['rate']:.2f}/day | "
        f"🗑️ Bins: {parsed['num_bins']} | "
        f"📋 Events: {len(parsed['events'])} | "
        f"🧮 Basis: {BASIS_LABEL.get(parsed['end_basis'], parsed['end_basis'])}"
    )
    lowest = results[0]["total"]
    highest = results[-1]["total"]
    lowest_ext = results[0].get("total_ext_days", 0)
    highest_ext = results[-1].get("total_ext_days", 0)
    m1, m2, m3 = st.columns(3)
    m1.metric("Lowest fee", fmt_fee(lowest, lowest_ext, show_days))
    m2.metric("Highest fee", fmt_fee(highest, highest_ext, show_days))
    m3.metric("Scenarios", len(results))
    st.dataframe(build_scenario_rows(results, parsed["num_bins"], show_days), **STRETCH)


# ──────────────────────────────────────────────
# Render: compare two records
# ──────────────────────────────────────────────
def render_record_comparison(rec_a, rec_b, show_days):
    """Side-by-side comparison of two records."""
    try:
        results_a, parsed_a = recompute_from_record(rec_a)
        results_b, parsed_b = recompute_from_record(rec_b)
    except Exception as ex:
        st.warning(f"Could not parse records: {ex}")
        return
    col_a, col_b = st.columns(2)
    for col, rec, results, parsed, icon in (
        (col_a, rec_a, results_a, parsed_a, "🅰️"),
        (col_b, rec_b, results_b, parsed_b, "🅱️"),
    ):
        with col:
            st.markdown(f"### {icon} {rec['customer']}")
            st.caption(f"{rec.get('version', '')} · Logged: {rec.get('logged_at', '—')}")
            if results:
                st.metric("Lowest", fmt_fee(results[0]["total"], results[0].get("total_ext_days", 0), show_days))
                st.metric("Highest", fmt_fee(results[-1]["total"], results[-1].get("total_ext_days", 0), show_days))
                st.metric("Scenarios", len(results))
                st.write(f"📋 Events: {len(parsed['events'])}")
                st.write(f"⏱️ Free days: {parsed['free_days']}")
                st.write(f"💰 Rate: ${parsed['rate']:.2f}/day")
                st.write(f"🧮 Basis: {BASIS_LABEL.get(parsed['end_basis'], parsed['end_basis'])}")
            else:
                st.warning("No valid scenarios")
    st.divider()
    st.markdown("**🔍 Differences (B minus A)**")
    if results_a and results_b:
        diff_lowest = results_b[0]["total"] - results_a[0]["total"]
        diff_highest = results_b[-1]["total"] - results_a[-1]["total"]
        d1, d2 = st.columns(2)
        d1.metric("Lowest", f"${diff_lowest:+,.0f}")
        d2.metric("Highest", f"${diff_highest:+,.0f}")


# ──────────────────────────────────────────────
# Render: re-run a record with new terms
# ──────────────────────────────────────────────
def render_rerun_results(rec, new_free_days, new_rate, show_days):
    """Re-run a record with new free days / rate."""
    try:
        parsed = parse_record_to_calc_inputs(rec)
        results = _run_parsed(parsed, new_free_days, new_rate)
    except TooManyScenarios as ex:
        st.warning(str(ex))
        return
    except Exception as ex:
        st.warning(f"Could not parse record: {ex}")
        return
    if not results:
        st.warning("No valid scenarios with these new terms.")
        return
    lowest = results[0]["total"]
    highest = results[-1]["total"]
    lowest_ext = results[0].get("total_ext_days", 0)
    highest_ext = results[-1].get("total_ext_days", 0)
    orig_min = rec.get("min_total", 0)
    orig_max = rec.get("max_total", 0)
    st.markdown(
        f"**Original:** {parsed['free_days']} free days @ "
        f"\\${parsed['rate']:.2f}/day → \\${orig_min:,.0f} – \\${orig_max:,.0f}"
    )
    st.markdown(f"**New:** {new_free_days} free days @ \\${new_rate:.2f}/day")
    diff_low = lowest - orig_min
    diff_high = highest - orig_max
    m1, m2 = st.columns(2)
    m1.metric("Lowest fee (new)", fmt_fee(lowest, lowest_ext, show_days), delta=f"${diff_low:+,.0f}")
    m2.metric("Highest fee (new)", fmt_fee(highest, highest_ext, show_days), delta=f"${diff_high:+,.0f}")
    st.dataframe(build_scenario_rows(results, parsed["num_bins"], show_days), **STRETCH)


# ──────────────────────────────────────────────
# [#1] Reload a record into the calculator
# ──────────────────────────────────────────────
def calc_is_pristine():
    """True when the Calculator holds nothing worth protecting from an overwrite."""
    if S.get("last_results"):
        return False
    if (S.get("customer_name") or "").strip() or (S.get("version_name") or "").strip():
        return False
    return bool(S.get("rows_default", True))


def reload_record_to_calculator(rec):
    """Load a record's inputs AND results into the Calculator. Must run inside a
    callback (before widgets are created) so it may set widget state."""
    parsed = parse_record_to_calc_inputs(rec)
    nb = int(parsed["num_bins"])
    # sidebar terms
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
    S["hide_empty_bins"] = bool(parsed["require_all_bins"])
    # header inputs
    S["customer_name"] = rec.get("customer", "")
    S["version_name"] = ""
    dd = {b: parsed["delivery_dates"].get(b) or min(parsed["delivery_dates"].values())
          for b in range(1, nb + 1)}
    S["staggered"] = len(set(dd.values())) > 1
    S["delivery_single"] = min(dd.values())
    for b in range(1, 6):
        S.pop(f"delivery_bin_{b}", None)
    for b, d in dd.items():
        S[f"delivery_bin_{b}"] = d
    S["delivery_last"] = dict(dd)
    # events (SSOT) + results snapshot
    rows = rows_from_record_inputs(parsed)
    sanitize_rows(rows, nb)
    S["rows"] = rows
    S["rows_default"] = False
    touch("other")
    results = _run_parsed(parsed)
    S["last_results"] = {
        "results": results, "events": parsed["events"], "num_bins": nb,
        "customer": rec.get("customer", ""), "delivery_dates": dd,
        "fixed": parsed["fixed_assignments"], "free_days": parsed["free_days"],
        "rate": parsed["rate"], "end_basis": parsed["end_basis"],
        "require_all_bins": parsed["require_all_bins"],
        "saved_msg": f"📌 Loaded from history: **{rec.get('customer', '')}** — {rec.get('version', '')}",
    }


def do_reload_cb(rec_id):
    rec = next((h for h in load_history() if h.get("id") == rec_id), None)
    if rec is None:
        S["_flash"] = ("error", "That record no longer exists.")
        return
    try:
        reload_record_to_calculator(rec)
        S["_flash"] = ("success", f"Loaded **{rec['customer']}** — {rec['version']} into the Calculator.")
        S["_goto_calc"] = True
    except Exception as ex:
        S["_flash"] = ("error", f"Could not load that record: {ex}")


def request_reload_cb(rec_id):
    """'Load' button: reload straight away unless the Calculator has content."""
    if calc_is_pristine():
        do_reload_cb(rec_id)
    else:
        S["_pending_reload"] = rec_id


@st.dialog("Overwrite the Calculator?")
def confirm_reload_dialog(rec_id):
    rec = next((h for h in load_history() if h.get("id") == rec_id), None)
    name = f"**{rec['customer']}** — {rec['version']}" if rec else "this record"
    st.write(
        f"The Calculator already has inputs or results. Loading {name} will "
        "replace them (the customer, dates, events, terms and results)."
    )
    c1, c2 = st.columns(2)
    if c1.button("Overwrite", type="primary", on_click=do_reload_cb, args=(rec_id,), **STRETCH):
        st.rerun()
    if c2.button("Cancel", **STRETCH):
        st.rerun()


@st.dialog("Confirm delete")
def confirm_delete_dialog(ids, customer, label):
    st.write(f"Delete {label}? This cannot be undone.")
    c1, c2 = st.columns(2)
    if c1.button("Delete", type="primary", **STRETCH):
        n = delete_history_records(ids=ids, customer=customer)
        S["_flash"] = ("success", f"Deleted {n} record(s).")
        st.rerun()
    if c2.button("Cancel", **STRETCH):
        st.rerun()


# ──────────────────────────────────────────────
# Events panel (table + pickers over one SSOT). Runs as a fragment so editing a
# cell reruns only this block instead of the whole page. [#8]
# ──────────────────────────────────────────────
def _seed(key, value):
    if key not in S:
        S[key] = value


def render_table_mode(num_bins):
    ensure_table_fresh()
    rows = S["rows"]
    n_sel = sum(1 for r in rows if r["sel"])
    bin_options = ["Unknown"] + [f"Bin {b + 1}" for b in range(int(num_bins))]
    type_options = list(TYPE_DISPLAY.keys())

    t1, t2, _ = st.columns([1, 1.6, 4])
    t1.button("➕ Add row", on_click=add_row_cb, key="tbl_add", **STRETCH)
    t2.button(f"🗑️ Delete ticked ({n_sel})", on_click=delete_selected_cb, key="tbl_del",
              disabled=(n_sel == 0), **STRETCH)

    st.info(
        "💡 **Table tips:** click a cell once to select it, press **Enter** to edit, type, then "
        "**Enter** again — Streamlit's grid has no one-click edit; **Individual pickers** open "
        "on a single click. Dates can be typed or pasted as `9/1`, `9/1/2026`, "
        "`2026-09-01`, `260901` or the log style `9/1 (8/30)` — the part in parentheses fills "
        "**Loaded date**. Press **Ctrl+Enter** anytime to run Calculate."
    )
    st.caption(
        "🔄 **Auto-fill (live):** Loaded date follows Disposal date, Request date follows Loaded "
        "date, and an S/Rtn Return date follows Disposal date — until you overwrite them. "
        "Clear a cell to go back to its default. S/Repo has no Return date."
    )
    with st.expander("📥 Paste dates from the roll-off log (adds rows)"):
        st.text_area(
            "One date per line (only the first column is read)",
            key="paste_box", height=110,
            placeholder="9/1 (8/30)\n9/15\n10/2",
        )
        st.button("Add pasted rows", on_click=add_pasted_rows_cb, key="paste_go")

    def _editor():
        return st.data_editor(
            S["tbl_base"],
            key=f"tbl_{S['tbl_ver']}",
            on_change=on_table_edit,
            num_rows="fixed",
            hide_index=True,
            column_order=TBL_COLS,
            disabled=[COL_NO],
            column_config={
                COL_DEL: st.column_config.CheckboxColumn(
                    "Del", help="Tick rows, then press 'Delete ticked'.", width="small", default=False),
                COL_NO: st.column_config.NumberColumn("No", format="%d", width="small"),
                COL_DISPOSAL: st.column_config.TextColumn(
                    COL_DISPOSAL, help="Date the bin was dumped (the roll-off log date). "
                    "Accepts 9/1, 9/1/2026, 2026-09-01, 260901 or 9/1 (8/30)."),
                COL_REQUEST: st.column_config.TextColumn(
                    COL_REQUEST, help="Date the customer asked for service. Same as or earlier "
                    "than the Loaded date; defaults to it."),
                COL_LOADED: st.column_config.TextColumn(
                    COL_LOADED, help="Date the bin left the site. Defaults to the Disposal date."),
                COL_TYPE: st.column_config.SelectboxColumn(
                    COL_TYPE, help="S/Rtn = bin returns; S/Repo = rental ends",
                    options=type_options, required=True, default="S/Rtn"),
                COL_RETURN: st.column_config.TextColumn(
                    COL_RETURN, help="Date the bin was back on site (starts the next cycle). "
                    "Defaults to the Disposal date; may be later. Blank for S/Repo."),
                COL_BIN: st.column_config.SelectboxColumn(
                    COL_BIN, help="Lock event to a specific bin, or leave Unknown",
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
    fallback = _anchor() + timedelta(days=10)
    for i, r in enumerate(rows, 1):
        if r["disposal"] is None:  # e.g. unreadable text typed in the table
            r["disposal"], r["err"], r["raw"] = fallback, {}, {}
            sync_row(r)
            S["_flash_notices"] = S.get("_flash_notices", []) + [
                f"Row {i} had no readable Disposal date — set to {fallback}."]
            touch("picker")
    v = S["pick_ver"]
    nkey = f"p{v}_n"
    _seed(nkey, len(rows))
    st.number_input("Number of events", min_value=1, max_value=40, key=nkey,
                    on_change=on_picker_resize, args=(v,),
                    help="Adds or removes events at the end of the list.")
    bin_options = ["Unknown"] + [f"Bin {b + 1}" for b in range(int(num_bins))]
    type_options = list(TYPE_DISPLAY.keys())
    for i, r in enumerate(rows):
        uid = r["uid"]
        k = lambda f: f"p{v}_{uid}_{f}"  # noqa: E731
        _seed(k("disp"), r["disposal"])
        _seed(k("req"), r["request"])
        _seed(k("load"), r["loaded"])
        _seed(k("type"), r["type"])
        _seed(k("bin"), r["bin"] if r["bin"] in bin_options else "Unknown")
        if r["type"] == "S/Rtn":
            _seed(k("ret"), r["ret"] or r["disposal"])
        st.markdown(f"**Event {i + 1}**")
        c = st.columns([1.3, 1.3, 1.3, 1, 1.3, 1])
        dkw = dict(min_value=DATE_MIN, max_value=DATE_MAX)
        with c[0]:
            st.date_input("Disposal date", key=k("disp"), on_change=on_picker_change,
                          args=(uid, "disp", v), help="Date the bin was dumped (roll-off log date).", **dkw)
        with c[1]:
            st.date_input("Request date", key=k("req"), on_change=on_picker_change,
                          args=(uid, "req", v),
                          help="Date the customer asked for service. Same as or earlier than the "
                               "Loaded date; defaults to it.", **dkw)
        with c[2]:
            st.date_input("Loaded date", key=k("load"), on_change=on_picker_change,
                          args=(uid, "load", v),
                          help="Date the bin left the site. Defaults to the Disposal date.", **dkw)
        with c[3]:
            st.selectbox("Type", type_options, key=k("type"), on_change=on_picker_change,
                         args=(uid, "type", v))
        with c[4]:
            if r["type"] == "S/Rtn":
                st.date_input("Return date", key=k("ret"), on_change=on_picker_change,
                              args=(uid, "ret", v),
                              help="Date the bin was back on site. Defaults to the Disposal "
                                   "date; may be later.", **dkw)
            else:
                st.markdown("_(rental ends — no return date)_")
        with c[5]:
            st.selectbox("Bin (if known)", bin_options, key=k("bin"),
                         on_change=on_picker_change, args=(uid, "bin", v))
        st.divider()


@st.fragment
def events_panel(num_bins):
    st.subheader("Events")
    st.caption("**S/Rtn** = Service & return (bin comes back) | **S/Repo** = Service & repo (rental ends)")
    mode = st.radio(
        "Input mode", [TABLE_MODE, PICKER_MODE], horizontal=True, key="input_mode",
        help="Both views edit the same list of events, so switching keeps your entries.",
    )
    # While the rows are still the untouched placeholders, keep them in step with
    # the delivery date (a stale placeholder year caused the old errors).
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
    errors, warns = validate_rows(S["rows"], int(num_bins))
    if errors:
        st.error("⚠️ Fix before calculating:\n\n" + "\n".join(f"- {e}" for e in errors))
    for w in warns:
        st.warning(w)
    st.caption(
        "💾 Saved as (if the version name is blank): "
        f"**{make_version_name(date.today(), [r['disposal'] for r in S['rows']], num_bins)}**"
    )


# ──────────────────────────────────────────────
# Calculation + results fragment
# ──────────────────────────────────────────────
def run_calculation(delivery_dates, free_days, rate, num_bins, end_basis, hide_empty):
    rows = S["rows"]
    sanitize_rows(rows, num_bins)
    errors, _ = validate_rows(rows, num_bins)
    if errors:
        st.error("⚠️ Fix before calculating:\n\n" + "\n".join(f"- {e}" for e in errors))
        return
    events, fixed = rows_to_events(rows)
    if not events:
        st.warning("Please add at least one event before calculating.")
        return
    try:
        results = calculate_allocations(
            delivery_dates, free_days, rate, events, fixed, num_bins,
            end_basis=end_basis, require_all_bins=hide_empty,
        )
    except TooManyScenarios as ex:
        st.error(str(ex))
        return
    customer = (S.get("customer_name") or "").strip()
    snapshot = {
        "results": results, "events": events, "num_bins": num_bins,
        "customer": customer, "delivery_dates": dict(delivery_dates),
        "fixed": dict(fixed), "free_days": free_days, "rate": rate,
        "end_basis": end_basis, "require_all_bins": hide_empty, "saved_msg": None,
    }
    if customer and results:
        rec = add_to_history(
            customer, (S.get("version_name") or "").strip(), delivery_dates, events,
            results, free_days, rate, num_bins, fixed, end_basis, hide_empty,
        )
        snapshot["saved_msg"] = f"✅ Saved to history under **{customer}** as _{rec['version']}_"
    S["last_results"] = snapshot


@st.fragment
def results_panel(show_tree, show_days, show_timeline, interchangeable,
                  hide_invalid_leaves, end_basis, hide_empty):
    cached = S.get("last_results")
    if not cached:
        return
    # The date-basis and empty-bin toggles apply live to the last calculation.
    if cached["end_basis"] != end_basis or bool(cached.get("require_all_bins")) != bool(hide_empty):
        try:
            cached["results"] = calculate_allocations(
                cached["delivery_dates"], cached["free_days"], cached["rate"], cached["events"],
                cached["fixed"], cached["num_bins"], end_basis=end_basis, require_all_bins=hide_empty,
            )
            cached["end_basis"], cached["require_all_bins"] = end_basis, bool(hide_empty)
        except TooManyScenarios as ex:
            st.error(str(ex))
            return
    render_results(cached, show_tree, show_days, show_timeline, interchangeable, hide_invalid_leaves)


# ──────────────────────────────────────────────
# History tab
# ──────────────────────────────────────────────
def _rec_label(h):
    return f"{h['customer']} · {h['version']} · logged {h.get('logged_at', '—')}"


def render_history(show_days):
    st.header("📚 Customer history")
    history = load_history()
    if not history:
        st.info("No history yet. Run a calculation with a customer name filled in to start logging.")
        return
    col_pick, col_recent = st.columns([2, 1])
    with col_pick:
        customers = sorted(set(h["customer"] for h in history))
        selected_customer = st.selectbox("Choose a customer", ["(all customers)"] + customers)
    with col_recent:
        recent_n = st.number_input(
            "Show last N records", min_value=1, max_value=50, value=10,
            help="Limit how many records to show for the selected customer.",
        )
    if selected_customer == "(all customers)":
        filtered = history
    else:
        filtered = [h for h in history if h["customer"] == selected_customer]
    filtered = list(reversed(filtered))[:int(recent_n)]  # newest first
    st.write(f"Showing **{len(filtered)}** record(s) (newest first)")

    rows = []
    for h in filtered:
        dts = _record_disposal_dates(h)
        date_range = f"{min(dts)} → {max(dts)}" if dts else "—"
        if "delivery_dates" in h:
            deliveries = sorted(set(h["delivery_dates"].values()))
            delivery_display = deliveries[0] if len(deliveries) == 1 else f"{deliveries[0]} → {deliveries[-1]}"
        else:
            delivery_display = h.get("delivery_date", "—")
        rows.append({
            "Customer": h["customer"],
            "Version": h["version"],
            "Delivery": delivery_display,
            "Event date range": date_range,
            "# Events": len(h["events"]),
            "Scenarios": h["scenario_count"],
            "Min fee": fmt_fee(h["min_total"], h.get("min_ext_days"), show_days),
            "Max fee": fmt_fee(h["max_total"], h.get("max_ext_days"), show_days),
            "Logged": h["logged_at"],
        })
    st.dataframe(rows, **STRETCH)

    st.divider()
    st.subheader("🔍 View / reload a record")
    labels = {h["id"]: _rec_label(h) for h in filtered}
    sel_id = st.selectbox(  # [#6] dropdown instead of a number with +/-
        "Record to view", list(labels), format_func=lambda i: labels[i],
        help="Pick a record from the table above.",
    )
    rec = next(h for h in filtered if h["id"] == sel_id)
    st.markdown(f"### {rec['customer']} — {rec['version']}")
    st.caption(f"Logged {rec.get('logged_at', '—')}")
    render_static_view_of_record(rec, show_days)

    st.divider()
    st.button("🔁 Load into Calculator", type="primary", key=f"reload_{sel_id}",
              on_click=request_reload_cb, args=(sel_id,),
              help="Fills the Calculator with this record's customer, dates, events, terms and results.")
    pending = S.pop("_pending_reload", None)
    if pending:
        confirm_reload_dialog(pending)

    with st.expander("🔄 Re-run with new rental terms"):
        st.write("Try different free-day allowances or rates without changing the original record.")
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

    with st.expander("⚖️ Compare with another record"):
        other_ids = [i for i in labels if i != sel_id]
        if not other_ids:
            st.info("Need at least 2 records in this filter to compare.")
        else:
            other_id = st.selectbox("Compare with which record?", other_ids,
                                    format_func=lambda i: labels[i], key=f"compare_{sel_id}")
            if st.button("Show comparison", key=f"comp_btn_{sel_id}"):
                render_record_comparison(rec, next(h for h in filtered if h["id"] == other_id), show_days)

    with st.expander("📄 Raw JSON"):
        st.json(rec)

    st.divider()
    # [#5] compact delete by customer and by version
    with st.expander("🗑️ Delete records"):
        dc1, dc2 = st.columns([1, 2])
        del_cust = dc1.selectbox("Customer", customers, key="del_customer")
        cust_recs = [h for h in history if h["customer"] == del_cust]
        ver_labels = {h["id"]: f"{h['version']} · {h.get('logged_at', '—')}" for h in cust_recs}
        vers = dc2.multiselect("Versions (leave empty to use 'Delete all')", list(ver_labels),
                               format_func=lambda i: ver_labels[i],
                               key=f"del_versions_{del_cust}_{len(cust_recs)}")
        b1, b2 = st.columns(2)
        if b1.button(f"Delete {len(vers)} selected version(s)", disabled=not vers, **STRETCH):
            confirm_delete_dialog(vers, None, f"{len(vers)} version(s) of {del_cust}")
        if b2.button(f"Delete all {len(cust_recs)} record(s) for {del_cust}", **STRETCH):
            confirm_delete_dialog([], del_cust, f"all {len(cust_recs)} record(s) for {del_cust}")
    with st.expander("⚠️ Danger zone"):
        if st.button("🗑️ Clear all history"):
            confirm_delete_dialog([h["id"] for h in history], None, f"ALL {len(history)} history record(s)")


# ──────────────────────────────────────────────
# Streamlit UI
# ──────────────────────────────────────────────
st.set_page_config(page_title="Bin Extension Fee Calculator", page_icon="🗑️", layout="wide")
st.title("🗑️ Bin Extension Fee Calculator")


def init_state():
    d = S.setdefault
    d("rev", 0)
    d("tbl_rev", -1)
    d("pick_rev", -1)
    d("tbl_ver", 0)
    d("pick_ver", 0)
    d("tbl_base", None)
    d("tbl_seen", None)
    d("rental_type", "Roll-off (10 free days)")
    d("rate_input", 50.0)
    d("num_bins_input", 2)
    d("basis_choice", "Request date")
    d("hide_empty_bins", False)
    d("customer_name", "")
    d("version_name", "")
    d("staggered", False)
    d("input_mode", TABLE_MODE)
    if "rows" not in S:
        S["rows"] = default_rows(_anchor())
        S["rows_default"] = True
        S["rows_anchor"] = _anchor()


init_state()

# One-shot messages (set by callbacks / dialogs before a rerun). The slot is ALWAYS
# created so the tabs below keep the same position; an element that appears and
# disappears above st.tabs makes Streamlit reset the selected tab.
_flash_slot = st.container()
_flash = S.pop("_flash", None)
if _flash:
    with _flash_slot:
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
    num_bins = st.number_input("Number of bins on site", min_value=1, max_value=5, key="num_bins_input")
    num_bins = int(num_bins)
    st.caption("Off-site days (between Loaded date and Return date) are not billed.")
    st.divider()

    st.subheader("Billing basis")
    basis_label = st.radio(
        "Extension days run to the…",
        list(BASIS_CHOICES.keys()),
        key="basis_choice",
        help=(
            "**Request date** (default): the customer is billed up to the day they asked for "
            "service, so the wait between request and service is not billed.\n\n"
            "**Loaded date**: billed up to the day the bin left the site.\n\n"
            "**Disposal date**: billed up to the roll-off log date, i.e. the old behavior.\n\n"
            "The **Waived** column shows what the chosen basis removes versus the Disposal date."
        ),
    )
    end_basis = BASIS_CHOICES[basis_label]
    hide_empty = st.checkbox(
        "🚫 Hide scenarios with an empty bin",
        key="hide_empty_bins",
        help="Hide any scenario in which a bin on site has no work order assigned to it.",
    )
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
            "Turn ON to collapse scenarios where the bin labels differ but "
            "the figures per bin and the groupings of events are identical.\n\n"
            "Turn OFF if the bins are not interchangeable (e.g., different "
            "sizes) AND you want to see all possible bin assignments."
        ),
    )
    st.divider()
    with st.expander("⌨️ Keyboard tips"):
        st.markdown(
            """
**In the events table:**
- **Arrow keys** = move between cells (most reliable)
- **Enter** or just **typing** = edit the selected cell
- **Tab** = next cell (sometimes escapes — use arrows)
- **Esc** = exit a cell editor

**Global shortcuts:**
- **Ctrl + Enter** = run Calculate (works from anywhere)
"""
        )

tab1, tab2 = st.tabs(["🧮 Calculator", "📚 History"])

# ──────────────────────────────────────────────
# Tab 1: Calculator
# ──────────────────────────────────────────────
with tab1:
    col_a, col_b = st.columns([1, 1])
    with col_a:
        st.text_input("Customer name (leave blank to skip saving to history)", key="customer_name")
        st.text_input(
            "Version name (optional)", key="version_name",
            placeholder="Blank = auto: Run YYMMDD · Range YYMMDD–YYMMDD · N bins",
            help="Run = the day you calculate. Range = first–last Disposal date. "
                 "If a name already exists for this customer, (v2), (v3)… is added.",
        )
        bc1, bc2 = st.columns(2)
        if "last_results" in S:
            bc1.button("🗑️ Clear results", key="clear_results",
                       on_click=lambda: S.pop("last_results", None),
                       help="Remove the results below (inputs are kept)", **STRETCH)
        bc2.button("🧹 Reset events", key="reset_events", on_click=reset_events_cb,
                   help="Put the events back to the 3 placeholder rows and clear results. "
                        "Use this if the table ever looks stuck.", **STRETCH)
    with col_b:
        staggered_delivery = st.checkbox(
            "Bins delivered on different dates?", key="staggered",
            help="Check if bins were dropped off on separate days.",
        )

    last_delivery = S.get("delivery_last") or {}
    fallback_delivery = (min(last_delivery.values()) if last_delivery
                         else date.today() - timedelta(days=30))
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

    events_panel(num_bins)

    calc_clicked = st.button(
        "🧮 Calculate all scenarios (or press Ctrl+Enter)",
        type="primary",
        key="calc_btn",
    )
    if calc_clicked:
        run_calculation(delivery_dates, free_days, rate, num_bins, end_basis, hide_empty)

    results_panel(show_tree, show_days, show_timeline, interchangeable,
                  hide_invalid_leaves, end_basis, hide_empty)

# ──────────────────────────────────────────────
# Tab 2: History
# ──────────────────────────────────────────────
with tab2:
    render_history(show_days)

# Ctrl+Enter shortcut (+ jump to the Calculator tab after a history reload)
_js_goto = (
    "for (const t of doc.querySelectorAll('button[role=\"tab\"]')) {"
    " if (t.innerText && t.innerText.includes('Calculator')) { t.click(); break; } }"
) if S.pop("_goto_calc", False) else ""
components.html(
    """
    <script>
    (function() {
        const doc = window.parent.document;
        %s
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
    """ % _js_goto,
    height=0,
)
