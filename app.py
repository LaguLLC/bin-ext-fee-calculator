import streamlit as st
import pandas as pd
import json
import os
from datetime import date, timedelta
from itertools import product


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


# ──────────────────────────────────────────────
# Core fee calculation
# ──────────────────────────────────────────────
def fee_for_bin(bin_events, bin_delivery_date, free_days, rate_per_day):
    if not bin_events:
        return 0, []
    fee = 0
    breakdown = []
    cycle_start = bin_delivery_date
    for ev in bin_events:
        cycle_days = (ev["haul_date"] - cycle_start).days + 1
        ext_days = max(0, cycle_days - free_days)
        cycle_fee = ext_days * rate_per_day
        fee += cycle_fee
        breakdown.append({
            "cycle_start": cycle_start,
            "haul_date": ev["haul_date"],
            "cycle_days": cycle_days,
            "ext_days": ext_days,
            "fee": cycle_fee,
        })
        if ev["type"] == REPO:
            break
        cycle_start = ev["return_date"]
    return fee, breakdown


def is_valid_assignment(events, assignment, delivery_dates):
    bins = {}
    for i, ev in enumerate(events):
        b = assignment[i]
        bins.setdefault(b, []).append(ev)
    for b, bin_events in bins.items():
        bin_events.sort(key=lambda e: e["haul_date"])
        repo_idx = [i for i, e in enumerate(bin_events) if e["type"] == REPO]
        if len(repo_idx) > 1:
            return False
        if repo_idx and repo_idx[0] != len(bin_events) - 1:
            return False
        bin_start = delivery_dates.get(b)
        if bin_start is None:
            return False
        for e in bin_events:
            if e["haul_date"] < bin_start:
                return False
    return True


def calculate_allocations(delivery_dates, free_days, rate_per_day, events,
                          fixed_assignments=None, num_bins=2):
    fixed_assignments = fixed_assignments or {}
    n = len(events)
    free_indices = [i for i in range(n) if i not in fixed_assignments]

    results = []
    for combo in product(range(1, num_bins + 1), repeat=len(free_indices)):
        assignment = dict(fixed_assignments)
        for idx, bin_num in zip(free_indices, combo):
            assignment[idx] = bin_num

        if not is_valid_assignment(events, assignment, delivery_dates):
            continue

        bins = {b: [] for b in range(1, num_bins + 1)}
        for i, ev in enumerate(events):
            bins[assignment[i]].append(ev)
        for b in bins:
            bins[b].sort(key=lambda e: e["haul_date"])

        fees = {}
        breakdowns = {}
        for b in bins:
            bin_delivery = delivery_dates.get(b)
            fees[b], breakdowns[b] = fee_for_bin(
                bins[b], bin_delivery, free_days, rate_per_day
            )
        total = sum(fees.values())

        results.append({
            "combo": combo,
            "assignment": {b: [e["label"] for e in bins[b]] for b in bins},
            "fees": fees,
            "breakdowns": breakdowns,
            "total": total,
        })

    results.sort(key=lambda r: r["total"])
    return results


# ──────────────────────────────────────────────
# Decision tree (Graphviz DOT)
# ──────────────────────────────────────────────
def build_decision_tree_dot(events, fixed_assignments, num_bins, delivery_dates,
                            free_days, rate_per_day):
    free_indices = [i for i in range(len(events)) if i not in fixed_assignments]

    if not free_indices:
        return None

    lines = []
    lines.append("digraph DT {")
    lines.append("  rankdir=TB;")
    lines.append('  node [shape=box, style="rounded,filled", fillcolor=white, fontname="Arial"];')
    lines.append('  edge [fontname="Arial", fontsize=10];')

    fixed_parts = []
    for idx, b in fixed_assignments.items():
        lbl = events[idx]["label"]
        fixed_parts.append(f"{lbl}=B{b}")
    fixed_summary = ", ".join(fixed_parts) if fixed_parts else "no fixed events"
    root_label = "Start\\n(" + fixed_summary + ")"
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
                nid = new_id()

                if is_last:
                    full_assignment = dict(fixed_assignments)
                    for fi, bn in zip(free_indices, new_partial):
                        full_assignment[fi] = bn

                    if is_valid_assignment(events, full_assignment, delivery_dates):
                        bins_map = {b: [] for b in range(1, num_bins + 1)}
                        for i, ev in enumerate(events):
                            bins_map[full_assignment[i]].append(ev)
                        for b in bins_map:
                            bins_map[b].sort(key=lambda e: e["haul_date"])
                        total = 0
                        for b in bins_map:
                            bin_delivery = delivery_dates.get(b)
                            f, _ = fee_for_bin(bins_map[b], bin_delivery, free_days, rate_per_day)
                            total += f
                        formatted_total = f"${total:,.0f}"
                        leaf_label = "Total: " + formatted_total
                        lines.append(f'  {nid} [label="{leaf_label}", fillcolor="#d1e7dd"];')
                    else:
                        lines.append(f'  {nid} [label="(invalid)", fillcolor="#f8d7da"];')
                else:
                    next_idx = free_indices[depth + 1]
                    next_lbl = events[next_idx]["label"]
                    node_label = "Service " + next_lbl + " -> ?"
                    lines.append(f'  {nid} [label="{node_label}"];')

                edge_label = f"Bin {bin_num}"
                lines.append(f'  {parent_id} -> {nid} [label="  {edge_label}  "];')
                next_frontier[new_partial] = nid

        frontier = next_frontier

    lines.append('  info [label="Each branch = which bin handled that service", shape=note, fillcolor="#fff3cd"];')
    lines.append("  info -> root [style=invis];")
    lines.append("}")
    return "\n".join(lines)


# ──────────────────────────────────────────────
# History storage
# ──────────────────────────────────────────────
def load_history():
    if not os.path.exists(HISTORY_FILE):
        return []
    try:
        with open(HISTORY_FILE, "r") as f:
            return json.load(f)
    except Exception:
        return []


def save_history(entries):
    with open(HISTORY_FILE, "w") as f:
        json.dump(entries, f, indent=2, default=str)


def add_to_history(customer, delivery_dates, events, results):
    history = load_history()
    history.append({
        "customer": customer,
        "delivery_dates": {str(b): str(d) for b, d in delivery_dates.items()},
        "events": [
            {
                "label": e["label"],
                "haul_date": str(e["haul_date"]),
                "return_date": str(e["return_date"]),
                "type": e["type"],
            } for e in events
        ],
        "min_total": results[0]["total"] if results else 0,
        "max_total": results[-1]["total"] if results else 0,
        "scenario_count": len(results),
        "logged_at": str(date.today()),
    })
    save_history(history)


# ──────────────────────────────────────────────
# Render results
# ──────────────────────────────────────────────
def render_results(results, events, num_bins, customer, delivery_dates,
                   show_tree, fixed_assignments, free_days, rate_per_day):
    if not results:
        st.error(
            "No valid scenarios found. Check that each bin has at most one "
            "S/Repo (and it's the last event for that bin), and that no event "
            "predates its bin's delivery date."
        )
        return

    st.success(f"Found {len(results)} valid scenario(s) across {len(events)} event(s).")

    lowest = results[0]["total"]
    highest = results[-1]["total"]
    spread = highest - lowest

    m1, m2, m3 = st.columns(3)
    m1.metric("Lowest total fee", f"${lowest:,.0f}")
    m2.metric("Highest total fee", f"${highest:,.0f}")
    m3.metric("Range", f"${spread:,.0f}")

    table_rows = []
    for i, r in enumerate(results, 1):
        row = {"#": i}
        for b in range(1, int(num_bins) + 1):
            services_list = r["assignment"][b]
            row[f"Bin {b}"] = ", ".join(services_list) if services_list else "(none)"
        for b in range(1, int(num_bins) + 1):
            bin_fee = r["fees"][b]
            row[f"Bin {b} Fee"] = f"${bin_fee:,.0f}"
        row["Total"] = f"${r['total']:,.0f}"
        table_rows.append(row)
    st.dataframe(table_rows, use_container_width=True)

    if show_tree:
        st.subheader("🌳 Decision tree")
        st.caption(
            "Each path from Start to a leaf is one scenario. "
            "Edge labels show which bin handled each service. "
            "Mouse wheel to zoom; click+drag to pan."
        )
        dot = build_decision_tree_dot(
            events, fixed_assignments, num_bins, delivery_dates, free_days, rate_per_day
        )
        if dot is None:
            st.info("No decisions to display — all events are locked to specific bins.")
        else:
            try:
                st.graphviz_chart(dot, use_container_width=True)
            except Exception as ex:
                st.warning(f"Could not render decision tree: {ex}")

    st.subheader("📋 Scenario breakdown")
    choice = st.selectbox(
        "View detailed cycle math for scenario:",
        list(range(1, len(results) + 1)),
    )
    r = results[choice - 1]
    for b in range(1, int(num_bins) + 1):
        bin_fee = r["fees"][b]
        bin_breakdown = r["breakdowns"][b]
        header = f"Bin {b} — ${bin_fee:,.0f}"
        with st.expander(header):
            if not bin_breakdown:
                st.write("_No events on this bin._")
            for c in bin_breakdown:
                line = (
                    f"• {c['cycle_start']} → {c['haul_date']}: "
                    f"{c['cycle_days']} days, {c['ext_days']} over → "
                    f"**${c['fee']:,.0f}**"
                )
                st.write(line)

    if customer.strip():
        add_to_history(customer.strip(), delivery_dates, events, results)
        st.info(f"✅ Saved to history under: **{customer.strip()}**")
    else:
        st.caption("ℹ️ Customer name was blank — not saved to history.")


# ──────────────────────────────────────────────
# Streamlit UI
# ──────────────────────────────────────────────
st.set_page_config(page_title="Bin Extension Fee Calculator", page_icon="🗑️", layout="wide")
st.title("🗑️ Bin Extension Fee Calculator")

tab1, tab2 = st.tabs(["🧮 Calculator", "📚 History"])

with st.sidebar:
    st.header("Rental Terms")

    rental_type = st.radio(
        "Rental type",
        ["Roll-off (10 free days)", "Short-term (3 free days)", "Custom"],
        help="Pick a preset to auto-fill free days, or choose Custom to set manually.",
    )

    if rental_type == "Roll-off (10 free days)":
        default_free_days = 10
    elif rental_type == "Short-term (3 free days)":
        default_free_days = 3
    else:
        default_free_days = 10

    free_days = st.number_input(
        "Free rental days per cycle",
        value=default_free_days,
        min_value=1,
        disabled=(rental_type != "Custom"),
        help="Locked unless you select Custom above.",
    )
    rate = st.number_input("Extension fee per day ($)", value=50.0, min_value=0.0)
    num_bins = st.number_input("Number of bins on site", value=2, min_value=1, max_value=5)
    st.caption("Off-site days (between haul and return) are not billed.")

    st.divider()
    show_tree = st.checkbox(
        "🌳 Show decision tree",
        value=False,
        help="Renders a Graphviz tree of all allocation possibilities. Can get wide for many unknowns — zoom/pan as needed.",
    )


with tab1:
    col_a, col_b = st.columns([1, 1])
    with col_a:
        customer = st.text_input("Customer name (leave blank to skip saving to history)", "")
    with col_b:
        staggered_delivery = st.checkbox(
            "Bins delivered on different dates?",
            help="Check if bins were dropped off on separate days (e.g., bin added mid-project).",
        )

    default_delivery = date.today() - timedelta(days=30)
    delivery_dates = {}

    if staggered_delivery:
        st.markdown("**Per-bin delivery dates:**")
        cols = st.columns(int(num_bins))
        for b in range(1, int(num_bins) + 1):
            with cols[b - 1]:
                delivery_dates[b] = st.date_input(
                    f"Bin {b} delivery",
                    value=default_delivery,
                    key=f"delivery_bin_{b}",
                )
    else:
        single_delivery = st.date_input("Delivery date (all bins)", value=default_delivery)
        for b in range(1, int(num_bins) + 1):
            delivery_dates[b] = single_delivery

    st.subheader("Events")
    st.caption("**S/Rtn** = Service & return (bin comes back) | **S/Repo** = Service & repo (rental ends)")

    input_mode = st.radio(
        "Input mode",
        ["📋 Table (paste from Excel)", "🎯 Individual pickers"],
        horizontal=True,
        help="Table mode supports pasting rows from Excel. Picker mode shows one form per event.",
    )

    bin_options = ["Unknown"] + [f"Bin {b+1}" for b in range(int(num_bins))]
    type_options = list(TYPE_DISPLAY.keys())

    events = []
    fixed = {}
    errors = []

    if input_mode == "📋 Table (paste from Excel)":
        st.caption(
            "🔄 **Auto-sync rules:** Return date clears automatically when Type = S/Repo. "
            "For S/Rtn, blank return date auto-fills with haul date (override for off-site gaps). "
            "Click 🔄 Apply auto-sync rules or 🧮 Calculate to refresh."
        )

        earliest_delivery = min(delivery_dates.values())

        # Initialize table state once per session so edits persist between reruns
        if "events_table_df" not in st.session_state:
            st.session_state["events_table_df"] = pd.DataFrame({
                "Haul date": [earliest_delivery + timedelta(days=10 * (i + 1)) for i in range(3)],
                "Type": ["S/Rtn"] * 3,
                "Return date": [earliest_delivery + timedelta(days=10 * (i + 1)) for i in range(3)],
                "Bin (if known)": ["Unknown"] * 3,
            })

        # Track which return dates have been manually overridden per row index.
        # synced=True means return follows haul; synced=False means user overrode it.
        if "row_sync_state" not in st.session_state:
            st.session_state["row_sync_state"] = {}

        # Show the table as-is from session state (don't pre-modify it)
        df_to_show = st.session_state["events_table_df"].copy()

        edited_df = st.data_editor(
            df_to_show,
            num_rows="dynamic",
            use_container_width=True,
            column_config={
                "Haul date": st.column_config.DateColumn(
                    "Haul date",
                    help="Date the bin was picked up for service",
                    format="YYYY-MM-DD",
                    required=True,
                ),
                "Type": st.column_config.SelectboxColumn(
                    "Type",
                    help="S/Rtn = bin returns; S/Repo = rental ends",
                    options=type_options,
                    required=True,
                ),
                "Return date": st.column_config.DateColumn(
                    "Return date",
                    help="Blank for S/Repo. For S/Rtn, follows haul date until manually overridden.",
                    format="YYYY-MM-DD",
                ),
                "Bin (if known)": st.column_config.SelectboxColumn(
                    "Bin (if known)",
                    help="Lock event to a specific bin, or leave Unknown",
                    options=bin_options,
                    required=True,
                ),
            },
            key="events_table",
        )

        # Apply auto-sync rules AFTER the user's edit (not before)
        sync_state = st.session_state["row_sync_state"]
        previous_df = st.session_state["events_table_df"]
        changed = False

        synced_df = edited_df.copy()

        for idx in synced_df.index:
            row_type = synced_df.at[idx, "Type"]
            row_haul = synced_df.at[idx, "Haul date"]
            row_return = synced_df.at[idx, "Return date"]

            # Get previous values to detect what changed
            prev_haul = None
            prev_return = None
            prev_type = None
            if idx in previous_df.index:
                prev_haul = previous_df.at[idx, "Haul date"]
                prev_return = previous_df.at[idx, "Return date"]
                prev_type = previous_df.at[idx, "Type"]

            was_synced = sync_state.get(idx, True)

            if row_type == "S/Repo":
                # Always clear return date for S/Repo
                if not pd.isna(row_return):
                    synced_df.at[idx, "Return date"] = pd.NaT
                    changed = True
                sync_state[idx] = True

            elif row_type == "S/Rtn":
                if pd.isna(row_haul):
                    # No haul date yet — nothing to sync
                    pass
                elif pd.isna(row_return):
                    # Blank return -> auto-fill with haul
                    synced_df.at[idx, "Return date"] = row_haul
                    sync_state[idx] = True
                    changed = True
                else:
                    # Both dates present — figure out what user just did
                    user_changed_return = (prev_return != row_return) and not (
                        pd.isna(prev_return) and pd.isna(row_return)
                    )
                    user_changed_haul = (prev_haul != row_haul) and not (
                        pd.isna(prev_haul) and pd.isna(row_haul)
                    )
                    type_changed_to_rtn = (prev_type == "S/Repo" and row_type == "S/Rtn")

                    if type_changed_to_rtn:
                        # Just switched from S/Repo back to S/Rtn — sync to haul
                        synced_df.at[idx, "Return date"] = row_haul
                        sync_state[idx] = True
                        changed = True
                    elif user_changed_return:
                        # User edited return date directly
                        if row_return == row_haul:
                            sync_state[idx] = True
                        else:
                            sync_state[idx] = False
                    elif user_changed_haul and was_synced:
                        # User changed haul and return was previously following — sync
                        synced_df.at[idx, "Return date"] = row_haul
                        sync_state[idx] = True
                        changed = True
                    # Otherwise: leave as-is, preserve current sync state

        # Build error column on the synced version
        synced_df["⚠️"] = ""
        for idx in synced_df.index:
            row_type = synced_df.at[idx, "Type"]
            row_haul = synced_df.at[idx, "Haul date"]
            row_return = synced_df.at[idx, "Return date"]
            if (
                row_type == "S/Rtn"
                and not pd.isna(row_haul)
                and not pd.isna(row_return)
                and row_return < row_haul
            ):
                synced_df.at[idx, "⚠️"] = "⚠️ Return before haul"

        # Save synced version (without the warning column) back to session
        df_to_save = synced_df.copy()
        if "⚠️" in df_to_save.columns:
            df_to_save = df_to_save.drop(columns=["⚠️"])
        st.session_state["events_table_df"] = df_to_save
        st.session_state["row_sync_state"] = sync_state

        # If we changed anything, rerun so the table re-renders with synced values
        if changed:
            st.rerun()

        # Use synced_df for downstream display & errors (so warnings show even before rerun)
        edited_df = synced_df

        # Show warning banner if any row has impossible dates
        invalid_rows = edited_df[edited_df.get("⚠️", "") != ""]
        if not invalid_rows.empty:
            st.error(
                f"⚠️ {len(invalid_rows)} row(s) have return date before haul date — "
                "this is impossible. Fix before calculating."
            )

        # Manual refresh button for users who want auto-sync without calculating
        col_refresh, _ = st.columns([1, 3])
        with col_refresh:
            if st.button("🔄 Apply auto-sync rules", help="Clear S/Repo return dates and fill blank S/Rtn return dates"):
                st.rerun()

        if st.button("🧮 Calculate all scenarios", type="primary", key="calc_table"):
            for i, row in edited_df.iterrows():
                haul = row["Haul date"]
                ev_type = row["Type"]
                return_date = row["Return date"]
                bin_choice = row["Bin (if known)"]

                if pd.isna(haul):
                    continue
                if hasattr(haul, "date"):
                    haul = haul.date()

                if ev_type == "S/Repo":
                    return_date = haul
                else:
                    if pd.isna(return_date):
                        return_date = haul
                    elif hasattr(return_date, "date"):
                        return_date = return_date.date()
                    if return_date < haul:
                        errors.append(
                            f"Row {i+1}: Return date ({return_date}) is before haul date ({haul})."
                        )
                        continue

                event = {
                    "label": haul.strftime("%b %d"),
                    "haul_date": haul,
                    "return_date": return_date,
                    "type": TYPE_DISPLAY.get(ev_type, SERVICE_RETURN),
                }
                events.append(event)

                if bin_choice and bin_choice != "Unknown":
                    fixed[len(events) - 1] = int(bin_choice.split()[-1])

            if errors:
                for err in errors:
                    st.error(err)
            elif not events:
                st.warning("Please add at least one event before calculating.")
            else:
                results = calculate_allocations(
                    delivery_dates, free_days, rate, events, fixed, int(num_bins)
                )
                render_results(
                    results, events, num_bins, customer, delivery_dates,
                    show_tree, fixed, free_days, rate
                )

    else:
        n_events = st.number_input(
            "Number of events",
            value=5,
            min_value=1,
            max_value=20,
            help="Use the +/- buttons to add or remove events.",
        )

        for i in range(int(n_events)):
            st.markdown(f"**Event {i+1}**")
            c1, c2, c3, c4 = st.columns([1.5, 1.5, 1.5, 1.5])

            with c1:
                haul = st.date_input(
                    "Haul date",
                    key=f"haul{i}",
                    value=min(delivery_dates.values()) + timedelta(days=10 * (i + 1)),
                )

            with c2:
                ev_type = st.selectbox(
                    "Type",
                    type_options,
                    key=f"type{i}",
                )

            with c3:
                if ev_type == "S/Rtn":
                    ret_key = f"ret{i}"
                    override_key = f"ret_overridden{i}"

                    has_override = st.session_state.get(override_key, False)
                    if override_key not in st.session_state:
                        st.session_state[override_key] = False

                    if not has_override:
                        st.session_state[ret_key] = haul

                    return_date = st.date_input(
                        "Return date",
                        key=ret_key,
                        help="Auto-fills to haul date. Edit only for off-site gaps.",
                    )

                    if return_date != haul:
                        st.session_state[override_key] = True
                    elif return_date == haul and has_override:
                        st.session_state[override_key] = False
                else:
                    return_date = haul
                    st.markdown("_(rental ends — no return date)_")

            with c4:
                bin_choice = st.selectbox("Bin (if known)", bin_options, key=f"bin{i}")

            if return_date < haul:
                errors.append(
                    f"Event {i+1}: Return date ({return_date}) is before haul date ({haul})."
                )

            events.append({
                "label": haul.strftime("%b %d"),
                "haul_date": haul,
                "return_date": return_date,
                "type": TYPE_DISPLAY.get(ev_type, SERVICE_RETURN),
            })
            if bin_choice != "Unknown":
                fixed[i] = int(bin_choice.split()[-1])
            st.divider()

        if st.button("🧮 Calculate all scenarios", type="primary", key="calc_picker"):
            if errors:
                for err in errors:
                    st.error(err)
            elif not events:
                st.warning("Please add at least one event before calculating.")
            else:
                results = calculate_allocations(
                    delivery_dates, free_days, rate, events, fixed, int(num_bins)
                )
                render_results(
                    results, events, num_bins, customer, delivery_dates,
                    show_tree, fixed, free_days, rate
                )


with tab2:
    st.header("📚 Customer history")
    history = load_history()

    if not history:
        st.info("No history yet. Run a calculation with a customer name filled in to start logging.")
    else:
        customers = sorted(set(h["customer"] for h in history))
        selected_customer = st.selectbox("Choose a customer", ["(all customers)"] + customers)

        if selected_customer == "(all customers)":
            filtered = history
        else:
            filtered = [h for h in history if h["customer"] == selected_customer]

        st.write(f"Showing **{len(filtered)}** record(s)")

        rows = []
        for h in filtered:
            event_dates = [e["haul_date"] for e in h["events"]]
            date_range = f"{min(event_dates)} → {max(event_dates)}" if event_dates else "—"

            if "delivery_dates" in h:
                deliveries = sorted(set(h["delivery_dates"].values()))
                if len(deliveries) == 1:
                    delivery_display = deliveries[0]
                else:
                    delivery_display = f"{deliveries[0]} → {deliveries[-1]}"
            else:
                delivery_display = h.get("delivery_date", "—")

            rows.append({
                "Customer": h["customer"],
                "Delivery": delivery_display,
                "Event date range": date_range,
                "# Events": len(h["events"]),
                "Scenarios": h["scenario_count"],
                "Min fee": f"${h['min_total']:,.0f}",
                "Max fee": f"${h['max_total']:,.0f}",
                "Logged": h["logged_at"],
            })
        st.dataframe(rows, use_container_width=True)

        st.subheader("🔍 View record details")
        if filtered:
            idx = st.number_input(
                "Record # to view",
                min_value=1,
                max_value=len(filtered),
                value=1,
            )
            rec = filtered[idx - 1]
            st.json(rec)

        st.divider()
        with st.expander("⚠️ Danger zone"):
            if st.button("🗑️ Clear all history"):
                save_history([])
                st.success("History cleared. Refresh the page to see the empty state.")
