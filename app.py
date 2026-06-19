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
# Core calculation logic
# ──────────────────────────────────────────────
def calculate_allocations(delivery_date, free_days, rate_per_day, events,
                          fixed_assignments=None, num_bins=2):
    fixed_assignments = fixed_assignments or {}
    n = len(events)
    free_indices = [i for i in range(n) if i not in fixed_assignments]

    def fee_for_bin(bin_events):
        if not bin_events:
            return 0, []
        fee = 0
        breakdown = []
        cycle_start = delivery_date
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

    results = []
    for combo in product(range(1, num_bins + 1), repeat=len(free_indices)):
        assignment = dict(fixed_assignments)
        for idx, bin_num in zip(free_indices, combo):
            assignment[idx] = bin_num

        bins = {b: [] for b in range(1, num_bins + 1)}
        for i, ev in enumerate(events):
            bins[assignment[i]].append(ev)
        for b in bins:
            bins[b].sort(key=lambda e: e["haul_date"])

        valid = True
        for b in bins:
            repo_indices = [i for i, e in enumerate(bins[b]) if e["type"] == REPO]
            if len(repo_indices) > 1:
                valid = False
                break
            if repo_indices and repo_indices[0] != len(bins[b]) - 1:
                valid = False
                break
        if not valid:
            continue

        fees = {}
        breakdowns = {}
        for b in bins:
            fees[b], breakdowns[b] = fee_for_bin(bins[b])
        total = sum(fees.values())

        results.append({
            "assignment": {b: [e["label"] for e in bins[b]] for b in bins},
            "fees": fees,
            "breakdowns": breakdowns,
            "total": total,
        })

    results.sort(key=lambda r: r["total"])
    return results


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

def add_to_history(customer, delivery_date, events, results):
    history = load_history()
    history.append({
        "customer": customer,
        "delivery_date": str(delivery_date),
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
# Render results (shared by both input modes)
# ──────────────────────────────────────────────
def render_results(results, events, num_bins, customer, delivery):
    if not results:
        st.error(
            "No valid scenarios found. Check that each bin has at most "
            "one S/Repo event and that it's the last event for that bin."
        )
        return

    st.success(f"Found {len(results)} valid scenario(s) across {len(events)} event(s).")

    m1, m2, m3 = st.columns(3)
    m1.metric("Lowest total fee", f"${results[0]['total']:,.0f}")
    m2.metric("Highest total fee", f"${results[-1]['total']:,.0f}")
    m3.metric("Range", f"${results[-1]['total'] - results[0]['total']:,.0f}")

    table_rows = []
    for i, r in enumerate(results, 1):
        row = {"#": i}
        for b in range(1, int(num_bins) + 1):
            row[f"Bin {b}"] = ", ".join(r["assignment"][b]) or "(none)"
        for b in range(1, int(num_bins) + 1):
            row[f"Bin {b} Fee"] = f"${r['fees'],.0f}"
        row["Total"] = f"${r['total']:,.0f}"
        table_rows.append(row)
    st.dataframe(table_rows, use_container_width=True)

    st.subheader("📋 Scenario breakdown")
    choice = st.selectbox(
        "View detailed cycle math for scenario:",
        list(range(1, len(results) + 1)),
    )
    r = results[choice - 1]
    for b in range(1, int(num_bins) + 1):
        with st.expander(f"Bin {b} — ${r['fees'],.0f}"):
            if not r["breakdowns"]st.write("_No events on this bin._")
            for c in r["breakdowns"]st.write(
                    f"• {c['cycle_start']} → {c['haul_date']}: "
                    f"{c['cycle_days']} days, {c['ext_days']} over → "
                    f"**${c['fee']:,.0f}**"
                )

    if customer.strip():
        add_to_history(customer.strip(), delivery, events, results)
        st.info(f"✅ Saved to history under: **{customer.strip()}**")
    else:
        st.caption("ℹ️ Customer name was blank — not saved to history.")


# ──────────────────────────────────────────────
# Streamlit UI
# ──────────────────────────────────────────────
st.set_page_config(page_title="Bin Extension Fee Calculator", page_icon="🗑️", layout="wide")
st.title("🗑️ Bin Extension Fee Calculator")

tab1, tab2 = st.tabs(["🧮 Calculator", "📚 History"])

# ─── Sidebar ──────────────────────────────────
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

# ─── Tab 1: Calculator ────────────────────────
with tab1:
    col_a, col_b = st.columns([1, 1])
    with col_a:
        customer = st.text_input("Customer name (leave blank to skip saving to history)", "")
    with col_b:
        delivery = st.date_input("Delivery date", value=date.today() - timedelta(days=30))

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

    # ─── MODE A: Table (Excel paste) ──────────
    if input_mode == "📋 Table (paste from Excel)":
        st.markdown(
            "💡 **Tip:** Copy rows from Excel (Haul date | Type | Return date | Bin), "
            "click the first cell below, and press **Ctrl+V**. "
            "Add rows with the **➕** button below the table, or delete with the trash icon."
        )
        st.caption(
            "Excel column format — Haul date: `YYYY-MM-DD` | Type: `S/Rtn` or `S/Repo` | "
            "Return date: `YYYY-MM-DD` (blank = same as haul) | Bin: `Unknown` or `Bin 1`, `Bin 2`, etc."
        )

        default_df = pd.DataFrame({
            "Haul date": [delivery + timedelta(days=10 * (i + 1)) for i in range(3)],
            "Type": ["S/Rtn"] * 3,
            "Return date": [delivery + timedelta(days=10 * (i + 1)) for i in range(3)],
            "Bin (if known)": ["Unknown"] * 3,
        })

        edited_df = st.data_editor(
            default_df,
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
                    help="Date bin was returned. Same as haul for same-day. Ignored for S/Repo.",
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
                        errors.append(f"Row {i+1}: Return date is before haul date.")
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
                    delivery, free_days, rate, events, fixed, int(num_bins)
                )
                render_results(results, events, num_bins, customer, delivery)

    # ─── MODE B: Individual pickers ───────────
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
                    value=delivery + timedelta(days=10 * (i + 1)),
                )
            with c2:
                ev_type = st.selectbox(
                    "Type",
                    type_options,
                    key=f"type{i}",
                )
            with c3:
                if ev_type == "S/Rtn":
                    return_date = st.date_input("Return date", key=f"ret{i}", value=haul)
                else:
                    return_date = haul
                    st.markdown("_(rental ends)_")
            with c4:
                bin_choice = st.selectbox("Bin (if known)", bin_options, key=f"bin{i}")

            if return_date < haul:
                errors.append(f"Event {i+1}: Return date is before haul date.")

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
                    delivery, free_days, rate, events, fixed, int(num_bins)
                )
                render_results(results, events, num_bins, customer, delivery)

# ─── Tab 2: History ───────────────────────────
with tab2:
    st.header("📚 Customer history")
    history = load_history()

    if not history:
        st.info("No history yet. Run a calculation with a customer name filled in to start logging.")
    else:
        customers = sorted(set(h["customer"] for h in history))
        selected_customer = st.selectbox("Choose a customer", ["(all customers)"] + customers)

        filtered = history if selected_customer == "(all customers)" else [
            h for h in history if h["customer"] == selected_customer
        ]

        st.write(f"Showing **{len(filtered)}** record(s)")

        rows = []
        for h in filtered:
            event_dates = [e["haul_date"] for e in h["events"]]
            date_range = f"{min(event_dates)} → {max(event_dates)}" if event_dates else "—"
            rows.append({
                "Customer": h["customer"],
                "Delivery": h["delivery_date"],
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
