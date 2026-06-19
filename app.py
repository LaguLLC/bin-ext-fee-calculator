from datetime import date
from itertools import product

# Event types
SERVICE_RETURN = "service_return"   # bin emptied and returned (clock resets on return date)
REPO = "repo"                       # final pickup, rental ends

def calculate_allocations(
    delivery_date,
    free_days,
    rate_per_day,
    events,
    fixed_assignments=None,
    num_bins=2,
):
    """
    Enumerate all bin-allocation scenarios and compute extension fees.

    Args:
        delivery_date: date when bins were dropped off.
        free_days: included rental days per cycle (e.g., 10).
        rate_per_day: $ charged per extension day (e.g., 50).
        events: list of dicts, each with:
            {
                "label": "May 11",           # display label
                "haul_date": date(...),      # date bin was picked up
                "return_date": date(...),    # date bin returned (same as haul if same-day)
                "type": SERVICE_RETURN or REPO,
            }
            For REPO events, return_date is ignored (rental ends).
            For SERVICE_RETURN events, return_date >= haul_date.
            Off-site days (return_date - haul_date) are NOT billed.
        fixed_assignments: dict mapping event index -> bin number.
        num_bins: number of bins on site (default 2).

    Returns:
        List of scenario dicts sorted by total fee ascending.
    """
    fixed_assignments = fixed_assignments or {}
    n = len(events)
    free_indices = [i for i in range(n) if i not in fixed_assignments]

    def fee_for_bin(bin_events):
        """
        Compute extension fee for one bin given chronological events.
        Cycle starts at delivery (or last return_date) and ends on next haul_date.
        Cycle length = (haul_date - cycle_start).days + 1
        Extension = max(0, cycle_length - free_days) * rate
        """
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
            # If repo, rental ends. If service-return, next cycle starts on return_date.
            if ev["type"] == REPO:
                break
            cycle_start = ev["return_date"]
        return fee, breakdown

    results = []
    for combo in product(range(1, num_bins + 1), repeat=len(free_indices)):
        assignment = dict(fixed_assignments)
        for idx, bin_num in zip(free_indices, combo):
            assignment[idx] = bin_num

        # Group events by bin, sorted chronologically
        bins = {b: [] for b in range(1, num_bins + 1)}
        for i, ev in enumerate(events):
            bins[assignment[i]].append(ev)
        for b in bins:
            bins[b].sort(key=lambda e: e["haul_date"])

        # Validate: each bin should have at most one REPO event, and it should be last
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

        # Compute fees
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


# ───────────────────────────────────────────
# Example: current customer (all same-day)
# ───────────────────────────────────────────
if __name__ == "__main__":
    events = [
        {"label": "May 6",  "haul_date": date(2026, 5, 6),  "return_date": date(2026, 5, 6),  "type": SERVICE_RETURN},
        {"label": "May 11", "haul_date": date(2026, 5, 11), "return_date": date(2026, 5, 11), "type": SERVICE_RETURN},
        {"label": "May 12", "haul_date": date(2026, 5, 12), "return_date": date(2026, 5, 12), "type": SERVICE_RETURN},
        {"label": "May 19", "haul_date": date(2026, 5, 19), "return_date": date(2026, 5, 19), "type": REPO},
        {"label": "May 27", "haul_date": date(2026, 5, 27), "return_date": date(2026, 5, 27), "type": REPO},
    ]

    results = calculate_allocations(
        delivery_date=date(2026, 4, 27),
        free_days=10,
        rate_per_day=50,
        events=events,
        fixed_assignments={3: 1, 4: 2},  # May 19 → Bin 1 repo; May 27 → Bin 2 repo
    )

    print(f"{'#':<3} {'Bin 1':<35} {'Bin 2':<35} {'Fee 1':>7} {'Fee 2':>7} {'Total':>7}")
    print("-" * 100)
    for i, r in enumerate(results, 1):
        b1 = ", ".join(r["assignment"][1]) or "(none)"
        b2 = ", ".join(r["assignment"][2]) or "(none)"
        print(f"{i:<3} {b1:<35} {b2:<35} ${r['fees'][1]:>5} ${r['fees'][2]:>5} ${r['total']:>5}")

  import streamlit as st
from datetime import date, timedelta
# (paste the calculate_allocations function and constants above)

st.set_page_config(page_title="Roll-Off Bin Fee Calculator", layout="wide")
st.title("🚛 Roll-Off Bin Extension Fee Calculator")

with st.sidebar:
    st.header("Rental Terms")
    free_days = st.number_input("Free rental days per cycle", value=10, min_value=1)
    rate = st.number_input("Extension fee per day ($)", value=50.0, min_value=0.0)
    num_bins = st.number_input("Number of bins on site", value=2, min_value=1, max_value=5)
    st.caption("Off-site days (between haul and return) are not billed.")

col1, col2 = st.columns([1, 2])
with col1:
    customer = st.text_input("Customer name", "")
    delivery = st.date_input("Delivery date", value=date.today() - timedelta(days=30))
    n_events = st.number_input("Number of events", value=5, min_value=1, max_value=12)

st.subheader("Events")
st.caption("Mark each event as service-and-return (with optional off-site gap) or final repo.")

events = []
fixed = {}
bin_options = ["Unknown"] + [f"Bin {b+1}" for b in range(int(num_bins))]

for i in range(int(n_events)):
    cols = st.columns([1.5, 1.5, 1.5, 1.5, 1.5])
    with cols[0]:
        haul = st.date_input(f"Event {i+1} haul date", key=f"haul{i}", value=delivery + timedelta(days=10*(i+1)))
    with colsev_type = st.selectbox("Type", ["Service & return", "Final repo"], key=f"type{i}")
    with cols[2]:
        if ev_type == "Service & return":
            return_date = st.date_input("Return date", key=f"ret{i}", value=haul)
        else:
            return_date = haul
            st.markdown("_(rental ends)_")
    with colsbin_choice = st.selectbox("Bin (if known)", bin_options, key=f"bin{i}")
    with colsst.text_input("Label (optional)", value=haul.strftime("%b %-d"), key=f"lbl{i}", disabled=True)

    events.append({
        "label": haul.strftime("%b %-d"),
        "haul_date": haul,
        "return_date": return_date,
        "type": REPO if ev_type == "Final repo" else SERVICE_RETURN,
    })
    if bin_choice != "Unknown":
        fixed[i] = int(bin_choice.split()[-1])

if st.button("🧮 Calculate all scenarios", type="primary"):
    results = calculate_allocations(delivery, free_days, rate, events, fixed, int(num_bins))

    if not results:
        st.error("No valid scenarios — check that each bin has at most one repo and it's the last event.")
    else:
        st.success(f"✅ Found {len(results)} valid scenario(s)")

        # Summary metrics
        m1, m2, m3 = st.columns(3)
        m1.metric("Lowest total fee", f"${results[0]['total']:,.0f}")
        m2.metric("Highest total fee", f"${results[-1]['total']:,.0f}")
        m3.metric("Range", f"${results[-1]['total'] - results[0]['total']:,.0f}")

        # Table
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

        # Drill-down
        st.subheader("📋 Scenario breakdown")
        choice = st.selectbox("View detailed cycle math for scenario:", range(1, len(results) + 1))
        r = results[choice - 1]
        for b in range(1, int(num_bins) + 1):
            with st.expander(f"Bin {b} — ${r['fees'],.0f}"):
                for c in r["breakdowns"]st.write(
                        f"• {c['cycle_start']} → {c['haul_date']}: "
                        f"{c['cycle_days']} days, {c['ext_days']} over → **${c['fee']:,.0f}**"
                    )
