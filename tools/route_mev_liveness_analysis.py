"""RC25 Route MEV/Liveness Economic Analysis.

Models the sandwich attack payoff boundaries under the stale-quote rejection
defense (quote_receipt_hash binding) and the tx-ordering schedulers
(stable_route_lift, component_repair). Quantifies the liveness cost of
stale-quote rejection vs executing at bad prices.

Three defense layers analyzed:
  1. quote_receipt_hash: binds pool reserves into the route intent. If any
     pool in the route is touched by a prior tx in the same block, the hash
     mismatches and the route is REJECTED.
  2. stable_route_lift: scheduler lifts routes before different-sender pool
     writers, preventing the "front-run" half of a sandwich.
  3. component_repair: FPT scheduler that repairs small conflict components,
     scaling past the bruteforce oracle cap.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import List, Tuple

BPS_DENOM = 10_000


def ceil_div(n: int, d: int) -> int:
    if d == 0:
        return 0
    q, r = divmod(n, d)
    return q + (1 if r > 0 else 0)


def swap_exact_in(amount_in: int, r_in: int, r_out: int, fee_bps: int) -> Tuple[int, int, int]:
    """Returns (amount_out, new_r_in, new_r_out). Matches Rust kernel."""
    fee_total = ceil_div(amount_in * fee_bps, BPS_DENOM)
    net_in = amount_in - fee_total
    amount_out = (r_out * net_in) // (r_in + net_in)
    return amount_out, r_in + amount_in, r_out - amount_out


@dataclass
class SandwichPayoff:
    victim_amount_in: int
    attacker_profit: int
    victim_loss: int
    front_run_amount_in: int
    front_run_amount_out: int
    back_run_amount_in: int


def sandwich_single_pool(
    victim_amount_in: int,
    r_in: int,
    r_out: int,
    fee_bps: int,
    attacker_capital: int,
) -> SandwichPayoff:
    """Classic sandwich attack on a swap_exact_in victim.

    1. Attacker front-runs: swap_exact_in(attacker_capital, r_in, r_out)
    2. Victim swaps: swap_exact_in(victim_amount_in, r_in_1, r_out_1)
    3. Attacker back-runs: swap_exact_in(front_out, r_out_2, r_in_2)
       (swapping asset_out back to asset_in — reverse direction)

    The back-run uses swap_exact_in in the reverse direction (asset_out is
    now the input asset, asset_in is the output). This is the correct model:
    the pool is symmetric, so we swap input=front_out against r_out_2 to
    get output in asset_in.
    """
    # Step 1: Attacker front-runs (asset_in -> asset_out)
    front_out, r_in_1, r_out_1 = swap_exact_in(attacker_capital, r_in, r_out, fee_bps)

    # Step 2: Victim swaps at inflated price (asset_in -> asset_out)
    victim_out, r_in_2, r_out_2 = swap_exact_in(victim_amount_in, r_in_1, r_out_1, fee_bps)

    # Step 3: Attacker back-runs (asset_out -> asset_in)
    # Pool reserves after step 2: r_in_2 (asset_in), r_out_2 (asset_out)
    # Attacker swaps front_out (asset_out) as input, gets asset_in back
    back_in, r_out_3, r_in_3 = swap_exact_in(front_out, r_out_2, r_in_2, fee_bps)

    attacker_profit = back_in - attacker_capital

    # Victim loss vs fair price (no sandwich)
    fair_out, _, _ = swap_exact_in(victim_amount_in, r_in, r_out, fee_bps)
    victim_loss = fair_out - victim_out

    return SandwichPayoff(
        victim_amount_in=victim_amount_in,
        attacker_profit=attacker_profit,
        victim_loss=victim_loss,
        front_run_amount_in=attacker_capital,
        front_run_amount_out=front_out,
        back_run_amount_in=back_in,
    )


def main() -> None:
    print("=" * 72)
    print("RC25 Route MEV/Liveness Economic Analysis")
    print("=" * 72)

    # --- Q1: Sandwich payoff without stale-quote defense ---
    print("\n## Q1: Sandwich payoff (no defense, 30 bps fee)")
    print(f"{'R_in':>10} {'R_out':>10} {'victim_in':>10} {'attacker_cap':>12} "
          f"{'profit':>10} {'victim_loss':>12}")
    for r_in, r_out, victim_in, attacker_cap in [
        (1_000_000, 1_000_000, 10_000, 50_000),
        (1_000_000, 1_000_000, 10_000, 100_000),
        (1_000_000, 1_000_000, 10_000, 500_000),
        (1_000_000, 1_000_000, 100_000, 500_000),
        (10_000_000, 10_000_000, 100_000, 1_000_000),
    ]:
        s = sandwich_single_pool(victim_in, r_in, r_out, 30, attacker_cap)
        print(f"{r_in:>10} {r_out:>10} {victim_in:>10} {attacker_cap:>12} "
              f"{s.attacker_profit:>10} {s.victim_loss:>12}")

    # --- Q2: Effect of fee tier on sandwich profitability ---
    print("\n## Q2: Sandwich payoff vs fee tier (10k victim, 100k attacker, 1M pool)")
    print(f"{'fee_bps':>8} {'profit':>10} {'victim_loss':>12}")
    for fee_bps in [1, 3, 10, 30, 100, 300]:
        s = sandwich_single_pool(10_000, 1_000_000, 1_000_000, fee_bps, 100_000)
        print(f"{fee_bps:>8} {s.attacker_profit:>10} {s.victim_loss:>12}")

    print("\nKey finding: Sandwiches ARE profitable at 30 bps. The attacker's")
    print("back-run benefits from the victim's price impact moving the pool")
    print("in the attacker's favor. Fee drag does NOT dominate at standard tiers.")
    print("The stale-quote defense is the PRIMARY MEV barrier, not defense-in-depth.")

    # --- Q3: Stale-quote defense effect ---
    print("\n## Q3: Effect of stale-quote defense on same-route-pool sandwich")
    print("Under stale-quote rejection, the attacker's front-run touches the")
    print("pool, making the victim's quote_receipt_hash stale. The victim's")
    print("route is REJECTED. Attacker is left with a single swap (no sandwich).")
    print("=> Same-route-pool front-run sandwich MEV = 0 (under quote_receipt_hash)")
    print("")
    print("Narrowed claim: this only blocks sandwiches where the front-run")
    print("touches a pool IN the route. It does NOT block:")
    print("  - Post-route back-running (attacker swaps after victim)")
    print("  - Cross-venue arbitrage (external pools)")
    print("  - Correlated non-route pool manipulation")

    # --- Q4: Liveness cost ---
    print("\n## Q4: Liveness cost of stale-quote rejection")
    print("A route is rejected if any of its pools is touched by a prior tx")
    print("AND the route cannot be lifted before the writer (same-sender barrier).")
    print("")
    print("The rejection rate depends on the same-sender prefix ordering in")
    print("stable_route_lift, NOT a simple birthday bound. A precise estimate")
    print("requires simulation of the scheduler over realistic tx mixes.")
    print("")
    print("Upper bound: if ALL routes share a sender with a prior writer,")
    print("rejection rate = collision_rate. Lower bound: if NO routes share")
    print("a sender, rejection rate = 0 (all routes are lifted).")
    print("")
    print("The birthday collision rate (P(any route-writer pool overlap)) is:")
    print(f"{'routes':>8} {'writers':>8} {'pools':>8} {'ppr':>6} {'collision%':>12}")
    for n_routes, n_writers, n_pools, ppr in [
        (1, 1, 10, 1),
        (5, 5, 50, 2),
        (10, 10, 100, 2),
        (20, 20, 200, 3),
        (50, 50, 500, 3),
        (100, 100, 1000, 4),
    ]:
        expected_collisions = n_routes * ppr * n_writers / n_pools
        collision_rate = 1.0 - math.exp(-expected_collisions)
        print(f"{n_routes:>8} {n_writers:>8} {n_pools:>8} {ppr:>6} "
              f"{collision_rate*100:>11.2f}%")

    print("\nThe actual rejection rate is between 0 and collision_rate,")
    print("depending on the same-sender fraction and scheduler behavior.")
    print("A precise estimate requires simulation, not a closed-form formula.")

    print("\n" + "=" * 72)
    print("CONCLUSION")
    print("=" * 72)
    print("""
The stale-quote defense (quote_receipt_hash) is the PRIMARY MEV barrier
for same-route-pool front-run sandwiches, reducing them to zero. Sandwiches
ARE profitable at 30 bps fee (contrary to a naive fee-drag argument), so
the defense is necessary, not merely defense-in-depth.

The liveness cost is bounded above by the birthday collision rate but
the actual rejection rate depends on same-sender prefix ordering in
stable_route_lift. A precise estimate requires scheduler simulation.

Residual MEV surfaces (NOT blocked by quote_receipt_hash):
  - Post-route back-running (attacker swaps after victim, no front-run)
  - Cross-venue arbitrage (external pools not in the route)
  - Correlated non-route pool manipulation
  - Inclusion/censorship liveness griefing
  - Reference-price staleness

Exact-out overdelivery is bounded by construction (surplus stays in pool),
independent of the stale-quote defense. The defense eliminates the
amplification that would occur if a sandwiched route executed at a bad
price with overdelivery, but the construction itself is the primary bound.
""")


if __name__ == "__main__":
    main()
