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

Usage:
  python3 tools/route_mev_liveness_analysis.py          # print analysis
  python3 tools/route_mev_liveness_analysis.py --check   # fail-closed check
"""

from __future__ import annotations

import math
import sys
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
    print("A route is rejected if any of its pools is touched by a prior")
    print("pool-mutating tx (writer OR prior route). For route-writer conflicts,")
    print("the same-sender barrier blocks lifting. For route-route conflicts,")
    print("the scheduler selects one route to win; the other is rejected.")
    print("")
    print("The rejection rate depends on the same-sender prefix ordering in")
    print("stable_route_lift, NOT a simple birthday bound. A precise estimate")
    print("requires simulation of the scheduler over realistic tx mixes.")
    print("")
    print("Three distinct probability quantities are relevant:")
    print("  RW per-route:  P(this route's pools overlap any prior writer)")
    print("  RR per-route:  P(this route's k pools overlap any prior route's k pools)")
    print("  Combined:      P(RW ∪ RR) = 1-(1-RW)(1-RR) under independence")
    print("  Batch RW:      P(at least one route collides with a writer)")
    print("")
    print("RR uses k²/n_pools overlap probability for two k-pool routes.")
    print("")
    print(f"{'routes':>8} {'writers':>8} {'pools':>8} {'ppr':>6} "
          f"{'RW%':>8} {'RR%':>8} {'comb%':>8} {'batchRW%':>10}")
    for n_routes, n_writers, n_pools, ppr in [
        (1, 1, 10, 1),
        (5, 5, 50, 2),
        (10, 10, 100, 2),
        (20, 20, 200, 3),
        (50, 50, 500, 3),
        (100, 100, 1000, 4),
    ]:
        rw = (1.0 - math.exp(-ppr * n_writers / n_pools)) * 100
        rr = (1.0 - math.exp(-(ppr * ppr) * (n_routes - 1) / n_pools)) * 100
        combined = (1.0 - (1.0 - rw / 100) * (1.0 - rr / 100)) * 100
        batch_rw = (1.0 - math.exp(-n_routes * ppr * n_writers / n_pools)) * 100
        print(f"{n_routes:>8} {n_writers:>8} {n_pools:>8} {ppr:>6} "
              f"{rw:>7.2f}% {rr:>7.2f}% {combined:>7.2f}% {batch_rw:>9.2f}%")

    print("\nBounds on per-route rejection rate:")
    print("  Distribution-free upper bound: min(1, rw + rr)  [union bound]")
    print("  Independence-based estimate:   1-(1-rw)(1-rr)   [Combined % column]")
    print("  Lower (distribution-free): zero — a route with no conflicting")
    print("  prior txs is never rejected. For a concrete conflicting batch")
    print("  with route-route same-pool overlap, realized rejection is positive.")
    print("A precise estimate requires scheduler simulation.")

    print("\n" + "=" * 72)
    print("CONCLUSION")
    print("=" * 72)
    print("""
The stale-quote defense (quote_receipt_hash) is the PRIMARY MEV barrier
for same-route-pool front-run sandwiches, reducing them to zero. Sandwiches
ARE profitable at 30 bps fee (contrary to a naive fee-drag argument), so
the defense is necessary, not merely defense-in-depth.

The liveness collision probabilities are Poisson approximations of pool
overlap events. The distribution-free rejection ceiling is the union bound
min(1, P(rw)+P(rr)); the Combined % column is an independence-based point
estimate, not a bound. The actual rejection rate depends on same-sender
prefix ordering in stable_route_lift. A precise estimate requires scheduler
simulation.

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


# Expected values for --check mode (fail-closed drift detection)
EXPECTED_SANDWICH_30BPS = {
    (10_000, 50_000): (640, 912),
    (10_000, 100_000): (1185, 1704),
    (10_000, 500_000): (3538, 5465),
    (100_000, 500_000): (54273, 49070),
    (100_000, 1_000_000): (11857, 17037),
}

EXPECTED_FEE_SENSITIVITY = {
    1: (1721, 1711),
    3: (1685, 1711),
    10: (1556, 1709),
    30: (1185, 1704),
    100: (-110, 1686),
    300: (-3775, 1638),
}

# (n_routes, n_writers, n_pools, ppr) -> (rw_pct, rr_pct, combined_pct, batch_rw_pct)
EXPECTED_COLLISION_TABLE = {
    (1, 1, 10, 1): (9.52, 0.00, 9.52, 9.52),
    (5, 5, 50, 2): (18.13, 27.39, 40.55, 63.21),
    (10, 10, 100, 2): (18.13, 30.23, 42.88, 86.47),
    (20, 20, 200, 3): (25.92, 57.47, 68.49, 99.75),
    (50, 50, 500, 3): (25.92, 58.60, 69.33, 100.00),
    (100, 100, 1000, 4): (32.97, 79.48, 86.25, 100.00),
}


def _approx(a: float, b: float, tol: float = 0.1) -> bool:
    return abs(a - b) < tol


def check() -> int:
    """Fail-closed check: verify all printed tables match expected values."""
    failures: List[str] = []

    # Q1: Sandwich payoff table (profit + victim_loss)
    for (victim_in, attacker_cap), (exp_profit, exp_loss) in EXPECTED_SANDWICH_30BPS.items():
        r_in = 10_000_000 if attacker_cap == 1_000_000 else 1_000_000
        s = sandwich_single_pool(victim_in, r_in, r_in, 30, attacker_cap)
        if s.attacker_profit != exp_profit:
            failures.append(
                f"Q1 victim={victim_in} attacker={attacker_cap}: "
                f"expected profit={exp_profit}, got {s.attacker_profit}"
            )
        if s.victim_loss != exp_loss:
            failures.append(
                f"Q1 victim={victim_in} attacker={attacker_cap}: "
                f"expected loss={exp_loss}, got {s.victim_loss}"
            )

    # Q2: Fee sensitivity table (profit + victim_loss)
    for fee_bps, (exp_profit, exp_loss) in EXPECTED_FEE_SENSITIVITY.items():
        s = sandwich_single_pool(10_000, 1_000_000, 1_000_000, fee_bps, 100_000)
        if s.attacker_profit != exp_profit:
            failures.append(
                f"Q2 fee={fee_bps}: expected profit={exp_profit}, got {s.attacker_profit}"
            )
        if s.victim_loss != exp_loss:
            failures.append(
                f"Q2 fee={fee_bps}: expected loss={exp_loss}, got {s.victim_loss}"
            )

    # Q4: Collision table (per-route RW, per-route RR, combined, batch RW)
    for (n_r, n_w, n_p, ppr), (exp_rw, exp_rr, exp_comb, exp_batch) in EXPECTED_COLLISION_TABLE.items():
        rw = (1.0 - math.exp(-ppr * n_w / n_p)) * 100
        rr = (1.0 - math.exp(-(ppr * ppr) * (n_r - 1) / n_p)) * 100
        combined = (1.0 - (1.0 - rw / 100) * (1.0 - rr / 100)) * 100
        batch = (1.0 - math.exp(-n_r * ppr * n_w / n_p)) * 100
        if not _approx(rw, exp_rw):
            failures.append(f"Q4 ({n_r},{n_w},{n_p},{ppr}): RW={rw:.2f}% expected={exp_rw}%")
        if not _approx(rr, exp_rr):
            failures.append(f"Q4 ({n_r},{n_w},{n_p},{ppr}): RR={rr:.2f}% expected={exp_rr}%")
        if not _approx(combined, exp_comb):
            failures.append(f"Q4 ({n_r},{n_w},{n_p},{ppr}): combined={combined:.2f}% expected={exp_comb}%")
        if not _approx(batch, exp_batch):
            failures.append(f"Q4 ({n_r},{n_w},{n_p},{ppr}): batch={batch:.2f}% expected={exp_batch}%")

    if failures:
        for f in failures:
            print(f"FAIL: {f}", file=sys.stderr)
        return 1
    print("OK: all sandwich, fee-sensitivity, and collision table values match expected", file=sys.stderr)
    return 0


if __name__ == "__main__":
    if "--check" in sys.argv:
        sys.exit(check())
    main()
