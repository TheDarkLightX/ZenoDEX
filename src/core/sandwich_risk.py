"""Sandwich risk estimation (UX + security).

This is *not* a consensus-critical module. It is intended for:
- UI warnings: show when a trade's slippage makes it sandwich-profitable
- deterministic agents: fail-closed gating under bounded search

Model:
  Attacker front-runs (exact-in) in the same direction as the victim,
  victim executes (exact-in) if `victim_out >= victim_min_out`,
  attacker back-runs (exact-in) in the opposite direction with the tokens
  acquired in the front-run.

Output:
  Profit is measured in units of the victim's input asset.

Evidence posture:
  - This module provides a *bounded* exhaustive search, returning `inconclusive`
    if the bound may exclude feasible attacker sizes.
  - Never treat `inconclusive` as "safe".
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from .cpmm import swap_exact_in


@dataclass(frozen=True)
class SandwichRisk:
    status: str  # "ok" | "victim_reverts" | "inconclusive"
    max_profit: int
    attacker_amount_in: int
    victim_amount_out: int
    victim_amount_out_isolated: int
    scanned_max_attacker_amount_in: int


def _inconclusive_risk(*, scanned_max_attacker_amount_in: int) -> SandwichRisk:
    return SandwichRisk(
        status="inconclusive",
        max_profit=0,
        attacker_amount_in=0,
        victim_amount_out=0,
        victim_amount_out_isolated=0,
        scanned_max_attacker_amount_in=int(scanned_max_attacker_amount_in),
    )


def _fee_total_ceil(*, amount_in: int, fee_bps: int) -> int:
    # Keep this local to avoid importing kernel helpers into non-kernel code.
    return (int(amount_in) * int(fee_bps) + 10_000 - 1) // 10_000


def attacker_amount_in_cutoff_upper_bound_cpmm_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    victim_amount_in: int,
    victim_min_out: int,
) -> int | None:
    """Upper bound on attacker size after which the victim MUST revert.

    This uses a continuous upper bound that ignores attacker reserve_out drain,
    making it conservative but deterministic and very cheap.

    Let x,y be pre-attack reserves and let net_v be the victim's exact net_in.
    For attacker size a (exact-in), the victim's output satisfies:

      victim_out_int(a) <= y * net_v / (x + a + net_v)

    Therefore if the RHS is strictly < victim_min_out, then the victim cannot
    execute for that a (and for all larger a).

    Returns:
      cutoff a0 such that for all a >= a0, victim_out < victim_min_out.
      None if victim_min_out <= 0 (no cutoff from this method).
    """
    x = int(reserve_in)
    y = int(reserve_out)
    if x <= 0 or y <= 0:
        raise ValueError("reserves must be positive")
    if int(victim_amount_in) <= 0:
        raise ValueError("victim_amount_in must be positive")
    if int(victim_min_out) <= 0:
        return None
    if int(fee_bps) < 0 or int(fee_bps) > 10_000:
        raise ValueError("fee_bps out of range")

    fee_total = _fee_total_ceil(amount_in=int(victim_amount_in), fee_bps=int(fee_bps))
    net_v = int(victim_amount_in) - int(fee_total)
    if net_v <= 0:
        # Victim output is zero; any positive min_out is impossible even at a=0.
        return 0

    # Solve for the smallest integer a such that:
    #   y*net_v < victim_min_out * (x + a + net_v)
    # i.e.
    #   victim_min_out * a > y*net_v - victim_min_out*(x + net_v)
    lhs = y * net_v
    rhs0 = int(victim_min_out) * (x + net_v)
    gap = lhs - rhs0
    if gap < 0:
        # Already strictly below at a=0.
        return 0
    return int(gap) // int(victim_min_out) + 1


def _try_swap_exact_in(
    *, reserve_in: int, reserve_out: int, amount_in: int, fee_bps: int
) -> tuple[int, tuple[int, int]] | None:
    try:
        out, (new_rin, new_rout) = swap_exact_in(
            reserve_in=int(reserve_in),
            reserve_out=int(reserve_out),
            amount_in=int(amount_in),
            fee_bps=int(fee_bps),
        )
    except (TypeError, ValueError):
        return None
    return int(out), (int(new_rin), int(new_rout))


def sandwich_profit_exact_in_cpmm(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    victim_amount_in: int,
    victim_min_out: int,
    attacker_amount_in: int,
) -> int | None:
    """Compute attacker profit for a given front-run size, or None if victim would not execute."""
    if attacker_amount_in < 0:
        return None
    if victim_amount_in <= 0:
        return None
    if victim_min_out < 0:
        return None

    # 1) Attacker front-run (same direction as victim).
    att1 = _try_swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=attacker_amount_in,
        fee_bps=fee_bps,
    )
    if att1 is None:
        return None
    attacker_amount_out, (rin1, rout1) = att1

    # 2) Victim executes on manipulated reserves.
    vic = _try_swap_exact_in(
        reserve_in=rin1,
        reserve_out=rout1,
        amount_in=victim_amount_in,
        fee_bps=fee_bps,
    )
    if vic is None:
        return None
    victim_amount_out, (rin2, rout2) = vic
    if victim_amount_out < victim_min_out:
        return None

    # 3) Attacker back-run (reverse direction).
    # Reserve order flips because the attacker now swaps the token they bought back into the original input asset.
    att2 = _try_swap_exact_in(
        reserve_in=rout2,
        reserve_out=rin2,
        amount_in=attacker_amount_out,
        fee_bps=fee_bps,
    )
    if att2 is None:
        return None
    attacker_amount_back, _ = att2
    return int(attacker_amount_back) - int(attacker_amount_in)


def max_sandwich_profit_exact_in_cpmm_bounded(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    victim_amount_in: int,
    victim_min_out: int,
    max_attacker_amount_in: int = 5_000,
) -> SandwichRisk:
    """Bounded exhaustive search for max sandwich profit under integer semantics.

    Returns:
      - status="ok": scan covered all attacker sizes that could make the victim execute,
        as proven by a cheap analytic cutoff on attacker size.
      - status="inconclusive": scan may have missed feasible attacker sizes (cap is below the cutoff).
      - status="victim_reverts": victim would not execute even with attacker_amount_in=0.
    """
    if max_attacker_amount_in < 0:
        raise ValueError("max_attacker_amount_in must be non-negative")

    # Baseline: victim output with no attack.
    base = _try_swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=victim_amount_in,
        fee_bps=fee_bps,
    )
    if base is None:
        return SandwichRisk(
            status="victim_reverts",
            max_profit=0,
            attacker_amount_in=0,
            victim_amount_out=0,
            victim_amount_out_isolated=0,
            scanned_max_attacker_amount_in=int(max_attacker_amount_in),
        )
    victim_out_iso, _ = base
    if victim_out_iso < victim_min_out:
        return SandwichRisk(
            status="victim_reverts",
            max_profit=0,
            attacker_amount_in=0,
            victim_amount_out=int(victim_out_iso),
            victim_amount_out_isolated=int(victim_out_iso),
            scanned_max_attacker_amount_in=int(max_attacker_amount_in),
        )

    cutoff = attacker_amount_in_cutoff_upper_bound_cpmm_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fee_bps=fee_bps,
        victim_amount_in=victim_amount_in,
        victim_min_out=victim_min_out,
    )
    if cutoff is None:
        # min_out <= 0: victim can execute at arbitrarily large attacker sizes in principle.
        # We keep the posture conservative (bounded scan only).
        scan_max = int(max_attacker_amount_in)
        covered_all_feasible = False
    else:
        feasible_a_max = max(0, int(cutoff) - 1)
        scan_max = min(int(max_attacker_amount_in), int(feasible_a_max))
        covered_all_feasible = bool(int(max_attacker_amount_in) >= int(feasible_a_max))

    best_profit = 0
    best_a = 0
    best_victim_out = int(victim_out_iso)
    for a in range(0, int(scan_max) + 1):
        att1 = _try_swap_exact_in(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=a,
            fee_bps=fee_bps,
        )
        if att1 is None:
            continue
        attacker_amount_out, (rin1, rout1) = att1

        vic = _try_swap_exact_in(
            reserve_in=rin1,
            reserve_out=rout1,
            amount_in=victim_amount_in,
            fee_bps=fee_bps,
        )
        if vic is None:
            continue
        victim_out, (rin2, rout2) = vic
        if victim_out < victim_min_out:
            continue

        att2 = _try_swap_exact_in(
            reserve_in=rout2,
            reserve_out=rin2,
            amount_in=attacker_amount_out,
            fee_bps=fee_bps,
        )
        if att2 is None:
            continue
        attacker_amount_back, _ = att2

        profit = int(attacker_amount_back) - int(a)
        if profit > best_profit:
            best_profit = int(profit)
            best_a = int(a)
            best_victim_out = int(victim_out)

    status = "ok" if covered_all_feasible else "inconclusive"

    return SandwichRisk(
        status=status,
        max_profit=int(best_profit),
        attacker_amount_in=int(best_a),
        victim_amount_out=int(best_victim_out),
        victim_amount_out_isolated=int(victim_out_iso),
        scanned_max_attacker_amount_in=int(scan_max),
    )


def sandwich_profit_exact_in_cpmm_dynamic_fee(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps_fn: Callable[[int, int, int], int],
    victim_amount_in: int,
    victim_min_out: int,
    attacker_amount_in: int,
) -> int | None:
    """Compute attacker profit under a dynamic fee function (diagnostic only).

    The fee function is evaluated per swap as:
      fee_bps_fn(reserve_in, reserve_out, amount_in)

    Returns None if the victim would revert or if any step is invalid.
    """
    if attacker_amount_in < 0:
        return None
    if victim_amount_in <= 0:
        return None
    if victim_min_out < 0:
        return None

    def _try_dyn(res_in: int, res_out: int, amt_in: int) -> tuple[int, tuple[int, int]] | None:
        try:
            fee_bps = int(fee_bps_fn(int(res_in), int(res_out), int(amt_in)))
        except (TypeError, ValueError):
            return None
        if fee_bps < 0 or fee_bps > 10_000:
            return None
        return _try_swap_exact_in(
            reserve_in=int(res_in),
            reserve_out=int(res_out),
            amount_in=int(amt_in),
            fee_bps=int(fee_bps),
        )

    # 1) Attacker front-run (same direction).
    att1 = _try_dyn(int(reserve_in), int(reserve_out), int(attacker_amount_in))
    if att1 is None:
        return None
    attacker_amount_out, (rin1, rout1) = att1

    # 2) Victim executes.
    vic = _try_dyn(int(rin1), int(rout1), int(victim_amount_in))
    if vic is None:
        return None
    victim_amount_out, (rin2, rout2) = vic
    if victim_amount_out < victim_min_out:
        return None

    # 3) Attacker back-run (reverse direction).
    att2 = _try_dyn(int(rout2), int(rin2), int(attacker_amount_out))
    if att2 is None:
        return None
    attacker_amount_back, _ = att2
    return int(attacker_amount_back) - int(attacker_amount_in)


def max_sandwich_profit_exact_in_cpmm_bounded_dynamic_fee(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps_fn: Callable[[int, int, int], int],
    victim_amount_in: int,
    victim_min_out: int,
    max_attacker_amount_in: int = 5_000,
) -> SandwichRisk:
    """Bounded max sandwich profit under a dynamic fee function.

    Evidence posture:
    - Always returns status=\"inconclusive\" (no analytic cutoff implemented for dynamic fees).
    - Never treat \"inconclusive\" as \"safe\".
    """
    if max_attacker_amount_in < 0:
        raise ValueError("max_attacker_amount_in must be non-negative")

    # Victim isolated out for reporting.
    try:
        fee0 = int(fee_bps_fn(int(reserve_in), int(reserve_out), int(victim_amount_in)))
    except (TypeError, ValueError):
        return _inconclusive_risk(scanned_max_attacker_amount_in=max_attacker_amount_in)
    if fee0 < 0 or fee0 > 10_000:
        return _inconclusive_risk(scanned_max_attacker_amount_in=max_attacker_amount_in)
    iso = _try_swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=victim_amount_in,
        fee_bps=fee0,
    )
    if iso is None:
        victim_iso_out = 0
    else:
        victim_iso_out, _ = iso

    # If victim cannot execute at a=0, mark victim_reverts.
    if victim_iso_out < int(victim_min_out):
        return SandwichRisk(
            status="victim_reverts",
            max_profit=0,
            attacker_amount_in=0,
            victim_amount_out=int(victim_iso_out),
            victim_amount_out_isolated=int(victim_iso_out),
            scanned_max_attacker_amount_in=int(max_attacker_amount_in),
        )

    best_profit = 0
    best_a = 0
    best_victim_out = int(victim_iso_out)

    def _try_dyn(res_in: int, res_out: int, amt_in: int) -> tuple[int, tuple[int, int]] | None:
        try:
            fee_bps = int(fee_bps_fn(int(res_in), int(res_out), int(amt_in)))
        except (TypeError, ValueError):
            return None
        if fee_bps < 0 or fee_bps > 10_000:
            return None
        return _try_swap_exact_in(
            reserve_in=int(res_in),
            reserve_out=int(res_out),
            amount_in=int(amt_in),
            fee_bps=int(fee_bps),
        )

    for a in range(0, int(max_attacker_amount_in) + 1):
        att1 = _try_dyn(int(reserve_in), int(reserve_out), int(a))
        if att1 is None:
            continue
        attacker_out, (rin1, rout1) = att1

        vic = _try_dyn(int(rin1), int(rout1), int(victim_amount_in))
        if vic is None:
            continue
        victim_out, (rin2, rout2) = vic
        if victim_out < victim_min_out:
            continue

        att2 = _try_dyn(int(rout2), int(rin2), int(attacker_out))
        if att2 is None:
            continue
        attacker_back, _ = att2

        profit = int(attacker_back) - int(a)
        if profit > best_profit:
            best_profit = int(profit)
            best_a = int(a)
            best_victim_out = int(victim_out)

    return SandwichRisk(
        status="inconclusive",
        max_profit=int(best_profit),
        attacker_amount_in=int(best_a),
        victim_amount_out=int(best_victim_out),
        victim_amount_out_isolated=int(victim_iso_out),
        scanned_max_attacker_amount_in=int(max_attacker_amount_in),
    )
