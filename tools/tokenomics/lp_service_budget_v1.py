"""Exact research model for funded service commitments; grants no authority.

Run: python3 tools/tokenomics/lp_service_budget_v1.py > report.json
Coefficients below are proof-test domains, never proposed governance settings.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path


def nonnegative(*values: int) -> None:
    if any(type(value) is not int or value < 0 for value in values):
        raise ValueError("expected nonnegative integer atoms")


@dataclass(frozen=True)
class AssetBudget:
    """Disjoint same-asset ownership buckets, not independently spendable totals."""

    asset: str
    principal: int
    earned_claims: int
    contract_escrow: int
    risk_reserve: int
    burn_reserve: int
    free: int

    def __post_init__(self) -> None:
        if type(self.asset) is not str or not self.asset:
            raise ValueError("asset identity required")
        nonnegative(*self.amounts)

    @property
    def amounts(self) -> tuple[int, ...]:
        return (self.principal, self.earned_claims, self.contract_escrow,
                self.risk_reserve, self.burn_reserve, self.free)

    @property
    def physical_atoms(self) -> int:
        return sum(self.amounts)


def reserve_service(budget: AssetBudget, payment_cap: int) -> AssetBudget:
    nonnegative(payment_cap)
    if payment_cap > budget.free:
        raise ValueError("unencumbered funding insufficient")
    return replace(budget, contract_escrow=budget.contract_escrow + payment_cap,
                   free=budget.free - payment_cap)


def fee_partition(fee: int, shares: tuple[int, ...], denominator: int) -> tuple[int, ...]:
    """One fee occurrence: named shares plus one owned rounding remainder."""
    nonnegative(fee, denominator, *shares)
    if denominator == 0 or sum(shares) > denominator:
        raise ValueError("fee allocation exceeds denominator")
    allocated = tuple(fee * share // denominator for share in shares)
    return (*allocated, fee - sum(allocated))


def terminal_claims(funded_cap: int, earned_total: int, paid_total: int) -> tuple[int, int]:
    """Partition the original cap, not the current physical escrow balance.

    Remaining physical escrow is funded_cap - paid_total. Returned atoms belong
    to the earned-but-unpaid provider and the original funder respectively.
    """
    nonnegative(funded_cap, earned_total, paid_total)
    if not paid_total <= earned_total <= funded_cap:
        raise ValueError("invalid earned/paid/escrow order")
    return earned_total - paid_total, funded_cap - earned_total


def service_entitlement(fees: int, numerator: int, denominator: int, cap: int) -> int:
    nonnegative(fees, numerator, denominator, cap)
    if denominator == 0 or numerator > denominator:
        raise ValueError("invalid frozen participation rate")
    return min(cap, numerator * fees // denominator)


def usage_weighted_reward(budget: int, own_usage: int, other_usage: int) -> int:
    """Unmitigated comparison policy: usage changes claims to an existing pool."""
    nonnegative(budget, own_usage, other_usage)
    total = own_usage + other_usage
    return budget * own_usage // total if total else 0


@dataclass(frozen=True)
class ServiceLot:
    lot_id: str
    position_id: str
    price: int


def select_unit_lots(lots: tuple[ServiceLot, ...], quantity: int, budget: int) -> tuple[str, ...]:
    """Minimum ask-cost for identical, independently deliverable one-unit lots.

    Position identity here is input data, not a verified collateral witness.
    """
    nonnegative(quantity, budget, *(lot.price for lot in lots))
    if len({lot.lot_id for lot in lots}) != len(lots):
        raise ValueError("duplicate lot identity")
    if len({lot.position_id for lot in lots}) != len(lots):
        raise ValueError("position already committed")
    if quantity > len(lots):
        raise ValueError("service quantity unavailable")
    chosen = sorted(lots, key=lambda lot: (lot.price, lot.lot_id))[:quantity]
    if sum(lot.price for lot in chosen) > budget:
        raise ValueError("unencumbered funding insufficient")
    return tuple(sorted(lot.lot_id for lot in chosen))


def _check_partitions() -> tuple[int, int]:
    budget_cases = 0
    for fee, denominator in product(range(25), range(1, 9)):
        for burn, service in product(range(denominator + 1), repeat=2):
            if burn + service > denominator:
                continue
            allocation = fee_partition(fee, (burn, service), denominator)
            if sum(allocation) != fee or min(allocation) < 0:
                raise RuntimeError("fee ownership partition failed")
            budget_cases += 1
    terminal_cases = 0
    for escrow in range(25):
        for earned in range(escrow + 1):
            for paid in range(earned + 1):
                provider, refund = terminal_claims(escrow, earned, paid)
                if provider + refund != escrow - paid:
                    raise RuntimeError("terminal partition failed")
                terminal_cases += 1

    return budget_cases, terminal_cases


def _check_floor_bounds() -> int:
    import z3

    # Each fixed coefficient query has unbounded nonnegative F, W and cap.
    coefficient_pairs = {(d, n) for d in range(1, 17) for n in range(d + 1)}
    coefficient_pairs.update((10_000, n) for n in (0, 1, 2500, 9999, 10_000))
    fees, wash, cap = z3.Ints("fees wash cap")
    for denominator, numerator in sorted(coefficient_pairs):
        before = numerator * fees / denominator
        after = numerator * (fees + wash) / denominator
        bounded_before = z3.If(before <= cap, before, cap)
        bounded_after = z3.If(after <= cap, after, cap)
        solver = z3.Solver()
        solver.set(timeout=3000)
        solver.add(fees >= 0, wash >= 0, cap >= 0)
        solver.add(z3.Or(after - before > wash, bounded_after - bounded_before > wash))
        verdict = solver.check()
        if verdict != z3.unsat:
            raise RuntimeError(f"floor bound unqualified: {denominator}/{numerator}: {verdict}")
    return len(coefficient_pairs)


def _check_procurement() -> int:
    # Exact independent small-set oracle for standardized unit procurement.
    auction_cases = 0
    for prices in product(range(4), repeat=4):
        lots = tuple(ServiceLot(str(i), f"position-{i}", price) for i, price in enumerate(prices))
        for quantity in range(5):
            chosen = select_unit_lots(lots, quantity, sum(prices))
            choices = combinations(lots, quantity)
            expected = min((sum(lot.price for lot in c), tuple(sorted(lot.lot_id for lot in c)))
                           for c in choices)[1]
            if chosen != expected:
                raise RuntimeError("unit procurement differs from exhaustive oracle")
            auction_cases += 1
    return auction_cases


def falsifying_controls() -> dict[str, dict[str, object]]:
    """Evaluate premise-breaking comparison policies; no market execution."""
    physical, principal, payment = 100, 100, 1
    fee, subsidy = 1, 2
    before_usage, after_usage, reward_pool = 0, 1, 10
    old_reward = usage_weighted_reward(reward_pool, before_usage, 0)
    new_reward = usage_weighted_reward(reward_pool, after_usage, 0)
    before = fee_partition(1, (1, 1), 2)
    after = fee_partition(2, (1, 1), 2)
    # Heterogeneous indivisible units: ratio order and an exhaustive cover oracle.
    lots, required = ((6, 6), (10, 11)), 10
    greedy_cost = greedy_units = 0
    for units, price in sorted(lots, key=lambda lot: Fraction(lot[1], lot[0])):
        if greedy_units < required:
            greedy_units += units
            greedy_cost += price
    optimal_cost = min(sum(price for _, price in choice)
                       for n in range(len(lots) + 1) for choice in combinations(lots, n)
                       if sum(units for units, _ in choice) >= required)
    winning_asks = (1, 9)
    for ask in winning_asks:
        selected = select_unit_lots((ServiceLot("a", "a", ask), ServiceLot("b", "b", 10)), 1, 10)
        if selected != ("a",):
            raise RuntimeError("reported-ask markup control lost its winner")

    falsifiers: dict[str, dict[str, object]] = {
        "principal_as_income": {"physical": physical, "principal_claim": principal,
                                "reward_paid": payment, "remaining_cover_gap": principal - (physical - payment)},
        "subsidy_unlocked_by_usage": {"fee": fee, "previous_reward": 0,
                                     "new_reward": subsidy * int(after_usage > 0),
                                     "incremental_profit": subsidy * int(after_usage > 0) - fee},
        "claim_weight_changes": {"fee_budget": reward_pool, "previous_weight": before_usage,
                                  "new_weight": after_usage, "fee": fee,
                                  "previous_reward": old_reward, "new_reward": new_reward,
                                  "incremental_profit": new_reward - old_reward - fee},
        "duplicate_fee_destinations": {"fee": 10, "burn": 6, "service": 6,
                                        "unfunded_atoms": sum((6, 6)) - 10},
        "rounding_unlocks_old_carry": {"fees_before": 1, "added_fee": 1,
                                       "payout_before": sum(before[:-1]), "payout_after": sum(after[:-1]),
                                       "owned_carry_before": before[-1], "owned_carry_after": after[-1],
                                       "payout_increment_above_new_fee": sum(after[:-1]) - sum(before[:-1]) - 1},
        "heterogeneous_ratio_greedy": {"required_units": required, "lots": lots,
                                       "greedy_cost": greedy_cost, "optimal_cost": optimal_cost},
        "pay_as_bid_markup": {"true_cost": 1, "winning_asks": winning_asks,
                              "utility_increase": (winning_asks[1] - 1) - (winning_asks[0] - 1)},
    }
    return falsifiers


def replay() -> dict[str, object]:
    import z3  # Existing local solver, optional outside this research command.

    budget_cases, terminal_cases = _check_partitions()
    floor_queries, auction_cases = _check_floor_bounds(), _check_procurement()
    library = Path(z3.__file__).parent / "lib" / "libz3.so"
    return {
        "schema": "zenodex/research-lp-service-budget/v1",
        "authority": "NONE", "production_promotion": False,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "z3_version": z3.get_version_string(),
        "z3_library_sha256": hashlib.sha256(library.read_bytes()).hexdigest(),
        "fee_partition_cases": budget_cases, "terminal_partition_cases": terminal_cases,
        "unit_procurement_cases": auction_cases,
        "unbounded_fee_wash_cap_unsat_queries": floor_queries,
        "coefficient_domain": "D=1..16, l=0..D; D=10000, l in {0,1,2500,9999,10000}",
        "falsifiers": falsifying_controls(),
        "nonclaims": ["no general trading or coalition strategyproofness",
                      "service verification and third-party demand are external premises",
                      "no runtime refinement or selected governance coefficients"],
    }


if __name__ == "__main__":
    print(json.dumps(replay(), sort_keys=True, indent=2))
