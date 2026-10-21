#!/usr/bin/env python3
"""Bounded regression witness for fee-aware routing nonconcavity.

This tool does not grant protocol authority. It mirrors the production v8 integer
fee/output formulas, checks the universal Lean witness pattern over a configured
finite grade range, and emits two concrete optimizer counterexamples:

* decreasing exact-out threshold increments; and
* failure of a unit-at-a-time marginal-cost greedy allocator.

The corresponding all-grades theorem candidate lives in
``lean-mathlib/Proofs/FeeAwareRoutingNonconcavity.lean``.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Sequence
from typing import Any

FEE_DENOMINATOR = 10_000


def ceil_div(numerator: int, denominator: int) -> int:
    """Return ceil(numerator / denominator) for nonnegative integers."""

    if numerator < 0:
        raise ValueError("numerator must be nonnegative")
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (numerator + denominator - 1) // denominator


def compute_fee(gross_input: int, fee_bps: int) -> int:
    """Mirror the v8 ceiling fee."""

    if gross_input < 0:
        raise ValueError("gross_input must be nonnegative")
    if not 0 <= fee_bps < FEE_DENOMINATOR:
        raise ValueError("fee_bps must be in [0, 10000)")
    return ceil_div(gross_input * fee_bps, FEE_DENOMINATOR)


def swap_output(
    reserve_in: int,
    reserve_out: int,
    gross_input: int,
    fee_bps: int,
) -> int:
    """Mirror the v8 exact-in CPMM output formula."""

    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("reserves must be positive")
    if gross_input < 0:
        raise ValueError("gross_input must be nonnegative")
    net_input = gross_input - compute_fee(gross_input, fee_bps)
    return reserve_out * net_input // (reserve_in + net_input)


def min_gross_for_output(
    reserve_in: int,
    reserve_out: int,
    target_output: int,
    fee_bps: int,
    *,
    max_gross: int = 1_000_000,
) -> int:
    """Return the first gross input whose exact quote reaches target_output."""

    if target_output < 0:
        raise ValueError("target_output must be nonnegative")
    if target_output == 0:
        return 0
    for gross_input in range(max_gross + 1):
        if swap_output(reserve_in, reserve_out, gross_input, fee_bps) >= target_output:
            return gross_input
    raise RuntimeError("search bound did not reach target_output")


def unit_greedy(cost_tables: Sequence[Sequence[int]], target_output: int) -> tuple[list[int], int]:
    """Allocate one output quota at a time using the cheapest next increment.

    Ties are resolved by the lowest pool index. This is the tempting greedy rule
    invalidated by the concrete witness below; it is not the repository's exact
    staircase dynamic program.
    """

    allocation = [0 for _ in cost_tables]
    unreachable = 1 << 255
    for _ in range(target_output):
        marginal_costs: list[int] = []
        for pool_index, costs in enumerate(cost_tables):
            quota = allocation[pool_index]
            if quota + 1 >= len(costs):
                marginal_costs.append(unreachable)
            else:
                marginal_costs.append(costs[quota + 1] - costs[quota])
        chosen = min(range(len(marginal_costs)), key=lambda i: (marginal_costs[i], i))
        allocation[chosen] += 1
    total_cost = sum(cost_tables[i][allocation[i]] for i in range(len(allocation)))
    return allocation, total_cost


def exact_two_pool_quota_optimum(
    cost_tables: Sequence[Sequence[int]],
    target_output: int,
) -> tuple[list[int], int]:
    """Enumerate the exact two-pool quota split with a canonical tie-break."""

    if len(cost_tables) != 2:
        raise ValueError("the bounded witness requires exactly two pools")
    candidates: list[tuple[int, tuple[int, int]]] = []
    for first_quota in range(target_output + 1):
        allocation = (first_quota, target_output - first_quota)
        if any(allocation[i] >= len(cost_tables[i]) for i in range(2)):
            continue
        total_cost = sum(cost_tables[i][allocation[i]] for i in range(2))
        candidates.append((total_cost, allocation))
    if not candidates:
        raise RuntimeError("no feasible quota allocation")
    total_cost, allocation = min(candidates)
    return list(allocation), total_cost


def build_report(max_grade: int) -> dict[str, Any]:
    """Construct and verify the canonical bounded evidence report."""

    if max_grade < 0:
        raise ValueError("max_grade must be nonnegative")

    for grade in range(max_grade + 1):
        reserve_out = 2 * (grade + 1)
        outputs = [swap_output(1, reserve_out, gross, 1) for gross in range(3)]
        expected = [0, 0, grade + 1]
        if outputs != expected:
            raise AssertionError(
                f"family witness drift at grade={grade}: outputs={outputs}, expected={expected}"
            )
        if not outputs[2] + outputs[0] > 2 * outputs[1] + grade:
            raise AssertionError(f"second-difference witness failed at grade={grade}")

    threshold_costs = [min_gross_for_output(1, 3, quota, 1) for quota in range(3)]
    threshold_increments = [
        threshold_costs[1] - threshold_costs[0],
        threshold_costs[2] - threshold_costs[1],
    ]
    if threshold_increments != [2, 1]:
        raise AssertionError(f"decreasing-threshold witness drift: {threshold_increments}")

    identical_pool_costs = [min_gross_for_output(1, 7, quota, 1) for quota in range(7)]
    greedy_allocation, greedy_total = unit_greedy(
        [identical_pool_costs, identical_pool_costs],
        6,
    )
    optimal_allocation, optimal_total = exact_two_pool_quota_optimum(
        [identical_pool_costs, identical_pool_costs],
        6,
    )
    if (greedy_allocation, greedy_total) != ([5, 1], 6):
        raise AssertionError("unit-greedy witness drift")
    if (optimal_allocation, optimal_total) != ([3, 3], 4):
        raise AssertionError("global-optimum witness drift")

    return {
        "authority": {
            "claim": (
                "bounded regression evidence only; Lean carries the universal theorem candidate"
            ),
            "production_authority": False,
            "settlement_authority": False,
        },
        "decreasing_threshold_witness": {
            "minimum_gross_for_output_quota_0_to_2": threshold_costs,
            "reserve_in": 1,
            "reserve_out": 3,
            "strictly_decreasing": True,
            "threshold_increments": threshold_increments,
        },
        "fee_semantics": {
            "fee_bps": 1,
            "fee_denominator": FEE_DENOMINATOR,
            "formula": (
                "fee(g)=ceil(g*fee_bps/10000); net=g-fee(g); "
                "out=floor(y*net/(x+net))"
            ),
        },
        "schema_version": 1,
        "unbounded_family_regression": {
            "all_checked": True,
            "checked_grade_max": max_grade,
            "checked_grade_min": 0,
            "gross_inputs": [0, 1, 2],
            "outputs_formula": ["0", "0", "grade+1"],
            "positive_second_difference_formula": "grade+1",
            "reserve_in": 1,
            "reserve_out_formula": "2*(grade+1)",
        },
        "unit_greedy_counterexample": {
            "global_allocation": optimal_allocation,
            "global_total_gross": optimal_total,
            "gross_gap": greedy_total - optimal_total,
            "minimum_gross_cost_table_for_quota_0_to_6": identical_pool_costs,
            "pools": [
                {"fee_bps": 1, "reserve_in": 1, "reserve_out": 7},
                {"fee_bps": 1, "reserve_in": 1, "reserve_out": 7},
            ],
            "relative_excess_bps": (greedy_total - optimal_total) * 10_000 // optimal_total,
            "target_output_quota": 6,
            "unit_greedy_allocation": greedy_allocation,
            "unit_greedy_tie_break": "lowest_pool_index",
            "unit_greedy_total_gross": greedy_total,
        },
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-grade", type=int, default=10_000)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = build_report(args.max_grade)
    except (AssertionError, RuntimeError, ValueError) as exc:
        print(json.dumps({"ok": False, "error": str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    output = {"ok": True, **report}
    if args.pretty:
        print(json.dumps(output, indent=2, sort_keys=True))
    else:
        print(json.dumps(output, separators=(",", ":"), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
