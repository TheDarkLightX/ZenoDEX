#!/usr/bin/env python3
"""Bounded SMT evidence for recursive-STARK per-asset conservation.

The model contains two assets, two child rows per asset, and four nonnegative
effect columns: debit, credit, mint, and burn. It proves that checked child-row
equations, checked aggregate bindings, and no-overflow bounds imply the runtime
aggregate conservation equation for each asset. Weakened models produce
concrete counterexamples when each of those guards is removed.

The result is a bounded integer-model certificate. It does not establish an
unbounded conservation theorem, parser correctness, asset authorization,
cryptographic binding, or equivalence with the recursive-STARK guest.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from typing import Any, Sequence

from z3 import BoolRef, Int, Not, Or, Solver, is_true, sat, unsat

SCHEMA = "zenodex.recursive_stark_conservation_smt.v1"
SOLVER_TIMEOUT_MS = 5_000
ASSET_COUNT = 2
ROW_COUNT = 2
AMOUNT_MIN = 0
AMOUNT_MAX = 3
AGGREGATE_MODULUS = 4
EFFECT_COLUMNS = ("debit", "credit", "mint", "burn")


@dataclass(frozen=True)
class CheckResult:
    """Normalized, deterministic result for one SMT query."""

    name: str
    expected_verdict: str
    verdict: str
    detail: str
    model: dict[str, bool | int] | None = None

    def as_json(self) -> dict[str, Any]:
        return {
            "detail": self.detail,
            "expected_verdict": self.expected_verdict,
            "model": self.model,
            "name": self.name,
            "verdict": self.verdict,
        }


@dataclass(frozen=True)
class ConservationVariables:
    rows: dict[tuple[int, int, str], Any]
    aggregates: dict[tuple[int, str], Any]
    symbols: tuple[tuple[str, Any], ...]


def _solver() -> Solver:
    solver = Solver()
    solver.set(timeout=SOLVER_TIMEOUT_MS, random_seed=0)
    return solver


def _normalized_model(
    solver: Solver,
    symbols: Sequence[tuple[str, Any]],
) -> dict[str, bool | int]:
    ordered_symbols = sorted(symbols, key=lambda row: row[0])
    for _name, symbol in ordered_symbols:
        if isinstance(symbol, BoolRef):
            solver.push()
            solver.add(Not(symbol))
            status = solver.check()
            solver.pop()
            if status == sat:
                solver.add(Not(symbol))
            elif status == unsat:
                solver.add(symbol)
            else:
                raise RuntimeError(
                    "solver became indeterminate while canonicalizing a Boolean"
                )
            if solver.check() != sat:
                raise RuntimeError("canonical Boolean assignment is not satisfiable")
            continue

        if solver.check() != sat:
            raise RuntimeError("model became indeterminate before integer minimization")
        best = solver.model().eval(symbol, model_completion=True).as_long()
        while True:
            solver.push()
            solver.add(symbol < best)
            status = solver.check()
            if status == sat:
                candidate = solver.model().eval(symbol, model_completion=True).as_long()
            else:
                candidate = best
            solver.pop()
            if status == sat:
                best = candidate
                continue
            if status == unsat:
                break
            raise RuntimeError(
                "solver became indeterminate while canonicalizing an integer"
            )
        solver.add(symbol == best)
        if solver.check() != sat:
            raise RuntimeError("canonical integer assignment is not satisfiable")

    if solver.check() != sat:
        raise RuntimeError("canonical model is not satisfiable")
    model = solver.model()
    normalized: dict[str, bool | int] = {}
    for name, symbol in ordered_symbols:
        value = model.eval(symbol, model_completion=True)
        if isinstance(symbol, BoolRef):
            normalized[name] = is_true(value)
        else:
            normalized[name] = value.as_long()
    return normalized


def _run_query(
    *,
    name: str,
    solver: Solver,
    expected_verdict: str,
    symbols: Sequence[tuple[str, Any]],
) -> CheckResult:
    try:
        status = solver.check()
        if status == unsat:
            verdict = "UNSAT_PROVED"
            detail = "no counterexample within the declared finite bounds"
            model = None
        elif status == sat:
            verdict = "SAT_COUNTEREXAMPLE"
            detail = "concrete counterexample within the declared finite bounds"
            model = _normalized_model(solver, symbols)
        else:
            reason = solver.reason_unknown()
            verdict = "TIMEOUT" if "timeout" in reason.lower() else "UNKNOWN"
            detail = reason or "solver returned unknown"
            model = None
    except Exception as exc:  # pragma: no cover - defensive fail-closed boundary
        verdict = "ERROR"
        detail = f"{type(exc).__name__}: {exc}"
        model = None
    return CheckResult(
        name=name,
        expected_verdict=expected_verdict,
        verdict=verdict,
        detail=detail,
        model=model,
    )


def _variables(prefix: str) -> ConservationVariables:
    rows = {
        (asset, row, column): Int(f"{prefix}_a{asset}_r{row}_{column}")
        for asset in range(ASSET_COUNT)
        for row in range(ROW_COUNT)
        for column in EFFECT_COLUMNS
    }
    aggregates = {
        (asset, column): Int(f"{prefix}_a{asset}_aggregate_{column}")
        for asset in range(ASSET_COUNT)
        for column in EFFECT_COLUMNS
    }
    symbols = [
        (f"asset_{asset}_row_{row}_{column}", rows[(asset, row, column)])
        for asset in range(ASSET_COUNT)
        for row in range(ROW_COUNT)
        for column in EFFECT_COLUMNS
    ]
    symbols.extend(
        (
            f"asset_{asset}_aggregate_{column}",
            aggregates[(asset, column)],
        )
        for asset in range(ASSET_COUNT)
        for column in EFFECT_COLUMNS
    )
    return ConservationVariables(rows, aggregates, tuple(symbols))


def _add_bounds(solver: Solver, variables: ConservationVariables) -> None:
    for amount in variables.rows.values():
        solver.add(amount >= AMOUNT_MIN, amount <= AMOUNT_MAX)
    for amount in variables.aggregates.values():
        solver.add(amount >= AMOUNT_MIN, amount < AGGREGATE_MODULUS)


def _column_sum(
    variables: ConservationVariables,
    asset: int,
    column: str,
) -> Any:
    return sum(variables.rows[(asset, row, column)] for row in range(ROW_COUNT))


def _row_equations(variables: ConservationVariables) -> tuple[BoolRef, ...]:
    return tuple(
        variables.rows[(asset, row, "debit")]
        + variables.rows[(asset, row, "mint")]
        == variables.rows[(asset, row, "credit")]
        + variables.rows[(asset, row, "burn")]
        for asset in range(ASSET_COUNT)
        for row in range(ROW_COUNT)
    )


def _checked_sum_bindings(
    variables: ConservationVariables,
) -> tuple[BoolRef, ...]:
    return tuple(
        variables.aggregates[(asset, column)]
        == _column_sum(variables, asset, column) % AGGREGATE_MODULUS
        for asset in range(ASSET_COUNT)
        for column in EFFECT_COLUMNS
    )


def _no_overflow_guards(
    variables: ConservationVariables,
) -> tuple[BoolRef, ...]:
    return tuple(
        _column_sum(variables, asset, column) < AGGREGATE_MODULUS
        for asset in range(ASSET_COUNT)
        for column in EFFECT_COLUMNS
    )


def _asset_conserved(variables: ConservationVariables, asset: int) -> BoolRef:
    return (
        variables.aggregates[(asset, "debit")]
        + variables.aggregates[(asset, "mint")]
        == variables.aggregates[(asset, "credit")]
        + variables.aggregates[(asset, "burn")]
    )


def _add_guards(
    solver: Solver,
    variables: ConservationVariables,
    *,
    row_equations: bool,
    checked_sum_bindings: bool,
    no_overflow: bool,
) -> None:
    _add_bounds(solver, variables)
    if row_equations:
        solver.add(*_row_equations(variables))
    if checked_sum_bindings:
        solver.add(*_checked_sum_bindings(variables))
    if no_overflow:
        solver.add(*_no_overflow_guards(variables))


def prove_per_asset_aggregate_conservation(asset: int) -> CheckResult:
    if asset < 0 or asset >= ASSET_COUNT:
        raise ValueError(f"asset index outside model: {asset}")
    solver = _solver()
    variables = _variables(f"safe_asset_{asset}")
    _add_guards(
        solver,
        variables,
        row_equations=True,
        checked_sum_bindings=True,
        no_overflow=True,
    )
    solver.add(Not(_asset_conserved(variables, asset)))
    return _run_query(
        name=f"asset_{asset}_aggregate_conservation",
        solver=solver,
        expected_verdict="UNSAT_PROVED",
        symbols=variables.symbols,
    )


def find_failure_without_row_equations() -> CheckResult:
    solver = _solver()
    variables = _variables("weak_rows")
    _add_guards(
        solver,
        variables,
        row_equations=False,
        checked_sum_bindings=True,
        no_overflow=True,
    )
    solver.add(Not(_asset_conserved(variables, 0)))
    return _run_query(
        name="removed_row_equations_allow_aggregate_imbalance",
        solver=solver,
        expected_verdict="SAT_COUNTEREXAMPLE",
        symbols=variables.symbols,
    )


def find_failure_without_checked_sum_bindings() -> CheckResult:
    solver = _solver()
    variables = _variables("weak_sums")
    _add_guards(
        solver,
        variables,
        row_equations=True,
        checked_sum_bindings=False,
        no_overflow=True,
    )
    solver.add(Not(_asset_conserved(variables, 0)))
    return _run_query(
        name="removed_checked_sum_bindings_allow_aggregate_imbalance",
        solver=solver,
        expected_verdict="SAT_COUNTEREXAMPLE",
        symbols=variables.symbols,
    )


def find_failure_without_no_overflow_guards() -> CheckResult:
    solver = _solver()
    variables = _variables("weak_overflow")
    _add_guards(
        solver,
        variables,
        row_equations=True,
        checked_sum_bindings=True,
        no_overflow=False,
    )
    target_overflows = Or(
        *(
            _column_sum(variables, 0, column) >= AGGREGATE_MODULUS
            for column in EFFECT_COLUMNS
        )
    )
    solver.add(target_overflows, Not(_asset_conserved(variables, 0)))
    return _run_query(
        name="removed_no_overflow_guards_allow_runtime_imbalance",
        solver=solver,
        expected_verdict="SAT_COUNTEREXAMPLE",
        symbols=variables.symbols,
    )


def run_checks() -> tuple[CheckResult, ...]:
    checks = [
        prove_per_asset_aggregate_conservation(asset)
        for asset in range(ASSET_COUNT)
    ]
    checks.extend(
        [
            find_failure_without_row_equations(),
            find_failure_without_checked_sum_bindings(),
            find_failure_without_no_overflow_guards(),
        ]
    )
    return tuple(checks)


def checks_succeeded(checks: Sequence[CheckResult | dict[str, Any]]) -> bool:
    """Return true only when every query produced its exact expected verdict."""

    for check in checks:
        actual: object
        expected: object
        if isinstance(check, CheckResult):
            actual = check.verdict
            expected = check.expected_verdict
        else:
            actual = check.get("verdict")
            expected = check.get("expected_verdict")
        if actual != expected or actual in {"UNKNOWN", "TIMEOUT", "ERROR"}:
            return False
    return True


def build_report() -> dict[str, Any]:
    checks = run_checks()
    return {
        "checks": [check.as_json() for check in checks],
        "claims": [
            {
                "id": "bounded_per_asset_aggregate_conservation",
                "statement": (
                    "For each of two modeled assets, checked child-row equations, "
                    "checked aggregate bindings, and no-overflow guards imply "
                    "aggregate debit + mint = aggregate credit + burn."
                ),
            }
        ],
        "model": {
            "assumptions": [
                "each child row is checked in mathematical integers",
                "aggregate columns bind to the modeled bounded-word addition",
                "every aggregate column is rejected before bounded-word overflow",
                "assets are indexed independently and rows are included exactly once",
            ],
            "exclusions": [
                "unbounded assets, child rows, or amount widths",
                "negative amounts, fees, rounding, dust, or unit conversion",
                "asset authorization and mint or burn authority",
                "parser, serialization, hash, proof-system, or guest equivalence",
                "liveness and concurrent state transitions",
            ],
            "finite_bounds": {
                "aggregate_modulus": AGGREGATE_MODULUS,
                "amount_domain": {"max": AMOUNT_MAX, "min": AMOUNT_MIN},
                "asset_count": ASSET_COUNT,
                "child_rows_per_asset": ROW_COUNT,
            },
            "state_variables": [
                "row[asset][child].debit",
                "row[asset][child].credit",
                "row[asset][child].mint",
                "row[asset][child].burn",
                "aggregate[asset].debit",
                "aggregate[asset].credit",
                "aggregate[asset].mint",
                "aggregate[asset].burn",
            ],
        },
        "ok": checks_succeeded(checks),
        "schema": SCHEMA,
        "solver": {"engine": "z3", "timeout_ms": SOLVER_TIMEOUT_MS},
    }


def render_report(report: dict[str, Any], *, pretty: bool = False) -> str:
    if pretty:
        return json.dumps(report, indent=2, sort_keys=True)
    return json.dumps(report, sort_keys=True, separators=(",", ":"))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pretty", action="store_true", help="pretty-print JSON")
    args = parser.parse_args(argv)
    report = build_report()
    print(render_report(report, pretty=args.pretty))
    return 0 if checks_succeeded(report["checks"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
