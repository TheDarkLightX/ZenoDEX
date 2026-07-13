#!/usr/bin/env python3
"""Bounded SMT evidence for recursive-STARK exact-once admission.

This certificate models two sequential root-admission attempts over finite,
namespaced identifier domains. It proves that the complete freshness guard
rejects reuse of a root, child, receipt, or message identifier and that a
rejected transition leaves committed state unchanged. Separate weakened models
produce concrete counterexamples for every omitted guard.

The result is a bounded model certificate. It does not prove an unbounded
protocol, cryptographic collision resistance, concurrent admission, or crash
recovery.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from typing import Any, Sequence

from z3 import And, Bool, BoolRef, If, Int, Not, Or, Solver, is_true, sat, unsat

SCHEMA = "zenodex.recursive_stark_exact_once_smt.v1"
SOLVER_TIMEOUT_MS = 5_000
ID_MIN = 0
ID_MAX = 2
STATE_DIGEST_MIN = 0
STATE_DIGEST_MAX = 7
SEEN_COUNT_MIN = 0
SEEN_COUNT_MAX = 2
ID_DOMAINS = ("root", "child", "receipt", "message")


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


def _admission_symbols(prefix: str) -> tuple[
    dict[tuple[int, str], Any],
    BoolRef,
    BoolRef,
    list[tuple[str, Any]],
]:
    ids = {
        (step, domain): Int(f"{prefix}_{domain}_id_{step}")
        for step in range(2)
        for domain in ID_DOMAINS
    }
    requested_0 = Bool(f"{prefix}_requested_0")
    requested_1 = Bool(f"{prefix}_requested_1")
    symbols: list[tuple[str, Any]] = [
        (f"{domain}_id_{step}", ids[(step, domain)])
        for step in range(2)
        for domain in ID_DOMAINS
    ]
    symbols.extend(
        [
            ("requested_0", requested_0),
            ("requested_1", requested_1),
        ]
    )
    return ids, requested_0, requested_1, symbols


def _add_id_bounds(solver: Solver, ids: dict[tuple[int, str], Any]) -> None:
    for identifier in ids.values():
        solver.add(identifier >= ID_MIN, identifier <= ID_MAX)


def _acceptance_formulas(
    ids: dict[tuple[int, str], Any],
    requested_0: BoolRef,
    requested_1: BoolRef,
    *,
    omitted_guard: str | None = None,
) -> tuple[BoolRef, BoolRef, dict[str, BoolRef]]:
    accepted_0 = requested_0
    freshness = {
        domain: Or(Not(accepted_0), ids[(1, domain)] != ids[(0, domain)])
        for domain in ID_DOMAINS
    }
    active_guards = [
        guard for domain, guard in freshness.items() if domain != omitted_guard
    ]
    accepted_1 = And(requested_1, *active_guards)
    return accepted_0, accepted_1, freshness


def prove_identifier_cannot_be_reused(domain: str) -> CheckResult:
    """Find no two accepted attempts that reuse an identifier in ``domain``."""

    if domain not in ID_DOMAINS:
        raise ValueError(f"unknown identifier domain: {domain}")
    solver = _solver()
    ids, requested_0, requested_1, symbols = _admission_symbols(f"safe_{domain}")
    _add_id_bounds(solver, ids)
    accepted_0, accepted_1, freshness = _acceptance_formulas(
        ids,
        requested_0,
        requested_1,
    )
    solver.add(accepted_0, accepted_1, ids[(1, domain)] == ids[(0, domain)])
    symbols.extend(
        [
            ("accepted_0", accepted_0),
            ("accepted_1", accepted_1),
            *[(f"fresh_{name}", guard) for name, guard in freshness.items()],
        ]
    )
    return _run_query(
        name=f"accepted_roots_cannot_reuse_{domain}_id",
        solver=solver,
        expected_verdict="UNSAT_PROVED",
        symbols=symbols,
    )


def find_reuse_when_guard_is_removed(domain: str) -> CheckResult:
    """Find an accepted replay after omitting one namespaced freshness guard."""

    if domain not in ID_DOMAINS:
        raise ValueError(f"unknown identifier domain: {domain}")
    solver = _solver()
    ids, requested_0, requested_1, symbols = _admission_symbols(f"weak_{domain}")
    _add_id_bounds(solver, ids)
    accepted_0, accepted_1, freshness = _acceptance_formulas(
        ids,
        requested_0,
        requested_1,
        omitted_guard=domain,
    )
    solver.add(accepted_0, accepted_1, ids[(1, domain)] == ids[(0, domain)])
    symbols.extend(
        [
            ("accepted_0", accepted_0),
            ("accepted_1", accepted_1),
            *[(f"fresh_{name}", guard) for name, guard in freshness.items()],
        ]
    )
    return _run_query(
        name=f"removed_{domain}_freshness_guard_allows_reuse",
        solver=solver,
        expected_verdict="SAT_COUNTEREXAMPLE",
        symbols=symbols,
    )


def _state_symbols(prefix: str) -> tuple[dict[str, Any], list[tuple[str, Any]]]:
    state: dict[str, Any] = {
        "accepted": Bool(f"{prefix}_accepted"),
        "committed_digest_before": Int(f"{prefix}_committed_digest_before"),
        "committed_digest_after": Int(f"{prefix}_committed_digest_after"),
        "accepted_digest": Int(f"{prefix}_accepted_digest"),
    }
    for domain in ID_DOMAINS:
        state[f"seen_{domain}_before"] = Int(f"{prefix}_seen_{domain}_before")
        state[f"seen_{domain}_after"] = Int(f"{prefix}_seen_{domain}_after")
    return state, list(state.items())


def _add_state_bounds(solver: Solver, state: dict[str, Any]) -> None:
    for name in ("committed_digest_before", "committed_digest_after", "accepted_digest"):
        solver.add(
            state[name] >= STATE_DIGEST_MIN,
            state[name] <= STATE_DIGEST_MAX,
        )
    for domain in ID_DOMAINS:
        for suffix in ("before", "after"):
            value = state[f"seen_{domain}_{suffix}"]
            solver.add(value >= SEEN_COUNT_MIN, value <= SEEN_COUNT_MAX)
        solver.add(state[f"seen_{domain}_before"] < SEEN_COUNT_MAX)


def _state_changed(state: dict[str, Any]) -> BoolRef:
    changes = [
        state["committed_digest_after"] != state["committed_digest_before"]
    ]
    changes.extend(
        state[f"seen_{domain}_after"] != state[f"seen_{domain}_before"]
        for domain in ID_DOMAINS
    )
    return Or(*changes)


def prove_reject_transition_is_noop() -> CheckResult:
    solver = _solver()
    state, symbols = _state_symbols("safe_reject")
    _add_state_bounds(solver, state)
    solver.add(
        state["committed_digest_after"]
        == If(
            state["accepted"],
            state["accepted_digest"],
            state["committed_digest_before"],
        )
    )
    for domain in ID_DOMAINS:
        solver.add(
            state[f"seen_{domain}_after"]
            == If(
                state["accepted"],
                state[f"seen_{domain}_before"] + 1,
                state[f"seen_{domain}_before"],
            )
        )
    solver.add(Not(state["accepted"]), _state_changed(state))
    return _run_query(
        name="rejected_transition_preserves_committed_state",
        solver=solver,
        expected_verdict="UNSAT_PROVED",
        symbols=symbols,
    )


def find_reject_mutation_without_noop_guard() -> CheckResult:
    solver = _solver()
    state, symbols = _state_symbols("weak_reject")
    _add_state_bounds(solver, state)
    solver.add(Not(state["accepted"]), _state_changed(state))
    return _run_query(
        name="removed_reject_noop_guard_allows_state_mutation",
        solver=solver,
        expected_verdict="SAT_COUNTEREXAMPLE",
        symbols=symbols,
    )


def run_checks() -> tuple[CheckResult, ...]:
    checks: list[CheckResult] = []
    for domain in ID_DOMAINS:
        checks.append(prove_identifier_cannot_be_reused(domain))
    checks.append(prove_reject_transition_is_noop())
    for domain in ID_DOMAINS:
        checks.append(find_reuse_when_guard_is_removed(domain))
    checks.append(find_reject_mutation_without_noop_guard())
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
                "id": "bounded_exact_once",
                "statement": (
                    "Across two sequential attempts, two accepted roots cannot "
                    "reuse a namespaced root, child, receipt, or message ID."
                ),
            },
            {
                "id": "bounded_reject_noop",
                "statement": (
                    "A rejected transition preserves the committed digest and "
                    "all four modeled seen-ID counters."
                ),
            },
        ],
        "model": {
            "assumptions": [
                "admission attempts execute sequentially",
                "the first attempt starts with no modeled ID already seen",
                "accepted IDs are committed atomically to all four seen domains",
                "identifier domains are namespaced and equality is exact",
                "rejection is represented by accepted=false",
            ],
            "exclusions": [
                "unbounded traces or recursion depth",
                "multiple child, receipt, or message IDs within one root",
                "hash collision resistance or proof-system soundness",
                "concurrent admissions, crashes, reorgs, forks, and liveness",
                "persistence durability outside the modeled state transition",
            ],
            "finite_bounds": {
                "admission_attempts": 2,
                "id_domain": {"max": ID_MAX, "min": ID_MIN},
                "seen_count_domain": {
                    "max": SEEN_COUNT_MAX,
                    "min": SEEN_COUNT_MIN,
                },
                "state_digest_domain": {
                    "max": STATE_DIGEST_MAX,
                    "min": STATE_DIGEST_MIN,
                },
            },
            "state_variables": [
                "requested[attempt]",
                "accepted[attempt]",
                "root_id[attempt]",
                "child_id[attempt]",
                "receipt_id[attempt]",
                "message_id[attempt]",
                "committed_digest_before",
                "committed_digest_after",
                "seen_<domain>_before",
                "seen_<domain>_after",
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
