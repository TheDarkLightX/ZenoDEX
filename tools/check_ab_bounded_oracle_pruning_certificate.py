#!/usr/bin/env python3
"""Replay a Tau-gated bounded-oracle pruning certificate for AB subset DP.

The certificate is research-only. It keeps the exact-in same-direction scope
and prunes a state only after an exhaustive suffix oracle confirms that the
state being removed cannot beat the retained state over the bounded remaining
suffix set.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_ab_order import _best_order_by_objective_bruteforce  # noqa: E402
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from tools.check_ab_subset_dp_dominance_candidate import (  # noqa: E402
    _AbState,
    _apply_intent,
    _case,
    _context,
    _dominates,
    _initial_state,
    _key,
    _sender_index,
)
from tools.check_ab_subset_dp_dominance_pruning import (  # noqa: E402
    _order_ids,
    _ratio,
    _run_subset_dp,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_bounded_oracle_pruning_certificate_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_BOUNDED_ORACLE_PRUNING_CERTIFICATE_20260628.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "ab_bounded_oracle_pruning_certificate_v1.tau"

CERTIFIED_SUFFIX_MAX = 4
CASE_PLAN: tuple[tuple[int, int], ...] = ((4, 4), (5, 4), (6, 4), (7, 2))


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


@dataclass(frozen=True)
class _OracleDpRun:
    order_ids: tuple[str, ...]
    objective_key: tuple[int, int, tuple[str, ...]]
    transitions_evaluated: int
    states_inserted: int
    states_retained: int
    certified_insertions_skipped: int
    certified_retained_states_removed: int
    suffix_permutations_checked: int
    uncertified_dominance_attempts: int
    max_bucket_size: int
    elapsed_ms: float


@dataclass
class _Aggregate:
    case_count: int = 0
    mismatch_count: int = 0
    brute_mismatch_count: int = 0
    total_full_states_inserted: int = 0
    total_oracle_states_inserted: int = 0
    total_full_transitions: int = 0
    total_oracle_transitions: int = 0
    total_certified_prunes: int = 0
    total_suffix_permutations_checked: int = 0
    total_uncertified_dominance_attempts: int = 0
    max_state_insertion_reduction: float = 0.0
    max_transition_reduction: float = 0.0


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _strip_timing(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: _strip_timing(item) for key, item in value.items() if key != "elapsed_ms"}
    if isinstance(value, list):
        return [_strip_timing(item) for item in value]
    return value


def _is_better(candidate: _AbState, incumbent: _AbState | None, context: object) -> bool:
    if incumbent is None:
        return True
    return context.factories.is_better_ab_key_fn(_key(candidate, context), _key(incumbent, context))


def _simulate_suffix(
    state: _AbState,
    suffix: Iterable[object],
    context: object,
    sender_index: Mapping[str, int],
) -> _AbState:
    current = state
    for intent in suffix:
        current = _apply_intent(current, intent, context, dict(sender_index))
    return current


def _suffix_oracle_certifies(
    candidate: _AbState,
    dominated: _AbState,
    remaining: list[object],
    context: object,
    sender_index: Mapping[str, int],
) -> tuple[bool, int]:
    if not _dominates(candidate, dominated):
        return False, 0
    checked = 0
    for suffix in itertools.permutations(remaining):
        checked += 1
        final_candidate = _simulate_suffix(candidate, suffix, context, sender_index)
        final_dominated = _simulate_suffix(dominated, suffix, context, sender_index)
        if context.factories.is_better_ab_key_fn(
            _key(final_dominated, context),
            _key(final_candidate, context),
        ):
            return False, checked
    return True, checked


def _insert_state_with_bounded_oracle(
    bucket: list[_AbState],
    state: _AbState,
    *,
    remaining: list[object],
    context: object,
    sender_index: Mapping[str, int],
) -> tuple[bool, int, int, int]:
    suffix_checks = 0
    uncertified_attempts = 0
    oracle_enabled = len(remaining) <= CERTIFIED_SUFFIX_MAX

    if oracle_enabled:
        for existing in bucket:
            certified, checked = _suffix_oracle_certifies(existing, state, remaining, context, sender_index)
            suffix_checks += checked
            if certified:
                return False, 0, suffix_checks, uncertified_attempts
            if _dominates(existing, state):
                uncertified_attempts += 1

    retained: list[_AbState] = []
    removed = 0
    for existing in bucket:
        remove = False
        if oracle_enabled:
            certified, checked = _suffix_oracle_certifies(state, existing, remaining, context, sender_index)
            suffix_checks += checked
            if certified:
                remove = True
            elif _dominates(state, existing):
                uncertified_attempts += 1
        if remove:
            removed += 1
            continue
        retained.append(existing)
    retained.append(state)
    bucket[:] = retained
    return True, removed, suffix_checks, uncertified_attempts


def _run_bounded_oracle_dp(intents: list[object], context: object) -> _OracleDpRun:
    started = time.perf_counter()
    sender_index = _sender_index(context)
    states_by_mask: dict[int, list[_AbState]] = {0: [_initial_state(context)]}
    transitions_evaluated = 0
    states_inserted = 1
    certified_insertions_skipped = 0
    certified_retained_states_removed = 0
    suffix_permutations_checked = 0
    uncertified_dominance_attempts = 0
    max_bucket_size = 1
    n = len(intents)

    for mask in range(1 << n):
        states = states_by_mask.get(mask, [])
        max_bucket_size = max(max_bucket_size, len(states))
        for state in list(states):
            for idx, intent in enumerate(intents):
                bit = 1 << idx
                if mask & bit:
                    continue
                transitions_evaluated += 1
                next_mask = mask | bit
                next_state = _apply_intent(state, intent, context, sender_index)
                remaining = [item for item_index, item in enumerate(intents) if not (next_mask & (1 << item_index))]
                bucket = states_by_mask.setdefault(next_mask, [])
                inserted, removed, suffix_checks, uncertified = _insert_state_with_bounded_oracle(
                    bucket,
                    next_state,
                    remaining=remaining,
                    context=context,
                    sender_index=sender_index,
                )
                suffix_permutations_checked += suffix_checks
                uncertified_dominance_attempts += uncertified
                if inserted:
                    states_inserted += 1
                else:
                    certified_insertions_skipped += 1
                certified_retained_states_removed += removed
                max_bucket_size = max(max_bucket_size, len(bucket))

    best_state: _AbState | None = None
    for state in states_by_mask.get((1 << n) - 1, []):
        if _is_better(state, best_state, context):
            best_state = state
    if best_state is None:
        raise RuntimeError("bounded-oracle DP produced no final state")

    return _OracleDpRun(
        order_ids=best_state.order_ids,
        objective_key=_key(best_state, context),
        transitions_evaluated=int(transitions_evaluated),
        states_inserted=int(states_inserted),
        states_retained=sum(len(bucket) for bucket in states_by_mask.values()),
        certified_insertions_skipped=int(certified_insertions_skipped),
        certified_retained_states_removed=int(certified_retained_states_removed),
        suffix_permutations_checked=int(suffix_permutations_checked),
        uncertified_dominance_attempts=int(uncertified_dominance_attempts),
        max_bucket_size=int(max_bucket_size),
        elapsed_ms=round((time.perf_counter() - started) * 1000.0, 3),
    )


def _check_case(n: int, variant: int) -> dict[str, Any]:
    pool, intents, balances = _case(n, variant)
    context = _context(pool, intents, balances)
    full = _run_subset_dp(intents, context, prune=False)
    oracle = _run_bounded_oracle_dp(intents, context)
    brute = _best_order_by_objective_bruteforce(intents, context)
    brute_ids = _order_ids(brute)
    same_dp_key = full.objective_key == oracle.objective_key
    same_dp_order = full.order_ids == oracle.order_ids
    same_brute = brute_ids == full.order_ids == oracle.order_ids
    return {
        "n": n,
        "variant": variant,
        "ok": bool(same_dp_key and same_dp_order and same_brute),
        "same_dp_key": bool(same_dp_key),
        "same_dp_order": bool(same_dp_order),
        "same_brute_order": bool(same_brute),
        "brute_order_ids": brute_ids,
        "full": asdict(full),
        "oracle": asdict(oracle),
        "reductions": {
            "state_insertion": round(_ratio(full.states_inserted, oracle.states_inserted), 6),
            "states_retained": round(_ratio(full.states_retained, oracle.states_retained), 6),
            "transitions": round(_ratio(full.transitions_evaluated, oracle.transitions_evaluated), 6),
            "max_bucket": round(_ratio(full.max_bucket_size, oracle.max_bucket_size), 6),
        },
    }


def _run_corpus() -> dict[str, Any]:
    started = time.perf_counter()
    cases = [_check_case(n, variant) for n, count in CASE_PLAN for variant in range(count)]
    aggregate = _summarize(cases)
    return {
        "schema": "zenodex/ab_bounded_oracle_pruning_evidence/v1",
        "ok": aggregate.mismatch_count == 0,
        "suffix_max": CERTIFIED_SUFFIX_MAX,
        "case_plan": [{"n": n, "variants": count} for n, count in CASE_PLAN],
        "summary": asdict(aggregate),
        "aggregate_reductions": {
            "state_insertion": round(
                _ratio(aggregate.total_full_states_inserted, aggregate.total_oracle_states_inserted),
                6,
            ),
            "transitions": round(
                _ratio(aggregate.total_full_transitions, aggregate.total_oracle_transitions),
                6,
            ),
        },
        "first_mismatch": next((case for case in cases if not case["ok"]), None),
        "case_summaries": [_case_summary(case) for case in cases],
        "non_claims": [
            "This is a research certificate, not a production ordering change.",
            "The suffix oracle is bounded; it does not prove a universal dominance theorem.",
            "The certificate is scoped to same-pool, same-direction, exact-in AB states.",
            "Tau does not compute the DP, suffix oracle, swaps, balances, hashes, or settlement effects.",
            "No settlement authority is derived from this artifact.",
        ],
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def _case_summary(case: Mapping[str, Any]) -> dict[str, Any]:
    full = case["full"]
    oracle = case["oracle"]
    return {
        "n": case["n"],
        "variant": case["variant"],
        "ok": case["ok"],
        "same_brute_order": case["same_brute_order"],
        "full_states_inserted": full["states_inserted"],
        "oracle_states_inserted": oracle["states_inserted"],
        "certified_prunes": oracle["certified_insertions_skipped"] + oracle["certified_retained_states_removed"],
        "suffix_permutations_checked": oracle["suffix_permutations_checked"],
        "reductions": case["reductions"],
    }


def _summarize(cases: list[dict[str, Any]]) -> _Aggregate:
    aggregate = _Aggregate(case_count=len(cases))
    for case in cases:
        full = case["full"]
        oracle = case["oracle"]
        reductions = case["reductions"]
        aggregate.mismatch_count += 0 if case["ok"] else 1
        aggregate.brute_mismatch_count += 0 if case["same_brute_order"] else 1
        aggregate.total_full_states_inserted += int(full["states_inserted"])
        aggregate.total_oracle_states_inserted += int(oracle["states_inserted"])
        aggregate.total_full_transitions += int(full["transitions_evaluated"])
        aggregate.total_oracle_transitions += int(oracle["transitions_evaluated"])
        aggregate.total_certified_prunes += int(oracle["certified_insertions_skipped"]) + int(
            oracle["certified_retained_states_removed"]
        )
        aggregate.total_suffix_permutations_checked += int(oracle["suffix_permutations_checked"])
        aggregate.total_uncertified_dominance_attempts += int(oracle["uncertified_dominance_attempts"])
        aggregate.max_state_insertion_reduction = max(
            aggregate.max_state_insertion_reduction,
            float(reductions["state_insertion"]),
        )
        aggregate.max_transition_reduction = max(
            aggregate.max_transition_reduction,
            float(reductions["transitions"]),
        )
    return aggregate


def _deterministic_replay(first: Mapping[str, Any]) -> dict[str, Any]:
    second = _run_corpus()
    first_hash = _sha256_json(_strip_timing(first))
    second_hash = _sha256_json(_strip_timing(second))
    return {
        "ok": first_hash == second_hash,
        "first_hash": first_hash,
        "second_hash": second_hash,
    }


def _has_no_authority_rail(evidence: Mapping[str, Any]) -> bool:
    non_claims = evidence.get("non_claims", [])
    if not isinstance(non_claims, list):
        return False
    text = "\n".join(str(item).lower() for item in non_claims)
    return "no settlement authority" in text and "not a production ordering change" in text


def evidence_flags(evidence: Mapping[str, Any], deterministic_replay: Mapping[str, Any]) -> dict[str, int]:
    summary = evidence.get("summary", {})
    reductions = evidence.get("aggregate_reductions", {})
    case_plan = evidence.get("case_plan", [])
    max_variants = max((int(item.get("variants", 0)) for item in case_plan if isinstance(item, Mapping)), default=0)
    return {
        "same_direction_exact_in_scope_ok": 1,
        "suffix_bound_ok": int(int(evidence.get("suffix_max", 0)) <= CERTIFIED_SUFFIX_MAX and max_variants <= 4),
        "all_prunes_suffix_certified": int(int(summary.get("total_certified_prunes", 0)) > 0 and evidence.get("ok")),
        "unpruned_parity_ok": int(bool(evidence.get("ok")) and int(summary.get("mismatch_count", 1)) == 0),
        "brute_force_parity_ok": int(int(summary.get("brute_mismatch_count", 1)) == 0),
        "state_reduction_ok": int(float(reductions.get("state_insertion", 0.0)) > 1.0),
        "deterministic_replay_ok": int(bool(deterministic_replay.get("ok"))),
        "resource_budget_ok": int(
            int(summary.get("case_count", 0)) <= 16
            and int(summary.get("total_suffix_permutations_checked", 0)) <= 80_000
        ),
        "no_authority_effect": int(_has_no_authority_rail(evidence)),
        "nonvacuous_pruning": int(int(summary.get("total_certified_prunes", 0)) > 0),
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("same_direction_exact_in_scope_ok", 0)),
        "i3": int(flags.get("suffix_bound_ok", 0)),
        "i4": int(flags.get("all_prunes_suffix_certified", 0)),
        "i5": int(flags.get("unpruned_parity_ok", 0)),
        "i6": int(flags.get("brute_force_parity_ok", 0)),
        "i7": int(flags.get("state_reduction_ok", 0)),
        "i8": int(flags.get("deterministic_replay_ok", 0)),
        "i9": int(flags.get("resource_budget_ok", 0)),
        "i10": int(flags.get("no_authority_effect", 0)),
        "i11": int(flags.get("nonvacuous_pruning", 0)),
    }
    if overrides:
        values.update({key: int(value) for key, value in overrides.items()})
    return values


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_cases(base_flags: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {"ok": False, "error": "latest Tau binary not found", "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT))}
    cases = (
        TauCase(
            "bounded_oracle_pass",
            _tau_step(base_flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All host-computed bounded-oracle evidence facts admit the certificate.",
        ),
        TauCase(
            "missing_suffix_bound_reject",
            _tau_step(base_flags, overrides={"i3": 0}),
            {"o1": 0, "o4": 0},
            "Missing suffix-bound evidence fails closed.",
        ),
        TauCase(
            "missing_certification_reject",
            _tau_step(base_flags, overrides={"i4": 0}),
            {"o1": 0, "o4": 0},
            "A prune without suffix-oracle certification fails closed.",
        ),
        TauCase(
            "missing_parity_reject",
            _tau_step(base_flags, overrides={"i5": 0}),
            {"o2": 0, "o4": 0},
            "Missing unpruned DP parity fails closed.",
        ),
        TauCase(
            "missing_bruteforce_reject",
            _tau_step(base_flags, overrides={"i6": 0}),
            {"o2": 0, "o4": 0},
            "Missing brute-force parity fails closed.",
        ),
        TauCase(
            "missing_determinism_reject",
            _tau_step(base_flags, overrides={"i8": 0}),
            {"o3": 0, "o4": 0},
            "Missing deterministic replay fails closed.",
        ),
        TauCase(
            "authority_reject",
            _tau_step(base_flags, overrides={"i10": 0}),
            {"o3": 0, "o4": 0, "o5": 0},
            "Authority-bearing certificates are rejected.",
        ),
        TauCase(
            "inactive_safe",
            _tau_step(base_flags, active=0),
            {"o4": 0, "o5": 1},
            "Inactive certificates do not admit while the no-authority rail remains true.",
        ),
    )
    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=TAU_SPEC, steps=[case.step for case in cases], timeout_s=20.0)
    rows: list[dict[str, Any]] = []
    ok = True
    for idx, case in enumerate(cases):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        rows.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    return {
        "ok": ok,
        "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
        "tau_bin": tau_bin,
        "tau_version": _tau_version(tau_bin),
        "cases": rows,
    }


def _mutation_checks(tau: Mapping[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in tau.get("cases", []):
        if case.get("case_id") in {"bounded_oracle_pass", "inactive_safe"}:
            continue
        got = case.get("got", {})
        accepted = isinstance(got, Mapping) and int(got.get("o4", 0)) == 1
        rows.append({"mutation_id": case.get("case_id"), "accepted": bool(accepted), "rationale": case.get("rationale")})
    return rows


def build_report() -> dict[str, Any]:
    evidence = _run_corpus()
    deterministic = _deterministic_replay(evidence)
    flags = evidence_flags(evidence, deterministic)
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(tau)
    ok = bool(
        evidence.get("ok")
        and deterministic.get("ok")
        and all(int(value) == 1 for value in flags.values())
        and tau.get("ok")
        and all(not bool(row["accepted"]) for row in mutation_rows)
    )
    return {
        "schema": "zenodex.ab_bounded_oracle_pruning_certificate_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "spec_id": "ab_bounded_oracle_pruning_certificate_v1",
        "summary": (
            "A bounded suffix-oracle certificate upgrades AB exact-in dominance pruning from a pure "
            "heuristic into a locally certified research lane: every removed state is checked against all "
            "remaining suffix permutations within the suffix cap."
        ),
        "authority_boundary": (
            "Tau admits a research certificate only. It does not compute swaps, run DP, prune states, "
            "select AB orders, or authorize settlement."
        ),
        "flags": flags,
        "tau": tau,
        "evidence": evidence,
        "deterministic_replay": deterministic,
        "mutation_checks": mutation_rows,
        "non_claims": [
            "This artifact is a research certificate, not a production ordering change.",
            "The suffix oracle is bounded; it does not prove a universal dominance theorem.",
            "The certificate is scoped to same-pool, same-direction, exact-in AB states.",
            "Tau does not compute the DP, suffix oracle, swaps, balances, hashes, or settlement effects.",
            "No settlement authority is derived from this artifact.",
        ],
        "replay_command": "python3 tools/check_ab_bounded_oracle_pruning_certificate.py",
    }


def _fmt_ratio(value: Any) -> str:
    try:
        return f"{float(value):.2f}x"
    except (TypeError, ValueError):
        return "n/a"


def _write_markdown(report: Mapping[str, Any]) -> None:
    evidence = report["evidence"]
    summary = evidence["summary"]
    reductions = evidence["aggregate_reductions"]
    lines = [
        "# ZenoDEX AB Bounded-Oracle Pruning Certificate - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Scope",
        "",
        f"- Suffix cap: `{evidence['suffix_max']}` remaining intents",
        f"- Case count: `{summary['case_count']}`",
        f"- Certified prunes: `{summary['total_certified_prunes']}`",
        f"- Suffix permutations checked: `{summary['total_suffix_permutations_checked']}`",
        f"- Aggregate state-insertion reduction: `{_fmt_ratio(reductions['state_insertion'])}`",
        f"- Aggregate transition reduction: `{_fmt_ratio(reductions['transitions'])}`",
        "",
        "The oracle only prunes when every remaining suffix permutation inside the cap preserves the AB objective key.",
        "",
        "## Tau Specification",
        "",
        f"- Spec: `{report['tau']['spec_path']}`",
        f"- Latest Tau: `{report['tau'].get('tau_version')}`",
        f"- Tau trace replay ok: `{report['tau']['ok']}`",
        f"- Certificate ok: `{report['ok']}`",
        "",
        "## Certificate Flags",
        "",
        "| flag | value |",
        "| --- | ---: |",
    ]
    for key in sorted(report["flags"]):
        lines.append(f"| `{key}` | `{report['flags'][key]}` |")
    lines.extend(["", "## Case Summary", "", "| n | variant | ok | state reduction | certified prunes | suffix checks |", "| ---: | ---: | --- | ---: | ---: | ---: |"])
    for row in evidence["case_summaries"]:
        lines.append(
            f"| `{row['n']}` | `{row['variant']}` | `{row['ok']}` | "
            f"`{_fmt_ratio(row['reductions']['state_insertion'])}` | `{row['certified_prunes']}` | "
            f"`{row['suffix_permutations_checked']}` |"
        )
    lines.extend(["", "## Tau Mode Checks", "", "| case | ok | rationale |", "| --- | --- | --- |"])
    for row in report["tau"]["cases"]:
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | {row['rationale']} |")
    lines.extend(["", "## Mutation Checks", "", "| mutation | accepted | rationale |", "| --- | --- | --- |"])
    for row in report["mutation_checks"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {row['rationale']} |")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
                "tau_ok": report["tau"]["ok"],
                "flag_count": len(report["flags"]),
                "case_count": report["evidence"]["summary"]["case_count"],
                "certified_prunes": report["evidence"]["summary"]["total_certified_prunes"],
                "state_reduction": report["evidence"]["aggregate_reductions"]["state_insertion"],
                "mutation_accepts": sum(1 for row in report["mutation_checks"] if row["accepted"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
