#!/usr/bin/env python3
"""Replay a Tau-gated uncoupled CoW Hungarian matching certificate."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_cow_search import (  # noqa: E402
    _CowCandidateExactIn,
    _CowSelectionContext,
    _assignment_balance_safe,
    _cow_pair_lex_tie_values,
    _cow_pair_rank_map,
    _cow_pair_selection_key,
    _pair_feasible,
    _partition_cow_candidates,
    _select_cow_pairs_assignment,
    _select_cow_pairs_bruteforce,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_cow_hungarian_matching_certificate"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_COW_HUNGARIAN_MATCHING_CERTIFICATE.md"
TAU_SPEC = REPO_ROOT / "src" / "tau_specs" / "recommended" / "cow_hungarian_matching_certificate_v1.tau"

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "c0" * 32


@dataclass(frozen=True)
class TauCase:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _pool() -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _swap(
    intent_no: int,
    *,
    sender_no: int,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    min_amount_out: int,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_no),
        sender_pubkey=_sender(sender_no),
        deadline=9_999_999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": int(amount_in),
            "min_amount_out": int(min_amount_out),
        },
    )


def _uncoupled_case(size: int, variant: int) -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _pool()
    balances = BalanceTable()
    intents: list[Intent] = []
    for idx in range(size):
        amount = 70 + ((idx * 31 + variant * 17) % 90)
        min_out = 20 + ((idx * 7 + variant * 11) % 45)
        sender_no = 300 + variant * 30 + idx
        balances.set(_sender(sender_no), ASSET0, amount)
        intents.append(
            _swap(
                30_000 + variant * 1_000 + size * 100 + idx,
                sender_no=sender_no,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_in=amount,
                min_amount_out=min_out,
            )
        )
    for idx in range(size):
        amount = 75 + ((idx * 29 + variant * 13) % 85)
        min_out = 20 + ((idx * 5 + variant * 19) % 45)
        sender_no = 600 + variant * 30 + idx
        balances.set(_sender(sender_no), ASSET1, amount)
        intents.append(
            _swap(
                40_000 + variant * 1_000 + size * 100 + idx,
                sender_no=sender_no,
                asset_in=ASSET1,
                asset_out=ASSET0,
                amount_in=amount,
                min_amount_out=min_out,
            )
        )
    return pool, intents, balances


def _coupled_boundary_case() -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _pool()
    balances = BalanceTable()
    coupled0 = _sender(91)
    coupled1 = _sender(92)
    balances.set(coupled0, ASSET0, 100)
    balances.set(coupled1, ASSET1, 100)
    return (
        pool,
        [
            _swap(91_001, sender_no=91, asset_in=ASSET0, asset_out=ASSET1, amount_in=70, min_amount_out=40),
            _swap(91_002, sender_no=91, asset_in=ASSET0, asset_out=ASSET1, amount_in=70, min_amount_out=40),
            _swap(92_001, sender_no=92, asset_in=ASSET1, asset_out=ASSET0, amount_in=70, min_amount_out=40),
            _swap(92_002, sender_no=92, asset_in=ASSET1, asset_out=ASSET0, amount_in=70, min_amount_out=40),
        ],
        balances,
    )


def _assignment_costs(
    side_01: Sequence[_CowCandidateExactIn],
    side_10: Sequence[_CowCandidateExactIn],
) -> list[list[int]]:
    n_left = len(side_01)
    n_right = len(side_10)
    size = n_left + n_right
    pair_ranks = _cow_pair_rank_map(list(side_01), list(side_10), seed=None)
    pair_tie_values = _cow_pair_lex_tie_values(pair_ranks, max_pairs=min(n_left, n_right))
    max_tie_bonus = sum(sorted(pair_tie_values.values(), reverse=True)[: min(n_left, n_right)])
    max_total_volume = sum(int(candidate.amount_in) for candidate in side_01)
    max_total_volume += sum(int(candidate.amount_in) for candidate in side_10)
    tie_scale = max_tie_bonus + 1
    volume_scale = (max_total_volume + 1) * tie_scale
    max_edge_score = max(1, max_total_volume * volume_scale + max_total_volume * tie_scale + max_tie_bonus)
    impossible_cost = max_edge_score * (size + 1)

    costs = [[0 for _ in range(size)] for _ in range(size)]
    for i, x in enumerate(side_01):
        for j, y in enumerate(side_10):
            if not _pair_feasible(x, y):
                costs[i][j] = impossible_cost
                continue
            volume = int(x.amount_in + y.amount_in)
            surplus = int(y.amount_in - x.min_amount_out + x.amount_in - y.min_amount_out)
            tie_bonus = pair_tie_values[(i, j)]
            score = volume * volume_scale + surplus * tie_scale + tie_bonus
            costs[i][j] = -score
    return costs


def _hungarian_min_assignment_with_dual(costs: Sequence[Sequence[int]]) -> tuple[list[int], list[int], list[int]]:
    n = len(costs)
    if n == 0:
        return [], [], []
    if any(len(row) != n for row in costs):
        raise ValueError("hungarian costs must be square")
    max_abs_cost = max(abs(int(value)) for row in costs for value in row)
    unreachable = max_abs_cost * (n + 1) + 1

    u = [0] * (n + 1)
    v = [0] * (n + 1)
    p = [0] * (n + 1)
    way = [0] * (n + 1)
    for i in range(1, n + 1):
        p[0] = i
        j0 = 0
        minv = [0] + [unreachable] * n
        used = [False] * (n + 1)
        while True:
            used[j0] = True
            i0 = p[j0]
            delta = unreachable
            j1 = 0
            for j in range(1, n + 1):
                if used[j]:
                    continue
                cur = int(costs[i0 - 1][j - 1]) - u[i0] - v[j]
                if cur < minv[j]:
                    minv[j] = cur
                    way[j] = j0
                if minv[j] < delta:
                    delta = minv[j]
                    j1 = j
            for j in range(0, n + 1):
                if used[j]:
                    u[p[j]] += delta
                    v[j] -= delta
                else:
                    minv[j] -= delta
            j0 = j1
            if p[j0] == 0:
                break
        while True:
            j1 = way[j0]
            p[j0] = p[j1]
            j0 = j1
            if j0 == 0:
                break

    assignment = [-1] * n
    for j in range(1, n + 1):
        if p[j] != 0:
            assignment[p[j] - 1] = j - 1
    return assignment, u[1:], v[1:]


def _dual_certificate_ok(costs: Sequence[Sequence[int]], assignment: Sequence[int], u: Sequence[int], v: Sequence[int]) -> bool:
    n = len(costs)
    if len(assignment) != n or len(u) != n or len(v) != n:
        return False
    for i in range(n):
        for j in range(n):
            if int(u[i]) + int(v[j]) > int(costs[i][j]):
                return False
    assigned_cost = 0
    dual_value = sum(int(value) for value in u) + sum(int(value) for value in v)
    for i, j in enumerate(assignment):
        if not 0 <= int(j) < n:
            return False
        assigned_cost += int(costs[i][j])
        if int(u[i]) + int(v[j]) != int(costs[i][j]):
            return False
    return assigned_cost == dual_value


def _pair_ids(pairs: Sequence[tuple[_CowCandidateExactIn, _CowCandidateExactIn]]) -> list[tuple[str, str]]:
    return [(x.intent.intent_id, y.intent.intent_id) for x, y in pairs]


def _case_result(size: int, variant: int) -> dict[str, Any]:
    pool, intents, balances = _uncoupled_case(size, variant)
    partition = _partition_cow_candidates(intents, pool)
    context = _CowSelectionContext(balances=balances, asset0=ASSET0, asset1=ASSET1)
    costs = _assignment_costs(partition.side_01, partition.side_10)
    certified_assignment, u, v = _hungarian_min_assignment_with_dual(costs)
    production_pairs = _select_cow_pairs_assignment(partition.side_01, partition.side_10, context=context)
    brute_pairs = _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context)
    production_key = _cow_pair_selection_key(production_pairs)
    brute_key = _cow_pair_selection_key(brute_pairs)
    certified_pair_ids = [
        (partition.side_01[i].intent.intent_id, partition.side_10[j].intent.intent_id)
        for i, j in enumerate(certified_assignment[: len(partition.side_01)])
        if 0 <= j < len(partition.side_10) and costs[i][j] < 0
    ]
    return {
        "case_id": f"uncoupled_size_{size}_variant_{variant}",
        "size": size,
        "variant": variant,
        "candidate_count": len(partition.side_01) + len(partition.side_10),
        "assignment_balance_safe": _assignment_balance_safe(partition.side_01, partition.side_10, context=context),
        "production_matches_bruteforce": production_key == brute_key,
        "same_economic_key": tuple(production_key[:2]) == tuple(brute_key[:2]),
        "same_pair_id_tie": production_key == brute_key,
        "dual_certificate_ok": _dual_certificate_ok(costs, certified_assignment, u, v),
        "certified_assignment_matches_production": certified_pair_ids == _pair_ids(production_pairs),
        "production_key": production_key,
        "bruteforce_key": brute_key,
        "production_pair_ids": _pair_ids(production_pairs),
        "bruteforce_pair_ids": _pair_ids(brute_pairs),
        "certified_pair_ids": certified_pair_ids,
    }


def _coupled_boundary_result() -> dict[str, Any]:
    pool, intents, balances = _coupled_boundary_case()
    partition = _partition_cow_candidates(intents, pool)
    context = _CowSelectionContext(balances=balances, asset0=ASSET0, asset1=ASSET1)
    assignment_safe = _assignment_balance_safe(partition.side_01, partition.side_10, context=context)
    brute_pairs = _select_cow_pairs_bruteforce(partition.side_01, partition.side_10, context=context)
    naive_assignment_pairs = _select_cow_pairs_assignment(partition.side_01, partition.side_10, context=context)
    return {
        "case_id": "coupled_capacity_boundary",
        "assignment_balance_safe": assignment_safe,
        "bruteforce_key": _cow_pair_selection_key(brute_pairs),
        "naive_assignment_key": _cow_pair_selection_key(naive_assignment_pairs),
        "naive_assignment_would_overdraw": not assignment_safe,
    }


def _core_evidence() -> dict[str, Any]:
    cases = [_case_result(size, variant) for size in range(2, 7) for variant in range(5)]
    coupled = _coupled_boundary_result()
    return {
        "case_count": len(cases),
        "max_candidate_count": max(row["candidate_count"] for row in cases),
        "cases": cases,
        "coupled_boundary": coupled,
        "mismatch_count": sum(1 for row in cases if not row["production_matches_bruteforce"]),
        "dual_violation_count": sum(1 for row in cases if not row["dual_certificate_ok"]),
        "certified_assignment_mismatch_count": sum(
            1 for row in cases if not row["certified_assignment_matches_production"]
        ),
        "assignment_safe_case_count": sum(1 for row in cases if row["assignment_balance_safe"]),
        "pair_tie_mismatch_count": sum(1 for row in cases if not row["same_pair_id_tie"]),
    }


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def _evidence_flags(core: Mapping[str, Any], deterministic_replay: Mapping[str, Any]) -> dict[str, int]:
    non_claims = "\n".join(_non_claims()).lower()
    return {
        "uncoupled_capacity_scope_ok": int(
            int(core.get("case_count", 0)) == 25
            and int(core.get("assignment_safe_case_count", 0)) == int(core.get("case_count", -1))
            and bool(core.get("coupled_boundary", {}).get("naive_assignment_would_overdraw"))
        ),
        "primal_assignment_ok": int(
            int(core.get("mismatch_count", 1)) == 0
            and int(core.get("certified_assignment_mismatch_count", 1)) == 0
        ),
        "dual_certificate_ok": int(int(core.get("dual_violation_count", 1)) == 0),
        "brute_force_parity_ok": int(int(core.get("mismatch_count", 1)) == 0),
        "grouped_capacity_fallback_ok": int(
            bool(core.get("coupled_boundary", {}).get("naive_assignment_would_overdraw"))
            and "not a certificate for grouped-capacity matching" in non_claims
        ),
        "deterministic_ties_ok": int(int(core.get("pair_tie_mismatch_count", 1)) == 0),
        "balance_scope_ok": int(int(core.get("assignment_safe_case_count", 0)) == int(core.get("case_count", -1))),
        "resource_budget_ok": int(int(core.get("max_candidate_count", 999)) <= 12 and int(core.get("case_count", 999)) <= 25),
        "no_arbitrary_grouped_capacity_claim": int("not a certificate for grouped-capacity matching" in non_claims),
        "no_settlement_authority": int("no settlement authority" in non_claims),
        "replay_evidence_ok": int(bool(deterministic_replay.get("ok"))),
    }


def _tau_step(flags: Mapping[str, int], *, active: int = 1, overrides: Mapping[str, int] | None = None) -> dict[str, int]:
    values = {
        "i1": int(active),
        "i2": int(flags.get("uncoupled_capacity_scope_ok", 0)),
        "i3": int(flags.get("primal_assignment_ok", 0)),
        "i4": int(flags.get("dual_certificate_ok", 0)),
        "i5": int(flags.get("brute_force_parity_ok", 0)),
        "i6": int(flags.get("grouped_capacity_fallback_ok", 0)),
        "i7": int(flags.get("deterministic_ties_ok", 0)),
        "i8": int(flags.get("balance_scope_ok", 0)),
        "i9": int(flags.get("resource_budget_ok", 0)),
        "i10": int(flags.get("no_arbitrary_grouped_capacity_claim", 0)),
        "i11": int(flags.get("no_settlement_authority", 0)),
        "i12": int(flags.get("replay_evidence_ok", 0)),
    }
    if overrides:
        values.update({key: int(value) for key, value in overrides.items()})
    return values


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    proc = subprocess.run([tau_bin, "--version"], cwd=REPO_ROOT, capture_output=True, text=True, timeout=10, check=False)
    return (proc.stdout + proc.stderr).strip()


def _run_tau_cases(flags: Mapping[str, int]) -> dict[str, Any]:
    tau_bin = find_tau_bin(REPO_ROOT, profile="latest")
    if not tau_bin:
        return {
            "ok": False,
            "error": "latest Tau binary not found",
            "spec_path": str(TAU_SPEC.relative_to(REPO_ROOT)),
            "tau_bin_available": False,
            "tau_version": None,
            "cases": [],
        }
    cases = [
        TauCase(
            "hungarian_certificate_pass",
            _tau_step(flags),
            {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
            "All host-projected assignment, boundary, replay, and authority facts admit the certificate.",
        ),
        TauCase(
            "inactive_safe",
            _tau_step(flags, active=0),
            {"o4": 0, "o5": 1},
            "Inactive certificate does not admit while no-authority remains true.",
        ),
    ]
    negative_inputs = {
        "scope_reject": "i2",
        "primal_reject": "i3",
        "dual_reject": "i4",
        "bruteforce_reject": "i5",
        "grouped_fallback_reject": "i6",
        "tie_reject": "i7",
        "balance_reject": "i8",
        "budget_reject": "i9",
        "grouped_claim_reject": "i10",
        "authority_reject": "i11",
        "replay_reject": "i12",
    }
    for case_id, input_name in negative_inputs.items():
        cases.append(
            TauCase(
                case_id,
                _tau_step(flags, overrides={input_name: 0}),
                {"o4": 0},
                f"Missing {input_name} fails the certificate closed.",
            )
        )

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=TAU_SPEC,
        steps=[case.step for case in cases],
        timeout_s=20.0,
    )
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
        "tau_bin_available": True,
        "tau_version": _tau_version(tau_bin),
        "case_count": len(rows),
        "cases": rows,
    }


def _mutation_checks(tau: Mapping[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in tau.get("cases", []):
        if case.get("case_id") in {"hungarian_certificate_pass", "inactive_safe"}:
            continue
        got = case.get("got", {})
        accepted = isinstance(got, Mapping) and int(got.get("o4", 0)) == 1
        rows.append(
            {
                "mutation_id": case.get("case_id"),
                "accepted": bool(accepted),
                "rationale": case.get("rationale"),
            }
        )
    return rows


def _non_claims() -> list[str]:
    return [
        "This is an uncoupled CoW Hungarian matching research certificate, not production activation.",
        "This is not a certificate for grouped-capacity matching; coupled senders require the capacity-DP or fallback boundary.",
        "The host computes the primal assignment and dual certificate; Tau combines projected facts only.",
        "No settlement authority, state-root authority, routing authority, pool mutation, or balance mutation is derived.",
    ]


def _compact_case_sample(row: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "case_id": row["case_id"],
        "candidate_count": row["candidate_count"],
        "assignment_balance_safe": row["assignment_balance_safe"],
        "production_matches_bruteforce": row["production_matches_bruteforce"],
        "dual_certificate_ok": row["dual_certificate_ok"],
        "certified_assignment_matches_production": row["certified_assignment_matches_production"],
        "same_pair_id_tie": row["same_pair_id_tie"],
        "production_key": row["production_key"],
    }


def build_report() -> dict[str, Any]:
    core = _core_evidence()
    second_core = _core_evidence()
    deterministic = {
        "ok": _sha256_json(core) == _sha256_json(second_core),
        "first_hash": _sha256_json(core),
        "second_hash": _sha256_json(second_core),
    }
    flags = _evidence_flags(core, deterministic)
    tau = _run_tau_cases(flags)
    mutation_rows = _mutation_checks(tau)
    ok = (
        all(int(value) == 1 for value in flags.values())
        and bool(tau.get("ok"))
        and all(not bool(row["accepted"]) for row in mutation_rows)
    )
    return {
        "schema": "zenodex.cow_hungarian_matching_certificate_report.v1",
        "date": "2026-06-29",
        "ok": ok,
        "spec_id": "cow_hungarian_matching_certificate_v1",
        "summary": (
            "A Tau host-projected certificate gates the uncoupled CoW Hungarian matching surface by requiring "
            "balance-scope separation, primal assignment parity, dual certificate consistency, brute-force parity, "
            "deterministic pair-id ties, resource limits, replay evidence, grouped-capacity non-claims, and no authority."
        ),
        "authority_boundary": (
            "The certificate is research evidence only. It does not select production pairs, materialize settlement, "
            "mutate balances, mutate pools, or authorize state roots."
        ),
        "flags": flags,
        "core": {
            key: value
            for key, value in core.items()
            if key != "cases"
        },
        "case_samples": [_compact_case_sample(row) for row in core["cases"][:3]],
        "deterministic_replay": deterministic,
        "tau": tau,
        "mutation_checks": mutation_rows,
        "non_claims": _non_claims(),
        "replay_command": "python3 tools/check_cow_hungarian_matching_certificate.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    core = report["core"]
    tau = report["tau"]
    lines = [
        "# ZenoDEX CoW Hungarian Matching Certificate - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Evidence Summary",
        "",
        f"- Certificate ok: `{report['ok']}`",
        f"- Case count: `{core['case_count']}`",
        f"- Max candidate count: `{core['max_candidate_count']}`",
        f"- Brute-force mismatches: `{core['mismatch_count']}`",
        f"- Dual certificate violations: `{core['dual_violation_count']}`",
        f"- Certified assignment mismatches: `{core['certified_assignment_mismatch_count']}`",
        f"- Pair-id tie mismatches: `{core['pair_tie_mismatch_count']}`",
        f"- Coupled boundary rejects assignment scope: `{core['coupled_boundary']['naive_assignment_would_overdraw']}`",
        "",
        "## Tau Specification",
        "",
        f"- Spec: `{tau['spec_path']}`",
        f"- Latest Tau available: `{tau.get('tau_bin_available')}`",
        f"- Latest Tau: `{tau.get('tau_version')}`",
        f"- Tau trace replay ok: `{tau.get('ok')}`",
        "",
        "## Certificate Flags",
        "",
        "| flag | value |",
        "| --- | ---: |",
    ]
    for key, value in sorted(report["flags"].items()):
        lines.append(f"| `{key}` | `{value}` |")
    lines.extend(["", "## Tau Mode Checks", "", "| case | ok | rationale |", "| --- | --- | --- |"])
    for row in tau.get("cases", []):
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | {row['rationale']} |")
    lines.extend(["", "## Mutation Checks", "", "| mutation | accepted | rationale |", "| --- | --- | --- |"])
    for row in report["mutation_checks"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {row['rationale']} |")
    lines.extend(["", "## Case Samples", ""])
    lines.append("```json")
    lines.append(json.dumps(report["case_samples"], indent=2, sort_keys=True))
    lines.append("```")
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
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
    output_json = Path(args.output_json)
    report = run(output_json)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "json": str(output_json.relative_to(REPO_ROOT) if output_json.is_relative_to(REPO_ROOT) else output_json),
                "report": str(REPORT_MD.relative_to(REPO_ROOT)),
                "case_count": report["core"]["case_count"],
                "tau_ok": report["tau"].get("ok"),
                "mutation_accepts": sum(1 for row in report["mutation_checks"] if row["accepted"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
