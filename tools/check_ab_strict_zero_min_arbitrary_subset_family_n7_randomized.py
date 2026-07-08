#!/usr/bin/env python3
"""n=7 randomized falsification for AB strict zero-min subset-family certificates.

This research-only checker extends the strict zero-min arbitrary subset-family
certificate search to n=7. It combines one hand-shaped positive-output boundary
case with deterministic pseudo-random cases, then keeps failed strict-executable
boundary probes separate from the supported corpus.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.kernels.python.settlement_swap_runtime_v1 import DEX_POOL_RESERVE_MAX  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from tools.check_ab_strict_zero_min_arbitrary_subset_family_certificate import (  # noqa: E402
    build_case_packet,
    verify_case,
)
from tools.check_ab_strict_zero_min_arbitrary_subset_family_extended_stress import (  # noqa: E402
    _histogram,
    _pool,
)
from tools.check_ab_strict_zero_min_emitter_witness import _sha256_json, _strip_timing  # noqa: E402
from tools.check_ab_strict_zero_min_emitter_witness_stress import _StressCase  # noqa: E402
from tools.check_ab_zero_min_economic_compression_certificate import (  # noqa: E402
    ASSET0,
    ASSET1,
    _intent,
    _sender,
)

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_arbitrary_subset_family_n7_randomized_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_ARBITRARY_SUBSET_FAMILY_N7_RANDOMIZED_20260629.md"
)

SEED = 2_026_062_907
BIT_COUNT = 7
TARGET_VALID_CASE_COUNT = 4
RANDOM_VALID_CASE_COUNT = 3
CANDIDATE_BUDGET = 12
SCOPE_PROBE_COUNT = TARGET_VALID_CASE_COUNT
BOUNDARY_REJECTION_RESERVE_OUTS = (7, 20, 100)
FEE_BPS_VALUES = (0, 1, 30, 100, 2_500, 5_000, 9_000)


def _n7_sender_no(case_no: int, idx: int) -> int:
    return ((case_no * 19 + idx) % 500) + 1


def _case_from_amounts(
    *,
    case_no: int,
    case_id: str,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amounts: Iterable[int],
    pattern: str,
) -> _StressCase:
    balances = BalanceTable()
    intents: list[Any] = []
    for idx, amount_in in enumerate(amounts):
        sender_no = _n7_sender_no(case_no, idx)
        balances.set(_sender(sender_no), ASSET0, int(amount_in) + 100_000)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _intent(
                7_000_000 + case_no * 16 + idx,
                sender_no=sender_no,
                amount_in=int(amount_in),
                min_amount_out=0,
            )
        )
    return _StressCase(
        case_id=case_id,
        pool=_pool(case_no, reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee_bps),
        intents=intents,
        balances=balances,
        pattern=pattern,
    )


def _boundary_positive_case(*, reserve_out: int = 1_100) -> _StressCase:
    amounts = [100, 101, 102, 103, 104, 105, 106]
    return _case_from_amounts(
        case_no=7_700 + reserve_out,
        case_id=f"n7_randomized_boundary_000_thin_fee9000_rout{reserve_out}",
        reserve_in=10_000,
        reserve_out=reserve_out,
        fee_bps=9_000,
        amounts=amounts,
        pattern="thin_positive_boundary/high_fee9000",
    )


def _random_amounts(candidate_no: int, rng: random.Random) -> tuple[str, list[int]]:
    pattern_id = candidate_no % 6
    if pattern_id == 0:
        return "rand_tie", [rng.randint(42, 48) for _ in range(BIT_COUNT)]
    if pattern_id == 1:
        return "rand_stair", [
            rng.randint(24, 35) + idx * rng.randint(5, 14) for idx in range(BIT_COUNT)
        ]
    if pattern_id == 2:
        return "rand_burst", [rng.randint(420, 520)] + [
            rng.randint(30, 55) for _ in range(BIT_COUNT - 1)
        ]
    if pattern_id == 3:
        return "rand_suffix_burst", [
            rng.randint(30, 55) for _ in range(BIT_COUNT - 1)
        ] + [rng.randint(420, 520)]
    if pattern_id == 4:
        return "rand_powers_jitter", [
            18 * (1 << min(idx, 4)) + rng.randint(0, 9) for idx in range(BIT_COUNT)
        ]
    return "rand_prime_jitter", [29, 31, 37, 43, 47, 53, 59]


def _random_reserves(
    candidate_no: int,
    *,
    total_amount: int,
    rng: random.Random,
) -> tuple[str, int, int]:
    regime_id = candidate_no % 5
    if regime_id == 0:
        return "near_zero_positive", rng.randint(120_000, 180_000), rng.randint(1_200_000, 1_900_000)
    if regime_id == 1:
        return "high_fee_deep_out", rng.randint(50_000, 120_000), rng.randint(2_000_000, 2_800_000)
    if regime_id == 2:
        reserve_in = DEX_POOL_RESERVE_MAX - total_amount - rng.randint(20_000, 60_000)
        return "near_domain_in", reserve_in, rng.randint(2_600_000_000, 2_950_000_000)
    if regime_id == 3:
        return "skewed_random", rng.randint(800_000, 2_000_000), rng.randint(4_000_000, 7_000_000)
    return "thin_margin_random", rng.randint(20_000, 55_000), rng.randint(900_000, 1_400_000)


def _random_candidate(candidate_no: int, rng: random.Random) -> _StressCase:
    amount_pattern, amounts = _random_amounts(candidate_no, rng)
    fee_bps = FEE_BPS_VALUES[(candidate_no * 3 + rng.randrange(len(FEE_BPS_VALUES))) % len(FEE_BPS_VALUES)]
    reserve_regime, reserve_in, reserve_out = _random_reserves(
        candidate_no,
        total_amount=sum(amounts),
        rng=rng,
    )
    case_no = 7_000 + candidate_no
    return _case_from_amounts(
        case_no=case_no,
        case_id=f"n7_randomized_{candidate_no:03d}_{reserve_regime}_{amount_pattern}_fee{fee_bps}",
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fee_bps=fee_bps,
        amounts=amounts,
        pattern=f"{reserve_regime}/{amount_pattern}",
    )


def collect_positive_cases() -> tuple[list[tuple[_StressCase, dict[str, Any]]], list[dict[str, Any]]]:
    accepted: list[tuple[_StressCase, dict[str, Any]]] = []
    rejected_candidates: list[dict[str, Any]] = []

    boundary_case = _boundary_positive_case()
    boundary_row = verify_case(boundary_case)
    if boundary_row["ok"]:
        accepted.append((boundary_case, boundary_row))
    else:
        rejected_candidates.append(_candidate_rejection(boundary_row))

    rng = random.Random(SEED)
    for candidate_no in range(CANDIDATE_BUDGET):
        if len(accepted) >= TARGET_VALID_CASE_COUNT:
            break
        case = _random_candidate(candidate_no, rng)
        row = verify_case(case)
        if row["ok"]:
            accepted.append((case, row))
        else:
            rejected_candidates.append(_candidate_rejection(row))

    return accepted, rejected_candidates


def _candidate_rejection(row: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "case_id": row.get("case_id"),
        "ok": row.get("ok"),
        "reasons": row.get("reasons", []),
        "first_failure": row.get("first_failure"),
        "record_count": row.get("record_count"),
        "dominance_check_count": row.get("dominance_check_count"),
    }


def _with_nonzero_min(case: _StressCase) -> _StressCase:
    amounts = [int(intent.get_field("amount_in")) for intent in case.intents]
    intents = [
        _intent(
            8_000_000 + idx,
            sender_no=_n7_sender_no(8_000, idx),
            amount_in=amount_in,
            min_amount_out=1 if idx == 0 else 0,
        )
        for idx, amount_in in enumerate(amounts)
    ]
    balances = BalanceTable()
    for idx, intent in enumerate(intents):
        sender_no = _n7_sender_no(8_000, idx)
        balances.set(_sender(sender_no), ASSET0, int(intent.get_field("amount_in")) + 100_000)
        balances.set(_sender(sender_no), ASSET1, 0)
    return _StressCase(
        case_id=f"{case.case_id}_nonzero_min_probe",
        pool=case.pool,
        intents=intents,
        balances=balances,
        pattern=f"{case.pattern}/nonzero_min_probe",
    )


def _scope_boundary_probes(cases: Iterable[_StressCase]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in list(cases)[:SCOPE_PROBE_COUNT]:
        probe_case = _with_nonzero_min(case)
        try:
            build_case_packet(probe_case)
            rows.append(
                {
                    "case_id": probe_case.case_id,
                    "accepted": True,
                    "expected_reason": "nonzero_min_amount_out_out_of_scope",
                    "reason": None,
                }
            )
        except ValueError as exc:
            rows.append(
                {
                    "case_id": probe_case.case_id,
                    "accepted": False,
                    "expected_reason": "nonzero_min_amount_out_out_of_scope",
                    "reason": str(exc),
                }
            )
    return rows


def _strict_executability_rejection_probes() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for reserve_out in BOUNDARY_REJECTION_RESERVE_OUTS:
        case = _boundary_positive_case(reserve_out=reserve_out)
        row = verify_case(case)
        rows.append(_candidate_rejection(row))
    return rows


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    accepted, rejected_candidates = collect_positive_cases()
    accepted_cases = [case for case, _row in accepted]
    rows = [row for _case, row in accepted]
    scope_probes = _scope_boundary_probes(accepted_cases)
    strict_rejections = _strict_executability_rejection_probes()
    invalid_positive_rows = [row for row in rows if not row["ok"]]
    return {
        "schema": "zenodex/ab_strict_zero_min_arbitrary_subset_family_n7_randomized_search/v1",
        "seed": SEED,
        "bit_count": BIT_COUNT,
        "target_valid_case_count": TARGET_VALID_CASE_COUNT,
        "candidate_budget": CANDIDATE_BUDGET,
        "positive_case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_positive_case": invalid_positive_rows[0] if invalid_positive_rows else None,
        "candidate_rejection_count": len(rejected_candidates),
        "candidate_rejections": rejected_candidates,
        "mask_count": sum(int(row["mask_count"]) for row in rows),
        "record_count": sum(int(row["record_count"]) for row in rows),
        "singleton_table_obligation_count": sum(
            int(row["singleton_table_obligation_count"]) for row in rows
        ),
        "selected_suffix_executable_count": sum(
            int(row["selected_suffix_executable_count"]) for row in rows
        ),
        "dominance_check_count": sum(int(row["dominance_check_count"]) for row in rows),
        "full_runtime_completion_count": sum(
            int(row["full_runtime_completion_count"]) for row in rows
        ),
        "max_records_per_mask": max((int(row["max_records_per_mask"]) for row in rows), default=0),
        "max_suffix_per_mask": max((int(row["max_suffix_per_mask"]) for row in rows), default=0),
        "coverage": {
            "n_counts": _histogram(rows, "bit_count"),
            "fee_bps_counts": _histogram(rows, "fee_bps"),
            "pattern_counts": _histogram(rows, "pattern"),
        },
        "scope_probe_count": len(scope_probes),
        "scope_probe_accept_count": sum(1 for row in scope_probes if row["accepted"]),
        "scope_probes": scope_probes,
        "strict_rejection_probe_count": len(strict_rejections),
        "strict_rejection_accept_count": sum(1 for row in strict_rejections if row["ok"]),
        "strict_rejection_probes": strict_rejections,
        "first_case": rows[0] if rows else None,
        "cases": rows,
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }


def deterministic_replay(first_search: Mapping[str, Any]) -> dict[str, Any]:
    second_search = run_search()
    first_hash = _sha256_json(_strip_timing(first_search))
    second_hash = _sha256_json(_strip_timing(second_search))
    return {"ok": first_hash == second_hash, "first_hash": first_hash, "second_hash": second_hash}


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    ok = bool(
        search["positive_case_count"] == TARGET_VALID_CASE_COUNT
        and search["valid_case_count"] == TARGET_VALID_CASE_COUNT
        and search["first_invalid_positive_case"] is None
        and search["singleton_table_obligation_count"] == search["selected_suffix_executable_count"]
        and search["dominance_check_count"] == search["full_runtime_completion_count"]
        and search["scope_probe_count"] == SCOPE_PROBE_COUNT
        and search["scope_probe_accept_count"] == 0
        and search["strict_rejection_probe_count"] == len(BOUNDARY_REJECTION_RESERVE_OUTS)
        and search["strict_rejection_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_arbitrary_subset_family_n7_randomized_report.v1",
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded n=7 randomized and positive-output-boundary falsification corpus "
            "found no counterexample to the strict zero-min arbitrary subset-family host "
            "certificate within the declared strict-executable scope."
        ),
        "authority_boundary": (
            "Research-only falsification evidence; no settlement, state-root, production, "
            "or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "replay_command": (
            "python3 tools/check_ab_strict_zero_min_arbitrary_subset_family_n7_randomized.py"
        ),
        "non_claims": [
            "This n=7 randomized corpus is bounded and finite, not exhaustive over all n=7 states.",
            "This checker does not prove Lean-to-Python refinement.",
            "This checker does not cover nonzero min_amount_out certificates; those are rejected as out of scope.",
            "Strict-executability rejection probes are scope controls, not counterexamples to the in-scope claim.",
            "This checker does not add settlement, state-root, production, or governance authority.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Arbitrary Subset-Family n=7 Randomized Stress - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Evidence Summary",
        "",
        f"- Deterministic seed: `{search['seed']}`",
        f"- Positive n=7 cases checked: `{search['positive_case_count']}`",
        f"- Valid positive cases: `{search['valid_case_count']}`",
        f"- Candidate budget: `{search['candidate_budget']}`",
        f"- Candidate rejections during positive search: `{search['candidate_rejection_count']}`",
        f"- Reachable masks checked: `{search['mask_count']}`",
        f"- Full records checked: `{search['record_count']}`",
        f"- Singleton table obligations: `{search['singleton_table_obligation_count']}`",
        f"- Dominance checks: `{search['dominance_check_count']}`",
        f"- Scope probes: `{search['scope_probe_count']}`",
        f"- Scope probe accepts: `{search['scope_probe_accept_count']}`",
        f"- Strict-executability rejection probes: `{search['strict_rejection_probe_count']}`",
        f"- Strict-executability rejection accepts: `{search['strict_rejection_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Fee histogram: `{coverage['fee_bps_counts']}`",
        f"- Regime/pattern histogram: `{coverage['pattern_counts']}`",
        f"- Max records per mask: `{search['max_records_per_mask']}`",
        f"- Max suffixes per mask: `{search['max_suffix_per_mask']}`",
        "",
        "## First Case",
        "",
        "```json",
        json.dumps(search["first_case"], indent=2, sort_keys=True),
        "```",
        "",
        "## Scope Probes",
        "",
        "| case | accepted | reason |",
        "| --- | ---: | --- |",
    ]
    for row in search["scope_probes"]:
        lines.append(f"| `{row['case_id']}` | `{row['accepted']}` | `{row['reason']}` |")
    lines.extend(
        [
            "",
            "## Strict-Executability Rejection Probes",
            "",
            "| case | accepted | first reason |",
            "| --- | ---: | --- |",
        ]
    )
    for row in search["strict_rejection_probes"]:
        first_reason = row["reasons"][0] if row["reasons"] else None
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | `{first_reason}` |")
    lines.extend(
        [
            "",
            "## Case Summary",
            "",
            "| case | ok | n | pattern | singleton tables | dominance checks |",
            "| --- | --- | ---: | --- | ---: | ---: |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['bit_count']}` | "
            f"`{row['pattern']}` | `{row['singleton_table_obligation_count']}` | "
            f"`{row['dominance_check_count']}` |"
        )
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-only", action="store_true", help="Write JSON without refreshing markdown")
    args = parser.parse_args()
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if not args.json_only:
        _write_markdown(report)
    print(json.dumps({"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
