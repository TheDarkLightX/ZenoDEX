#!/usr/bin/env python3
"""Extended stress falsification for AB strict zero-min subset-family certificates.

This research-only checker broadens the deterministic corpus used by
`check_ab_strict_zero_min_arbitrary_subset_family_certificate.py`.  It keeps the
same certificate verifier and changes only the case generator: reserve regimes,
fee schedules, tie-heavy vectors, bursty inputs, and near-domain reserves are
varied to search for counterexamples outside the original random seed.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.kernels.python.settlement_swap_runtime_v1 import DEX_POOL_RESERVE_MAX  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402
from tools.check_ab_strict_zero_min_arbitrary_subset_family_certificate import (  # noqa: E402
    build_case_packet,
    verify_case,
)
from tools.check_ab_strict_zero_min_emitter_witness import _sha256_json, _strip_timing  # noqa: E402
from tools.check_ab_strict_zero_min_emitter_witness_stress import _StressCase  # noqa: E402
from tools.check_ab_zero_min_economic_compression_certificate import (  # noqa: E402
    ASSET0,
    ASSET1,
    POOL_ID,
    _intent,
    _sender,
)

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_arbitrary_subset_family_extended_stress_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_ARBITRARY_SUBSET_FAMILY_EXTENDED_STRESS_20260629.md"
)

SEED = 2_026_062_902
CASE_COUNT = 90
MIN_VALID_CASE_COUNT = CASE_COUNT
SCOPE_PROBE_COUNT = 5
FEE_BPS_VALUES = (0, 1, 5, 30, 75, 100, 500, 2_500, 5_000, 9_000)


def _pool(case_no: int, *, reserve_in: int, reserve_out: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=int(reserve_in),
        reserve1=int(reserve_out),
        fee_bps=int(fee_bps),
        lp_supply=50_000 + case_no,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _amount_pattern(case_no: int, n: int) -> tuple[str, list[int]]:
    pattern_id = case_no % 10
    if pattern_id == 0:
        return "tie_heavy_flat", [32 + (case_no % 3)] * n
    if pattern_id == 1:
        return "near_tie_stagger", [41 + ((idx + case_no) % 3) for idx in range(n)]
    if pattern_id == 2:
        return "ascending_stair", [24 + idx * 11 + (case_no % 5) for idx in range(n)]
    if pattern_id == 3:
        return "descending_stair", [24 + (n - idx) * 11 + (case_no % 5) for idx in range(n)]
    if pattern_id == 4:
        return "alternating_large", [28 if idx % 2 == 0 else 190 + (case_no % 17) for idx in range(n)]
    if pattern_id == 5:
        return "burst_prefix", [360 + (case_no % 29), *([26 + (case_no % 7)] * (n - 1))]
    if pattern_id == 6:
        return "burst_suffix", [26 + (case_no % 7)] * (n - 1) + [360 + (case_no % 29)]
    if pattern_id == 7:
        return "powers", [18 * (1 << min(idx, 4)) for idx in range(n)]
    if pattern_id == 8:
        return "prime_steps", [29, 31, 37, 43, 47, 53][:n]
    return "high_fee_safe", [80 + idx * 9 + (case_no % 11) for idx in range(n)]


def _reserve_regime(case_no: int, *, total_amount: int) -> tuple[str, int, int]:
    regime_id = case_no % 9
    if regime_id == 0:
        return "balanced_mid", 900 + case_no * 3, 160_000 + total_amount * 300
    if regime_id == 1:
        return "low_in_high_out", 50 + (case_no % 17), 280_000 + total_amount * 700
    if regime_id == 2:
        reserve_in = DEX_POOL_RESERVE_MAX - total_amount - 2_000 - case_no
        return "near_domain_reserve_in", reserve_in, 2_850_000_000
    if regime_id == 3:
        return "tight_out_positive", 700 + case_no, max(12_000, total_amount * 85 + 3_000)
    if regime_id == 4:
        return "huge_out", 2_000 + case_no * 5, 2_900_000_000 - case_no * 97
    if regime_id == 5:
        return "skewed_in", 2_000_000 + case_no * 211, 750_000 + total_amount * 500
    if regime_id == 6:
        return "small_balanced", 180 + (case_no % 23), 70_000 + total_amount * 250
    if regime_id == 7:
        return "deep_balanced", 1_250_000 + case_no * 101, 1_800_000 + total_amount * 50
    return "thin_margin_high_out", 5_000 + case_no * 13, 35_000 + total_amount * 110


def _sender_no(case_no: int, idx: int) -> int:
    return ((case_no * 19 + idx) % 500) + 1


def _build_case(case_no: int) -> _StressCase:
    n = 2 + (case_no % 5)
    pattern, amounts = _amount_pattern(case_no, n)
    reserve_regime, reserve_in, reserve_out = _reserve_regime(case_no, total_amount=sum(amounts))
    fee_bps = FEE_BPS_VALUES[case_no % len(FEE_BPS_VALUES)]
    pool = _pool(case_no, reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee_bps)
    balances = BalanceTable()
    intents: list[Any] = []
    for idx, amount_in in enumerate(amounts):
        sender_no = _sender_no(case_no, idx)
        balances.set(_sender(sender_no), ASSET0, int(amount_in) + 100_000)
        balances.set(_sender(sender_no), ASSET1, 0)
        intents.append(
            _intent(
                900_000 + case_no * 16 + idx,
                sender_no=sender_no,
                amount_in=int(amount_in),
                min_amount_out=0,
            )
        )
    return _StressCase(
        case_id=f"extended_{case_no:03d}_{reserve_regime}_{pattern}_n{n}_fee{fee_bps}",
        pool=pool,
        intents=intents,
        balances=balances,
        pattern=f"{reserve_regime}/{pattern}",
    )


def iter_extended_cases() -> list[_StressCase]:
    return [_build_case(case_no) for case_no in range(CASE_COUNT)]


def _with_nonzero_min(case: _StressCase) -> _StressCase:
    intents = [
        _intent(
            1_100_000 + idx,
            sender_no=_sender_no(10_000, idx),
            amount_in=int(intent.get_field("amount_in")),
            min_amount_out=1 if idx == 0 else 0,
        )
        for idx, intent in enumerate(case.intents)
    ]
    balances = BalanceTable()
    for idx, intent in enumerate(intents):
        balances.set(_sender(_sender_no(10_000, idx)), ASSET0, int(intent.get_field("amount_in")) + 100_000)
        balances.set(_sender(_sender_no(10_000, idx)), ASSET1, 0)
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


def _histogram(rows: Iterable[Mapping[str, Any]], key: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for row in rows:
        value = str(row[key])
        out[value] = out.get(value, 0) + 1
    return dict(sorted(out.items()))


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    cases = iter_extended_cases()
    rows = [verify_case(case) for case in cases]
    invalid_rows = [row for row in rows if not row["ok"]]
    scope_probes = _scope_boundary_probes(cases)
    return {
        "schema": "zenodex/ab_strict_zero_min_arbitrary_subset_family_extended_stress_search/v1",
        "seed": SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
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
        search["case_count"] == CASE_COUNT
        and search["valid_case_count"] >= MIN_VALID_CASE_COUNT
        and search["singleton_table_obligation_count"] == search["selected_suffix_executable_count"]
        and search["dominance_check_count"] == search["full_runtime_completion_count"]
        and search["scope_probe_count"] == SCOPE_PROBE_COUNT
        and search["scope_probe_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_arbitrary_subset_family_extended_stress_report.v1",
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A broader deterministic falsification corpus found no counterexample to "
            "the strict zero-min arbitrary subset-family host certificate across "
            "reserve extremes, high fee schedules, tie-heavy inputs, and bursty inputs."
        ),
        "authority_boundary": (
            "Research-only falsification evidence; no settlement, state-root, production, "
            "or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "replay_command": (
            "python3 tools/check_ab_strict_zero_min_arbitrary_subset_family_extended_stress.py"
        ),
        "non_claims": [
            "This extended stress corpus is deterministic and finite, not exhaustive over all states.",
            "This checker does not prove Lean-to-Python refinement.",
            "This checker does not cover nonzero min_amount_out certificates; those are rejected as out of scope.",
            "This checker does not define canonical tie order.",
            "This checker does not add settlement, state-root, production, or governance authority.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Arbitrary Subset-Family Extended Stress - 2026-06-29",
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
        f"- Cases checked: `{search['case_count']}`",
        f"- Valid cases: `{search['valid_case_count']}`",
        f"- Reachable masks checked: `{search['mask_count']}`",
        f"- Full records checked: `{search['record_count']}`",
        f"- Singleton table obligations: `{search['singleton_table_obligation_count']}`",
        f"- Dominance checks: `{search['dominance_check_count']}`",
        f"- Scope probes: `{search['scope_probe_count']}`",
        f"- Scope probe accepts: `{search['scope_probe_accept_count']}`",
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
