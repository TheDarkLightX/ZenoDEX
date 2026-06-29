#!/usr/bin/env python3
"""Check subset-mask induction witnesses for AB strict zero-min compression.

This research-only checker turns the current subset-mask induction frontier into
a bounded host oracle. For each deterministic strict zero-min stress case, it
checks every reachable subset mask: the compressed representative must be a
full-state record, share the processed reserve-in sum, retain minimum output
reserve, and dominate every runtime-executable suffix completion observed from
the full-state records.
"""

from __future__ import annotations

import argparse
import copy
import itertools
import json
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_in  # noqa: E402
from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _HostRecord,
    _compressed_records,
    _full_state_records,
    _sha256_json,
    _strip_timing,
)
from tools.check_ab_strict_zero_min_emitter_witness_stress import (  # noqa: E402
    CASE_COUNT,
    MIN_STRICT_PACKET_COUNT,
    SEED,
    _StressCase,
    _iter_cases,
)
from tools.check_ab_zero_min_economic_compression_certificate import _context, _short  # noqa: E402

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_strict_zero_min_subset_induction_witness_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_SUBSET_INDUCTION_WITNESS_20260629.md"
)

EXPECTED_NEGATIVE_CONTROL_COUNT = 6


def _amount_sums(intents: list[Any]) -> list[int]:
    n = len(intents)
    return [
        sum(int(intent.get_field("amount_in")) for idx, intent in enumerate(intents) if mask & (1 << idx))
        for mask in range(1 << n)
    ]


def _record_identity(record: _HostRecord) -> tuple[int, int, tuple[str, ...]]:
    return (int(record.processed_reserve_in), int(record.reserve_out), tuple(record.order_ids))


def _record_json(record: _HostRecord) -> dict[str, Any]:
    return {
        "processed_reserve_in": int(record.processed_reserve_in),
        "reserve_out": int(record.reserve_out),
        "order_short": _short(tuple(record.order_ids)),
    }


def _remaining_intents(mask_id: int, intents: list[Any]) -> list[Any]:
    return [intent for idx, intent in enumerate(intents) if not (int(mask_id) & (1 << idx))]


def _run_suffix(
    record: _HostRecord,
    suffix: tuple[Any, ...],
    context: Any,
) -> _HostRecord | None:
    reserve_in = int(record.processed_reserve_in)
    reserve_out = int(record.reserve_out)
    order_ids = tuple(record.order_ids)
    for intent in suffix:
        try:
            quote = quote_cpmm_swap_exact_in(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=int(intent.get_field("amount_in")),
                fee_bps=int(context.pool_state.fee_bps),
            )
        except ValueError:
            return None
        if int(quote.amount_out) < int(intent.get_field("min_amount_out", 0)):
            return None
        reserve_in = int(quote.reserve_in_after)
        reserve_out = int(quote.reserve_out_after)
        order_ids = (*order_ids, intent.intent_id)
    return _HostRecord(reserve_in, reserve_out, order_ids)


def _verify_case_arrays(
    case: _StressCase,
    *,
    full_dp: list[list[_HostRecord]],
    compressed_dp: list[_HostRecord | None],
) -> dict[str, Any]:
    context = _context(case.pool, case.intents, case.balances)
    n = len(case.intents)
    full_mask = (1 << n) - 1
    reasons: list[str] = []
    first_failure: dict[str, Any] | None = None
    amount_sums = _amount_sums(case.intents)
    mask_count = 0
    record_count = 0
    suffix_check_count = 0
    executable_completion_count = 0
    max_records_per_mask = 0
    max_suffix_per_record = 0

    if compressed_dp[full_mask] is None:
        reasons.append("compressed_full_mask_not_executable")

    for mask_id, full_records in enumerate(full_dp):
        if not full_records:
            continue
        mask_count += 1
        record_count += len(full_records)
        max_records_per_mask = max(max_records_per_mask, len(full_records))
        selected = compressed_dp[mask_id]
        expected_processed_reserve_in = int(context.r_in0) + int(amount_sums[mask_id])
        if selected is None:
            reasons.append("compressed_record_missing")
            if first_failure is None:
                first_failure = {"case_id": case.case_id, "mask_id": mask_id, "reason": "compressed_record_missing"}
            continue

        selected_identity = _record_identity(selected)
        full_identities = {_record_identity(record) for record in full_records}
        if selected_identity not in full_identities:
            reasons.append("selected_record_not_in_full_state_records")
            if first_failure is None:
                first_failure = {
                    "case_id": case.case_id,
                    "mask_id": mask_id,
                    "reason": "selected_record_not_in_full_state_records",
                    "selected": _record_json(selected),
                }
        if int(selected.processed_reserve_in) != expected_processed_reserve_in:
            reasons.append("selected_processed_reserve_in_mismatch")
        for record in full_records:
            if int(record.processed_reserve_in) != expected_processed_reserve_in:
                reasons.append("full_record_processed_reserve_in_mismatch")
                if first_failure is None:
                    first_failure = {
                        "case_id": case.case_id,
                        "mask_id": mask_id,
                        "reason": "full_record_processed_reserve_in_mismatch",
                        "record": _record_json(record),
                        "expected_processed_reserve_in": expected_processed_reserve_in,
                    }

        min_reserve_out = min(int(record.reserve_out) for record in full_records)
        if int(selected.reserve_out) != min_reserve_out:
            reasons.append("selected_reserve_out_not_min")
            if first_failure is None:
                first_failure = {
                    "case_id": case.case_id,
                    "mask_id": mask_id,
                    "reason": "selected_reserve_out_not_min",
                    "selected": _record_json(selected),
                    "min_reserve_out": min_reserve_out,
                }

        suffixes = tuple(itertools.permutations(_remaining_intents(mask_id, case.intents)))
        max_suffix_per_record = max(max_suffix_per_record, len(suffixes))
        selected_suffix_cache: dict[tuple[str, ...], _HostRecord | None] = {}
        for record in full_records:
            for suffix in suffixes:
                suffix_ids = tuple(intent.intent_id for intent in suffix)
                suffix_check_count += 1
                full_result = _run_suffix(record, suffix, context)
                if full_result is None:
                    continue
                executable_completion_count += 1
                selected_result = selected_suffix_cache.get(suffix_ids)
                if suffix_ids not in selected_suffix_cache:
                    selected_result = _run_suffix(selected, suffix, context)
                    selected_suffix_cache[suffix_ids] = selected_result
                if selected_result is None:
                    reasons.append("selected_suffix_executability_gap")
                    if first_failure is None:
                        first_failure = {
                            "case_id": case.case_id,
                            "mask_id": mask_id,
                            "reason": "selected_suffix_executability_gap",
                            "full_record": _record_json(record),
                            "selected": _record_json(selected),
                            "suffix_short": _short(suffix_ids),
                        }
                    continue
                if int(selected_result.reserve_out) > int(full_result.reserve_out):
                    reasons.append("selected_final_reserve_dominance_failure")
                    if first_failure is None:
                        first_failure = {
                            "case_id": case.case_id,
                            "mask_id": mask_id,
                            "reason": "selected_final_reserve_dominance_failure",
                            "full_final": _record_json(full_result),
                            "selected_final": _record_json(selected_result),
                            "suffix_short": _short(suffix_ids),
                        }

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "case_id": case.case_id,
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "first_failure": first_failure,
        "bit_count": n,
        "fee_bps": int(case.pool.fee_bps),
        "pattern": case.pattern,
        "mask_count": mask_count,
        "record_count": record_count,
        "suffix_check_count": suffix_check_count,
        "executable_completion_count": executable_completion_count,
        "max_records_per_mask": max_records_per_mask,
        "max_suffix_per_record": max_suffix_per_record,
        "full_mask_selected": _record_json(compressed_dp[full_mask]) if compressed_dp[full_mask] is not None else None,
    }


def verify_case(case: _StressCase) -> dict[str, Any]:
    context = _context(case.pool, case.intents, case.balances)
    return _verify_case_arrays(
        case,
        full_dp=_full_state_records(case.intents, context),
        compressed_dp=_compressed_records(case.intents, context),
    )


def _clone_full_dp(full_dp: list[list[_HostRecord]]) -> list[list[_HostRecord]]:
    return [list(records) for records in full_dp]


def _clone_compressed_dp(compressed_dp: list[_HostRecord | None]) -> list[_HostRecord | None]:
    return list(compressed_dp)


def _negative_controls(case: _StressCase) -> list[dict[str, Any]]:
    context = _context(case.pool, case.intents, case.balances)
    base_full = _full_state_records(case.intents, context)
    base_compressed = _compressed_records(case.intents, context)
    controls: list[tuple[str, list[list[_HostRecord]], list[_HostRecord | None], str]] = []

    missing_compressed = _clone_compressed_dp(base_compressed)
    missing_compressed[0] = None
    controls.append(
        ("compressed_record_missing", _clone_full_dp(base_full), missing_compressed, "compressed_record_missing")
    )

    processed_mismatch_full = _clone_full_dp(base_full)
    processed_mismatch_full[0][0] = _HostRecord(
        int(processed_mismatch_full[0][0].processed_reserve_in) + 1,
        int(processed_mismatch_full[0][0].reserve_out),
        tuple(processed_mismatch_full[0][0].order_ids),
    )
    controls.append(
        (
            "full_record_processed_reserve_in_mismatch",
            processed_mismatch_full,
            _clone_compressed_dp(base_compressed),
            "full_record_processed_reserve_in_mismatch",
        )
    )

    selected_not_min = _clone_compressed_dp(base_compressed)
    selected_not_min[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        int(base_full[0][0].reserve_out) + 1,
        tuple(base_compressed[0].order_ids),
    )
    controls.append(
        (
            "selected_reserve_out_not_min",
            _clone_full_dp(base_full),
            selected_not_min,
            "selected_reserve_out_not_min",
        )
    )

    selected_not_member = _clone_compressed_dp(base_compressed)
    selected_not_member[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        int(base_compressed[0].reserve_out),
        ("mutated-order",),
    )
    controls.append(
        (
            "selected_record_not_in_full_state_records",
            _clone_full_dp(base_full),
            selected_not_member,
            "selected_record_not_in_full_state_records",
        )
    )

    suffix_gap = _clone_compressed_dp(base_compressed)
    suffix_gap[0] = _HostRecord(int(base_compressed[0].processed_reserve_in), 1, tuple(base_compressed[0].order_ids))
    controls.append(
        (
            "selected_suffix_executability_gap",
            _clone_full_dp(base_full),
            suffix_gap,
            "selected_suffix_executability_gap",
        )
    )

    dominance_failure = _clone_compressed_dp(base_compressed)
    dominance_failure[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        int(base_full[0][0].reserve_out) + 1_000,
        tuple(base_compressed[0].order_ids),
    )
    controls.append(
        (
            "selected_final_reserve_dominance_failure",
            _clone_full_dp(base_full),
            dominance_failure,
            "selected_final_reserve_dominance_failure",
        )
    )

    rows: list[dict[str, Any]] = []
    for mutation_id, full_dp, compressed_dp, expected_reason in controls:
        verification = _verify_case_arrays(case, full_dp=full_dp, compressed_dp=compressed_dp)
        rows.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(verification["ok"]),
                "expected_reason": expected_reason,
                "reasons": verification["reasons"],
                "first_failure": verification["first_failure"],
            }
        )
    return rows


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    rows: list[dict[str, Any]] = []
    first_case: _StressCase | None = None
    for case in _iter_cases():
        if first_case is None:
            first_case = case
        rows.append(verify_case(case))

    invalid_rows = [row for row in rows if not row["ok"]]
    negative_controls = _negative_controls(first_case) if first_case is not None else []
    n_counts: dict[str, int] = {}
    pattern_counts: dict[str, int] = {}
    fee_counts: dict[str, int] = {}
    for row in rows:
        n_counts[str(row["bit_count"])] = n_counts.get(str(row["bit_count"]), 0) + 1
        pattern_counts[str(row["pattern"])] = pattern_counts.get(str(row["pattern"]), 0) + 1
        fee_counts[str(row["fee_bps"])] = fee_counts.get(str(row["fee_bps"]), 0) + 1

    return {
        "schema": "zenodex/ab_strict_zero_min_subset_induction_witness_search/v1",
        "seed": SEED,
        "case_count": CASE_COUNT,
        "strict_case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "mask_count": sum(int(row["mask_count"]) for row in rows),
        "record_count": sum(int(row["record_count"]) for row in rows),
        "suffix_check_count": sum(int(row["suffix_check_count"]) for row in rows),
        "executable_completion_count": sum(int(row["executable_completion_count"]) for row in rows),
        "max_records_per_mask": max((int(row["max_records_per_mask"]) for row in rows), default=0),
        "max_suffix_per_record": max((int(row["max_suffix_per_record"]) for row in rows), default=0),
        "coverage": {
            "n_counts": dict(sorted(n_counts.items())),
            "fee_bps_counts": dict(sorted(fee_counts.items(), key=lambda item: int(item[0]))),
            "pattern_counts": dict(sorted(pattern_counts.items())),
        },
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(1 for row in negative_controls if row["accepted"]),
        "negative_controls": negative_controls,
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
        and search["strict_case_count"] >= MIN_STRICT_PACKET_COUNT
        and search["valid_case_count"] == search["strict_case_count"]
        and search["mask_count"] > 0
        and search["record_count"] > 0
        and search["suffix_check_count"] > 0
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": "zenodex.ab_strict_zero_min_subset_induction_witness_report.v1",
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded host oracle checks the subset-mask induction obligations for strict "
            "zero-min one-record min-reserve-out compression across the deterministic stress corpus."
        ),
        "authority_boundary": (
            "Research-only induction witness evidence; no settlement, state-root, production, "
            "or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "non_claims": [
            "This bounded oracle is not a Lean proof of the full subset-mask induction theorem.",
            "This checker does not prove Lean-to-Python refinement.",
            "This checker does not define canonical tie order.",
            "Nonzero min_amount_out batches are outside this artifact.",
            "The stress corpus is deterministic and finite, not exhaustive over all pool states.",
            "No settlement authority is derived from this artifact.",
        ],
        "replay_command": "python3 tools/check_ab_strict_zero_min_subset_induction_witness.py",
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Subset Induction Witness - 2026-06-29",
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
        f"- Generated cases: `{search['case_count']}`",
        f"- Strict cases checked: `{search['strict_case_count']}`",
        f"- Valid cases: `{search['valid_case_count']}`",
        f"- Reachable masks checked: `{search['mask_count']}`",
        f"- Full records checked: `{search['record_count']}`",
        f"- Suffix checks: `{search['suffix_check_count']}`",
        f"- Runtime-executable completions: `{search['executable_completion_count']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Induction Obligations Checked",
        "",
        "```text",
        "for each reachable subset mask:",
        "  selected compressed record is present in the full-state record set",
        "  all records share reserve_in = initial_reserve_in + subset_amount_sum",
        "  selected reserve_out is the minimum reserve_out at that mask",
        "  every runtime-executable full-record suffix completion executes from selected",
        "  selected final reserve_out <= full-record final reserve_out",
        "```",
        "",
        "The last line is the host analogue of the Lean reserve-dominance direction:",
        "lower final output reserve means weakly greater zero-min surplus.",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Fee histogram: `{coverage['fee_bps_counts']}`",
        f"- Pattern histogram: `{coverage['pattern_counts']}`",
        f"- Max records per mask: `{search['max_records_per_mask']}`",
        f"- Max suffixes per record: `{search['max_suffix_per_record']}`",
        "",
        "## First Case",
        "",
        "```json",
        json.dumps(search["cases"][0], indent=2, sort_keys=True),
        "```",
        "",
        "## Negative Controls",
        "",
        "| mutation | accepted | expected reason |",
        "| --- | ---: | --- |",
    ]
    for row in search["negative_controls"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | `{row['expected_reason']}` |")
    lines.extend(["", "## Case Summary", "", "| case | ok | n | masks | records | suffix checks |", "| --- | --- | ---: | ---: | ---: | ---: |"])
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['bit_count']}` | "
            f"`{row['mask_count']}` | `{row['record_count']}` | `{row['suffix_check_count']}` |"
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
