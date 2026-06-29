#!/usr/bin/env python3
"""Check sampled n=8 reserve-state child-frontier generation.

This research-only checker reuses the deterministic n=8 reserve-state quotient
sample and verifies that each sampled child quotient family equals the union of
sampled predecessor `ReserveState.afterStep` images.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_reserve_state_child_frontier_generation_20260629 import (  # noqa: E402
    _new_failure,
    _state_rows,
    _state_set_digest,
)
from tools.check_ab_reserve_state_transition_projection_20260629 import (  # noqa: E402
    _packet_hash,
    _short,
    _sorted_states,
    _state_set,
    _with_packet_hash,
)
from tools.check_ab_strict_zero_min_arbitrary_subset_family_certificate import (  # noqa: E402
    AUTHORITY_BOUNDARY,
    _case_has_zero_min_amount_out,
    _case_summary_inputs,
)
from tools.check_ab_strict_zero_min_arbitrary_subset_family_extended_stress import (  # noqa: E402
    _histogram,
)
from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _HostRecord,
    _full_state_records,
    _sha256_json,
    _strip_timing,
)
from tools.check_ab_strict_zero_min_reserve_state_quotient_certificate import (  # noqa: E402
    _case_context,
    _quotient_digest,
    _run_suffix_from_state,
)
from tools.check_ab_strict_zero_min_reserve_state_quotient_n8_sample_20260629 import (  # noqa: E402
    BIT_COUNT,
    SEED,
    TARGET_CASE_COUNT,
    _n8_cases,
    _sample_mask_ids,
    _sample_plan,
)
from tools.check_ab_strict_zero_min_subset_induction_witness import _clone_full_dp  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_n8_sample_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_N8_SAMPLE_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_reserve_state_child_frontier_n8_sample_packet.v1"
REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_n8_sample_report.v1"
SEARCH_SCHEMA = "zenodex/ab_reserve_state_child_frontier_n8_sample_search/v1"
SCOPE = "n8_same_pool_same_direction_exact_in_zero_min_reserve_state_child_frontier_sample"
EXPECTED_NEGATIVE_CONTROL_COUNT = 7


def _lean_contract() -> dict[str, str]:
    return {
        "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
        "transition_def": "ReserveState.afterStep",
        "transition_invariant_endpoint": "reserveStateQuotientInvariant_afterStep",
        "transition_executability_endpoint": (
            "reserveStateQuotientInvariant_familySuffixExecutable"
        ),
        "host_generation_shape": (
            "sampled child quotient state set equals union of predecessor afterStep images"
        ),
    }


def _sampled_child_mask_ids(n: int) -> list[int]:
    return [mask_id for mask_id in _sample_mask_ids(n) if mask_id != 0]


def _packet_rail_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["sample_packet_missing"]
    reasons: list[str] = []
    if packet.get("schema") != PACKET_SCHEMA:
        reasons.append("packet_schema_mismatch")
    if packet.get("scope") != SCOPE:
        reasons.append("packet_scope_mismatch")
    if packet.get("authority_boundary") != AUTHORITY_BOUNDARY:
        reasons.append("authority_boundary_mismatch")
    if packet.get("packet_hash_bound") is not True:
        reasons.append("packet_hash_bound_missing")
    if packet.get("no_authority_effect") is not True:
        reasons.append("authority_effect_present")
    if packet.get("sampled_n8_bound") is not True:
        reasons.append("sampled_n8_bound_missing")
    if packet.get("child_frontier_generation_bound") is not True:
        reasons.append("child_frontier_generation_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("sample_plan") != _sample_plan(BIT_COUNT):
        reasons.append("packet_sample_plan_mismatch")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _predecessor_rows(
    case: Any,
    *,
    child_mask_id: int,
    full_dp: list[list[_HostRecord]],
) -> tuple[list[dict[str, Any]], set[Any], list[str]]:
    context = _case_context(case)
    generated_states: set[Any] = set()
    rows: list[dict[str, Any]] = []
    reasons: list[str] = []
    for step_bit_index, intent in enumerate(case.intents):
        if not (child_mask_id & (1 << step_bit_index)):
            continue
        parent_mask_id = child_mask_id ^ (1 << step_bit_index)
        parent_states = _state_set(full_dp[parent_mask_id])
        local_states: set[Any] = set()
        executable_count = 0
        for state in _sorted_states(parent_states):
            child_state = _run_suffix_from_state(state, (intent,), context)
            if child_state is None:
                reasons.append("predecessor_transition_not_executable")
                continue
            executable_count += 1
            local_states.add(child_state)
            generated_states.add(child_state)
        rows.append(
            {
                "parent_mask_id": int(parent_mask_id),
                "step_bit_index": int(step_bit_index),
                "step_order_id": intent.intent_id,
                "step_order_short": _short((intent.intent_id,)),
                "parent_state_count": len(parent_states),
                "predecessor_transition_count": len(parent_states),
                "predecessor_transition_executable_count": executable_count,
                "generated_state_count": len(local_states),
                "parent_quotient_digest": _quotient_digest(full_dp[parent_mask_id]),
                "generated_state_digest": _state_set_digest(local_states),
            }
        )
    return rows, generated_states, list(dict.fromkeys(reasons))


def _frontier_row(
    case: Any,
    *,
    child_mask_id: int,
    full_dp: list[list[_HostRecord]],
) -> tuple[dict[str, Any], list[str]]:
    child_states = _state_set(full_dp[child_mask_id])
    predecessor_rows, generated_states, reasons = _predecessor_rows(
        case,
        child_mask_id=child_mask_id,
        full_dp=full_dp,
    )
    missing_states = child_states - generated_states
    extra_states = generated_states - child_states
    if missing_states:
        reasons.append("generated_frontier_missing_child_state")
    if extra_states:
        reasons.append("generated_frontier_extra_child_state")
    row = {
        "case_id": case.case_id,
        "child_mask_id": int(child_mask_id),
        "child_quotient_digest": _quotient_digest(full_dp[child_mask_id]),
        "child_state_count": len(child_states),
        "generated_state_count": len(generated_states),
        "generated_state_digest": _state_set_digest(generated_states),
        "frontier_equal": not missing_states and not extra_states,
        "missing_child_state_count": len(missing_states),
        "extra_generated_state_count": len(extra_states),
        "missing_child_states": _state_rows(missing_states),
        "extra_generated_states": _state_rows(extra_states),
        "predecessor_count": len(predecessor_rows),
        "predecessor_transition_count": sum(
            int(row["predecessor_transition_count"]) for row in predecessor_rows
        ),
        "predecessor_transition_executable_count": sum(
            int(row["predecessor_transition_executable_count"]) for row in predecessor_rows
        ),
        "predecessor_rows_digest": _sha256_json(predecessor_rows),
        "first_predecessor": predecessor_rows[0] if predecessor_rows else None,
    }
    return row, list(dict.fromkeys(reasons))


def _summary_keys() -> tuple[str, ...]:
    return (
        "sampled_child_mask_count",
        "frontier_equal_count",
        "predecessor_edge_count",
        "predecessor_transition_count",
        "predecessor_transition_executable_count",
        "sampled_child_state_count",
        "generated_state_count",
        "missing_child_state_count",
        "extra_generated_state_count",
        "max_child_state_count",
        "max_generated_state_count",
        "frontier_rows_digest",
    )


def _verify_case_arrays(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]],
    packet: Mapping[str, Any] | None,
) -> dict[str, Any]:
    n = len(case.intents)
    reasons: list[str] = []
    first_failure: dict[str, Any] | None = None
    if packet is not None:
        reasons.extend(_packet_rail_reasons(packet))
    if n != BIT_COUNT:
        reasons.append("bit_count_out_of_scope")
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=0,
            reason="bit_count_out_of_scope",
            bit_count=n,
        )
    if not _case_has_zero_min_amount_out(case):
        reasons.append("nonzero_min_amount_out_out_of_scope")
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=0,
            reason="nonzero_min_amount_out_out_of_scope",
        )

    rows: list[dict[str, Any]] = []
    predecessor_edge_count = 0
    predecessor_transition_count = 0
    predecessor_transition_executable_count = 0
    sampled_child_state_count = 0
    generated_state_count = 0
    missing_child_state_count = 0
    extra_generated_state_count = 0
    max_child_state_count = 0
    max_generated_state_count = 0

    for child_mask_id in _sampled_child_mask_ids(n):
        row, row_reasons = _frontier_row(
            case,
            child_mask_id=child_mask_id,
            full_dp=full_dp,
        )
        rows.append(row)
        predecessor_edge_count += int(row["predecessor_count"])
        predecessor_transition_count += int(row["predecessor_transition_count"])
        predecessor_transition_executable_count += int(
            row["predecessor_transition_executable_count"]
        )
        sampled_child_state_count += int(row["child_state_count"])
        generated_state_count += int(row["generated_state_count"])
        missing_child_state_count += int(row["missing_child_state_count"])
        extra_generated_state_count += int(row["extra_generated_state_count"])
        max_child_state_count = max(max_child_state_count, int(row["child_state_count"]))
        max_generated_state_count = max(
            max_generated_state_count,
            int(row["generated_state_count"]),
        )
        if row_reasons:
            reasons.extend(row_reasons)
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=child_mask_id,
                reason=row_reasons[0],
            )

    summary = {
        "sampled_child_mask_count": len(rows),
        "frontier_equal_count": sum(1 for row in rows if row["frontier_equal"]),
        "predecessor_edge_count": predecessor_edge_count,
        "predecessor_transition_count": predecessor_transition_count,
        "predecessor_transition_executable_count": predecessor_transition_executable_count,
        "sampled_child_state_count": sampled_child_state_count,
        "generated_state_count": generated_state_count,
        "missing_child_state_count": missing_child_state_count,
        "extra_generated_state_count": extra_generated_state_count,
        "max_child_state_count": max_child_state_count,
        "max_generated_state_count": max_generated_state_count,
        "frontier_rows_digest": _sha256_json(rows),
    }
    first_frontier = rows[0] if rows else None

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("frontier_summary") != summary:
            reasons.append("packet_frontier_summary_mismatch")
        if packet.get("first_frontier") != first_frontier:
            reasons.append("packet_first_frontier_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "case_id": case.case_id,
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "first_failure": first_failure,
        "bit_count": n,
        "fee_bps": int(case.pool.fee_bps),
        "pattern": case.pattern,
        "first_frontier": first_frontier,
        **summary,
    }


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
) -> dict[str, Any]:
    if full_dp is None:
        full_dp = _full_state_records(case.intents, _case_context(case))
    verification = _verify_case_arrays(case, full_dp=full_dp, packet=None)
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "sampled_n8_bound": True,
        "child_frontier_generation_bound": True,
        "reserve_state_only_bound": True,
        "sample_plan": _sample_plan(len(case.intents)),
        "sampled_child_mask_ids": _sampled_child_mask_ids(len(case.intents)),
        "lean_contract": _lean_contract(),
        "frontier_summary": {key: verification[key] for key in _summary_keys()},
        "first_frontier": verification["first_frontier"],
    }
    return _with_packet_hash(packet)


def verify_case(case: Any) -> dict[str, Any]:
    full_dp = _full_state_records(case.intents, _case_context(case))
    packet = build_case_packet(case, full_dp=full_dp)
    verification = _verify_case_arrays(case, full_dp=full_dp, packet=packet)
    return verification | {"packet_hash": packet["packet_hash"]}


def _negative_controls(cases: list[Any]) -> list[dict[str, Any]]:
    case = cases[0]
    full_dp = _full_state_records(case.intents, _case_context(case))
    base_packet = build_case_packet(case, full_dp=full_dp)
    controls: list[tuple[str, Any, list[list[_HostRecord]], dict[str, Any] | None, str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", case, _clone_full_dp(full_dp), bad_hash, "packet_hash_mismatch"))

    bad_sample = copy.deepcopy(base_packet)
    bad_sample["sampled_n8_bound"] = False
    controls.append(("sampled_n8_bound_missing", case, _clone_full_dp(full_dp), _with_packet_hash(bad_sample), "sampled_n8_bound_missing"))

    bad_plan = copy.deepcopy(base_packet)
    bad_plan["sample_plan"]["bit_count"] += 1
    controls.append(("packet_sample_plan_mismatch", case, _clone_full_dp(full_dp), _with_packet_hash(bad_plan), "packet_sample_plan_mismatch"))

    bad_contract = copy.deepcopy(base_packet)
    bad_contract["lean_contract"]["host_generation_shape"] = "stale_generation_shape"
    controls.append(("packet_lean_contract_mismatch", case, _clone_full_dp(full_dp), _with_packet_hash(bad_contract), "packet_lean_contract_mismatch"))

    bad_authority = copy.deepcopy(base_packet)
    bad_authority["no_authority_effect"] = False
    controls.append(("authority_effect_present", case, _clone_full_dp(full_dp), _with_packet_hash(bad_authority), "authority_effect_present"))

    missing_parent = _clone_full_dp(full_dp)
    missing_parent[0] = []
    controls.append(("generated_frontier_missing_child_state", case, missing_parent, None, "generated_frontier_missing_child_state"))

    extra_parent = _clone_full_dp(full_dp)
    extra_parent[0] = [
        _HostRecord(
            int(extra_parent[0][0].processed_reserve_in),
            int(extra_parent[0][0].reserve_out) + 50,
            tuple(extra_parent[0][0].order_ids),
        )
    ]
    controls.append(("generated_frontier_extra_child_state", case, extra_parent, None, "generated_frontier_extra_child_state"))

    output: list[dict[str, Any]] = []
    for mutation_id, target_case, mutated_full, packet, expected_reason in controls:
        verification = _verify_case_arrays(target_case, full_dp=mutated_full, packet=packet)
        output.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(verification["ok"]),
                "expected_reason": expected_reason,
                "reasons": verification["reasons"],
                "first_failure": verification["first_failure"],
            }
        )
    return output


def run_search() -> dict[str, Any]:
    started = time.perf_counter()
    cases = _n8_cases()
    rows = [verify_case(case) for case in cases]
    invalid_rows = [row for row in rows if not row["ok"]]
    negative_controls = _negative_controls(cases)
    return {
        "schema": SEARCH_SCHEMA,
        "source_seed": SEED,
        "sample_plan": _sample_plan(BIT_COUNT),
        "sampled_child_mask_ids": _sampled_child_mask_ids(BIT_COUNT),
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "sampled_child_mask_count": sum(int(row["sampled_child_mask_count"]) for row in rows),
        "frontier_equal_count": sum(int(row["frontier_equal_count"]) for row in rows),
        "predecessor_edge_count": sum(int(row["predecessor_edge_count"]) for row in rows),
        "predecessor_transition_count": sum(int(row["predecessor_transition_count"]) for row in rows),
        "predecessor_transition_executable_count": sum(
            int(row["predecessor_transition_executable_count"]) for row in rows
        ),
        "sampled_child_state_count": sum(int(row["sampled_child_state_count"]) for row in rows),
        "generated_state_count": sum(int(row["generated_state_count"]) for row in rows),
        "missing_child_state_count": sum(int(row["missing_child_state_count"]) for row in rows),
        "extra_generated_state_count": sum(int(row["extra_generated_state_count"]) for row in rows),
        "max_child_state_count": max((int(row["max_child_state_count"]) for row in rows), default=0),
        "max_generated_state_count": max((int(row["max_generated_state_count"]) for row in rows), default=0),
        "frontier_rows_digest": _sha256_json([row["frontier_rows_digest"] for row in rows]),
        "coverage": {
            "n_counts": _histogram(rows, "bit_count"),
            "fee_bps_counts": _histogram(rows, "fee_bps"),
            "pattern_counts": _histogram(rows, "pattern"),
            "reason_classes": sorted(
                {
                    reason
                    for control in negative_controls
                    for reason in control["reasons"]
                }
            ),
        },
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(1 for row in negative_controls if row["accepted"]),
        "negative_controls": negative_controls,
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
        search["case_count"] == TARGET_CASE_COUNT
        and search["valid_case_count"] == TARGET_CASE_COUNT
        and search["first_invalid_case"] is None
        and search["sample_plan"]["bit_count"] == BIT_COUNT
        and search["sampled_child_mask_count"] == search["frontier_equal_count"]
        and search["predecessor_transition_count"]
        == search["predecessor_transition_executable_count"]
        and search["sampled_child_state_count"] == search["generated_state_count"]
        and search["missing_child_state_count"] == 0
        and search["extra_generated_state_count"] == 0
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded deterministic n=8 sample supports reserve-state "
            "child-frontier generation on the sampled masks: each sampled child "
            "quotient family equals the union of predecessor afterStep images."
        ),
        "authority_boundary": (
            "Research-only certificate-compression evidence; no settlement, state-root, "
            "production, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_n8_sample_20260629.py"
        ),
        "non_claims": [
            "This is a bounded deterministic n=8 sample, not exhaustive n=8 coverage.",
            "This checker covers only sampled zero-min exact-in cases and sampled child masks.",
            "This checker does not prove Python-to-Lean refinement.",
            "This checker does not prove child-frontier generation in Lean.",
            "This checker does not define canonical tie order or preserve order-id history.",
            "No settlement, state-root, production, routing, matching, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Reserve-State Child Frontier n=8 Sample - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Evidence Summary",
        "",
        f"- Cases checked: `{search['case_count']}`",
        f"- Sampled child masks: `{search['sampled_child_mask_count']}`",
        f"- Frontier equalities: `{search['frontier_equal_count']}`",
        f"- Predecessor edges: `{search['predecessor_edge_count']}`",
        f"- Predecessor transitions: `{search['predecessor_transition_count']}`",
        f"- Sampled child states: `{search['sampled_child_state_count']}`",
        f"- Generated states: `{search['generated_state_count']}`",
        f"- Missing child states: `{search['missing_child_state_count']}`",
        f"- Extra generated states: `{search['extra_generated_state_count']}`",
        f"- Max child states per sampled mask: `{search['max_child_state_count']}`",
        f"- Frontier digest: `{search['frontier_rows_digest']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Fee histogram: `{coverage['fee_bps_counts']}`",
        f"- Regime/pattern histogram: `{coverage['pattern_counts']}`",
        f"- Reason classes: `{coverage['reason_classes']}`",
        "",
        "## Sample Plan",
        "",
        "```json",
        json.dumps(search["sample_plan"], indent=2, sort_keys=True),
        "```",
        "",
        "## Lean Projection Shape",
        "",
        "```json",
        json.dumps(report["lean_contract"], indent=2, sort_keys=True),
        "```",
        "",
        "The host checker computes, for each sampled child mask, the union of every",
        "predecessor quotient state's one-step child under the same exact-in step.",
        "That generated set must match the sampled child mask's quotient state set.",
        "",
        "## First Frontier Row",
        "",
        "```json",
        json.dumps(search["first_case"]["first_frontier"], indent=2, sort_keys=True),
        "```",
        "",
        "## Negative Controls",
        "",
        "| mutation | accepted | expected reason |",
        "| --- | ---: | --- |",
    ]
    for row in search["negative_controls"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | `{row['expected_reason']}` |")
    lines.extend(
        [
            "",
            "## Case Summary",
            "",
            "| case | ok | sampled child masks | child states | generated states | digest |",
            "| --- | --- | ---: | ---: | ---: | --- |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | "
            f"`{row['sampled_child_mask_count']}` | "
            f"`{row['sampled_child_state_count']}` | "
            f"`{row['generated_state_count']}` | "
            f"`{row['frontier_rows_digest']}` |"
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
