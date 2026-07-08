#!/usr/bin/env python3
"""Check compressed predecessor witnesses for AB reserve-state child frontiers.

This research-only checker turns child-frontier equality into a smaller
proof-object shape: one predecessor witness per child quotient state.
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
    _lean_contract as _frontier_lean_contract,
    _state_rows,
    _state_set_digest,
)
from tools.check_ab_reserve_state_transition_projection_20260629 import (  # noqa: E402
    _new_failure,
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
    N7_SEED,
    _ReserveState,
    _case_context,
    _first_n7_positive_cases,
    _quotient_digest,
    _run_suffix_from_state,
    _state_json,
)
from tools.check_ab_strict_zero_min_subset_induction_witness import _clone_full_dp  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_witness_compression_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_WITNESS_COMPRESSION_20260629.md"
)
FRONTIER_REPORT_JSON = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_generation_20260629"
    / "report.json"
)

PACKET_SCHEMA = "zenodex.ab_reserve_state_child_frontier_witness_packet.v1"
REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_witness_compression_report.v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_child_frontier_predecessor_witnesses"
TARGET_CASE_COUNT = 4
EXPECTED_NEGATIVE_CONTROL_COUNT = 8


def _lean_contract() -> dict[str, str]:
    base = _frontier_lean_contract()
    return {
        **base,
        "host_witness_shape": (
            "one predecessor ReserveState.afterStep witness per child quotient state"
        ),
    }


def _state_from_json(row: Mapping[str, Any]) -> _ReserveState:
    return _ReserveState(
        int(row["processed_reserve_in"]),
        int(row["reserve_out"]),
    )


def _witness_rows_digest(rows: Iterable[Mapping[str, Any]]) -> str:
    return _sha256_json(list(rows))


def _linked_frontier_summary() -> dict[str, Any]:
    if not FRONTIER_REPORT_JSON.exists():
        return {
            "path": str(FRONTIER_REPORT_JSON.relative_to(REPO_ROOT)),
            "available": False,
        }
    report = json.loads(FRONTIER_REPORT_JSON.read_text(encoding="utf-8"))
    search = report.get("search", {})
    return {
        "path": str(FRONTIER_REPORT_JSON.relative_to(REPO_ROOT)),
        "available": True,
        "ok": bool(report.get("ok")),
        "schema": report.get("schema"),
        "frontier_rows_digest": search.get("frontier_rows_digest"),
        "child_mask_count": int(search.get("child_mask_count", -1)),
        "child_state_count": int(search.get("child_state_count", -1)),
        "generated_state_count": int(search.get("generated_state_count", -1)),
        "missing_child_state_count": int(search.get("missing_child_state_count", -1)),
        "extra_generated_state_count": int(search.get("extra_generated_state_count", -1)),
    }


def _linked_frontier_reasons(summary: Mapping[str, Any] | None) -> list[str]:
    if summary is None:
        return ["linked_frontier_summary_missing"]
    reasons: list[str] = []
    if summary.get("available") is not True:
        reasons.append("linked_frontier_report_missing")
    if summary.get("ok") is not True:
        reasons.append("linked_frontier_report_not_ok")
    if int(summary.get("missing_child_state_count", -1)) != 0:
        reasons.append("linked_frontier_missing_child_state")
    if int(summary.get("extra_generated_state_count", -1)) != 0:
        reasons.append("linked_frontier_extra_generated_state")
    if int(summary.get("child_state_count", -1)) != int(summary.get("generated_state_count", -2)):
        reasons.append("linked_frontier_state_count_mismatch")
    return reasons


def _packet_rail_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["witness_packet_missing"]
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
    if packet.get("predecessor_witness_bound") is not True:
        reasons.append("predecessor_witness_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("linked_frontier_summary") != _linked_frontier_summary():
        reasons.append("linked_frontier_summary_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _find_predecessor_witness(
    case: Any,
    *,
    child_mask_id: int,
    child_state: _ReserveState,
    full_dp: list[list[_HostRecord]],
) -> dict[str, Any] | None:
    context = _case_context(case)
    for step_bit_index, intent in enumerate(case.intents):
        if not (child_mask_id & (1 << step_bit_index)):
            continue
        parent_mask_id = child_mask_id ^ (1 << step_bit_index)
        parent_states = _state_set(full_dp[parent_mask_id])
        for parent_state in _sorted_states(parent_states):
            generated_child = _run_suffix_from_state(parent_state, (intent,), context)
            if generated_child == child_state:
                return {
                    "case_id": case.case_id,
                    "child_mask_id": int(child_mask_id),
                    "child_state": _state_json(child_state),
                    "parent_mask_id": int(parent_mask_id),
                    "step_bit_index": int(step_bit_index),
                    "step_order_id": intent.intent_id,
                    "step_order_short": _short((intent.intent_id,)),
                    "parent_state": _state_json(parent_state),
                    "parent_quotient_digest": _quotient_digest(full_dp[parent_mask_id]),
                    "child_quotient_digest": _quotient_digest(full_dp[child_mask_id]),
                }
    return None


def _build_witness_rows(case: Any, *, full_dp: list[list[_HostRecord]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    n = len(case.intents)
    for child_mask_id in range(1, 1 << n):
        child_states = _state_set(full_dp[child_mask_id])
        for child_state in _sorted_states(child_states):
            witness = _find_predecessor_witness(
                case,
                child_mask_id=child_mask_id,
                child_state=child_state,
                full_dp=full_dp,
            )
            if witness is not None:
                rows.append(witness)
    return rows


def _packet_summary_from_rows(rows: list[Mapping[str, Any]]) -> dict[str, Any]:
    child_masks = {int(row["child_mask_id"]) for row in rows}
    child_state_keys = {
        (int(row["child_mask_id"]), tuple(sorted(dict(row["child_state"]).items())))
        for row in rows
    }
    duplicate_count = len(rows) - len(child_state_keys)
    return {
        "child_mask_count": len(child_masks),
        "witness_count": len(rows),
        "unique_child_witness_count": len(child_state_keys),
        "duplicate_witness_count": duplicate_count,
        "witness_rows_digest": _witness_rows_digest(rows),
    }


def _verify_witness_rows(
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
    if not _case_has_zero_min_amount_out(case):
        reasons.append("nonzero_min_amount_out_out_of_scope")
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=0,
            reason="nonzero_min_amount_out_out_of_scope",
        )

    child_frontier: dict[int, set[_ReserveState]] = {
        child_mask_id: _state_set(full_dp[child_mask_id])
        for child_mask_id in range(1, 1 << n)
    }
    expected_child_keys = {
        (child_mask_id, state)
        for child_mask_id, states in child_frontier.items()
        for state in states
    }
    rows = list(packet.get("witness_rows", []) if packet is not None else [])
    seen_child_keys: set[tuple[int, _ReserveState]] = set()
    duplicate_witness_count = 0
    invalid_witness_count = 0

    for index, row in enumerate(rows):
        row_reasons: list[str] = []
        try:
            child_mask_id = int(row["child_mask_id"])
            parent_mask_id = int(row["parent_mask_id"])
            step_bit_index = int(row["step_bit_index"])
            parent_state = _state_from_json(row["parent_state"])
            child_state = _state_from_json(row["child_state"])
        except (KeyError, TypeError, ValueError):
            row_reasons.append("witness_row_malformed")
            child_mask_id = -1
            parent_mask_id = -1
            step_bit_index = -1
            parent_state = _ReserveState(-1, -1)
            child_state = _ReserveState(-1, -1)

        if row.get("case_id") != case.case_id:
            row_reasons.append("witness_case_id_mismatch")
        if child_mask_id <= 0 or child_mask_id >= (1 << n):
            row_reasons.append("witness_child_mask_out_of_range")
        if step_bit_index < 0 or step_bit_index >= n:
            row_reasons.append("witness_step_bit_out_of_range")
        elif not (child_mask_id & (1 << step_bit_index)):
            row_reasons.append("witness_step_not_in_child_mask")
        elif parent_mask_id != (child_mask_id ^ (1 << step_bit_index)):
            row_reasons.append("witness_parent_mask_mismatch")

        if 0 <= parent_mask_id < (1 << n):
            parent_states = _state_set(full_dp[parent_mask_id])
            if parent_state not in parent_states:
                row_reasons.append("witness_parent_state_not_in_parent_frontier")
            expected_parent_digest = _quotient_digest(full_dp[parent_mask_id])
            if row.get("parent_quotient_digest") != expected_parent_digest:
                row_reasons.append("witness_parent_quotient_digest_mismatch")
        else:
            row_reasons.append("witness_parent_mask_out_of_range")

        if 0 < child_mask_id < (1 << n):
            child_states = child_frontier[child_mask_id]
            if child_state not in child_states:
                row_reasons.append("witness_child_state_not_in_child_frontier")
            expected_child_digest = _quotient_digest(full_dp[child_mask_id])
            if row.get("child_quotient_digest") != expected_child_digest:
                row_reasons.append("witness_child_quotient_digest_mismatch")
        elif "witness_child_mask_out_of_range" not in row_reasons:
            row_reasons.append("witness_child_mask_out_of_range")

        if 0 <= step_bit_index < n:
            intent = case.intents[step_bit_index]
            if row.get("step_order_id") != intent.intent_id:
                row_reasons.append("witness_step_order_id_mismatch")
            generated_child = _run_suffix_from_state(
                parent_state,
                (intent,),
                _case_context(case),
            )
            if generated_child != child_state:
                row_reasons.append("witness_afterstep_mismatch")

        child_key = (child_mask_id, child_state)
        if child_key in seen_child_keys:
            duplicate_witness_count += 1
            row_reasons.append("duplicate_witness_row")
        seen_child_keys.add(child_key)

        if row_reasons:
            invalid_witness_count += 1
            reasons.extend(row_reasons)
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=child_mask_id,
                reason=row_reasons[0],
                detail={"row_index": index},
            )

    missing_child_keys = expected_child_keys - seen_child_keys
    extra_child_keys = seen_child_keys - expected_child_keys
    if missing_child_keys:
        reasons.append("missing_child_state_witness")
        child_mask_id, _ = sorted(
            missing_child_keys,
            key=lambda item: (
                item[0],
                item[1].processed_reserve_in,
                item[1].reserve_out,
            ),
        )[0]
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=child_mask_id,
            reason="missing_child_state_witness",
        )
    if extra_child_keys:
        reasons.append("extra_child_state_witness")
    if duplicate_witness_count:
        reasons.append("duplicate_witness_row")

    linked_reasons = _linked_frontier_reasons(
        packet.get("linked_frontier_summary") if packet is not None else None
    )
    reasons.extend(linked_reasons)

    summary = _packet_summary_from_rows(rows)
    summary.update(
        {
            "expected_child_state_count": len(expected_child_keys),
            "covered_child_state_count": len(seen_child_keys & expected_child_keys),
            "missing_child_state_witness_count": len(missing_child_keys),
            "extra_child_state_witness_count": len(extra_child_keys),
            "invalid_witness_count": invalid_witness_count,
            "frontier_witness_compression_ratio": round(
                int(packet.get("predecessor_transition_count", 0)) / max(len(rows), 1),
                6,
            )
            if packet is not None
            else 0,
        }
    )

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("witness_summary") != summary:
            reasons.append("packet_witness_summary_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "case_id": case.case_id,
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "first_failure": first_failure,
        "bit_count": n,
        "fee_bps": int(case.pool.fee_bps),
        "pattern": case.pattern,
        **summary,
    }


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
) -> dict[str, Any]:
    if full_dp is None:
        full_dp = _full_state_records(case.intents, _case_context(case))
    witness_rows = _build_witness_rows(case, full_dp=full_dp)
    predecessor_transition_count = 0
    n = len(case.intents)
    for child_mask_id in range(1, 1 << n):
        for step_bit_index, _intent in enumerate(case.intents):
            if child_mask_id & (1 << step_bit_index):
                parent_mask_id = child_mask_id ^ (1 << step_bit_index)
                predecessor_transition_count += len(_state_set(full_dp[parent_mask_id]))
    summary = _packet_summary_from_rows(witness_rows)
    summary.update(
        {
            "expected_child_state_count": summary["witness_count"],
            "covered_child_state_count": summary["witness_count"],
            "missing_child_state_witness_count": 0,
            "extra_child_state_witness_count": 0,
            "invalid_witness_count": 0,
            "frontier_witness_compression_ratio": round(
                predecessor_transition_count / max(summary["witness_count"], 1),
                6,
            ),
        }
    )
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "predecessor_witness_bound": True,
        "reserve_state_only_bound": True,
        "lean_contract": _lean_contract(),
        "linked_frontier_summary": _linked_frontier_summary(),
        "predecessor_transition_count": predecessor_transition_count,
        "witness_rows": witness_rows,
        "witness_summary": summary,
    }
    return _with_packet_hash(packet)


def verify_case(case: Any) -> dict[str, Any]:
    full_dp = _full_state_records(case.intents, _case_context(case))
    packet = build_case_packet(case, full_dp=full_dp)
    verification = _verify_witness_rows(case, full_dp=full_dp, packet=packet)
    return verification | {
        "packet_hash": packet["packet_hash"],
        "predecessor_transition_count": int(packet["predecessor_transition_count"]),
    }


def _negative_controls(cases: list[Any]) -> list[dict[str, Any]]:
    case = cases[0]
    full_dp = _full_state_records(case.intents, _case_context(case))
    base_packet = build_case_packet(case, full_dp=full_dp)

    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    missing_witness = copy.deepcopy(base_packet)
    missing_witness["witness_rows"] = missing_witness["witness_rows"][1:]
    missing_witness["witness_summary"] = _packet_summary_from_rows(
        missing_witness["witness_rows"]
    )
    controls.append(
        (
            "missing_child_state_witness",
            _with_packet_hash(missing_witness),
            "missing_child_state_witness",
        )
    )

    bad_parent = copy.deepcopy(base_packet)
    bad_parent["witness_rows"][0]["parent_state"]["reserve_out"] += 1
    bad_parent["witness_summary"] = _packet_summary_from_rows(bad_parent["witness_rows"])
    controls.append(
        (
            "witness_parent_state_not_in_parent_frontier",
            _with_packet_hash(bad_parent),
            "witness_parent_state_not_in_parent_frontier",
        )
    )

    bad_child = copy.deepcopy(base_packet)
    bad_child["witness_rows"][0]["child_state"]["reserve_out"] += 1
    bad_child["witness_summary"] = _packet_summary_from_rows(bad_child["witness_rows"])
    controls.append(
        (
            "witness_child_state_not_in_child_frontier",
            _with_packet_hash(bad_child),
            "witness_child_state_not_in_child_frontier",
        )
    )

    bad_step = copy.deepcopy(base_packet)
    bad_step["witness_rows"][0]["step_bit_index"] = len(case.intents)
    bad_step["witness_summary"] = _packet_summary_from_rows(bad_step["witness_rows"])
    controls.append(
        (
            "witness_step_bit_out_of_range",
            _with_packet_hash(bad_step),
            "witness_step_bit_out_of_range",
        )
    )

    duplicate = copy.deepcopy(base_packet)
    duplicate["witness_rows"].append(copy.deepcopy(duplicate["witness_rows"][0]))
    duplicate["witness_summary"] = _packet_summary_from_rows(duplicate["witness_rows"])
    controls.append(
        (
            "duplicate_witness_row",
            _with_packet_hash(duplicate),
            "duplicate_witness_row",
        )
    )

    bad_link = copy.deepcopy(base_packet)
    bad_link["linked_frontier_summary"]["extra_generated_state_count"] = 1
    controls.append(
        (
            "linked_frontier_extra_generated_state",
            _with_packet_hash(bad_link),
            "linked_frontier_extra_generated_state",
        )
    )

    bad_authority = copy.deepcopy(base_packet)
    bad_authority["no_authority_effect"] = False
    controls.append(
        (
            "authority_effect_present",
            _with_packet_hash(bad_authority),
            "authority_effect_present",
        )
    )

    output: list[dict[str, Any]] = []
    for mutation_id, packet, expected_reason in controls:
        verification = _verify_witness_rows(case, full_dp=_clone_full_dp(full_dp), packet=packet)
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
    cases = _first_n7_positive_cases()
    rows = [verify_case(case) for case in cases]
    invalid_rows = [row for row in rows if not row["ok"]]
    negative_controls = _negative_controls(cases)
    witness_count = sum(int(row["witness_count"]) for row in rows)
    predecessor_transition_count = sum(
        int(row["predecessor_transition_count"]) for row in rows
    )
    return {
        "schema": "zenodex/ab_reserve_state_child_frontier_witness_compression_search/v1",
        "source_seed": N7_SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "child_mask_count": sum(int(row["child_mask_count"]) for row in rows),
        "expected_child_state_count": sum(
            int(row["expected_child_state_count"]) for row in rows
        ),
        "witness_count": witness_count,
        "covered_child_state_count": sum(
            int(row["covered_child_state_count"]) for row in rows
        ),
        "missing_child_state_witness_count": sum(
            int(row["missing_child_state_witness_count"]) for row in rows
        ),
        "extra_child_state_witness_count": sum(
            int(row["extra_child_state_witness_count"]) for row in rows
        ),
        "invalid_witness_count": sum(int(row["invalid_witness_count"]) for row in rows),
        "duplicate_witness_count": sum(
            int(row["duplicate_witness_count"]) for row in rows
        ),
        "predecessor_transition_count": predecessor_transition_count,
        "witness_compression_ratio": round(
            predecessor_transition_count / max(witness_count, 1),
            6,
        ),
        "witness_transition_checks_saved": predecessor_transition_count - witness_count,
        "witness_rows_digest": _sha256_json([row["witness_rows_digest"] for row in rows]),
        "linked_frontier_summary": _linked_frontier_summary(),
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
        and search["expected_child_state_count"] == search["witness_count"]
        and search["expected_child_state_count"] == search["covered_child_state_count"]
        and search["missing_child_state_witness_count"] == 0
        and search["extra_child_state_witness_count"] == 0
        and search["invalid_witness_count"] == 0
        and search["duplicate_witness_count"] == 0
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and not _linked_frontier_reasons(search["linked_frontier_summary"])
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded host checker supports a compressed child-frontier proof object "
            "for the n=7 strict zero-min reserve-state quotient: one predecessor "
            "witness covers each child quotient state."
        ),
        "authority_boundary": (
            "Research-only certificate-compression evidence; no settlement, state-root, "
            "production, routing, matching, pool-mutation, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_witness_compression_20260629.py"
        ),
        "non_claims": [
            "This witness checker is bounded to the committed n=7 randomized corpus.",
            "This checker covers only zero-min exact-in cases in the scoped corpus.",
            "This checker does not prove Python-to-Lean refinement.",
            "This checker does not prove child-frontier generation in Lean.",
            "The no-extra generated-state fact is linked to the existing child-frontier equality report, not reproved by the one-witness object alone.",
            "This checker does not define canonical tie order or preserve order-id history.",
            "This checker does not cover nonzero min_amount_out behavior.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Reserve-State Child-Frontier Witness Compression - 2026-06-29",
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
        f"- Valid cases: `{search['valid_case_count']}`",
        f"- Child masks checked: `{search['child_mask_count']}`",
        f"- Expected child states: `{search['expected_child_state_count']}`",
        f"- Witness rows: `{search['witness_count']}`",
        f"- Covered child states: `{search['covered_child_state_count']}`",
        f"- Missing witness count: `{search['missing_child_state_witness_count']}`",
        f"- Extra witness count: `{search['extra_child_state_witness_count']}`",
        f"- Invalid witness count: `{search['invalid_witness_count']}`",
        f"- Duplicate witness count: `{search['duplicate_witness_count']}`",
        f"- Baseline predecessor transitions: `{search['predecessor_transition_count']}`",
        f"- Witness compression ratio: `{search['witness_compression_ratio']}`",
        f"- Transition checks saved: `{search['witness_transition_checks_saved']}`",
        f"- Witness digest: `{search['witness_rows_digest']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Linked Frontier Equality Report",
        "",
        "```json",
        json.dumps(search["linked_frontier_summary"], indent=2, sort_keys=True),
        "```",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Fee histogram: `{coverage['fee_bps_counts']}`",
        f"- Regime/pattern histogram: `{coverage['pattern_counts']}`",
        f"- Reason classes: `{coverage['reason_classes']}`",
        "",
        "## First Case",
        "",
        "```json",
        json.dumps(search["first_case"], indent=2, sort_keys=True),
        "```",
        "",
        "## Negative Controls",
        "",
        "| mutation | accepted | expected reason |",
        "| --- | ---: | --- |",
    ]
    for control in search["negative_controls"]:
        lines.append(
            f"| `{control['mutation_id']}` | `{control['accepted']}` | `{control['expected_reason']}` |"
        )
    lines.extend(["", "## Case Summary", ""])
    lines.extend(
        [
            "| case | ok | witnesses | predecessor transitions | ratio | digest |",
            "| --- | --- | ---: | ---: | ---: | --- |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            "| "
            f"`{row['case_id']}` | `{row['ok']}` | `{row['witness_count']}` | "
            f"`{row['predecessor_transition_count']}` | `{row['frontier_witness_compression_ratio']}` | "
            f"`{row['witness_rows_digest']}` |"
        )
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```"])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="print full report")
    args = parser.parse_args()
    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
