#!/usr/bin/env python3
"""Check bounded reserve-state transition projections for AB n=7 cases.

This research-only checker binds host transition rows to the Lean
`ReserveState.afterStep` surface.  It checks parent quotient states, selected
one-step children, and candidate one-step children for the committed strict
zero-min n=7 corpus without running the heavier suffix-permutation checker.
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
    _compressed_records,
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
    _quotient_rows,
    _reserve_state,
    _run_suffix_from_state,
    _short,
    _state_digest,
    _state_json,
)
from tools.check_ab_strict_zero_min_subset_induction_witness import (  # noqa: E402
    _clone_compressed_dp,
    _clone_full_dp,
)

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_transition_projection_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_TRANSITION_PROJECTION_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_reserve_state_transition_projection_packet.v1"
REPORT_SCHEMA = "zenodex.ab_reserve_state_transition_projection_report.v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_reserve_state_transition_projection"
TARGET_CASE_COUNT = 4
EXPECTED_NEGATIVE_CONTROL_COUNT = 7


def _lean_contract() -> dict[str, str]:
    return {
        "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
        "transition_def": "ReserveState.afterStep",
        "transition_invariant_endpoint": "reserveStateQuotientInvariant_afterStep",
        "transition_executability_endpoint": (
            "reserveStateQuotientInvariant_familySuffixExecutable"
        ),
        "host_projection": "bounded parent-mask one-step transition rows",
    }


def _without_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in packet.items() if key != "packet_hash"}


def _packet_hash(packet: Mapping[str, Any]) -> str:
    return _sha256_json(_without_packet_hash(packet))


def _with_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    out = dict(packet)
    out["packet_hash"] = _packet_hash(out)
    return out


def _state_set(records: Iterable[_HostRecord]) -> set[_ReserveState]:
    return {_reserve_state(record) for record in records}


def _sorted_states(states: Iterable[_ReserveState]) -> list[_ReserveState]:
    return sorted(
        states,
        key=lambda state: (int(state.processed_reserve_in), int(state.reserve_out)),
    )


def _transition_pairs(n: int) -> list[tuple[int, int]]:
    pairs: list[tuple[int, int]] = []
    for mask_id in range(1 << n):
        for step_bit_index in range(n):
            if mask_id & (1 << step_bit_index):
                continue
            pairs.append((mask_id, step_bit_index))
    return pairs


def _packet_rail_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["certificate_packet_missing"]
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
    if packet.get("transition_family_bound") is not True:
        reasons.append("transition_family_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _new_failure(
    first_failure: dict[str, Any] | None,
    *,
    case_id: str,
    mask_id: int,
    reason: str,
    **details: Any,
) -> dict[str, Any] | None:
    if first_failure is not None:
        return first_failure
    return {"case_id": case_id, "mask_id": int(mask_id), "reason": reason, **details}


def _candidate_child_rows(
    *,
    parent_states: set[_ReserveState],
    selected_child_state: _ReserveState | None,
    child_states: set[_ReserveState],
    intent: Any,
    context: Any,
) -> tuple[list[dict[str, Any]], dict[str, int], list[str]]:
    rows: list[dict[str, Any]] = []
    counters = {
        "candidate_transition_count": 0,
        "candidate_transition_executable_count": 0,
        "candidate_child_membership_count": 0,
        "candidate_processed_match_count": 0,
        "candidate_min_reserve_check_count": 0,
    }
    reasons: list[str] = []
    for state in _sorted_states(parent_states):
        counters["candidate_transition_count"] += 1
        candidate_child_state = _run_suffix_from_state(state, (intent,), context)
        row = {
            "parent_state_digest": _state_digest(state),
            "parent_state": _state_json(state),
            "candidate_child_state": (
                _state_json(candidate_child_state)
                if candidate_child_state is not None
                else None
            ),
            "candidate_child_state_digest": (
                _state_digest(candidate_child_state)
                if candidate_child_state is not None
                else None
            ),
            "candidate_child_in_child_family": False,
            "processed_reserve_in_matches_selected": False,
            "selected_child_min_reserve_out": False,
        }
        if candidate_child_state is None:
            reasons.append("candidate_transition_not_executable")
            rows.append(row)
            continue
        counters["candidate_transition_executable_count"] += 1
        if candidate_child_state in child_states:
            counters["candidate_child_membership_count"] += 1
            row["candidate_child_in_child_family"] = True
        else:
            reasons.append("candidate_transition_child_not_in_child_quotient")
        if selected_child_state is not None:
            if (
                int(selected_child_state.processed_reserve_in)
                == int(candidate_child_state.processed_reserve_in)
            ):
                counters["candidate_processed_match_count"] += 1
                row["processed_reserve_in_matches_selected"] = True
            else:
                reasons.append("transition_processed_reserve_in_mismatch")
            if int(selected_child_state.reserve_out) <= int(candidate_child_state.reserve_out):
                counters["candidate_min_reserve_check_count"] += 1
                row["selected_child_min_reserve_out"] = True
            else:
                reasons.append("transition_min_reserve_failure")
        rows.append(row)
    return rows, counters, reasons


def _transition_row(
    case: Any,
    *,
    mask_id: int,
    step_bit_index: int,
    full_dp: list[list[_HostRecord]],
    compressed_dp: list[_HostRecord | None],
) -> tuple[dict[str, Any], list[str]]:
    context = _case_context(case)
    intent = case.intents[step_bit_index]
    child_mask_id = mask_id | (1 << step_bit_index)
    parent_records = full_dp[mask_id]
    child_records = full_dp[child_mask_id]
    parent_states = _state_set(parent_records)
    child_states = _state_set(child_records)
    selected_record = compressed_dp[mask_id]
    reasons: list[str] = []
    selected_state = _reserve_state(selected_record) if selected_record is not None else None
    selected_child_state = (
        _run_suffix_from_state(selected_state, (intent,), context)
        if selected_state is not None
        else None
    )
    if selected_state is None:
        reasons.append("compressed_record_missing")
    elif selected_state not in parent_states:
        reasons.append("selected_state_not_in_parent_quotient")
    if selected_child_state is None:
        reasons.append("selected_transition_not_executable")
    elif selected_child_state not in child_states:
        reasons.append("selected_transition_child_not_in_child_quotient")

    candidate_rows, counters, candidate_reasons = _candidate_child_rows(
        parent_states=parent_states,
        selected_child_state=selected_child_state,
        child_states=child_states,
        intent=intent,
        context=context,
    )
    reasons.extend(candidate_reasons)
    row = {
        "case_id": case.case_id,
        "mask_id": int(mask_id),
        "child_mask_id": int(child_mask_id),
        "step_bit_index": int(step_bit_index),
        "step_order_id": intent.intent_id,
        "step_order_short": _short((intent.intent_id,)),
        "lean_transition_def": "ReserveState.afterStep",
        "lean_invariant_endpoint": "reserveStateQuotientInvariant_afterStep",
        "lean_executability_endpoint": (
            "reserveStateQuotientInvariant_familySuffixExecutable"
        ),
        "parent_selected_state": _state_json(selected_state) if selected_state else None,
        "parent_selected_state_digest": _state_digest(selected_state)
        if selected_state
        else None,
        "selected_child_state": (
            _state_json(selected_child_state) if selected_child_state else None
        ),
        "selected_child_state_digest": (
            _state_digest(selected_child_state) if selected_child_state else None
        ),
        "selected_child_in_child_family": bool(
            selected_child_state is not None and selected_child_state in child_states
        ),
        "parent_quotient_digest": _quotient_digest(parent_records),
        "child_quotient_digest": _quotient_digest(child_records),
        "parent_state_count": len(parent_states),
        "child_state_count": len(child_states),
        "candidate_child_digest": _sha256_json(candidate_rows),
        **counters,
    }
    return row, list(dict.fromkeys(reasons))


def _summary_keys() -> tuple[str, ...]:
    return (
        "mask_count",
        "transition_projection_count",
        "selected_transition_count",
        "selected_child_membership_count",
        "candidate_transition_count",
        "candidate_transition_executable_count",
        "candidate_child_membership_count",
        "candidate_processed_match_count",
        "candidate_min_reserve_check_count",
        "max_parent_state_count",
        "max_child_state_count",
        "transition_rows_digest",
    )


def _verify_case_arrays(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]],
    compressed_dp: list[_HostRecord | None],
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

    rows: list[dict[str, Any]] = []
    parent_masks: set[int] = set()
    selected_transition_count = 0
    selected_child_membership_count = 0
    candidate_transition_count = 0
    candidate_transition_executable_count = 0
    candidate_child_membership_count = 0
    candidate_processed_match_count = 0
    candidate_min_reserve_check_count = 0
    max_parent_state_count = 0
    max_child_state_count = 0

    for mask_id, step_bit_index in _transition_pairs(n):
        if not full_dp[mask_id]:
            continue
        if compressed_dp[mask_id] is None:
            reasons.append("compressed_record_missing")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=mask_id,
                reason="compressed_record_missing",
            )
            continue
        parent_masks.add(mask_id)
        row, row_reasons = _transition_row(
            case,
            mask_id=mask_id,
            step_bit_index=step_bit_index,
            full_dp=full_dp,
            compressed_dp=compressed_dp,
        )
        rows.append(row)
        selected_transition_count += int(row["selected_child_state"] is not None)
        selected_child_membership_count += int(row["selected_child_in_child_family"])
        candidate_transition_count += int(row["candidate_transition_count"])
        candidate_transition_executable_count += int(
            row["candidate_transition_executable_count"]
        )
        candidate_child_membership_count += int(row["candidate_child_membership_count"])
        candidate_processed_match_count += int(row["candidate_processed_match_count"])
        candidate_min_reserve_check_count += int(row["candidate_min_reserve_check_count"])
        max_parent_state_count = max(max_parent_state_count, int(row["parent_state_count"]))
        max_child_state_count = max(max_child_state_count, int(row["child_state_count"]))
        if row_reasons:
            reasons.extend(row_reasons)
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=mask_id,
                reason=row_reasons[0],
                child_mask_id=row["child_mask_id"],
                step_order_short=row["step_order_short"],
            )

    summary = {
        "mask_count": len(parent_masks),
        "transition_projection_count": len(rows),
        "selected_transition_count": selected_transition_count,
        "selected_child_membership_count": selected_child_membership_count,
        "candidate_transition_count": candidate_transition_count,
        "candidate_transition_executable_count": candidate_transition_executable_count,
        "candidate_child_membership_count": candidate_child_membership_count,
        "candidate_processed_match_count": candidate_processed_match_count,
        "candidate_min_reserve_check_count": candidate_min_reserve_check_count,
        "max_parent_state_count": max_parent_state_count,
        "max_child_state_count": max_child_state_count,
        "transition_rows_digest": _sha256_json(rows),
    }
    first_transition = rows[0] if rows else None

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("transition_summary") != summary:
            reasons.append("packet_transition_summary_mismatch")
        if packet.get("first_transition") != first_transition:
            reasons.append("packet_first_transition_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "case_id": case.case_id,
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "first_failure": first_failure,
        "bit_count": n,
        "fee_bps": int(case.pool.fee_bps),
        "pattern": case.pattern,
        "first_transition": first_transition,
        **summary,
    }


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
    compressed_dp: list[_HostRecord | None] | None = None,
) -> dict[str, Any]:
    context = _case_context(case)
    if full_dp is None:
        full_dp = _full_state_records(case.intents, context)
    if compressed_dp is None:
        compressed_dp = _compressed_records(case.intents, context)
    verification = _verify_case_arrays(
        case,
        full_dp=full_dp,
        compressed_dp=compressed_dp,
        packet=None,
    )
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "transition_family_bound": True,
        "reserve_state_only_bound": True,
        "lean_contract": _lean_contract(),
        "transition_summary": {key: verification[key] for key in _summary_keys()},
        "first_transition": verification["first_transition"],
    }
    return _with_packet_hash(packet)


def verify_case_packet(case: Any, packet: Mapping[str, Any]) -> dict[str, Any]:
    context = _case_context(case)
    return _verify_case_arrays(
        case,
        full_dp=_full_state_records(case.intents, context),
        compressed_dp=_compressed_records(case.intents, context),
        packet=packet,
    )


def verify_case(case: Any) -> dict[str, Any]:
    context = _case_context(case)
    full_dp = _full_state_records(case.intents, context)
    compressed_dp = _compressed_records(case.intents, context)
    packet = build_case_packet(case, full_dp=full_dp, compressed_dp=compressed_dp)
    verification = _verify_case_arrays(
        case,
        full_dp=full_dp,
        compressed_dp=compressed_dp,
        packet=packet,
    )
    return verification | {"packet_hash": packet["packet_hash"]}


def _find_multistate_mask(full_dp: list[list[_HostRecord]]) -> int:
    for mask_id, records in enumerate(full_dp):
        if len(_state_set(records)) > 1:
            return mask_id
    raise ValueError("no multi-state mask available")


def _find_candidate_child_gap(
    case: Any,
    full_dp: list[list[_HostRecord]],
    compressed_dp: list[_HostRecord | None],
) -> tuple[int, int, _ReserveState, _ReserveState]:
    context = _case_context(case)
    n = len(case.intents)
    for mask_id, step_bit_index in _transition_pairs(n):
        selected_record = compressed_dp[mask_id]
        if selected_record is None:
            continue
        selected_state = _reserve_state(selected_record)
        selected_child = _run_suffix_from_state(
            selected_state,
            (case.intents[step_bit_index],),
            context,
        )
        if selected_child is None:
            continue
        for state in _sorted_states(_state_set(full_dp[mask_id])):
            candidate_child = _run_suffix_from_state(
                state,
                (case.intents[step_bit_index],),
                context,
            )
            if candidate_child is not None and candidate_child != selected_child:
                return mask_id, step_bit_index, selected_child, candidate_child
    raise ValueError("no candidate child gap available")


def _negative_controls(cases: list[Any]) -> list[dict[str, Any]]:
    case = cases[0]
    context = _case_context(case)
    base_full = _full_state_records(case.intents, context)
    base_compressed = _compressed_records(case.intents, context)
    base_packet = build_case_packet(case, full_dp=base_full, compressed_dp=base_compressed)

    multi_case = cases[1]
    multi_context = _case_context(multi_case)
    multi_full = _full_state_records(multi_case.intents, multi_context)
    multi_compressed = _compressed_records(multi_case.intents, multi_context)

    controls: list[tuple[str, Any, list[list[_HostRecord]], list[_HostRecord | None], dict[str, Any] | None, str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(
        (
            "packet_hash_mismatch",
            case,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            bad_hash,
            "packet_hash_mismatch",
        )
    )

    bad_contract = copy.deepcopy(base_packet)
    bad_contract["lean_contract"]["transition_def"] = "ReserveState.staleAfterStep"
    controls.append(
        (
            "packet_lean_contract_mismatch",
            case,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _with_packet_hash(bad_contract),
            "packet_lean_contract_mismatch",
        )
    )

    bad_summary = copy.deepcopy(base_packet)
    bad_summary["transition_summary"]["transition_projection_count"] += 1
    controls.append(
        (
            "packet_transition_summary_mismatch",
            case,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _with_packet_hash(bad_summary),
            "packet_transition_summary_mismatch",
        )
    )

    bad_authority = copy.deepcopy(base_packet)
    bad_authority["no_authority_effect"] = False
    controls.append(
        (
            "authority_effect_present",
            case,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _with_packet_hash(bad_authority),
            "authority_effect_present",
        )
    )

    selected_missing_full = _clone_full_dp(base_full)
    selected_missing_full[1] = []
    controls.append(
        (
            "selected_transition_child_not_in_child_quotient",
            case,
            selected_missing_full,
            _clone_compressed_dp(base_compressed),
            None,
            "selected_transition_child_not_in_child_quotient",
        )
    )

    gap_mask, gap_step, selected_child, candidate_child = _find_candidate_child_gap(
        multi_case,
        multi_full,
        multi_compressed,
    )
    gap_child_mask = gap_mask | (1 << gap_step)
    candidate_missing_full = _clone_full_dp(multi_full)
    candidate_missing_full[gap_child_mask] = [
        record
        for record in candidate_missing_full[gap_child_mask]
        if _reserve_state(record) != candidate_child or _reserve_state(record) == selected_child
    ]
    controls.append(
        (
            "candidate_transition_child_not_in_child_quotient",
            multi_case,
            candidate_missing_full,
            _clone_compressed_dp(multi_compressed),
            None,
            "candidate_transition_child_not_in_child_quotient",
        )
    )

    multistate_mask = _find_multistate_mask(multi_full)
    selected_not_min = _clone_compressed_dp(multi_compressed)
    selected_not_min[multistate_mask] = max(
        multi_full[multistate_mask],
        key=lambda record: int(record.reserve_out),
    )
    controls.append(
        (
            "transition_min_reserve_failure",
            multi_case,
            _clone_full_dp(multi_full),
            selected_not_min,
            None,
            "transition_min_reserve_failure",
        )
    )

    output: list[dict[str, Any]] = []
    for mutation_id, target_case, full_dp, compressed_dp, packet, expected_reason in controls:
        verification = _verify_case_arrays(
            target_case,
            full_dp=full_dp,
            compressed_dp=compressed_dp,
            packet=packet,
        )
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
    transition_projection_count = sum(
        int(row["transition_projection_count"]) for row in rows
    )
    candidate_transition_count = sum(int(row["candidate_transition_count"]) for row in rows)
    return {
        "schema": "zenodex/ab_reserve_state_transition_projection_search/v1",
        "source_seed": N7_SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "mask_count": sum(int(row["mask_count"]) for row in rows),
        "transition_projection_count": transition_projection_count,
        "selected_transition_count": sum(
            int(row["selected_transition_count"]) for row in rows
        ),
        "selected_child_membership_count": sum(
            int(row["selected_child_membership_count"]) for row in rows
        ),
        "candidate_transition_count": candidate_transition_count,
        "candidate_transition_executable_count": sum(
            int(row["candidate_transition_executable_count"]) for row in rows
        ),
        "candidate_child_membership_count": sum(
            int(row["candidate_child_membership_count"]) for row in rows
        ),
        "candidate_processed_match_count": sum(
            int(row["candidate_processed_match_count"]) for row in rows
        ),
        "candidate_min_reserve_check_count": sum(
            int(row["candidate_min_reserve_check_count"]) for row in rows
        ),
        "transition_rows_digest": _sha256_json(
            [row["transition_rows_digest"] for row in rows]
        ),
        "max_parent_state_count": max(
            (int(row["max_parent_state_count"]) for row in rows),
            default=0,
        ),
        "max_child_state_count": max(
            (int(row["max_child_state_count"]) for row in rows),
            default=0,
        ),
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
        and search["transition_projection_count"] == search["selected_transition_count"]
        and search["selected_transition_count"] == search["selected_child_membership_count"]
        and search["candidate_transition_count"] == search["candidate_transition_executable_count"]
        and search["candidate_transition_count"] == search["candidate_child_membership_count"]
        and search["candidate_transition_count"] == search["candidate_processed_match_count"]
        and search["candidate_transition_count"] == search["candidate_min_reserve_check_count"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded host checker supports the reserve-state quotient transition "
            "projection for the committed n=7 strict zero-min corpus by replaying "
            "one-step parent-to-child rows against the Lean ReserveState.afterStep surface."
        ),
        "authority_boundary": (
            "Research-only certificate-compression evidence; no settlement, state-root, "
            "production, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_reserve_state_transition_projection_20260629.py"
        ),
        "non_claims": [
            "This transition checker is bounded to the committed n=7 randomized corpus.",
            "This checker samples no nonzero min_amount_out certificates.",
            "This checker does not prove Python-to-Lean refinement.",
            "This checker does not prove full child-frontier generation in Lean.",
            "This checker does not define canonical tie order or preserve order-id history.",
            "No settlement, state-root, production, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Reserve-State Transition Projection - 2026-06-29",
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
        f"- Reachable masks checked: `{search['mask_count']}`",
        f"- Transition rows checked: `{search['transition_projection_count']}`",
        f"- Selected child memberships: `{search['selected_child_membership_count']}`",
        f"- Candidate transitions checked: `{search['candidate_transition_count']}`",
        f"- Candidate child memberships: `{search['candidate_child_membership_count']}`",
        f"- Candidate processed-reserve matches: `{search['candidate_processed_match_count']}`",
        f"- Candidate min-reserve checks: `{search['candidate_min_reserve_check_count']}`",
        f"- Max parent states per row: `{search['max_parent_state_count']}`",
        f"- Max child states per row: `{search['max_child_state_count']}`",
        f"- Transition digest: `{search['transition_rows_digest']}`",
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
        "## Lean Projection Shape",
        "",
        "```json",
        json.dumps(report["lean_contract"], indent=2, sort_keys=True),
        "```",
        "",
        "Each transition row binds a parent mask, child mask, step bit, selected",
        "parent state, selected child state, parent quotient digest, child quotient",
        "digest, and candidate-child digest. The row checks that every reachable",
        "candidate child remains in the child quotient family and that the selected",
        "child has no greater reserve-out than those candidates.",
        "",
        "## First Transition",
        "",
        "```json",
        json.dumps(search["first_case"]["first_transition"], indent=2, sort_keys=True),
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
            "| case | ok | transitions | candidate transitions | digest |",
            "| --- | --- | ---: | ---: | --- |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | "
            f"`{row['transition_projection_count']}` | "
            f"`{row['candidate_transition_count']}` | "
            f"`{row['transition_rows_digest']}` |"
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
