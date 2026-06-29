#!/usr/bin/env python3
"""Check bidirectional transition closure for AB reserve-state child frontiers.

This research-only checker strengthens the child-frontier proof-object chain by
binding both directions of the frontier equality:

- child -> predecessor is linked from the existing witness+Merkle report;
- predecessor afterStep -> child is checked here with one transition row per
  executable predecessor transition and a canonical child-frontier membership
  proof for the generated child state.
"""

from __future__ import annotations

import argparse
import copy
import functools
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools import check_ab_reserve_state_child_frontier_canonical_merkle_20260629 as merkle  # noqa: E402
from tools import check_ab_reserve_state_child_frontier_witness_merkle_20260629 as witness_merkle  # noqa: E402
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
    / "zenodex_ab_reserve_state_child_frontier_bidirectional_transition_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_BIDIRECTIONAL_TRANSITION_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_reserve_state_child_frontier_bidirectional_transition_packet.v1"
REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_bidirectional_transition_report.v1"
SEARCH_SCHEMA = "zenodex/ab_reserve_state_child_frontier_bidirectional_transition_search/v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_child_frontier_bidirectional_transition"
TARGET_CASE_COUNT = 4
EXPECTED_NEGATIVE_CONTROL_COUNT = 9


def _state_from_json(row: Mapping[str, Any]) -> _ReserveState:
    return _ReserveState(
        int(row["processed_reserve_in"]),
        int(row["reserve_out"]),
    )


def _state_key(state: _ReserveState) -> tuple[int, int]:
    return int(state.processed_reserve_in), int(state.reserve_out)


def _state_key_from_json(row: Mapping[str, Any]) -> tuple[int, int]:
    return int(row["processed_reserve_in"]), int(row["reserve_out"])


def _transition_key_from_parts(
    *,
    child_mask_id: int,
    parent_mask_id: int,
    step_bit_index: int,
    parent_state: _ReserveState,
    generated_child_state: _ReserveState,
) -> tuple[int, int, int, tuple[int, int], tuple[int, int]]:
    return (
        int(child_mask_id),
        int(parent_mask_id),
        int(step_bit_index),
        _state_key(parent_state),
        _state_key(generated_child_state),
    )


def _transition_key(row: Mapping[str, Any]) -> tuple[int, int, int, tuple[int, int], tuple[int, int]]:
    return _transition_key_from_parts(
        child_mask_id=int(row["child_mask_id"]),
        parent_mask_id=int(row["parent_mask_id"]),
        step_bit_index=int(row["step_bit_index"]),
        parent_state=_state_from_json(row["parent_state"]),
        generated_child_state=_state_from_json(row["generated_child_state"]),
    )


@functools.lru_cache(maxsize=1)
def _linked_witness_merkle_summary() -> dict[str, Any]:
    path = witness_merkle.REPORT_JSON
    if path.exists():
        report = json.loads(path.read_text(encoding="utf-8"))
    else:
        report = witness_merkle.build_report()
    search = report.get("search", {})
    return {
        "kind": "witness_merkle",
        "path": str(path.relative_to(REPO_ROOT)),
        "available": True,
        "ok": bool(report.get("ok")),
        "schema": report.get("schema"),
        "case_count": int(search.get("case_count", -1)),
        "valid_case_count": int(search.get("valid_case_count", -1)),
        "child_mask_count": int(search.get("child_mask_count", -1)),
        "bound_row_count": int(search.get("bound_row_count", -1)),
        "witness_count": int(search.get("witness_count", -1)),
        "membership_count": int(search.get("membership_count", -1)),
        "negative_control_accept_count": int(
            search.get("negative_control_accept_count", -1)
        ),
        "bound_rows_digest": search.get("bound_rows_digest"),
    }


def _linked_witness_merkle_reasons(summary: Mapping[str, Any] | None) -> list[str]:
    if summary is None:
        return ["linked_witness_merkle_summary_missing"]
    reasons: list[str] = []
    if summary.get("available") is not True:
        reasons.append("linked_witness_merkle_report_missing")
    if summary.get("ok") is not True:
        reasons.append("linked_witness_merkle_report_not_ok")
    if int(summary.get("case_count", -1)) != TARGET_CASE_COUNT:
        reasons.append("linked_witness_merkle_case_count_mismatch")
    if int(summary.get("valid_case_count", -1)) != TARGET_CASE_COUNT:
        reasons.append("linked_witness_merkle_valid_case_count_mismatch")
    if int(summary.get("child_mask_count", -1)) != 508:
        reasons.append("linked_witness_merkle_child_mask_count_mismatch")
    if int(summary.get("bound_row_count", -1)) != 864:
        reasons.append("linked_witness_merkle_bound_row_count_mismatch")
    if int(summary.get("witness_count", -1)) != 864:
        reasons.append("linked_witness_merkle_witness_count_mismatch")
    if int(summary.get("membership_count", -1)) != 864:
        reasons.append("linked_witness_merkle_membership_count_mismatch")
    if int(summary.get("negative_control_accept_count", -1)) != 0:
        reasons.append("linked_witness_merkle_negative_control_accepts")
    return reasons


def _lean_contract() -> dict[str, str]:
    return {
        **witness_merkle._lean_contract(),
        "host_bidirectional_shape": (
            "child coverage is linked from witness+Merkle rows; every predecessor "
            "afterStep image carries canonical child-frontier membership here"
        ),
    }


def _packet_rail_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["bidirectional_transition_packet_missing"]
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
    if packet.get("linked_child_coverage_bound") is not True:
        reasons.append("linked_child_coverage_bound_missing")
    if packet.get("forward_transition_membership_bound") is not True:
        reasons.append("forward_transition_membership_bound_missing")
    if packet.get("bidirectional_frontier_bound") is not True:
        reasons.append("bidirectional_frontier_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("linked_witness_merkle_summary") != _linked_witness_merkle_summary():
        reasons.append("linked_witness_merkle_summary_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _frontier_rows_by_mask(
    full_dp: list[list[_HostRecord]],
) -> dict[int, Mapping[str, Any]]:
    return {
        int(row["child_mask_id"]): row
        for row in merkle._frontier_rows_for_case(full_dp=full_dp)
    }


def _membership_by_key(
    frontier_rows: Mapping[int, Mapping[str, Any]],
) -> dict[tuple[int, tuple[int, int]], Mapping[str, Any]]:
    memberships: dict[tuple[int, tuple[int, int]], Mapping[str, Any]] = {}
    for mask_id, row in frontier_rows.items():
        for member in row["membership_rows"]:
            memberships[(mask_id, _state_key_from_json(member["child_state"]))] = {
                **member,
                "generated_state_count": int(row["generated_state_count"]),
                "generated_state_root": row["generated_state_root"],
            }
    return memberships


def _expected_transition_keys(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]],
) -> set[tuple[int, int, int, tuple[int, int], tuple[int, int]]]:
    context = _case_context(case)
    keys: set[tuple[int, int, int, tuple[int, int], tuple[int, int]]] = set()
    for child_mask_id in range(1, 1 << len(case.intents)):
        for step_bit_index, intent in enumerate(case.intents):
            if not (child_mask_id & (1 << step_bit_index)):
                continue
            parent_mask_id = child_mask_id ^ (1 << step_bit_index)
            for parent_state in _sorted_states(_state_set(full_dp[parent_mask_id])):
                child_state = _run_suffix_from_state(parent_state, (intent,), context)
                if child_state is not None:
                    keys.add(
                        _transition_key_from_parts(
                            child_mask_id=child_mask_id,
                            parent_mask_id=parent_mask_id,
                            step_bit_index=step_bit_index,
                            parent_state=parent_state,
                            generated_child_state=child_state,
                        )
                    )
    return keys


def _build_transition_rows(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]],
) -> list[dict[str, Any]]:
    context = _case_context(case)
    memberships = _membership_by_key(_frontier_rows_by_mask(full_dp))
    rows: list[dict[str, Any]] = []
    for child_mask_id in range(1, 1 << len(case.intents)):
        for step_bit_index, intent in enumerate(case.intents):
            if not (child_mask_id & (1 << step_bit_index)):
                continue
            parent_mask_id = child_mask_id ^ (1 << step_bit_index)
            parent_states = _state_set(full_dp[parent_mask_id])
            for parent_state in _sorted_states(parent_states):
                generated_child_state = _run_suffix_from_state(parent_state, (intent,), context)
                if generated_child_state is None:
                    continue
                member = memberships[(child_mask_id, _state_key(generated_child_state))]
                rows.append(
                    {
                        "case_id": case.case_id,
                        "child_mask_id": int(child_mask_id),
                        "parent_mask_id": int(parent_mask_id),
                        "step_bit_index": int(step_bit_index),
                        "step_order_id": intent.intent_id,
                        "step_order_short": _short((intent.intent_id,)),
                        "parent_state": _state_json(parent_state),
                        "generated_child_state": _state_json(generated_child_state),
                        "parent_quotient_digest": _quotient_digest(full_dp[parent_mask_id]),
                        "child_quotient_digest": _quotient_digest(full_dp[child_mask_id]),
                        "generated_state_count": int(member["generated_state_count"]),
                        "generated_state_root": member["generated_state_root"],
                        "leaf_index": int(member["leaf_index"]),
                        "membership_proof": list(member["proof"]),
                    }
                )
    return rows


def _packet_summary_from_rows(rows: list[Mapping[str, Any]]) -> dict[str, Any]:
    transition_keys = {_transition_key(row) for row in rows}
    child_masks = {int(row["child_mask_id"]) for row in rows}
    child_state_keys = {
        (int(row["child_mask_id"]), _state_key_from_json(row["generated_child_state"]))
        for row in rows
    }
    duplicate_count = len(rows) - len(transition_keys)
    return {
        "child_mask_count": len(child_masks),
        "transition_row_count": len(rows),
        "unique_transition_count": len(transition_keys),
        "unique_generated_child_count": len(child_state_keys),
        "duplicate_transition_row_count": duplicate_count,
        "transition_rows_digest": _sha256_json(rows),
    }


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
) -> dict[str, Any]:
    if full_dp is None:
        full_dp = _full_state_records(case.intents, _case_context(case))
    rows = _build_transition_rows(case, full_dp=full_dp)
    expected_transition_count = len(_expected_transition_keys(case, full_dp=full_dp))
    summary = _packet_summary_from_rows(rows)
    summary.update(
        {
            "expected_transition_count": expected_transition_count,
            "covered_transition_count": expected_transition_count,
            "missing_transition_count": 0,
            "extra_transition_count": 0,
            "invalid_transition_row_count": 0,
        }
    )
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "linked_child_coverage_bound": True,
        "forward_transition_membership_bound": True,
        "bidirectional_frontier_bound": True,
        "reserve_state_only_bound": True,
        "lean_contract": _lean_contract(),
        "linked_witness_merkle_summary": _linked_witness_merkle_summary(),
        "transition_rows": rows,
        "transition_summary": summary,
    }
    return _with_packet_hash(packet)


def _verify_transition_rows(
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

    expected_transition_keys = _expected_transition_keys(case, full_dp=full_dp)
    child_frontier = {
        child_mask_id: _sorted_states(_state_set(full_dp[child_mask_id]))
        for child_mask_id in range(1, 1 << n)
    }
    rows = list(packet.get("transition_rows", []) if packet is not None else [])
    seen_transition_keys: set[tuple[int, int, int, tuple[int, int], tuple[int, int]]] = set()
    duplicate_transition_count = 0
    invalid_transition_count = 0

    for index, row in enumerate(rows):
        row_reasons: list[str] = []
        try:
            child_mask_id = int(row["child_mask_id"])
            parent_mask_id = int(row["parent_mask_id"])
            step_bit_index = int(row["step_bit_index"])
            parent_state = _state_from_json(row["parent_state"])
            generated_child_state = _state_from_json(row["generated_child_state"])
            leaf_index = int(row["leaf_index"])
            generated_state_count = int(row["generated_state_count"])
            generated_state_root = str(row["generated_state_root"])
            proof = list(row["membership_proof"])
        except (KeyError, TypeError, ValueError):
            row_reasons.append("transition_row_malformed")
            child_mask_id = -1
            parent_mask_id = -1
            step_bit_index = -1
            parent_state = _ReserveState(-1, -1)
            generated_child_state = _ReserveState(-1, -1)
            leaf_index = -1
            generated_state_count = -1
            generated_state_root = ""
            proof = []

        if row.get("case_id") != case.case_id:
            row_reasons.append("transition_case_id_mismatch")
        if child_mask_id <= 0 or child_mask_id >= (1 << n):
            row_reasons.append("transition_child_mask_out_of_range")
        if step_bit_index < 0 or step_bit_index >= n:
            row_reasons.append("transition_step_bit_out_of_range")
        elif not (child_mask_id & (1 << step_bit_index)):
            row_reasons.append("transition_step_not_in_child_mask")
        elif parent_mask_id != (child_mask_id ^ (1 << step_bit_index)):
            row_reasons.append("transition_parent_mask_mismatch")

        if 0 <= parent_mask_id < (1 << n):
            parent_states = _state_set(full_dp[parent_mask_id])
            if parent_state not in parent_states:
                row_reasons.append("transition_parent_state_not_in_parent_frontier")
            if row.get("parent_quotient_digest") != _quotient_digest(full_dp[parent_mask_id]):
                row_reasons.append("transition_parent_quotient_digest_mismatch")
        else:
            row_reasons.append("transition_parent_mask_out_of_range")

        expected_states = child_frontier.get(child_mask_id, [])
        expected_index_by_key = {
            _state_key(state): idx for idx, state in enumerate(expected_states)
        }
        generated_key = _state_key(generated_child_state)
        if generated_key not in expected_index_by_key:
            row_reasons.append("generated_child_not_in_child_frontier")
        elif expected_index_by_key[generated_key] != leaf_index:
            row_reasons.append("canonical_leaf_index_mismatch")

        if 0 < child_mask_id < (1 << n):
            if row.get("child_quotient_digest") != _quotient_digest(full_dp[child_mask_id]):
                row_reasons.append("transition_child_quotient_digest_mismatch")

        if generated_state_count != len(expected_states):
            row_reasons.append("generated_state_count_mismatch")
        if expected_states and generated_state_root != merkle._merkle_root(expected_states):
            row_reasons.append("generated_state_root_mismatch")
        expected_sides = merkle._expected_sides(leaf_index, len(expected_states))
        if expected_sides is None:
            row_reasons.append("membership_leaf_index_out_of_range")
        elif [step.get("side") for step in proof] != expected_sides:
            row_reasons.append("membership_proof_shape_mismatch")
        elif not merkle._verify_membership_hash(
            _state_json(generated_child_state),
            proof,
            generated_state_root,
        ):
            row_reasons.append("membership_proof_hash_mismatch")

        if 0 <= step_bit_index < n:
            intent = case.intents[step_bit_index]
            if row.get("step_order_id") != intent.intent_id:
                row_reasons.append("transition_step_order_id_mismatch")
            expected_child = _run_suffix_from_state(
                parent_state,
                (intent,),
                _case_context(case),
            )
            if expected_child != generated_child_state:
                row_reasons.append("afterstep_generated_child_mismatch")

        try:
            transition_key = _transition_key(row)
        except (KeyError, TypeError, ValueError):
            transition_key = (-1, -1, -1, (-1, -1), (-1, -1))
        if transition_key in seen_transition_keys:
            duplicate_transition_count += 1
            row_reasons.append("duplicate_transition_row")
        seen_transition_keys.add(transition_key)

        if row_reasons:
            invalid_transition_count += 1
            reasons.extend(row_reasons)
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=child_mask_id,
                reason=row_reasons[0],
                detail={"row_index": index},
            )

    missing_transition_keys = expected_transition_keys - seen_transition_keys
    extra_transition_keys = seen_transition_keys - expected_transition_keys
    if missing_transition_keys:
        reasons.append("missing_predecessor_transition_row")
        first_missing = sorted(missing_transition_keys)[0]
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=int(first_missing[0]),
            reason="missing_predecessor_transition_row",
        )
    if extra_transition_keys:
        reasons.append("extra_predecessor_transition_row")
    if duplicate_transition_count:
        reasons.append("duplicate_transition_row")

    reasons.extend(
        _linked_witness_merkle_reasons(
            packet.get("linked_witness_merkle_summary") if packet is not None else None
        )
    )

    summary = _packet_summary_from_rows(rows)
    summary.update(
        {
            "expected_transition_count": len(expected_transition_keys),
            "covered_transition_count": len(seen_transition_keys & expected_transition_keys),
            "missing_transition_count": len(missing_transition_keys),
            "extra_transition_count": len(extra_transition_keys),
            "invalid_transition_row_count": invalid_transition_count,
        }
    )

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("transition_summary") != summary:
            reasons.append("packet_transition_summary_mismatch")

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


def verify_case(case: Any) -> dict[str, Any]:
    full_dp = _full_state_records(case.intents, _case_context(case))
    packet = build_case_packet(case, full_dp=full_dp)
    verification = _verify_transition_rows(case, full_dp=full_dp, packet=packet)
    return verification | {"packet_hash": packet["packet_hash"]}


def _negative_controls(cases: list[Any]) -> list[dict[str, Any]]:
    case = cases[1]
    full_dp = _full_state_records(case.intents, _case_context(case))
    base_packet = build_case_packet(case, full_dp=full_dp)
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    missing_row = copy.deepcopy(base_packet)
    missing_row["transition_rows"] = missing_row["transition_rows"][1:]
    missing_row["transition_summary"] = _packet_summary_from_rows(
        missing_row["transition_rows"]
    )
    controls.append(
        (
            "missing_predecessor_transition_row",
            _with_packet_hash(missing_row),
            "missing_predecessor_transition_row",
        )
    )

    bad_parent = copy.deepcopy(base_packet)
    bad_parent["transition_rows"][0]["parent_state"]["reserve_out"] += 1
    bad_parent["transition_summary"] = _packet_summary_from_rows(
        bad_parent["transition_rows"]
    )
    controls.append(
        (
            "transition_parent_state_not_in_parent_frontier",
            _with_packet_hash(bad_parent),
            "transition_parent_state_not_in_parent_frontier",
        )
    )

    bad_child = copy.deepcopy(base_packet)
    bad_child["transition_rows"][0]["generated_child_state"]["reserve_out"] += 1
    bad_child["transition_summary"] = _packet_summary_from_rows(
        bad_child["transition_rows"]
    )
    controls.append(
        (
            "afterstep_generated_child_mismatch",
            _with_packet_hash(bad_child),
            "afterstep_generated_child_mismatch",
        )
    )

    bad_step = copy.deepcopy(base_packet)
    bad_step["transition_rows"][0]["step_bit_index"] = len(case.intents)
    bad_step["transition_summary"] = _packet_summary_from_rows(
        bad_step["transition_rows"]
    )
    controls.append(
        (
            "transition_step_bit_out_of_range",
            _with_packet_hash(bad_step),
            "transition_step_bit_out_of_range",
        )
    )

    bad_root = copy.deepcopy(base_packet)
    bad_root["transition_rows"][0]["generated_state_root"] = "0" * 64
    bad_root["transition_summary"] = _packet_summary_from_rows(
        bad_root["transition_rows"]
    )
    controls.append(
        (
            "generated_state_root_mismatch",
            _with_packet_hash(bad_root),
            "generated_state_root_mismatch",
        )
    )

    target_index = next(
        index
        for index, row in enumerate(base_packet["transition_rows"])
        if int(row["generated_state_count"]) >= 2
    )
    bad_proof = copy.deepcopy(base_packet)
    bad_proof["transition_rows"][target_index]["membership_proof"][0]["hash"] = "0" * 64
    bad_proof["transition_summary"] = _packet_summary_from_rows(
        bad_proof["transition_rows"]
    )
    controls.append(
        (
            "membership_proof_hash_mismatch",
            _with_packet_hash(bad_proof),
            "membership_proof_hash_mismatch",
        )
    )

    bad_link = copy.deepcopy(base_packet)
    bad_link["linked_witness_merkle_summary"]["bound_row_count"] += 1
    controls.append(
        (
            "linked_witness_merkle_bound_row_count_mismatch",
            _with_packet_hash(bad_link),
            "linked_witness_merkle_bound_row_count_mismatch",
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
        verification = _verify_transition_rows(
            case,
            full_dp=_clone_full_dp(full_dp),
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
    transition_row_count = sum(int(row["transition_row_count"]) for row in rows)
    return {
        "schema": SEARCH_SCHEMA,
        "source_seed": N7_SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "child_mask_count": sum(int(row["child_mask_count"]) for row in rows),
        "transition_row_count": transition_row_count,
        "expected_transition_count": sum(
            int(row["expected_transition_count"]) for row in rows
        ),
        "covered_transition_count": sum(
            int(row["covered_transition_count"]) for row in rows
        ),
        "unique_transition_count": sum(
            int(row["unique_transition_count"]) for row in rows
        ),
        "unique_generated_child_count": sum(
            int(row["unique_generated_child_count"]) for row in rows
        ),
        "missing_transition_count": sum(
            int(row["missing_transition_count"]) for row in rows
        ),
        "extra_transition_count": sum(int(row["extra_transition_count"]) for row in rows),
        "invalid_transition_row_count": sum(
            int(row["invalid_transition_row_count"]) for row in rows
        ),
        "duplicate_transition_row_count": sum(
            int(row["duplicate_transition_row_count"]) for row in rows
        ),
        "linked_child_coverage_witness_count": int(
            _linked_witness_merkle_summary()["witness_count"]
        ),
        "transition_to_child_witness_ratio": round(
            transition_row_count
            / max(int(_linked_witness_merkle_summary()["witness_count"]), 1),
            6,
        ),
        "transition_rows_digest": _sha256_json(
            [row["transition_rows_digest"] for row in rows]
        ),
        "linked_witness_merkle_summary": _linked_witness_merkle_summary(),
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
        and search["transition_row_count"] == search["expected_transition_count"]
        and search["transition_row_count"] == search["covered_transition_count"]
        and search["transition_row_count"] == search["unique_transition_count"]
        and search["missing_transition_count"] == 0
        and search["extra_transition_count"] == 0
        and search["invalid_transition_row_count"] == 0
        and search["duplicate_transition_row_count"] == 0
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and not _linked_witness_merkle_reasons(search["linked_witness_merkle_summary"])
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded bidirectional transition certificate supports the n=7 "
            "strict zero-min AB reserve-state child-frontier equality: linked "
            "witness+Merkle rows cover child states, and every predecessor "
            "afterStep image is a canonical Merkle member of the child frontier."
        ),
        "authority_boundary": (
            "Research-only certificate-boundary evidence; no settlement, state-root, "
            "production, routing, matching, pool-mutation, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_bidirectional_transition_20260629.py"
        ),
        "non_claims": [
            "This checker is bounded to the committed n=7 randomized corpus.",
            "This checker covers only zero-min exact-in cases in the scoped corpus.",
            "This checker links the child coverage direction to the existing witness+Merkle report.",
            "This checker does not prove Python-to-Lean refinement.",
            "This checker does not prove child-frontier generation in Lean.",
            "This checker does not define canonical tie order or preserve order-id history.",
            "This checker does not cover nonzero min_amount_out behavior.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Reserve-State Child-Frontier Bidirectional Transition Certificate - 2026-06-29",
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
        f"- Transition rows: `{search['transition_row_count']}`",
        f"- Expected transitions: `{search['expected_transition_count']}`",
        f"- Covered transitions: `{search['covered_transition_count']}`",
        f"- Unique transition rows: `{search['unique_transition_count']}`",
        f"- Unique generated child states across masks: `{search['unique_generated_child_count']}`",
        f"- Missing transitions: `{search['missing_transition_count']}`",
        f"- Extra transitions: `{search['extra_transition_count']}`",
        f"- Invalid transition rows: `{search['invalid_transition_row_count']}`",
        f"- Duplicate transition rows: `{search['duplicate_transition_row_count']}`",
        f"- Linked child coverage witnesses: `{search['linked_child_coverage_witness_count']}`",
        f"- Transition-to-child-witness ratio: `{search['transition_to_child_witness_ratio']}`",
        f"- Transition rows digest: `{search['transition_rows_digest']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Linked Child Coverage Report",
        "",
        "```json",
        json.dumps(search["linked_witness_merkle_summary"], indent=2, sort_keys=True),
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
            "| case | ok | transitions | child masks | unique generated children | digest |",
            "| --- | --- | ---: | ---: | ---: | --- |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            "| `{case_id}` | `{ok}` | `{transition_row_count}` | `{child_mask_count}` | "
            "`{unique_generated_child_count}` | `{digest}` |".format(
                case_id=row["case_id"],
                ok=row["ok"],
                transition_row_count=row["transition_row_count"],
                child_mask_count=row["child_mask_count"],
                unique_generated_child_count=row["unique_generated_child_count"],
                digest=row["transition_rows_digest"],
            )
        )
    lines.extend(
        [
            "",
            "## Non-Claims",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.append("")
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def write_report(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    _write_markdown(report)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print full report JSON")
    args = parser.parse_args()

    report = build_report()
    write_report(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            json.dumps(
                {
                    "ok": report["ok"],
                    "report": str(REPORT_JSON.relative_to(REPO_ROOT)),
                },
                sort_keys=True,
            )
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
