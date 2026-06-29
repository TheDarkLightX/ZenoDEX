#!/usr/bin/env python3
"""Check canonical Merkle roots for AB reserve-state child frontiers.

This research-only checker lifts the canonical-index Merkle certificate from a
two-state countermodel to the committed n=7 reserve-state child-frontier corpus.
Each child-mask frontier receives a canonical generated-state root, a generated
count, and one count-aware membership proof per child quotient state.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_reserve_state_child_frontier_generation_20260629 import (  # noqa: E402
    _lean_contract as _frontier_lean_contract,
)
from tools.check_ab_reserve_state_child_frontier_witness_compression_20260629 import (  # noqa: E402
    _linked_frontier_summary,
)
from tools.check_ab_reserve_state_transition_projection_20260629 import (  # noqa: E402
    _new_failure,
    _packet_hash,
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
    _state_json,
)
from tools.check_ab_strict_zero_min_subset_induction_witness import _clone_full_dp  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_canonical_merkle_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_CANONICAL_MERKLE_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_reserve_state_child_frontier_canonical_merkle_packet.v1"
REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_canonical_merkle_report.v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_child_frontier_canonical_merkle"
LEAF_SCHEMA = "zenodex.ab_reserve_state_child_frontier_merkle_leaf.v1"
NODE_SCHEMA = "zenodex.ab_reserve_state_child_frontier_merkle_node.v1"
TARGET_CASE_COUNT = 4
EXPECTED_NEGATIVE_CONTROL_COUNT = 8


def _lean_contract() -> dict[str, str]:
    base = _frontier_lean_contract()
    return {
        **base,
        "host_merkle_shape": (
            "canonical sorted leaf-index Merkle root per child quotient frontier"
        ),
    }


def _state_from_json(row: Mapping[str, Any]) -> _ReserveState:
    return _ReserveState(
        int(row["processed_reserve_in"]),
        int(row["reserve_out"]),
    )


def _state_rows(states: Iterable[_ReserveState]) -> list[dict[str, int]]:
    return [_state_json(state) for state in _sorted_states(states)]


def _state_key_from_json(row: Mapping[str, Any]) -> tuple[int, int]:
    return int(row["processed_reserve_in"]), int(row["reserve_out"])


def _leaf_hash(state: _ReserveState | Mapping[str, Any]) -> str:
    if isinstance(state, _ReserveState):
        state_row = _state_json(state)
    else:
        state_row = {
            "processed_reserve_in": int(state["processed_reserve_in"]),
            "reserve_out": int(state["reserve_out"]),
        }
    return _sha256_json({"schema": LEAF_SCHEMA, "state": state_row})


def _node_hash(left_hash: str, right_hash: str) -> str:
    return _sha256_json(
        {"schema": NODE_SCHEMA, "left_hash": left_hash, "right_hash": right_hash}
    )


def _merkle_levels(states: Sequence[_ReserveState]) -> list[list[str]]:
    leaf_hashes = [_leaf_hash(state) for state in states]
    if not leaf_hashes:
        return [[_sha256_json({"schema": NODE_SCHEMA, "empty": True})]]
    levels: list[list[str]] = [leaf_hashes]
    while len(levels[-1]) > 1:
        previous = levels[-1]
        next_level: list[str] = []
        for index in range(0, len(previous), 2):
            left_hash = previous[index]
            right_hash = previous[index + 1] if index + 1 < len(previous) else left_hash
            next_level.append(_node_hash(left_hash, right_hash))
        levels.append(next_level)
    return levels


def _merkle_root(states: Sequence[_ReserveState]) -> str:
    return _merkle_levels(states)[-1][0]


def _expected_sides(leaf_index: int, leaf_count: int) -> list[str] | None:
    if leaf_count <= 0 or leaf_index < 0 or leaf_index >= leaf_count:
        return None
    index = leaf_index
    count = leaf_count
    sides: list[str] = []
    while count > 1:
        sides.append("right" if index % 2 == 0 else "left")
        index //= 2
        count = (count + 1) // 2
    return sides


def _membership_proof(
    states: Sequence[_ReserveState],
    *,
    leaf_index: int,
) -> list[dict[str, str]]:
    levels = _merkle_levels(states)
    proof: list[dict[str, str]] = []
    index = leaf_index
    for level in levels[:-1]:
        if index % 2 == 0:
            sibling_index = index + 1 if index + 1 < len(level) else index
            proof.append({"side": "right", "hash": level[sibling_index]})
        else:
            proof.append({"side": "left", "hash": level[index - 1]})
        index //= 2
    return proof


def _verify_membership_hash(
    state: Mapping[str, Any],
    proof: Sequence[Mapping[str, Any]],
    expected_root_hash: str,
) -> bool:
    current_hash = _leaf_hash(state)
    for step in proof:
        side = step.get("side")
        sibling_hash = step.get("hash")
        if side == "right" and isinstance(sibling_hash, str):
            current_hash = _node_hash(current_hash, sibling_hash)
        elif side == "left" and isinstance(sibling_hash, str):
            current_hash = _node_hash(sibling_hash, current_hash)
        else:
            return False
    return current_hash == expected_root_hash


def _frontier_row_from_states(
    *,
    child_mask_id: int,
    states: Sequence[_ReserveState],
    generated_order: Sequence[_ReserveState] | None = None,
) -> dict[str, Any]:
    canonical_states = _sorted_states(states)
    generated_order = list(generated_order) if generated_order is not None else canonical_states
    canonical_index = {state: index for index, state in enumerate(canonical_states)}
    membership_rows = [
        {
            "child_state": _state_json(state),
            "leaf_index": int(canonical_index[state])
            if generated_order == canonical_states
            else int(generated_order.index(state)),
            "proof": _membership_proof(
                generated_order,
                leaf_index=int(generated_order.index(state)),
            ),
        }
        for state in canonical_states
    ]
    return {
        "child_mask_id": int(child_mask_id),
        "child_state_count": len(canonical_states),
        "generated_state_count": len(generated_order),
        "child_state_digest": _sha256_json(_state_rows(canonical_states)),
        "generated_state_root": _merkle_root(generated_order),
        "membership_rows": membership_rows,
        "membership_rows_digest": _sha256_json(membership_rows),
    }


def _frontier_rows_for_case(
    *,
    full_dp: list[list[_HostRecord]],
) -> list[dict[str, Any]]:
    n = (len(full_dp)).bit_length() - 1
    rows: list[dict[str, Any]] = []
    for child_mask_id in range(1, 1 << n):
        rows.append(
            _frontier_row_from_states(
                child_mask_id=child_mask_id,
                states=_state_set(full_dp[child_mask_id]),
            )
        )
    return rows


def _case_summary_from_rows(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    return {
        "child_mask_count": len(rows),
        "frontier_root_count": len(rows),
        "child_state_count": sum(int(row["child_state_count"]) for row in rows),
        "membership_count": sum(len(row["membership_rows"]) for row in rows),
        "max_leaf_count": max((int(row["child_state_count"]) for row in rows), default=0),
        "frontier_roots_digest": _sha256_json(
            [
                {
                    "child_mask_id": int(row["child_mask_id"]),
                    "generated_state_count": int(row["generated_state_count"]),
                    "generated_state_root": row["generated_state_root"],
                }
                for row in rows
            ]
        ),
        "membership_rows_digest": _sha256_json(
            [row["membership_rows_digest"] for row in rows]
        ),
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
        return ["canonical_merkle_packet_missing"]
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
    if packet.get("canonical_merkle_bound") is not True:
        reasons.append("canonical_merkle_bound_missing")
    if packet.get("canonical_leaf_index_bound") is not True:
        reasons.append("canonical_leaf_index_bound_missing")
    if packet.get("count_aware_membership_bound") is not True:
        reasons.append("count_aware_membership_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("linked_frontier_summary") != _linked_frontier_summary():
        reasons.append("linked_frontier_summary_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
) -> dict[str, Any]:
    if full_dp is None:
        full_dp = _full_state_records(case.intents, _case_context(case))
    frontier_rows = _frontier_rows_for_case(full_dp=full_dp)
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "canonical_merkle_bound": True,
        "canonical_leaf_index_bound": True,
        "count_aware_membership_bound": True,
        "reserve_state_only_bound": True,
        "lean_contract": _lean_contract(),
        "linked_frontier_summary": _linked_frontier_summary(),
        "frontier_rows": frontier_rows,
        "canonical_merkle_summary": _case_summary_from_rows(frontier_rows),
    }
    return _with_packet_hash(packet)


def _verify_case_packet(
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

    expected_by_mask = {
        child_mask_id: _sorted_states(_state_set(full_dp[child_mask_id]))
        for child_mask_id in range(1, 1 << n)
    }
    rows = list(packet.get("frontier_rows", []) if packet is not None else [])
    rows_by_mask: dict[int, Mapping[str, Any]] = {}
    duplicate_frontier_row_count = 0
    missing_membership_count = 0
    extra_membership_count = 0
    invalid_membership_count = 0
    root_mismatch_count = 0

    for row_index, row in enumerate(rows):
        try:
            child_mask_id = int(row["child_mask_id"])
        except (KeyError, TypeError, ValueError):
            reasons.append("frontier_row_malformed")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=-1,
                reason="frontier_row_malformed",
                detail={"row_index": row_index},
            )
            continue
        if child_mask_id in rows_by_mask:
            duplicate_frontier_row_count += 1
            reasons.append("duplicate_frontier_row")
        rows_by_mask[child_mask_id] = row

        expected_states = expected_by_mask.get(child_mask_id)
        if expected_states is None:
            reasons.append("frontier_child_mask_out_of_range")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=child_mask_id,
                reason="frontier_child_mask_out_of_range",
            )
            continue
        expected_state_rows = _state_rows(expected_states)
        expected_root = _merkle_root(expected_states)
        if int(row.get("child_state_count", -1)) != len(expected_states):
            reasons.append("frontier_child_state_count_mismatch")
        if int(row.get("generated_state_count", -1)) != len(expected_states):
            reasons.append("frontier_generated_state_count_mismatch")
        if row.get("child_state_digest") != _sha256_json(expected_state_rows):
            reasons.append("frontier_child_state_digest_mismatch")
        if row.get("generated_state_root") != expected_root:
            root_mismatch_count += 1
            reasons.append("frontier_generated_state_root_mismatch")

        membership_rows = list(row.get("membership_rows", []))
        if row.get("membership_rows_digest") != _sha256_json(membership_rows):
            reasons.append("membership_rows_digest_mismatch")
        expected_index_by_key = {
            (state.processed_reserve_in, state.reserve_out): index
            for index, state in enumerate(expected_states)
        }
        seen_keys: set[tuple[int, int]] = set()
        seen_indices: set[int] = set()
        for member_index, member in enumerate(membership_rows):
            try:
                child_state = dict(member["child_state"])
                state_key = _state_key_from_json(child_state)
                leaf_index = int(member["leaf_index"])
                proof = list(member["proof"])
            except (KeyError, TypeError, ValueError):
                invalid_membership_count += 1
                reasons.append("membership_row_malformed")
                continue
            if state_key not in expected_index_by_key:
                extra_membership_count += 1
                reasons.append("membership_child_state_not_in_frontier")
            expected_index = expected_index_by_key.get(state_key)
            if expected_index != leaf_index:
                invalid_membership_count += 1
                reasons.append("canonical_leaf_index_mismatch")
            if leaf_index in seen_indices:
                invalid_membership_count += 1
                reasons.append("duplicate_leaf_index")
            seen_indices.add(leaf_index)
            if state_key in seen_keys:
                invalid_membership_count += 1
                reasons.append("duplicate_membership_row")
            seen_keys.add(state_key)
            expected_sides = _expected_sides(leaf_index, len(expected_states))
            if expected_sides is None:
                invalid_membership_count += 1
                reasons.append("membership_leaf_index_out_of_range")
            elif [step.get("side") for step in proof] != expected_sides:
                invalid_membership_count += 1
                reasons.append("membership_proof_shape_mismatch")
            elif not _verify_membership_hash(child_state, proof, str(row.get("generated_state_root"))):
                invalid_membership_count += 1
                reasons.append("membership_proof_hash_mismatch")
            if reasons and first_failure is None:
                first_failure = _new_failure(
                    first_failure,
                    case_id=case.case_id,
                    mask_id=child_mask_id,
                    reason=reasons[-1],
                    detail={"member_index": member_index},
                )
        missing_keys = set(expected_index_by_key) - seen_keys
        if missing_keys:
            missing_membership_count += len(missing_keys)
            reasons.append("missing_membership_proof")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=child_mask_id,
                reason="missing_membership_proof",
            )

    missing_frontier_masks = set(expected_by_mask) - set(rows_by_mask)
    extra_frontier_masks = set(rows_by_mask) - set(expected_by_mask)
    if missing_frontier_masks:
        reasons.append("missing_frontier_row")
    if extra_frontier_masks:
        reasons.append("extra_frontier_row")

    linked_reasons = _linked_frontier_reasons(
        packet.get("linked_frontier_summary") if packet is not None else None
    )
    reasons.extend(linked_reasons)

    expected_summary = _case_summary_from_rows(
        [_frontier_row_from_states(child_mask_id=mask, states=states) for mask, states in expected_by_mask.items()]
    )
    actual_summary = _case_summary_from_rows(rows) if rows else {
        "child_mask_count": 0,
        "frontier_root_count": 0,
        "child_state_count": 0,
        "membership_count": 0,
        "max_leaf_count": 0,
        "frontier_roots_digest": _sha256_json([]),
        "membership_rows_digest": _sha256_json([]),
    }
    summary = {
        **actual_summary,
        "expected_child_mask_count": len(expected_by_mask),
        "expected_child_state_count": sum(len(states) for states in expected_by_mask.values()),
        "covered_child_state_count": actual_summary["membership_count"] - extra_membership_count,
        "missing_frontier_row_count": len(missing_frontier_masks),
        "extra_frontier_row_count": len(extra_frontier_masks),
        "duplicate_frontier_row_count": duplicate_frontier_row_count,
        "missing_membership_proof_count": missing_membership_count,
        "extra_membership_proof_count": extra_membership_count,
        "invalid_membership_proof_count": invalid_membership_count,
        "root_mismatch_count": root_mismatch_count,
        "expected_frontier_roots_digest": expected_summary["frontier_roots_digest"],
    }

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("canonical_merkle_summary") != actual_summary:
            reasons.append("packet_canonical_merkle_summary_mismatch")

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
    verification = _verify_case_packet(case, full_dp=full_dp, packet=packet)
    return verification | {"packet_hash": packet["packet_hash"]}


def _count_aware_accepts_row(row: Mapping[str, Any]) -> bool:
    leaf_count = int(row["generated_state_count"])
    root = str(row["generated_state_root"])
    for member in row["membership_rows"]:
        leaf_index = int(member["leaf_index"])
        expected_sides = _expected_sides(leaf_index, leaf_count)
        if expected_sides is None:
            return False
        if [step.get("side") for step in member["proof"]] != expected_sides:
            return False
        if not _verify_membership_hash(member["child_state"], member["proof"], root):
            return False
    return True


def _permutation_countermodel(cases: list[Any]) -> dict[str, Any]:
    case = cases[1]
    full_dp = _full_state_records(case.intents, _case_context(case))
    for child_mask_id in range(1, 1 << len(case.intents)):
        states = _sorted_states(_state_set(full_dp[child_mask_id]))
        if len(states) >= 2:
            canonical_row = _frontier_row_from_states(child_mask_id=child_mask_id, states=states)
            permuted_row = _frontier_row_from_states(
                child_mask_id=child_mask_id,
                states=states,
                generated_order=list(reversed(states)),
            )
            return {
                "case_id": case.case_id,
                "child_mask_id": int(child_mask_id),
                "leaf_count": len(states),
                "canonical_root": canonical_row["generated_state_root"],
                "permuted_root": permuted_row["generated_state_root"],
                "roots_differ": canonical_row["generated_state_root"]
                != permuted_row["generated_state_root"],
                "count_aware_accepts_permuted": _count_aware_accepts_row(permuted_row),
                "canonical_index_reject_reason": "canonical_leaf_index_mismatch",
            }
    return {"case_id": None, "child_mask_id": None, "roots_differ": False}


def _negative_controls(cases: list[Any]) -> list[dict[str, Any]]:
    case = cases[1]
    full_dp = _full_state_records(case.intents, _case_context(case))
    base_packet = build_case_packet(case, full_dp=full_dp)
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    stale_root = copy.deepcopy(base_packet)
    stale_root["frontier_rows"][0]["generated_state_root"] = "0" * 64
    stale_root["canonical_merkle_summary"] = _case_summary_from_rows(stale_root["frontier_rows"])
    controls.append(
        (
            "frontier_generated_state_root_mismatch",
            _with_packet_hash(stale_root),
            "frontier_generated_state_root_mismatch",
        )
    )

    permuted = copy.deepcopy(base_packet)
    target_index = next(
        index
        for index, row in enumerate(permuted["frontier_rows"])
        if int(row["child_state_count"]) >= 2
    )
    child_mask_id = int(permuted["frontier_rows"][target_index]["child_mask_id"])
    states = _sorted_states(_state_set(full_dp[child_mask_id]))
    permuted["frontier_rows"][target_index] = _frontier_row_from_states(
        child_mask_id=child_mask_id,
        states=states,
        generated_order=list(reversed(states)),
    )
    permuted["canonical_merkle_summary"] = _case_summary_from_rows(permuted["frontier_rows"])
    controls.append(
        (
            "canonical_leaf_index_mismatch",
            _with_packet_hash(permuted),
            "canonical_leaf_index_mismatch",
        )
    )

    missing_member = copy.deepcopy(base_packet)
    missing_member["frontier_rows"][0]["membership_rows"] = []
    missing_member["frontier_rows"][0]["membership_rows_digest"] = _sha256_json([])
    missing_member["canonical_merkle_summary"] = _case_summary_from_rows(
        missing_member["frontier_rows"]
    )
    controls.append(
        (
            "missing_membership_proof",
            _with_packet_hash(missing_member),
            "missing_membership_proof",
        )
    )

    duplicate_leaf = copy.deepcopy(base_packet)
    duplicate_row_index = next(
        index
        for index, row in enumerate(duplicate_leaf["frontier_rows"])
        if len(row["membership_rows"]) >= 2
    )
    duplicate_leaf["frontier_rows"][duplicate_row_index]["membership_rows"][1][
        "leaf_index"
    ] = duplicate_leaf["frontier_rows"][duplicate_row_index]["membership_rows"][0][
        "leaf_index"
    ]
    duplicate_leaf["frontier_rows"][duplicate_row_index]["membership_rows_digest"] = _sha256_json(
        duplicate_leaf["frontier_rows"][duplicate_row_index]["membership_rows"]
    )
    duplicate_leaf["canonical_merkle_summary"] = _case_summary_from_rows(
        duplicate_leaf["frontier_rows"]
    )
    controls.append(
        (
            "duplicate_leaf_index",
            _with_packet_hash(duplicate_leaf),
            "duplicate_leaf_index",
        )
    )

    bad_summary = copy.deepcopy(base_packet)
    bad_summary["canonical_merkle_summary"]["frontier_root_count"] += 1
    controls.append(
        (
            "packet_canonical_merkle_summary_mismatch",
            _with_packet_hash(bad_summary),
            "packet_canonical_merkle_summary_mismatch",
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
        verification = _verify_case_packet(case, full_dp=_clone_full_dp(full_dp), packet=packet)
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
    permutation_countermodel = _permutation_countermodel(cases)
    child_state_count = sum(int(row["child_state_count"]) for row in rows)
    membership_count = sum(int(row["membership_count"]) for row in rows)
    return {
        "schema": "zenodex/ab_reserve_state_child_frontier_canonical_merkle_search/v1",
        "source_seed": N7_SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "child_mask_count": sum(int(row["child_mask_count"]) for row in rows),
        "frontier_root_count": sum(int(row["frontier_root_count"]) for row in rows),
        "child_state_count": child_state_count,
        "membership_count": membership_count,
        "covered_child_state_count": sum(int(row["covered_child_state_count"]) for row in rows),
        "missing_frontier_row_count": sum(int(row["missing_frontier_row_count"]) for row in rows),
        "extra_frontier_row_count": sum(int(row["extra_frontier_row_count"]) for row in rows),
        "missing_membership_proof_count": sum(int(row["missing_membership_proof_count"]) for row in rows),
        "extra_membership_proof_count": sum(int(row["extra_membership_proof_count"]) for row in rows),
        "invalid_membership_proof_count": sum(int(row["invalid_membership_proof_count"]) for row in rows),
        "root_mismatch_count": sum(int(row["root_mismatch_count"]) for row in rows),
        "max_leaf_count": max((int(row["max_leaf_count"]) for row in rows), default=0),
        "frontier_roots_digest": _sha256_json(
            [row["frontier_roots_digest"] for row in rows]
        ),
        "membership_rows_digest": _sha256_json(
            [row["membership_rows_digest"] for row in rows]
        ),
        "permutation_countermodel": permutation_countermodel,
        "permutation_countermodel_valid": bool(
            permutation_countermodel.get("roots_differ")
            and permutation_countermodel.get("count_aware_accepts_permuted")
        ),
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
        and search["child_mask_count"] == 508
        and search["frontier_root_count"] == 508
        and search["child_state_count"] == 864
        and search["membership_count"] == 864
        and search["covered_child_state_count"] == 864
        and search["missing_membership_proof_count"] == 0
        and search["invalid_membership_proof_count"] == 0
        and search["root_mismatch_count"] == 0
        and search["permutation_countermodel_valid"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded n=7 host checker supports canonical-index Merkle roots "
            "for AB reserve-state child frontiers: 508 child-mask roots cover "
            "864 child quotient states with zero missing, invalid, or stale "
            "membership proofs."
        ),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_canonical_merkle_20260629.py"
        ),
        "non_claims": [
            "This canonical Merkle checker is bounded to the committed n=7 randomized corpus.",
            "This checker covers only zero-min exact-in cases in the scoped corpus.",
            "This checker does not prove Python-to-Lean refinement.",
            "This checker does not prove child-frontier generation in Lean.",
            "This checker does not replace a deterministic generated-image producer.",
            "This checker does not cover nonzero min_amount_out behavior.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Reserve-State Child-Frontier Canonical Merkle - 2026-06-29",
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
        f"- Frontier roots: `{search['frontier_root_count']}`",
        f"- Child quotient states: `{search['child_state_count']}`",
        f"- Membership proofs: `{search['membership_count']}`",
        f"- Covered child states: `{search['covered_child_state_count']}`",
        f"- Missing membership proofs: `{search['missing_membership_proof_count']}`",
        f"- Invalid membership proofs: `{search['invalid_membership_proof_count']}`",
        f"- Root mismatches: `{search['root_mismatch_count']}`",
        f"- Max leaves per root: `{search['max_leaf_count']}`",
        f"- Frontier roots digest: `{search['frontier_roots_digest']}`",
        f"- Membership rows digest: `{search['membership_rows_digest']}`",
        f"- Permutation countermodel valid: `{search['permutation_countermodel_valid']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Permutation Countermodel",
        "",
        "```json",
        json.dumps(search["permutation_countermodel"], indent=2, sort_keys=True),
        "```",
        "",
        "## Coverage",
        "",
        "```json",
        json.dumps(coverage, indent=2, sort_keys=True),
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
    REPORT_JSON.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    _write_markdown(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            json.dumps(
                {"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}
            )
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
