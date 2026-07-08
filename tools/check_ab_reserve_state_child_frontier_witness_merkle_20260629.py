#!/usr/bin/env python3
"""Check cross-bound witness+Merkle rows for AB reserve-state child frontiers.

This research-only checker composes two previously supported n=7 facts:
one predecessor witness per child quotient state, and canonical-index Merkle
membership for each child quotient state. The new obligation is the cross-bind:
the same child state and child mask must satisfy both witnesses in one row.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools import check_ab_reserve_state_child_frontier_canonical_merkle_20260629 as merkle  # noqa: E402
from tools import check_ab_reserve_state_child_frontier_witness_compression_20260629 as witness  # noqa: E402
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
    _quotient_digest,
    _run_suffix_from_state,
    _state_json,
)
from tools.check_ab_strict_zero_min_subset_induction_witness import _clone_full_dp  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_witness_merkle_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_WITNESS_MERKLE_20260629.md"
)
WITNESS_REPORT_JSON = witness.REPORT_JSON
MERKLE_REPORT_JSON = merkle.REPORT_JSON

PACKET_SCHEMA = "zenodex.ab_reserve_state_child_frontier_witness_merkle_packet.v1"
REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_witness_merkle_report.v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_child_frontier_witness_merkle"
TARGET_CASE_COUNT = 4
EXPECTED_NEGATIVE_CONTROL_COUNT = 10


def _lean_contract() -> dict[str, str]:
    return {
        **witness._lean_contract(),
        "host_merkle_shape": (
            "canonical sorted leaf-index Merkle root per child quotient frontier"
        ),
        "host_cross_binding_shape": (
            "each predecessor witness row is bound to a canonical Merkle "
            "membership proof for the same child mask and child state"
        ),
    }


def _state_from_json(row: Mapping[str, Any]) -> _ReserveState:
    return _ReserveState(
        int(row["processed_reserve_in"]),
        int(row["reserve_out"]),
    )


def _state_key(state: _ReserveState) -> tuple[int, int]:
    return int(state.processed_reserve_in), int(state.reserve_out)


def _state_key_from_json(row: Mapping[str, Any]) -> tuple[int, int]:
    return int(row["processed_reserve_in"]), int(row["reserve_out"])


def _report_summary(path: Path, *, kind: str) -> dict[str, Any]:
    if not path.exists():
        return {
            "kind": kind,
            "path": str(path.relative_to(REPO_ROOT)),
            "available": False,
        }
    report = json.loads(path.read_text(encoding="utf-8"))
    search = report.get("search", {})
    return {
        "kind": kind,
        "path": str(path.relative_to(REPO_ROOT)),
        "available": True,
        "ok": bool(report.get("ok")),
        "schema": report.get("schema"),
        "case_count": int(search.get("case_count", -1)),
        "valid_case_count": int(search.get("valid_case_count", -1)),
        "child_mask_count": int(search.get("child_mask_count", -1)),
        "child_state_count": int(
            search.get("child_state_count", search.get("expected_child_state_count", -1))
        ),
        "negative_control_accept_count": int(
            search.get("negative_control_accept_count", -1)
        ),
        "digest": search.get(
            "membership_rows_digest",
            search.get("witness_rows_digest", search.get("frontier_rows_digest")),
        ),
    }


def _linked_report_reasons(summary: Mapping[str, Any] | None, *, kind: str) -> list[str]:
    if summary is None:
        return [f"linked_{kind}_summary_missing"]
    reasons: list[str] = []
    if summary.get("available") is not True:
        reasons.append(f"linked_{kind}_report_missing")
    if summary.get("ok") is not True:
        reasons.append(f"linked_{kind}_report_not_ok")
    if int(summary.get("case_count", -1)) != TARGET_CASE_COUNT:
        reasons.append(f"linked_{kind}_case_count_mismatch")
    if int(summary.get("valid_case_count", -1)) != TARGET_CASE_COUNT:
        reasons.append(f"linked_{kind}_valid_case_count_mismatch")
    if int(summary.get("child_mask_count", -1)) != 508:
        reasons.append(f"linked_{kind}_child_mask_count_mismatch")
    if int(summary.get("child_state_count", -1)) != 864:
        reasons.append(f"linked_{kind}_child_state_count_mismatch")
    if int(summary.get("negative_control_accept_count", -1)) != 0:
        reasons.append(f"linked_{kind}_negative_control_accepts")
    return reasons


def _packet_rail_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["witness_merkle_packet_missing"]
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
    if packet.get("canonical_merkle_bound") is not True:
        reasons.append("canonical_merkle_bound_missing")
    if packet.get("cross_binding_bound") is not True:
        reasons.append("cross_binding_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("linked_witness_summary") != _report_summary(
        WITNESS_REPORT_JSON,
        kind="witness",
    ):
        reasons.append("linked_witness_summary_mismatch")
    if packet.get("linked_merkle_summary") != _report_summary(
        MERKLE_REPORT_JSON,
        kind="merkle",
    ):
        reasons.append("linked_merkle_summary_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _bound_rows_digest(rows: list[Mapping[str, Any]]) -> str:
    return _sha256_json(rows)


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
            memberships[
                (mask_id, _state_key_from_json(member["child_state"]))
            ] = member | {
                "generated_state_count": int(row["generated_state_count"]),
                "generated_state_root": row["generated_state_root"],
            }
    return memberships


def _build_bound_rows(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]],
) -> list[dict[str, Any]]:
    witness_rows = witness._build_witness_rows(case, full_dp=full_dp)
    memberships = _membership_by_key(_frontier_rows_by_mask(full_dp))
    bound_rows: list[dict[str, Any]] = []
    for witness_row in witness_rows:
        mask_id = int(witness_row["child_mask_id"])
        state_key = _state_key_from_json(witness_row["child_state"])
        member = memberships[(mask_id, state_key)]
        bound_rows.append(
            {
                "case_id": case.case_id,
                "child_mask_id": mask_id,
                "child_state": copy.deepcopy(witness_row["child_state"]),
                "witness": copy.deepcopy(witness_row),
                "leaf_index": int(member["leaf_index"]),
                "generated_state_count": int(member["generated_state_count"]),
                "generated_state_root": member["generated_state_root"],
                "membership_proof": list(member["proof"]),
            }
        )
    return bound_rows


def _predecessor_transition_count(case: Any, full_dp: list[list[_HostRecord]]) -> int:
    total = 0
    for child_mask_id in range(1, 1 << len(case.intents)):
        for step_bit_index, _intent in enumerate(case.intents):
            if child_mask_id & (1 << step_bit_index):
                total += len(_state_set(full_dp[child_mask_id ^ (1 << step_bit_index)]))
    return total


def _packet_summary_from_rows(rows: list[Mapping[str, Any]]) -> dict[str, Any]:
    child_masks = {int(row["child_mask_id"]) for row in rows}
    child_state_keys = {
        (int(row["child_mask_id"]), _state_key_from_json(row["child_state"]))
        for row in rows
    }
    duplicate_count = len(rows) - len(child_state_keys)
    return {
        "child_mask_count": len(child_masks),
        "bound_row_count": len(rows),
        "unique_child_bound_count": len(child_state_keys),
        "duplicate_bound_row_count": duplicate_count,
        "witness_count": len(rows),
        "membership_count": len(rows),
        "bound_rows_digest": _bound_rows_digest(rows),
    }


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
) -> dict[str, Any]:
    if full_dp is None:
        full_dp = _full_state_records(case.intents, _case_context(case))
    rows = _build_bound_rows(case, full_dp=full_dp)
    predecessor_transition_count = _predecessor_transition_count(case, full_dp)
    summary = _packet_summary_from_rows(rows)
    summary.update(
        {
            "expected_child_state_count": summary["bound_row_count"],
            "covered_child_state_count": summary["bound_row_count"],
            "missing_child_bound_count": 0,
            "extra_child_bound_count": 0,
            "invalid_bound_row_count": 0,
            "predecessor_transition_count": predecessor_transition_count,
            "witness_transition_checks_saved": (
                predecessor_transition_count - summary["bound_row_count"]
            ),
            "frontier_witness_compression_ratio": round(
                predecessor_transition_count / max(summary["bound_row_count"], 1),
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
        "canonical_merkle_bound": True,
        "cross_binding_bound": True,
        "reserve_state_only_bound": True,
        "lean_contract": _lean_contract(),
        "linked_witness_summary": _report_summary(WITNESS_REPORT_JSON, kind="witness"),
        "linked_merkle_summary": _report_summary(MERKLE_REPORT_JSON, kind="merkle"),
        "bound_rows": rows,
        "witness_merkle_summary": summary,
    }
    return _with_packet_hash(packet)


def _verify_bound_rows(
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

    child_frontier: dict[int, list[_ReserveState]] = {
        child_mask_id: _sorted_states(_state_set(full_dp[child_mask_id]))
        for child_mask_id in range(1, 1 << n)
    }
    expected_child_keys = {
        (child_mask_id, _state_key(state))
        for child_mask_id, states in child_frontier.items()
        for state in states
    }
    rows = list(packet.get("bound_rows", []) if packet is not None else [])
    seen_child_keys: set[tuple[int, tuple[int, int]]] = set()
    duplicate_bound_count = 0
    invalid_bound_count = 0

    for index, row in enumerate(rows):
        row_reasons: list[str] = []
        try:
            child_mask_id = int(row["child_mask_id"])
            child_state = _state_from_json(row["child_state"])
            witness_row = dict(row["witness"])
            witness_child_state = _state_from_json(witness_row["child_state"])
            parent_mask_id = int(witness_row["parent_mask_id"])
            step_bit_index = int(witness_row["step_bit_index"])
            parent_state = _state_from_json(witness_row["parent_state"])
            leaf_index = int(row["leaf_index"])
            generated_state_count = int(row["generated_state_count"])
            generated_state_root = str(row["generated_state_root"])
            proof = list(row["membership_proof"])
        except (KeyError, TypeError, ValueError):
            row_reasons.append("bound_row_malformed")
            child_mask_id = -1
            child_state = _ReserveState(-1, -1)
            witness_child_state = _ReserveState(-2, -2)
            parent_mask_id = -1
            step_bit_index = -1
            parent_state = _ReserveState(-1, -1)
            leaf_index = -1
            generated_state_count = -1
            generated_state_root = ""
            proof = []

        if row.get("case_id") != case.case_id:
            row_reasons.append("bound_case_id_mismatch")
        if witness_row.get("case_id") != case.case_id:
            row_reasons.append("witness_case_id_mismatch")
        if int(witness_row.get("child_mask_id", -1)) != child_mask_id:
            row_reasons.append("witness_child_mask_mismatch")
        if witness_child_state != child_state:
            row_reasons.append("cross_bound_child_state_mismatch")
        if child_mask_id <= 0 or child_mask_id >= (1 << n):
            row_reasons.append("bound_child_mask_out_of_range")

        expected_states = child_frontier.get(child_mask_id, [])
        expected_index_by_key = {_state_key(state): idx for idx, state in enumerate(expected_states)}
        state_key = _state_key(child_state)
        if state_key not in expected_index_by_key:
            row_reasons.append("bound_child_state_not_in_frontier")
        elif expected_index_by_key[state_key] != leaf_index:
            row_reasons.append("canonical_leaf_index_mismatch")

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
            _state_json(child_state),
            proof,
            generated_state_root,
        ):
            row_reasons.append("membership_proof_hash_mismatch")

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
            if witness_row.get("parent_quotient_digest") != _quotient_digest(
                full_dp[parent_mask_id]
            ):
                row_reasons.append("witness_parent_quotient_digest_mismatch")
        else:
            row_reasons.append("witness_parent_mask_out_of_range")

        if 0 < child_mask_id < (1 << n):
            if child_state not in set(expected_states):
                row_reasons.append("witness_child_state_not_in_child_frontier")
            if witness_row.get("child_quotient_digest") != _quotient_digest(
                full_dp[child_mask_id]
            ):
                row_reasons.append("witness_child_quotient_digest_mismatch")

        if 0 <= step_bit_index < n:
            intent = case.intents[step_bit_index]
            if witness_row.get("step_order_id") != intent.intent_id:
                row_reasons.append("witness_step_order_id_mismatch")
            generated_child = _run_suffix_from_state(
                parent_state,
                (intent,),
                _case_context(case),
            )
            if generated_child != child_state:
                row_reasons.append("witness_afterstep_mismatch")

        child_key = (child_mask_id, state_key)
        if child_key in seen_child_keys:
            duplicate_bound_count += 1
            row_reasons.append("duplicate_bound_row")
        seen_child_keys.add(child_key)

        if row_reasons:
            invalid_bound_count += 1
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
        reasons.append("missing_child_bound_row")
        child_mask_id, _state = sorted(missing_child_keys)[0]
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=child_mask_id,
            reason="missing_child_bound_row",
        )
    if extra_child_keys:
        reasons.append("extra_child_bound_row")
    if duplicate_bound_count:
        reasons.append("duplicate_bound_row")

    reasons.extend(
        _linked_report_reasons(
            packet.get("linked_witness_summary") if packet is not None else None,
            kind="witness",
        )
    )
    reasons.extend(
        _linked_report_reasons(
            packet.get("linked_merkle_summary") if packet is not None else None,
            kind="merkle",
        )
    )

    summary = _packet_summary_from_rows(rows)
    predecessor_transition_count = int(
        packet.get("witness_merkle_summary", {}).get(
            "predecessor_transition_count",
            0,
        )
    ) if packet is not None else 0
    summary.update(
        {
            "expected_child_state_count": len(expected_child_keys),
            "covered_child_state_count": len(seen_child_keys & expected_child_keys),
            "missing_child_bound_count": len(missing_child_keys),
            "extra_child_bound_count": len(extra_child_keys),
            "invalid_bound_row_count": invalid_bound_count,
            "predecessor_transition_count": predecessor_transition_count,
            "witness_transition_checks_saved": (
                predecessor_transition_count - len(rows)
            ),
            "frontier_witness_compression_ratio": round(
                predecessor_transition_count / max(len(rows), 1),
                6,
            ),
        }
    )

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("witness_merkle_summary") != summary:
            reasons.append("packet_witness_merkle_summary_mismatch")

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
    verification = _verify_bound_rows(case, full_dp=full_dp, packet=packet)
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
    missing_row["bound_rows"] = missing_row["bound_rows"][1:]
    missing_row["witness_merkle_summary"] = _packet_summary_from_rows(
        missing_row["bound_rows"]
    )
    controls.append(
        (
            "missing_child_bound_row",
            _with_packet_hash(missing_row),
            "missing_child_bound_row",
        )
    )

    bad_parent = copy.deepcopy(base_packet)
    bad_parent["bound_rows"][0]["witness"]["parent_state"]["reserve_out"] += 1
    bad_parent["witness_merkle_summary"] = _packet_summary_from_rows(
        bad_parent["bound_rows"]
    )
    controls.append(
        (
            "witness_parent_state_not_in_parent_frontier",
            _with_packet_hash(bad_parent),
            "witness_parent_state_not_in_parent_frontier",
        )
    )

    bad_afterstep = copy.deepcopy(base_packet)
    bad_afterstep["bound_rows"][0]["witness"]["step_bit_index"] = len(case.intents)
    bad_afterstep["witness_merkle_summary"] = _packet_summary_from_rows(
        bad_afterstep["bound_rows"]
    )
    controls.append(
        (
            "witness_step_bit_out_of_range",
            _with_packet_hash(bad_afterstep),
            "witness_step_bit_out_of_range",
        )
    )

    bad_root = copy.deepcopy(base_packet)
    bad_root["bound_rows"][0]["generated_state_root"] = "0" * 64
    bad_root["witness_merkle_summary"] = _packet_summary_from_rows(
        bad_root["bound_rows"]
    )
    controls.append(
        (
            "generated_state_root_mismatch",
            _with_packet_hash(bad_root),
            "generated_state_root_mismatch",
        )
    )

    bad_leaf = copy.deepcopy(base_packet)
    target_index = next(
        index
        for index, row in enumerate(bad_leaf["bound_rows"])
        if int(row["generated_state_count"]) >= 2
    )
    bad_leaf["bound_rows"][target_index]["leaf_index"] = (
        int(bad_leaf["bound_rows"][target_index]["leaf_index"]) + 1
    ) % int(bad_leaf["bound_rows"][target_index]["generated_state_count"])
    bad_leaf["witness_merkle_summary"] = _packet_summary_from_rows(
        bad_leaf["bound_rows"]
    )
    controls.append(
        (
            "canonical_leaf_index_mismatch",
            _with_packet_hash(bad_leaf),
            "canonical_leaf_index_mismatch",
        )
    )

    bad_proof = copy.deepcopy(base_packet)
    bad_proof["bound_rows"][target_index]["membership_proof"][0]["hash"] = "0" * 64
    bad_proof["witness_merkle_summary"] = _packet_summary_from_rows(
        bad_proof["bound_rows"]
    )
    controls.append(
        (
            "membership_proof_hash_mismatch",
            _with_packet_hash(bad_proof),
            "membership_proof_hash_mismatch",
        )
    )

    cross_mismatch = copy.deepcopy(base_packet)
    cross_mismatch["bound_rows"][0]["child_state"]["reserve_out"] += 1
    cross_mismatch["witness_merkle_summary"] = _packet_summary_from_rows(
        cross_mismatch["bound_rows"]
    )
    controls.append(
        (
            "cross_bound_child_state_mismatch",
            _with_packet_hash(cross_mismatch),
            "cross_bound_child_state_mismatch",
        )
    )

    duplicate = copy.deepcopy(base_packet)
    duplicate["bound_rows"].append(copy.deepcopy(duplicate["bound_rows"][0]))
    duplicate["witness_merkle_summary"] = _packet_summary_from_rows(
        duplicate["bound_rows"]
    )
    controls.append(
        (
            "duplicate_bound_row",
            _with_packet_hash(duplicate),
            "duplicate_bound_row",
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
        verification = _verify_bound_rows(
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
    bound_row_count = sum(int(row["bound_row_count"]) for row in rows)
    predecessor_transition_count = sum(
        int(row["predecessor_transition_count"]) for row in rows
    )
    return {
        "schema": "zenodex/ab_reserve_state_child_frontier_witness_merkle_search/v1",
        "source_seed": N7_SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "child_mask_count": sum(int(row["child_mask_count"]) for row in rows),
        "expected_child_state_count": sum(
            int(row["expected_child_state_count"]) for row in rows
        ),
        "bound_row_count": bound_row_count,
        "witness_count": sum(int(row["witness_count"]) for row in rows),
        "membership_count": sum(int(row["membership_count"]) for row in rows),
        "covered_child_state_count": sum(
            int(row["covered_child_state_count"]) for row in rows
        ),
        "missing_child_bound_count": sum(
            int(row["missing_child_bound_count"]) for row in rows
        ),
        "extra_child_bound_count": sum(
            int(row["extra_child_bound_count"]) for row in rows
        ),
        "invalid_bound_row_count": sum(int(row["invalid_bound_row_count"]) for row in rows),
        "duplicate_bound_row_count": sum(
            int(row["duplicate_bound_row_count"]) for row in rows
        ),
        "predecessor_transition_count": predecessor_transition_count,
        "witness_merkle_compression_ratio": round(
            predecessor_transition_count / max(bound_row_count, 1),
            6,
        ),
        "witness_transition_checks_saved": predecessor_transition_count - bound_row_count,
        "bound_rows_digest": _sha256_json([row["bound_rows_digest"] for row in rows]),
        "linked_witness_summary": _report_summary(WITNESS_REPORT_JSON, kind="witness"),
        "linked_merkle_summary": _report_summary(MERKLE_REPORT_JSON, kind="merkle"),
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
    return {
        "ok": first_hash == second_hash,
        "first_hash": first_hash,
        "second_hash": second_hash,
    }


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    ok = bool(
        search["case_count"] == TARGET_CASE_COUNT
        and search["valid_case_count"] == TARGET_CASE_COUNT
        and search["first_invalid_case"] is None
        and search["expected_child_state_count"] == 864
        and search["bound_row_count"] == 864
        and search["witness_count"] == 864
        and search["membership_count"] == 864
        and search["covered_child_state_count"] == 864
        and search["missing_child_bound_count"] == 0
        and search["extra_child_bound_count"] == 0
        and search["invalid_bound_row_count"] == 0
        and search["duplicate_bound_row_count"] == 0
        and search["predecessor_transition_count"] == 2_777
        and search["witness_transition_checks_saved"] == 1_913
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and not _linked_report_reasons(search["linked_witness_summary"], kind="witness")
        and not _linked_report_reasons(search["linked_merkle_summary"], kind="merkle")
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded n=7 host checker supports a cross-bound child-frontier "
            "proof object: each child quotient state has both a predecessor "
            "witness and a canonical-index Merkle membership proof for the same "
            "child mask and reserve state."
        ),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_witness_merkle_20260629.py"
        ),
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N7-WITNESS-MERKLE-CROSS-BIND-20260629",
            "mechanism_change": (
                "Bind each predecessor witness row to a canonical Merkle "
                "membership proof for the same child mask and child state."
            ),
            "representation_shift_used": "certificate_boundary",
            "expected_metric_delta": {
                "safety": "+rejects witness/Merkle row mismatch and root malleability",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+Merkle proof verification per child state",
                "determinism_simplicity": "+single row shape for generation and membership",
            },
            "null_hypothesis": (
                "Composing the witness and canonical-Merkle certificates into one "
                "row shape does not add detectable constraints beyond the two "
                "independent reports."
            ),
            "falsification_recipe": (
                "Mutate witness parents, step bits, Merkle roots, leaf indexes, "
                "membership hashes, cross-bound child states, duplicate rows, "
                "packet hash, and authority rails."
            ),
            "support_recipe": (
                "Verify all n=7 corpus rows, link both prior reports, assert zero "
                "missing/extra/invalid/duplicate bound rows, and assert zero "
                "accepted negative controls."
            ),
            "formal_obligations": (
                "A production-grade theorem would need Python-to-Lean refinement "
                "or a Lean-native generated-image and canonical-Merkle checker."
            ),
            "risk_modes": [
                "witness row and membership proof refer to different child states",
                "generated root is stale",
                "leaf index is noncanonical",
                "coverage witness overclaimed as no-extra generation",
                "authority leakage",
            ],
            "status": "supported_bounded",
        },
        "non_claims": [
            "This cross-bound checker is bounded to the committed n=7 randomized corpus.",
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
        "# ZenoDEX AB Reserve-State Child-Frontier Witness+Merkle Cross-Binding - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Certificate Shape",
        "",
        "```text",
        "predecessor_witness(child_mask, child_state) + canonical_merkle_membership(child_mask, child_state)",
        "  -> cross-bound child-frontier row",
        "```",
        "",
        "The checker accepts only when both proofs point at the same child mask and reserve-state quotient.",
        "",
        "## Evidence Summary",
        "",
        f"- Cases checked: `{search['case_count']}`",
        f"- Valid cases: `{search['valid_case_count']}`",
        f"- Child masks checked: `{search['child_mask_count']}`",
        f"- Expected child states: `{search['expected_child_state_count']}`",
        f"- Cross-bound rows: `{search['bound_row_count']}`",
        f"- Witness rows: `{search['witness_count']}`",
        f"- Merkle memberships: `{search['membership_count']}`",
        f"- Covered child states: `{search['covered_child_state_count']}`",
        f"- Missing bound rows: `{search['missing_child_bound_count']}`",
        f"- Extra bound rows: `{search['extra_child_bound_count']}`",
        f"- Invalid bound rows: `{search['invalid_bound_row_count']}`",
        f"- Duplicate bound rows: `{search['duplicate_bound_row_count']}`",
        f"- Baseline predecessor transitions: `{search['predecessor_transition_count']}`",
        f"- Witness/Merkle compression ratio: `{search['witness_merkle_compression_ratio']}`",
        f"- Transition checks saved: `{search['witness_transition_checks_saved']}`",
        f"- Bound rows digest: `{search['bound_rows_digest']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Linked Reports",
        "",
        "```json",
        json.dumps(
            {
                "witness": search["linked_witness_summary"],
                "merkle": search["linked_merkle_summary"],
            },
            indent=2,
            sort_keys=True,
        ),
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
    lines.extend(["", "## Case Summary", ""])
    lines.extend(
        [
            "| case | ok | bound rows | predecessor transitions | ratio | digest |",
            "| --- | --- | ---: | ---: | ---: | --- |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            "| "
            f"`{row['case_id']}` | `{row['ok']}` | `{row['bound_row_count']}` | "
            f"`{row['predecessor_transition_count']}` | `{row['frontier_witness_compression_ratio']}` | "
            f"`{row['bound_rows_digest']}` |"
        )
    lines.extend(["", "## Hypothesis Card", "", "```json"])
    lines.append(json.dumps(report["hypothesis_card"], indent=2, sort_keys=True))
    lines.extend(["```", "", "## Non-Claims", ""])
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
