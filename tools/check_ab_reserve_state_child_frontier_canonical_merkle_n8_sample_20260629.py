#!/usr/bin/env python3
"""Check sampled n=8 canonical Merkle roots for child frontiers.

This research-only checker extends the n=7 canonical-index Merkle proof-object
shape to the deterministic n=8 sample. Each sampled child-mask frontier receives
a canonical generated-state root and one count-aware membership proof per
sampled child quotient state.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools import check_ab_reserve_state_child_frontier_canonical_merkle_20260629 as merkle  # noqa: E402
from tools.check_ab_reserve_state_child_frontier_n8_sample_20260629 import (  # noqa: E402
    BIT_COUNT,
    REPORT_JSON as FRONTIER_N8_REPORT_JSON,
    SEED,
    TARGET_CASE_COUNT,
    _lean_contract as _n8_frontier_lean_contract,
    _n8_cases,
    _sample_plan,
    _sampled_child_mask_ids,
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
from tools.check_ab_strict_zero_min_reserve_state_quotient_certificate import _case_context  # noqa: E402
from tools.check_ab_strict_zero_min_subset_induction_witness import _clone_full_dp  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_CANONICAL_MERKLE_N8_SAMPLE_20260629.md"
)

PACKET_SCHEMA = (
    "zenodex.ab_reserve_state_child_frontier_canonical_merkle_n8_sample_packet.v1"
)
REPORT_SCHEMA = (
    "zenodex.ab_reserve_state_child_frontier_canonical_merkle_n8_sample_report.v1"
)
SEARCH_SCHEMA = (
    "zenodex/ab_reserve_state_child_frontier_canonical_merkle_n8_sample_search/v1"
)
SCOPE = "n8_sampled_zero_min_child_frontier_canonical_merkle"
EXPECTED_NEGATIVE_CONTROL_COUNT = 9


def _lean_contract() -> dict[str, str]:
    return {
        **_n8_frontier_lean_contract(),
        "host_merkle_shape": (
            "canonical sorted leaf-index Merkle root per sampled child quotient frontier"
        ),
    }


def _linked_frontier_summary() -> dict[str, Any]:
    if not FRONTIER_N8_REPORT_JSON.exists():
        return {
            "path": str(FRONTIER_N8_REPORT_JSON.relative_to(REPO_ROOT)),
            "available": False,
        }
    report = json.loads(FRONTIER_N8_REPORT_JSON.read_text(encoding="utf-8"))
    search = report.get("search", {})
    return {
        "path": str(FRONTIER_N8_REPORT_JSON.relative_to(REPO_ROOT)),
        "available": True,
        "ok": bool(report.get("ok")),
        "schema": report.get("schema"),
        "frontier_rows_digest": search.get("frontier_rows_digest"),
        "sampled_child_mask_count": int(search.get("sampled_child_mask_count", -1)),
        "sampled_child_state_count": int(search.get("sampled_child_state_count", -1)),
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
    if int(summary.get("sampled_child_state_count", -1)) != int(
        summary.get("generated_state_count", -2)
    ):
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
    if packet.get("sampled_n8_bound") is not True:
        reasons.append("sampled_n8_bound_missing")
    if packet.get("canonical_merkle_bound") is not True:
        reasons.append("canonical_merkle_bound_missing")
    if packet.get("canonical_leaf_index_bound") is not True:
        reasons.append("canonical_leaf_index_bound_missing")
    if packet.get("count_aware_membership_bound") is not True:
        reasons.append("count_aware_membership_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("sample_plan") != _sample_plan(BIT_COUNT):
        reasons.append("packet_sample_plan_mismatch")
    if packet.get("sampled_child_mask_ids") != _sampled_child_mask_ids(BIT_COUNT):
        reasons.append("packet_sampled_child_mask_ids_mismatch")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("linked_frontier_summary") != _linked_frontier_summary():
        reasons.append("linked_frontier_summary_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _frontier_rows_for_sample(
    *,
    full_dp: list[list[_HostRecord]],
) -> list[dict[str, Any]]:
    return [
        merkle._frontier_row_from_states(
            child_mask_id=child_mask_id,
            states=_state_set(full_dp[child_mask_id]),
        )
        for child_mask_id in _sampled_child_mask_ids(BIT_COUNT)
    ]


def _sampled_case_summary_from_rows(rows: list[Mapping[str, Any]]) -> dict[str, Any]:
    base = merkle._case_summary_from_rows(rows)
    return {
        "sampled_child_mask_count": base["child_mask_count"],
        "frontier_root_count": base["frontier_root_count"],
        "sampled_child_state_count": base["child_state_count"],
        "membership_count": base["membership_count"],
        "max_leaf_count": base["max_leaf_count"],
        "frontier_roots_digest": base["frontier_roots_digest"],
        "membership_rows_digest": base["membership_rows_digest"],
    }


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
) -> dict[str, Any]:
    if full_dp is None:
        full_dp = _full_state_records(case.intents, _case_context(case))
    frontier_rows = _frontier_rows_for_sample(full_dp=full_dp)
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "sampled_n8_bound": True,
        "canonical_merkle_bound": True,
        "canonical_leaf_index_bound": True,
        "count_aware_membership_bound": True,
        "reserve_state_only_bound": True,
        "sample_plan": _sample_plan(len(case.intents)),
        "sampled_child_mask_ids": _sampled_child_mask_ids(len(case.intents)),
        "lean_contract": _lean_contract(),
        "linked_frontier_summary": _linked_frontier_summary(),
        "frontier_rows": frontier_rows,
        "canonical_merkle_summary": _sampled_case_summary_from_rows(frontier_rows),
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
    if n != BIT_COUNT:
        reasons.append("bit_count_out_of_scope")
    if not _case_has_zero_min_amount_out(case):
        reasons.append("nonzero_min_amount_out_out_of_scope")

    sampled_masks = set(_sampled_child_mask_ids(n))
    expected_by_mask = {
        child_mask_id: _sorted_states(_state_set(full_dp[child_mask_id]))
        for child_mask_id in sampled_masks
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
            reasons.append("frontier_child_mask_not_sampled")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=child_mask_id,
                reason="frontier_child_mask_not_sampled",
            )
            continue
        expected_state_rows = merkle._state_rows(expected_states)
        expected_root = merkle._merkle_root(expected_states)
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
                state_key = merkle._state_key_from_json(child_state)
                leaf_index = int(member["leaf_index"])
                proof = list(member["proof"])
            except (KeyError, TypeError, ValueError):
                invalid_membership_count += 1
                reasons.append("membership_row_malformed")
                continue
            if state_key not in expected_index_by_key:
                extra_membership_count += 1
                reasons.append("membership_child_state_not_in_sampled_frontier")
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
            expected_sides = merkle._expected_sides(leaf_index, len(expected_states))
            if expected_sides is None:
                invalid_membership_count += 1
                reasons.append("membership_leaf_index_out_of_range")
            elif [step.get("side") for step in proof] != expected_sides:
                invalid_membership_count += 1
                reasons.append("membership_proof_shape_mismatch")
            elif not merkle._verify_membership_hash(
                child_state,
                proof,
                str(row.get("generated_state_root")),
            ):
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

    missing_frontier_masks = sampled_masks - set(rows_by_mask)
    extra_frontier_masks = set(rows_by_mask) - sampled_masks
    if missing_frontier_masks:
        reasons.append("missing_frontier_row")
    if extra_frontier_masks:
        reasons.append("extra_frontier_row")

    reasons.extend(
        _linked_frontier_reasons(
            packet.get("linked_frontier_summary") if packet is not None else None
        )
    )

    expected_rows = [
        merkle._frontier_row_from_states(child_mask_id=mask, states=states)
        for mask, states in sorted(expected_by_mask.items())
    ]
    expected_summary = _sampled_case_summary_from_rows(expected_rows)
    actual_summary = _sampled_case_summary_from_rows(rows) if rows else {
        "sampled_child_mask_count": 0,
        "frontier_root_count": 0,
        "sampled_child_state_count": 0,
        "membership_count": 0,
        "max_leaf_count": 0,
        "frontier_roots_digest": _sha256_json([]),
        "membership_rows_digest": _sha256_json([]),
    }
    summary = {
        **actual_summary,
        "expected_sampled_child_mask_count": len(expected_by_mask),
        "expected_sampled_child_state_count": sum(
            len(states) for states in expected_by_mask.values()
        ),
        "covered_sampled_child_state_count": (
            actual_summary["membership_count"] - extra_membership_count
        ),
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


def _negative_controls(cases: list[Any]) -> list[dict[str, Any]]:
    case = cases[1]
    full_dp = _full_state_records(case.intents, _case_context(case))
    base_packet = build_case_packet(case, full_dp=full_dp)
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    bad_sample = copy.deepcopy(base_packet)
    bad_sample["sampled_n8_bound"] = False
    controls.append(
        ("sampled_n8_bound_missing", _with_packet_hash(bad_sample), "sampled_n8_bound_missing")
    )

    bad_plan = copy.deepcopy(base_packet)
    bad_plan["sample_plan"]["bit_count"] += 1
    controls.append(
        ("packet_sample_plan_mismatch", _with_packet_hash(bad_plan), "packet_sample_plan_mismatch")
    )

    stale_root = copy.deepcopy(base_packet)
    stale_root["frontier_rows"][0]["generated_state_root"] = "0" * 64
    stale_root["canonical_merkle_summary"] = _sampled_case_summary_from_rows(
        stale_root["frontier_rows"]
    )
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
    permuted["frontier_rows"][target_index] = merkle._frontier_row_from_states(
        child_mask_id=child_mask_id,
        states=states,
        generated_order=list(reversed(states)),
    )
    permuted["canonical_merkle_summary"] = _sampled_case_summary_from_rows(
        permuted["frontier_rows"]
    )
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
    missing_member["canonical_merkle_summary"] = _sampled_case_summary_from_rows(
        missing_member["frontier_rows"]
    )
    controls.append(
        (
            "missing_membership_proof",
            _with_packet_hash(missing_member),
            "missing_membership_proof",
        )
    )

    bad_proof = copy.deepcopy(base_packet)
    proof_target = next(
        index
        for index, row in enumerate(bad_proof["frontier_rows"])
        if row["membership_rows"] and row["membership_rows"][0]["proof"]
    )
    bad_proof["frontier_rows"][proof_target]["membership_rows"][0]["proof"][0][
        "hash"
    ] = "0" * 64
    bad_proof["frontier_rows"][proof_target]["membership_rows_digest"] = _sha256_json(
        bad_proof["frontier_rows"][proof_target]["membership_rows"]
    )
    bad_proof["canonical_merkle_summary"] = _sampled_case_summary_from_rows(
        bad_proof["frontier_rows"]
    )
    controls.append(
        (
            "membership_proof_hash_mismatch",
            _with_packet_hash(bad_proof),
            "membership_proof_hash_mismatch",
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
        ("authority_effect_present", _with_packet_hash(bad_authority), "authority_effect_present")
    )

    output: list[dict[str, Any]] = []
    for mutation_id, packet, expected_reason in controls:
        verification = _verify_case_packet(
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
        "frontier_root_count": sum(int(row["frontier_root_count"]) for row in rows),
        "sampled_child_state_count": sum(int(row["sampled_child_state_count"]) for row in rows),
        "membership_count": sum(int(row["membership_count"]) for row in rows),
        "expected_sampled_child_mask_count": sum(
            int(row["expected_sampled_child_mask_count"]) for row in rows
        ),
        "expected_sampled_child_state_count": sum(
            int(row["expected_sampled_child_state_count"]) for row in rows
        ),
        "covered_sampled_child_state_count": sum(
            int(row["covered_sampled_child_state_count"]) for row in rows
        ),
        "missing_frontier_row_count": sum(int(row["missing_frontier_row_count"]) for row in rows),
        "extra_frontier_row_count": sum(int(row["extra_frontier_row_count"]) for row in rows),
        "duplicate_frontier_row_count": sum(
            int(row["duplicate_frontier_row_count"]) for row in rows
        ),
        "missing_membership_proof_count": sum(
            int(row["missing_membership_proof_count"]) for row in rows
        ),
        "extra_membership_proof_count": sum(
            int(row["extra_membership_proof_count"]) for row in rows
        ),
        "invalid_membership_proof_count": sum(
            int(row["invalid_membership_proof_count"]) for row in rows
        ),
        "root_mismatch_count": sum(int(row["root_mismatch_count"]) for row in rows),
        "max_leaf_count": max((int(row["max_leaf_count"]) for row in rows), default=0),
        "frontier_roots_digest": _sha256_json(
            [row["frontier_roots_digest"] for row in rows]
        ),
        "membership_rows_digest": _sha256_json(
            [row["membership_rows_digest"] for row in rows]
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
        and search["sampled_child_mask_count"] == search["frontier_root_count"]
        and search["sampled_child_state_count"] == search["membership_count"]
        and search["expected_sampled_child_state_count"]
        == search["covered_sampled_child_state_count"]
        and search["missing_frontier_row_count"] == 0
        and search["extra_frontier_row_count"] == 0
        and search["duplicate_frontier_row_count"] == 0
        and search["missing_membership_proof_count"] == 0
        and search["extra_membership_proof_count"] == 0
        and search["invalid_membership_proof_count"] == 0
        and search["root_mismatch_count"] == 0
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
            "A bounded deterministic n=8 sample supports canonical-index Merkle "
            "membership for sampled reserve-state child frontiers."
        ),
        "authority_boundary": (
            "Research-only certificate-compression evidence; no settlement, state-root, "
            "production, routing, matching, pool-mutation, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629.py"
        ),
        "non_claims": [
            "This canonical Merkle checker is bounded to the deterministic n=8 sample, not exhaustive n=8 coverage.",
            "This checker covers only sampled zero-min exact-in cases and sampled child masks.",
            "This checker does not prove Python-to-Lean refinement.",
            "This checker does not prove child-frontier generation in Lean.",
            "This checker does not define canonical tie order beyond reserve-state leaf ordering.",
            "This checker does not cover nonzero min_amount_out behavior.",
            "No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Reserve-State Child-Frontier Canonical Merkle n=8 Sample - 2026-06-29",
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
        f"- Sampled child masks checked: `{search['sampled_child_mask_count']}`",
        f"- Frontier roots: `{search['frontier_root_count']}`",
        f"- Sampled child states: `{search['sampled_child_state_count']}`",
        f"- Membership proofs: `{search['membership_count']}`",
        f"- Missing frontier rows: `{search['missing_frontier_row_count']}`",
        f"- Extra frontier rows: `{search['extra_frontier_row_count']}`",
        f"- Invalid membership proofs: `{search['invalid_membership_proof_count']}`",
        f"- Root mismatches: `{search['root_mismatch_count']}`",
        f"- Max leaf count: `{search['max_leaf_count']}`",
        f"- Frontier roots digest: `{search['frontier_roots_digest']}`",
        f"- Membership rows digest: `{search['membership_rows_digest']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Linked n=8 Frontier Equality Report",
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
        "## Sample Plan",
        "",
        "```json",
        json.dumps(search["sample_plan"], indent=2, sort_keys=True),
        "```",
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
            "| case | ok | roots | memberships | max leaves | membership digest |",
            "| --- | --- | ---: | ---: | ---: | --- |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            "| `{case_id}` | `{ok}` | `{frontier_root_count}` | `{membership_count}` | "
            "`{max_leaf_count}` | `{digest}` |".format(
                case_id=row["case_id"],
                ok=row["ok"],
                frontier_root_count=row["frontier_root_count"],
                membership_count=row["membership_count"],
                max_leaf_count=row["max_leaf_count"],
                digest=row["membership_rows_digest"],
            )
        )
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
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
