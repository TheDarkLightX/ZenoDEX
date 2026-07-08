#!/usr/bin/env python3
"""Check a compressed AB child-frontier transition-group certificate.

The source bidirectional transition certificate carries one row per predecessor
afterStep transition. This checker compresses that object to one row per
generated child state. Each compressed row carries the count and digest of all
transitions that generate the child, plus one representative executable
transition and the canonical Merkle membership proof for the child state.
"""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools import check_ab_reserve_state_child_frontier_bidirectional_transition_20260629 as bidir  # noqa: E402
from tools import check_ab_reserve_state_child_frontier_canonical_merkle_20260629 as merkle  # noqa: E402

OUT_DIR = REPO_ROOT / "generated" / "zenodex_ab_child_frontier_transition_group_compression_20260629"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_AB_CHILD_FRONTIER_TRANSITION_GROUP_COMPRESSION_20260629.md"

PACKET_SCHEMA = "zenodex.ab_child_frontier_transition_group_compression_packet.v1"
REPORT_SCHEMA = "zenodex.ab_child_frontier_transition_group_compression_report.v1"
SEARCH_SCHEMA = "zenodex/ab_child_frontier_transition_group_compression_search/v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_transition_group_compression"
AUTHORITY_BOUNDARY = (
    "research evidence only; no settlement, state-root, production, governance, "
    "routing, matching, or pool-mutation authority"
)

SOURCE_BIDIRECTIONAL_REPORT = (
    "generated/zenodex_ab_reserve_state_child_frontier_bidirectional_transition_20260629/report.json"
)
EXPECTED_SOURCE_REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_bidirectional_transition_report.v1"
EXPECTED_SOURCE_REPORT_HASH = "8aecb36a829164725f85ba8e4360d17fb0fdf032e4cafd082349189b8c81b883"
EXPECTED_SOURCE_TRANSITION_ROWS_DIGEST = "fccc26b63521b510776546e4663cecabcf58849af42bcda799484bf092a81f82"
EXPECTED_SOURCE_REPLAY_HASH = "54e80016a0c0dc4eb629d22b43265091b3b1c4dc75324320107b17dbd42668b7"
EXPECTED_CASE_COUNT = 4
EXPECTED_TRANSITION_ROW_COUNT = 2_777
EXPECTED_GENERATED_CHILD_COUNT = 864
EXPECTED_COMPRESSED_ROW_COUNT = 864
EXPECTED_NEGATIVE_CONTROL_COUNT = 8


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256_json(obj: Any) -> str:
    return hashlib.sha256(
        json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _state_key_from_json(state: Mapping[str, Any]) -> tuple[int, int]:
    return (int(state["processed_reserve_in"]), int(state["reserve_out"]))


def _transition_key_json(
    key: tuple[int, int, int, tuple[int, int], tuple[int, int]]
) -> dict[str, Any]:
    child_mask_id, parent_mask_id, step_bit_index, parent_state, generated_child_state = key
    return {
        "child_mask_id": int(child_mask_id),
        "parent_mask_id": int(parent_mask_id),
        "step_bit_index": int(step_bit_index),
        "parent_state": {
            "processed_reserve_in": int(parent_state[0]),
            "reserve_out": int(parent_state[1]),
        },
        "generated_child_state": {
            "processed_reserve_in": int(generated_child_state[0]),
            "reserve_out": int(generated_child_state[1]),
        },
    }


def _group_key(row: Mapping[str, Any]) -> tuple[str, int, tuple[int, int]]:
    return (
        str(row["case_id"]),
        int(row["child_mask_id"]),
        _state_key_from_json(row["generated_child_state"]),
    )


def _group_transition_digest(
    keys: list[tuple[int, int, int, tuple[int, int], tuple[int, int]]]
) -> str:
    return _sha256_json([_transition_key_json(key) for key in sorted(keys)])


def _group_rows_by_generated_child(
    rows: list[Mapping[str, Any]],
) -> dict[tuple[str, int, tuple[int, int]], list[Mapping[str, Any]]]:
    groups: dict[tuple[str, int, tuple[int, int]], list[Mapping[str, Any]]] = {}
    for row in rows:
        groups.setdefault(_group_key(row), []).append(row)
    return groups


def _source_report() -> dict[str, Any]:
    return _read_json(REPO_ROOT / SOURCE_BIDIRECTIONAL_REPORT)


def _source_report_summary() -> dict[str, Any]:
    report = _source_report()
    search = report.get("search", {})
    replay = report.get("deterministic_replay", {})
    return {
        "path": SOURCE_BIDIRECTIONAL_REPORT,
        "schema": report.get("schema"),
        "sha256": _sha256(REPO_ROOT / SOURCE_BIDIRECTIONAL_REPORT),
        "ok": bool(report.get("ok")),
        "transition_row_count": int(search.get("transition_row_count", -1)),
        "unique_generated_child_count": int(search.get("unique_generated_child_count", -1)),
        "transition_rows_digest": search.get("transition_rows_digest"),
        "deterministic_replay_hash": replay.get("first_hash"),
    }


def _source_report_reasons(summary: Mapping[str, Any]) -> list[str]:
    reasons: list[str] = []
    if summary.get("schema") != EXPECTED_SOURCE_REPORT_SCHEMA:
        reasons.append("source_report_schema_mismatch")
    if summary.get("sha256") != EXPECTED_SOURCE_REPORT_HASH:
        reasons.append("source_report_hash_mismatch")
    if summary.get("ok") is not True:
        reasons.append("source_report_not_ok")
    if summary.get("transition_row_count") != EXPECTED_TRANSITION_ROW_COUNT:
        reasons.append("source_transition_row_count_mismatch")
    if summary.get("unique_generated_child_count") != EXPECTED_GENERATED_CHILD_COUNT:
        reasons.append("source_generated_child_count_mismatch")
    if summary.get("transition_rows_digest") != EXPECTED_SOURCE_TRANSITION_ROWS_DIGEST:
        reasons.append("source_transition_rows_digest_mismatch")
    if summary.get("deterministic_replay_hash") != EXPECTED_SOURCE_REPLAY_HASH:
        reasons.append("source_replay_hash_mismatch")
    return reasons


def _compressed_rows_from_transition_rows(
    case: Any,
    *,
    full_dp: list[list[bidir._HostRecord]],
    transition_rows: list[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    groups = _group_rows_by_generated_child(transition_rows)
    rows: list[dict[str, Any]] = []
    for (case_id, child_mask_id, generated_child_key), group_rows in sorted(groups.items()):
        transition_keys = [bidir._transition_key(row) for row in group_rows]
        representative = min(group_rows, key=bidir._transition_key)
        child_states = bidir._sorted_states(bidir._state_set(full_dp[child_mask_id]))
        leaf_index = next(
            index
            for index, state in enumerate(child_states)
            if bidir._state_key(state) == generated_child_key
        )
        rows.append(
            {
                "case_id": case_id,
                "child_mask_id": int(child_mask_id),
                "generated_child_state": dict(representative["generated_child_state"]),
                "transition_group_count": len(group_rows),
                "transition_group_digest": _group_transition_digest(transition_keys),
                "representative_parent_mask_id": int(representative["parent_mask_id"]),
                "representative_step_bit_index": int(representative["step_bit_index"]),
                "representative_step_order_id": representative["step_order_id"],
                "representative_parent_state": dict(representative["parent_state"]),
                "child_quotient_digest": representative["child_quotient_digest"],
                "parent_quotient_digest": representative["parent_quotient_digest"],
                "generated_state_count": int(representative["generated_state_count"]),
                "generated_state_root": representative["generated_state_root"],
                "leaf_index": int(leaf_index),
                "membership_proof": list(representative["membership_proof"]),
            }
        )
    return rows


def _compressed_summary(
    *,
    transition_rows: list[Mapping[str, Any]],
    compressed_rows: list[Mapping[str, Any]],
) -> dict[str, Any]:
    transition_bytes = len(
        json.dumps(transition_rows, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )
    compressed_bytes = len(
        json.dumps(compressed_rows, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )
    transition_count = len(transition_rows)
    compressed_count = len(compressed_rows)
    saved_rows = transition_count - compressed_count
    saved_bytes = transition_bytes - compressed_bytes
    return {
        "source_transition_row_count": transition_count,
        "compressed_row_count": compressed_count,
        "row_reduction_count": saved_rows,
        "row_reduction_ratio": round(saved_rows / max(transition_count, 1), 6),
        "source_transition_json_bytes": transition_bytes,
        "compressed_json_bytes": compressed_bytes,
        "byte_reduction_count": saved_bytes,
        "byte_reduction_ratio": round(saved_bytes / max(transition_bytes, 1), 6),
        "transition_groups_digest": _sha256_json(
            [row["transition_group_digest"] for row in compressed_rows]
        ),
        "compressed_rows_digest": _sha256_json(compressed_rows),
    }


def _packet_compression_summary(
    *,
    transition_rows: list[Mapping[str, Any]],
    compressed_rows: list[Mapping[str, Any]],
) -> dict[str, Any]:
    summary = _compressed_summary(
        transition_rows=transition_rows,
        compressed_rows=compressed_rows,
    )
    summary.update(
        {
            "expected_group_count": len(compressed_rows),
            "covered_group_count": len(compressed_rows),
            "missing_group_count": 0,
            "extra_group_count": 0,
            "invalid_compressed_row_count": 0,
            "duplicate_group_count": 0,
        }
    )
    return summary


def build_case_packet(
    case: Any,
    *,
    full_dp: list[list[bidir._HostRecord]] | None = None,
) -> dict[str, Any]:
    if full_dp is None:
        full_dp = bidir._full_state_records(case.intents, bidir._case_context(case))
    transition_rows = bidir._build_transition_rows(case, full_dp=full_dp)
    compressed_rows = _compressed_rows_from_transition_rows(
        case,
        full_dp=full_dp,
        transition_rows=transition_rows,
    )
    packet = {
        "schema": PACKET_SCHEMA,
        **bidir._case_summary_inputs(case),
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "transition_group_compression_bound": True,
        "generated_image_digest_bound": True,
        "representative_transition_bound": True,
        "source_bidirectional_report": _source_report_summary(),
        "compression_summary": _packet_compression_summary(
            transition_rows=transition_rows,
            compressed_rows=compressed_rows,
        ),
        "compressed_transition_groups": compressed_rows,
    }
    return bidir._with_packet_hash(packet)


def _packet_rail_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["transition_group_packet_missing"]
    reasons: list[str] = []
    expected_hash = bidir._packet_hash({k: v for k, v in packet.items() if k != "packet_hash"})
    if packet.get("packet_hash") != expected_hash:
        reasons.append("packet_hash_mismatch")
    if packet.get("schema") != PACKET_SCHEMA:
        reasons.append("packet_schema_mismatch")
    if packet.get("scope") != SCOPE:
        reasons.append("scope_mismatch")
    if packet.get("authority_boundary") != AUTHORITY_BOUNDARY:
        reasons.append("authority_boundary_mismatch")
    if packet.get("packet_hash_bound") is not True:
        reasons.append("packet_hash_bound_missing")
    if packet.get("no_authority_effect") is not True:
        reasons.append("authority_effect_present")
    if packet.get("transition_group_compression_bound") is not True:
        reasons.append("transition_group_compression_bound_missing")
    if packet.get("generated_image_digest_bound") is not True:
        reasons.append("generated_image_digest_bound_missing")
    if packet.get("representative_transition_bound") is not True:
        reasons.append("representative_transition_bound_missing")
    reasons.extend(_source_report_reasons(packet.get("source_bidirectional_report", {})))
    return reasons


def _verify_compressed_packet(
    case: Any,
    *,
    full_dp: list[list[bidir._HostRecord]],
    packet: Mapping[str, Any] | None,
) -> dict[str, Any]:
    reasons = _packet_rail_reasons(packet)
    first_failure: dict[str, Any] | None = None
    transition_rows = bidir._build_transition_rows(case, full_dp=full_dp)
    expected_groups = _group_rows_by_generated_child(transition_rows)
    expected_group_digests = {
        key: _group_transition_digest([bidir._transition_key(row) for row in rows])
        for key, rows in expected_groups.items()
    }
    expected_group_counts = {key: len(rows) for key, rows in expected_groups.items()}

    compressed_rows = list(packet.get("compressed_transition_groups", []) if packet is not None else [])
    seen_groups: set[tuple[str, int, tuple[int, int]]] = set()
    invalid_row_count = 0
    duplicate_group_count = 0
    compressed_group_keys: set[tuple[str, int, tuple[int, int]]] = set()

    for index, row in enumerate(compressed_rows):
        row_reasons: list[str] = []
        try:
            case_id = str(row["case_id"])
            child_mask_id = int(row["child_mask_id"])
            generated_child_state = bidir._state_from_json(row["generated_child_state"])
            parent_mask_id = int(row["representative_parent_mask_id"])
            step_bit_index = int(row["representative_step_bit_index"])
            parent_state = bidir._state_from_json(row["representative_parent_state"])
            group_count = int(row["transition_group_count"])
            group_digest = str(row["transition_group_digest"])
            leaf_index = int(row["leaf_index"])
            generated_state_count = int(row["generated_state_count"])
            generated_state_root = str(row["generated_state_root"])
            proof = list(row["membership_proof"])
        except (KeyError, TypeError, ValueError):
            row_reasons.append("compressed_row_malformed")
            case_id = ""
            child_mask_id = -1
            generated_child_state = bidir._ReserveState(-1, -1)
            parent_mask_id = -1
            step_bit_index = -1
            parent_state = bidir._ReserveState(-1, -1)
            group_count = -1
            group_digest = ""
            leaf_index = -1
            generated_state_count = -1
            generated_state_root = ""
            proof = []

        group_key = (case_id, child_mask_id, bidir._state_key(generated_child_state))
        compressed_group_keys.add(group_key)
        if group_key in seen_groups:
            duplicate_group_count += 1
            row_reasons.append("duplicate_generated_image_witness")
        seen_groups.add(group_key)

        if case_id != case.case_id:
            row_reasons.append("case_id_mismatch")
        if group_key not in expected_groups:
            row_reasons.append("extra_generated_image_witness")
        else:
            if group_count != expected_group_counts[group_key]:
                row_reasons.append("transition_group_count_mismatch")
            if group_digest != expected_group_digests[group_key]:
                row_reasons.append("transition_group_digest_mismatch")

        n = len(case.intents)
        if child_mask_id <= 0 or child_mask_id >= (1 << n):
            row_reasons.append("child_mask_out_of_range")
        if step_bit_index < 0 or step_bit_index >= n:
            row_reasons.append("transition_step_bit_out_of_range")
        elif not (child_mask_id & (1 << step_bit_index)):
            row_reasons.append("transition_step_not_in_child_mask")
        elif parent_mask_id != (child_mask_id ^ (1 << step_bit_index)):
            row_reasons.append("transition_parent_mask_mismatch")

        if 0 <= parent_mask_id < (1 << n):
            if parent_state not in bidir._state_set(full_dp[parent_mask_id]):
                row_reasons.append("transition_parent_state_not_in_parent_frontier")
            if row.get("parent_quotient_digest") != bidir._quotient_digest(full_dp[parent_mask_id]):
                row_reasons.append("transition_parent_quotient_digest_mismatch")
        else:
            row_reasons.append("transition_parent_mask_out_of_range")

        if 0 < child_mask_id < (1 << n):
            child_states = bidir._sorted_states(bidir._state_set(full_dp[child_mask_id]))
            if row.get("child_quotient_digest") != bidir._quotient_digest(full_dp[child_mask_id]):
                row_reasons.append("transition_child_quotient_digest_mismatch")
            expected_index_by_key = {
                bidir._state_key(state): idx for idx, state in enumerate(child_states)
            }
            generated_key = bidir._state_key(generated_child_state)
            if generated_key not in expected_index_by_key:
                row_reasons.append("generated_child_not_in_child_frontier")
            elif expected_index_by_key[generated_key] != leaf_index:
                row_reasons.append("canonical_leaf_index_mismatch")
            if generated_state_count != len(child_states):
                row_reasons.append("generated_state_count_mismatch")
            if child_states and generated_state_root != merkle._merkle_root(child_states):
                row_reasons.append("generated_state_root_mismatch")
            expected_sides = merkle._expected_sides(leaf_index, len(child_states))
            if expected_sides is None:
                row_reasons.append("membership_leaf_index_out_of_range")
            elif [step.get("side") for step in proof] != expected_sides:
                row_reasons.append("membership_proof_shape_mismatch")
            elif not merkle._verify_membership_hash(
                bidir._state_json(generated_child_state),
                proof,
                generated_state_root,
            ):
                row_reasons.append("membership_proof_hash_mismatch")

        if 0 <= step_bit_index < n:
            intent = case.intents[step_bit_index]
            if row.get("representative_step_order_id") != intent.intent_id:
                row_reasons.append("transition_step_order_id_mismatch")
            expected_child = bidir._run_suffix_from_state(
                parent_state,
                (intent,),
                bidir._case_context(case),
            )
            if expected_child != generated_child_state:
                row_reasons.append("afterstep_generated_child_mismatch")

        if row_reasons:
            invalid_row_count += 1
            reasons.extend(row_reasons)
            first_failure = bidir._new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=child_mask_id,
                reason=row_reasons[0],
                detail={"row_index": index},
            )

    missing_groups = set(expected_groups) - compressed_group_keys
    extra_groups = compressed_group_keys - set(expected_groups)
    if missing_groups:
        reasons.append("missing_generated_image_witness")
        first_missing = sorted(missing_groups)[0]
        first_failure = bidir._new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=int(first_missing[1]),
            reason="missing_generated_image_witness",
        )
    if extra_groups:
        reasons.append("extra_generated_image_witness")
    if duplicate_group_count:
        reasons.append("duplicate_generated_image_witness")

    summary = _compressed_summary(
        transition_rows=transition_rows,
        compressed_rows=compressed_rows,
    )
    summary.update(
        {
            "expected_group_count": len(expected_groups),
            "covered_group_count": len(compressed_group_keys & set(expected_groups)),
            "missing_group_count": len(missing_groups),
            "extra_group_count": len(extra_groups),
            "invalid_compressed_row_count": invalid_row_count,
            "duplicate_group_count": duplicate_group_count,
        }
    )
    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != len(case.intents):
            reasons.append("packet_bit_count_mismatch")
        if packet.get("compression_summary") != summary:
            reasons.append("packet_compression_summary_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "case_id": case.case_id,
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "first_failure": first_failure,
        "bit_count": len(case.intents),
        "fee_bps": int(case.pool.fee_bps),
        "pattern": case.pattern,
        **summary,
    }


def verify_case(case: Any) -> dict[str, Any]:
    full_dp = bidir._full_state_records(case.intents, bidir._case_context(case))
    packet = build_case_packet(case, full_dp=full_dp)
    verification = _verify_compressed_packet(case, full_dp=full_dp, packet=packet)
    return verification | {"packet_hash": packet["packet_hash"]}


def _negative_controls(cases: list[Any]) -> list[dict[str, Any]]:
    case = cases[1]
    full_dp = bidir._full_state_records(case.intents, bidir._case_context(case))
    base_packet = build_case_packet(case, full_dp=full_dp)
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    missing_row = copy.deepcopy(base_packet)
    missing_row["compressed_transition_groups"] = missing_row["compressed_transition_groups"][1:]
    missing_row["compression_summary"] = _packet_compression_summary(
        transition_rows=bidir._build_transition_rows(case, full_dp=full_dp),
        compressed_rows=missing_row["compressed_transition_groups"],
    )
    controls.append(
        (
            "missing_generated_image_witness",
            bidir._with_packet_hash(missing_row),
            "missing_generated_image_witness",
        )
    )

    extra_row = copy.deepcopy(base_packet)
    new_row = copy.deepcopy(extra_row["compressed_transition_groups"][0])
    new_row["generated_child_state"]["reserve_out"] += 1
    extra_row["compressed_transition_groups"].append(new_row)
    extra_row["compression_summary"] = _packet_compression_summary(
        transition_rows=bidir._build_transition_rows(case, full_dp=full_dp),
        compressed_rows=extra_row["compressed_transition_groups"],
    )
    controls.append(
        (
            "extra_generated_image_witness",
            bidir._with_packet_hash(extra_row),
            "extra_generated_image_witness",
        )
    )

    bad_group_count = copy.deepcopy(base_packet)
    bad_group_count["compressed_transition_groups"][0]["transition_group_count"] += 1
    bad_group_count["compression_summary"] = _packet_compression_summary(
        transition_rows=bidir._build_transition_rows(case, full_dp=full_dp),
        compressed_rows=bad_group_count["compressed_transition_groups"],
    )
    controls.append(
        (
            "transition_group_count_mismatch",
            bidir._with_packet_hash(bad_group_count),
            "transition_group_count_mismatch",
        )
    )

    bad_group_digest = copy.deepcopy(base_packet)
    bad_group_digest["compressed_transition_groups"][0]["transition_group_digest"] = "0" * 64
    bad_group_digest["compression_summary"] = _packet_compression_summary(
        transition_rows=bidir._build_transition_rows(case, full_dp=full_dp),
        compressed_rows=bad_group_digest["compressed_transition_groups"],
    )
    controls.append(
        (
            "transition_group_digest_mismatch",
            bidir._with_packet_hash(bad_group_digest),
            "transition_group_digest_mismatch",
        )
    )

    bad_parent = copy.deepcopy(base_packet)
    bad_parent["compressed_transition_groups"][0]["representative_parent_state"]["reserve_out"] += 1
    bad_parent["compression_summary"] = _packet_compression_summary(
        transition_rows=bidir._build_transition_rows(case, full_dp=full_dp),
        compressed_rows=bad_parent["compressed_transition_groups"],
    )
    controls.append(
        (
            "transition_parent_state_not_in_parent_frontier",
            bidir._with_packet_hash(bad_parent),
            "transition_parent_state_not_in_parent_frontier",
        )
    )

    target_index = next(
        index
        for index, row in enumerate(base_packet["compressed_transition_groups"])
        if int(row["generated_state_count"]) >= 2
    )
    bad_proof = copy.deepcopy(base_packet)
    bad_proof["compressed_transition_groups"][target_index]["membership_proof"][0]["hash"] = "0" * 64
    bad_proof["compression_summary"] = _packet_compression_summary(
        transition_rows=bidir._build_transition_rows(case, full_dp=full_dp),
        compressed_rows=bad_proof["compressed_transition_groups"],
    )
    controls.append(
        (
            "membership_proof_hash_mismatch",
            bidir._with_packet_hash(bad_proof),
            "membership_proof_hash_mismatch",
        )
    )

    bad_authority = copy.deepcopy(base_packet)
    bad_authority["no_authority_effect"] = False
    controls.append(("authority_effect_present", bidir._with_packet_hash(bad_authority), "authority_effect_present"))

    output: list[dict[str, Any]] = []
    for mutation_id, packet, expected_reason in controls:
        verification = _verify_compressed_packet(
            case,
            full_dp=bidir._clone_full_dp(full_dp),
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
    cases = bidir._first_n7_positive_cases()
    rows = [verify_case(case) for case in cases]
    invalid_rows = [row for row in rows if not row["ok"]]
    negative_controls = _negative_controls(cases)
    transition_row_count = sum(int(row["source_transition_row_count"]) for row in rows)
    compressed_row_count = sum(int(row["compressed_row_count"]) for row in rows)
    source_bytes = sum(int(row["source_transition_json_bytes"]) for row in rows)
    compressed_bytes = sum(int(row["compressed_json_bytes"]) for row in rows)
    saved_rows = transition_row_count - compressed_row_count
    saved_bytes = source_bytes - compressed_bytes
    return {
        "schema": SEARCH_SCHEMA,
        "source_seed": bidir.N7_SEED,
        "source_bidirectional_report": _source_report_summary(),
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "source_transition_row_count": transition_row_count,
        "compressed_row_count": compressed_row_count,
        "expected_group_count": sum(int(row["expected_group_count"]) for row in rows),
        "covered_group_count": sum(int(row["covered_group_count"]) for row in rows),
        "missing_group_count": sum(int(row["missing_group_count"]) for row in rows),
        "extra_group_count": sum(int(row["extra_group_count"]) for row in rows),
        "invalid_compressed_row_count": sum(int(row["invalid_compressed_row_count"]) for row in rows),
        "duplicate_group_count": sum(int(row["duplicate_group_count"]) for row in rows),
        "row_reduction_count": saved_rows,
        "row_reduction_ratio": round(saved_rows / max(transition_row_count, 1), 6),
        "source_transition_json_bytes": source_bytes,
        "compressed_json_bytes": compressed_bytes,
        "byte_reduction_count": saved_bytes,
        "byte_reduction_ratio": round(saved_bytes / max(source_bytes, 1), 6),
        "transition_groups_digest": _sha256_json([row["transition_groups_digest"] for row in rows]),
        "compressed_rows_digest": _sha256_json([row["compressed_rows_digest"] for row in rows]),
        "coverage": {
            "n_counts": bidir._histogram(rows, "bit_count"),
            "fee_bps_counts": bidir._histogram(rows, "fee_bps"),
            "pattern_counts": bidir._histogram(rows, "pattern"),
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


def _strip_timing(search: Mapping[str, Any]) -> dict[str, Any]:
    stripped = dict(search)
    stripped.pop("elapsed_ms", None)
    return stripped


def deterministic_replay(first_search: Mapping[str, Any]) -> dict[str, Any]:
    second_search = run_search()
    first_hash = _sha256_json(_strip_timing(first_search))
    second_hash = _sha256_json(_strip_timing(second_search))
    return {"ok": first_hash == second_hash, "first_hash": first_hash, "second_hash": second_hash}


def build_report() -> dict[str, Any]:
    search = run_search()
    deterministic = deterministic_replay(search)
    ok = bool(
        search["case_count"] == EXPECTED_CASE_COUNT
        and search["valid_case_count"] == EXPECTED_CASE_COUNT
        and search["first_invalid_case"] is None
        and search["source_transition_row_count"] == EXPECTED_TRANSITION_ROW_COUNT
        and search["compressed_row_count"] == EXPECTED_COMPRESSED_ROW_COUNT
        and search["expected_group_count"] == EXPECTED_COMPRESSED_ROW_COUNT
        and search["covered_group_count"] == EXPECTED_COMPRESSED_ROW_COUNT
        and search["missing_group_count"] == 0
        and search["extra_group_count"] == 0
        and search["invalid_compressed_row_count"] == 0
        and search["duplicate_group_count"] == 0
        and search["row_reduction_count"] == 1_913
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
        and not _source_report_reasons(search["source_bidirectional_report"])
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded transition-group compression certificate reduces the n=7 AB child-frontier "
            "bidirectional proof object from 2,777 per-transition rows to 864 per-generated-child "
            "rows while preserving host-recomputed transition-group counts, group digests, canonical "
            "child membership, and no-authority rails."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N7-TRANSITION-GROUP-COMPRESSION-20260629",
            "mechanism_change": "Compress child-frontier transition proof objects by grouping all transitions that generate the same child state.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": {
                "safety": "+explicit no-extra digest binding",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+host recomputation, -proof object bytes",
                "determinism_simplicity": "+one row per generated child state",
            },
            "null_hypothesis": "Per-child transition groups cannot preserve both coverage and no-extra generated-image checks without carrying every transition row.",
            "falsification_recipe": "Remove a group, add an extra group, alter group count or digest, corrupt representative transition or membership proof, and require rejection.",
            "support_recipe": "Recompute full transition groups from the host DP, verify compressed group counts/digests, and compare compression ratios with deterministic replay.",
            "formal_obligations": "Research-only host checker; production use needs a smaller trusted transition relation or Lean refinement.",
            "risk_modes": [
                "host recomputation bug",
                "stale source bidirectional report",
                "group digest collision outside SHA-256 assumptions",
                "membership proof mismatch",
                "authority leakage",
            ],
            "status": "supported",
        },
        "source_report": search["source_bidirectional_report"],
        "non_claims": [
            "This certificate is bounded to the committed n=7 zero-min bidirectional transition report.",
            "This certificate compresses the proof object; it does not remove host recomputation of the transition image.",
            "This certificate does not prove Python-to-Lean refinement.",
            "This certificate does not prove child-frontier generation in Lean.",
            "This certificate does not cover nonzero min_amount_out behavior.",
            "This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.",
        ],
        "replay_command": "python3 tools/check_ab_child_frontier_transition_group_compression_20260629.py",
        "authority_boundary": AUTHORITY_BOUNDARY,
    }


def write_reports(report: Mapping[str, Any]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    search = report["search"]
    lines = [
        "# ZenoDEX AB Child-Frontier Transition-Group Compression - 2026-06-29",
        "",
        "## Executive Result",
        "",
        str(report["summary"]),
        "",
        "Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.",
        "",
        "## Compression",
        "",
        f"- Source transition rows: `{search['source_transition_row_count']}`",
        f"- Compressed rows: `{search['compressed_row_count']}`",
        f"- Row reduction: `{search['row_reduction_count']}` (`{search['row_reduction_ratio']}`)",
        f"- Source JSON bytes: `{search['source_transition_json_bytes']}`",
        f"- Compressed JSON bytes: `{search['compressed_json_bytes']}`",
        f"- Byte reduction: `{search['byte_reduction_count']}` (`{search['byte_reduction_ratio']}`)",
        f"- Transition-group digest: `{search['transition_groups_digest']}`",
        f"- Compressed-row digest: `{search['compressed_rows_digest']}`",
        "",
        "## Verification",
        "",
        f"- Cases: `{search['valid_case_count']}` / `{search['case_count']}`",
        f"- Expected groups: `{search['expected_group_count']}`",
        f"- Covered groups: `{search['covered_group_count']}`",
        f"- Missing groups: `{search['missing_group_count']}`",
        f"- Extra groups: `{search['extra_group_count']}`",
        f"- Invalid compressed rows: `{search['invalid_compressed_row_count']}`",
        f"- Duplicate groups: `{search['duplicate_group_count']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay: `{report['deterministic_replay']['ok']}`",
        "",
        "## Negative Controls",
        "",
        "| mutation | accepted | expected reason |",
        "| --- | ---: | --- |",
    ]
    for control in search["negative_controls"]:
        lines.append(
            "| `{}` | `{}` | `{}` |".format(
                control["mutation_id"],
                control["accepted"],
                control["expected_reason"],
            )
        )
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    report = build_report()
    write_reports(report)
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "source_rows": report["search"]["source_transition_row_count"],
                "compressed_rows": report["search"]["compressed_row_count"],
                "row_reduction_ratio": report["search"]["row_reduction_ratio"],
                "byte_reduction_ratio": report["search"]["byte_reduction_ratio"],
                "report": str(REPORT_JSON.relative_to(REPO_ROOT)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
