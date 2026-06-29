#!/usr/bin/env python3
"""Check a two-level corpus root for AB reserve-state child-frontier rows.

This research-only checker compresses the supported n=7 witness+Merkle
cross-binding rows into case roots and one corpus root. Each row receipt proves
membership in its case root, then proves that the case root is included in the
corpus root.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
import time
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools import check_ab_reserve_state_child_frontier_witness_merkle_20260629 as wm  # noqa: E402
from tools.check_ab_reserve_state_transition_projection_20260629 import (  # noqa: E402
    _new_failure,
    _packet_hash,
    _with_packet_hash,
)
from tools.check_ab_strict_zero_min_arbitrary_subset_family_certificate import (  # noqa: E402
    AUTHORITY_BOUNDARY,
)
from tools.check_ab_strict_zero_min_arbitrary_subset_family_extended_stress import (  # noqa: E402
    _histogram,
)
from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _full_state_records,
    _sha256_json,
    _strip_timing,
)
from tools.check_ab_strict_zero_min_reserve_state_quotient_certificate import (  # noqa: E402
    N7_SEED,
    _case_context,
    _first_n7_positive_cases,
)

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_reserve_state_child_frontier_corpus_root_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_RESERVE_STATE_CHILD_FRONTIER_CORPUS_ROOT_20260629.md"
)
CROSS_BINDING_REPORT_JSON = wm.REPORT_JSON

PACKET_SCHEMA = "zenodex.ab_reserve_state_child_frontier_corpus_root_packet.v1"
REPORT_SCHEMA = "zenodex.ab_reserve_state_child_frontier_corpus_root_report.v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_child_frontier_corpus_root"
ROW_LEAF_SCHEMA = "zenodex.ab_reserve_state_child_frontier_corpus_row_leaf.v1"
CASE_LEAF_SCHEMA = "zenodex.ab_reserve_state_child_frontier_corpus_case_leaf.v1"
NODE_SCHEMA = "zenodex.ab_reserve_state_child_frontier_corpus_node.v1"
TARGET_CASE_COUNT = 4
EXPECTED_NEGATIVE_CONTROL_COUNT = 10


def _node_hash(left_hash: str, right_hash: str) -> str:
    return _sha256_json(
        {"schema": NODE_SCHEMA, "left_hash": left_hash, "right_hash": right_hash}
    )


def _merkle_levels(leaf_hashes: Sequence[str]) -> list[list[str]]:
    if not leaf_hashes:
        return [[_sha256_json({"schema": NODE_SCHEMA, "empty": True})]]
    levels: list[list[str]] = [list(leaf_hashes)]
    while len(levels[-1]) > 1:
        previous = levels[-1]
        next_level: list[str] = []
        for index in range(0, len(previous), 2):
            left_hash = previous[index]
            right_hash = previous[index + 1] if index + 1 < len(previous) else left_hash
            next_level.append(_node_hash(left_hash, right_hash))
        levels.append(next_level)
    return levels


def _merkle_root(leaf_hashes: Sequence[str]) -> str:
    return _merkle_levels(leaf_hashes)[-1][0]


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
    leaf_hashes: Sequence[str],
    *,
    leaf_index: int,
) -> list[dict[str, str]]:
    levels = _merkle_levels(leaf_hashes)
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
    leaf_hash: str,
    proof: Sequence[Mapping[str, Any]],
    expected_root_hash: str,
) -> bool:
    current_hash = leaf_hash
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


def _state_key(row: Mapping[str, Any]) -> tuple[int, int]:
    return int(row["processed_reserve_in"]), int(row["reserve_out"])


def _row_key(row: Mapping[str, Any]) -> tuple[Any, ...]:
    witness = row["witness"]
    return (
        str(row["case_id"]),
        int(row["child_mask_id"]),
        *_state_key(row["child_state"]),
        int(witness["parent_mask_id"]),
        int(witness["step_bit_index"]),
        *_state_key(witness["parent_state"]),
        int(row["leaf_index"]),
    )


def _canonical_rows(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    return [copy.deepcopy(row) for row in sorted(rows, key=_row_key)]


def _row_leaf_hash(row: Mapping[str, Any]) -> str:
    return _sha256_json({"schema": ROW_LEAF_SCHEMA, "bound_row": row})


def _case_leaf_hash(summary: Mapping[str, Any]) -> str:
    return _sha256_json({"schema": CASE_LEAF_SCHEMA, "case_summary": summary})


def _linked_cross_binding_summary() -> dict[str, Any]:
    if not CROSS_BINDING_REPORT_JSON.exists():
        return {
            "path": str(CROSS_BINDING_REPORT_JSON.relative_to(REPO_ROOT)),
            "available": False,
        }
    report = json.loads(CROSS_BINDING_REPORT_JSON.read_text(encoding="utf-8"))
    search = report.get("search", {})
    return {
        "path": str(CROSS_BINDING_REPORT_JSON.relative_to(REPO_ROOT)),
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


def _linked_cross_binding_reasons(summary: Mapping[str, Any] | None) -> list[str]:
    if summary is None:
        return ["linked_cross_binding_summary_missing"]
    reasons: list[str] = []
    if summary.get("available") is not True:
        reasons.append("linked_cross_binding_report_missing")
    if summary.get("ok") is not True:
        reasons.append("linked_cross_binding_report_not_ok")
    if int(summary.get("case_count", -1)) != TARGET_CASE_COUNT:
        reasons.append("linked_cross_binding_case_count_mismatch")
    if int(summary.get("valid_case_count", -1)) != TARGET_CASE_COUNT:
        reasons.append("linked_cross_binding_valid_case_count_mismatch")
    if int(summary.get("child_mask_count", -1)) != 508:
        reasons.append("linked_cross_binding_child_mask_count_mismatch")
    if int(summary.get("bound_row_count", -1)) != 864:
        reasons.append("linked_cross_binding_bound_row_count_mismatch")
    if int(summary.get("witness_count", -1)) != 864:
        reasons.append("linked_cross_binding_witness_count_mismatch")
    if int(summary.get("membership_count", -1)) != 864:
        reasons.append("linked_cross_binding_membership_count_mismatch")
    if int(summary.get("negative_control_accept_count", -1)) != 0:
        reasons.append("linked_cross_binding_negative_control_accepts")
    return reasons


def _packet_rail_reasons(packet: Mapping[str, Any] | None) -> list[str]:
    if packet is None:
        return ["corpus_root_packet_missing"]
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
    if packet.get("case_root_bound") is not True:
        reasons.append("case_root_bound_missing")
    if packet.get("corpus_root_bound") is not True:
        reasons.append("corpus_root_bound_missing")
    if packet.get("row_inclusion_bound") is not True:
        reasons.append("row_inclusion_bound_missing")
    if packet.get("cross_binding_bound") is not True:
        reasons.append("cross_binding_bound_missing")
    if packet.get("linked_cross_binding_summary") != _linked_cross_binding_summary():
        reasons.append("linked_cross_binding_summary_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _case_packet(case: Any) -> dict[str, Any]:
    full_dp = _full_state_records(case.intents, _case_context(case))
    return wm.build_case_packet(case, full_dp=full_dp)


def _case_summary_from_packet(
    *,
    case_index: int,
    case_packet: Mapping[str, Any],
) -> tuple[dict[str, Any], list[dict[str, Any]], list[str]]:
    rows = _canonical_rows(case_packet["bound_rows"])
    row_hashes = [_row_leaf_hash(row) for row in rows]
    case_summary = {
        "case_index": int(case_index),
        "case_id": str(case_packet["case_id"]),
        "case_packet_hash": str(case_packet["packet_hash"]),
        "bit_count": int(case_packet["bit_count"]),
        "row_count": len(rows),
        "row_root": _merkle_root(row_hashes),
        "bound_rows_digest": _sha256_json(rows),
    }
    return case_summary, rows, row_hashes


@lru_cache(maxsize=1)
def build_corpus_packet() -> dict[str, Any]:
    cases = sorted(_first_n7_positive_cases(), key=lambda case: case.case_id)
    case_material: list[tuple[dict[str, Any], list[dict[str, Any]], list[str]]] = []
    for case_index, case in enumerate(cases):
        case_material.append(
            _case_summary_from_packet(
                case_index=case_index,
                case_packet=_case_packet(case),
            )
        )
    case_summaries = [item[0] for item in case_material]
    case_hashes = [_case_leaf_hash(summary) for summary in case_summaries]
    corpus_root = _merkle_root(case_hashes)

    row_receipts: list[dict[str, Any]] = []
    for case_summary, rows, row_hashes in case_material:
        case_index = int(case_summary["case_index"])
        case_proof = _membership_proof(case_hashes, leaf_index=case_index)
        for row_index, row in enumerate(rows):
            row_receipts.append(
                {
                    "case_index": case_index,
                    "case_id": case_summary["case_id"],
                    "row_index": row_index,
                    "bound_row": row,
                    "row_hash": row_hashes[row_index],
                    "row_membership_proof": _membership_proof(
                        row_hashes,
                        leaf_index=row_index,
                    ),
                    "case_row_root": case_summary["row_root"],
                    "case_summary": copy.deepcopy(case_summary),
                    "case_hash": case_hashes[case_index],
                    "case_membership_proof": copy.deepcopy(case_proof),
                }
            )

    summary = {
        "case_count": len(case_summaries),
        "row_count": len(row_receipts),
        "case_root_count": len(case_hashes),
        "corpus_root": corpus_root,
        "case_summaries_digest": _sha256_json(case_summaries),
        "row_receipts_digest": _sha256_json(row_receipts),
        "max_case_row_count": max(
            (int(summary["row_count"]) for summary in case_summaries),
            default=0,
        ),
    }
    packet = {
        "schema": PACKET_SCHEMA,
        "scope": SCOPE,
        "source_seed": N7_SEED,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "case_root_bound": True,
        "corpus_root_bound": True,
        "row_inclusion_bound": True,
        "cross_binding_bound": True,
        "linked_cross_binding_summary": _linked_cross_binding_summary(),
        "case_summaries": case_summaries,
        "row_receipts": row_receipts,
        "corpus_summary": summary,
    }
    return _with_packet_hash(packet)


def _expected_material() -> tuple[
    list[dict[str, Any]],
    dict[tuple[int, int], dict[str, Any]],
    dict[int, list[str]],
    list[str],
]:
    packet = build_corpus_packet()
    case_summaries = list(packet["case_summaries"])
    case_hashes = [_case_leaf_hash(summary) for summary in case_summaries]
    rows_by_key = {
        (int(receipt["case_index"]), int(receipt["row_index"])): receipt
        for receipt in packet["row_receipts"]
    }
    row_hashes_by_case: dict[int, list[str]] = {}
    for receipt in packet["row_receipts"]:
        row_hashes_by_case.setdefault(int(receipt["case_index"]), []).append(
            str(receipt["row_hash"])
        )
    return case_summaries, rows_by_key, row_hashes_by_case, case_hashes


def verify_corpus_packet(packet: Mapping[str, Any] | None) -> dict[str, Any]:
    reasons: list[str] = []
    first_failure: dict[str, Any] | None = None
    reasons.extend(_packet_rail_reasons(packet))

    expected_case_summaries, expected_rows, expected_row_hashes, expected_case_hashes = (
        _expected_material()
    )
    expected_corpus_root = _merkle_root(expected_case_hashes)
    expected_row_keys = set(expected_rows)

    case_summaries = list(packet.get("case_summaries", []) if packet is not None else [])
    row_receipts = list(packet.get("row_receipts", []) if packet is not None else [])
    corpus_summary = dict(packet.get("corpus_summary", {}) if packet is not None else {})

    invalid_receipt_count = 0
    duplicate_receipt_count = 0
    case_root_mismatch_count = 0
    corpus_root_mismatch_count = 0
    row_membership_mismatch_count = 0
    seen_keys: set[tuple[int, int]] = set()

    if case_summaries != expected_case_summaries:
        reasons.append("case_summaries_mismatch")
    if corpus_summary.get("corpus_root") != expected_corpus_root:
        reasons.append("corpus_root_mismatch")

    expected_case_summary_by_index = {
        int(summary["case_index"]): summary for summary in expected_case_summaries
    }

    for receipt_index, receipt in enumerate(row_receipts):
        row_reasons: list[str] = []
        try:
            case_index = int(receipt["case_index"])
            row_index = int(receipt["row_index"])
            bound_row = dict(receipt["bound_row"])
            row_hash = str(receipt["row_hash"])
            row_proof = list(receipt["row_membership_proof"])
            case_row_root = str(receipt["case_row_root"])
            case_summary = dict(receipt["case_summary"])
            case_hash = str(receipt["case_hash"])
            case_proof = list(receipt["case_membership_proof"])
        except (KeyError, TypeError, ValueError):
            row_reasons.append("row_receipt_malformed")
            case_index = -1
            row_index = -1
            bound_row = {}
            row_hash = ""
            row_proof = []
            case_row_root = ""
            case_summary = {}
            case_hash = ""
            case_proof = []

        receipt_key = (case_index, row_index)
        if receipt_key in seen_keys:
            duplicate_receipt_count += 1
            row_reasons.append("duplicate_row_receipt")
        seen_keys.add(receipt_key)

        expected_receipt = expected_rows.get(receipt_key)
        if expected_receipt is None:
            row_reasons.append("row_receipt_index_out_of_range")
        else:
            if bound_row != expected_receipt["bound_row"]:
                row_reasons.append("bound_row_mismatch")
            if row_hash != expected_receipt["row_hash"]:
                row_reasons.append("row_hash_mismatch")
            if case_row_root != expected_receipt["case_row_root"]:
                row_reasons.append("case_row_root_mismatch")
                case_root_mismatch_count += 1
            if case_summary != expected_receipt["case_summary"]:
                row_reasons.append("case_summary_mismatch")
            if case_hash != expected_receipt["case_hash"]:
                row_reasons.append("case_hash_mismatch")

        if row_hash != _row_leaf_hash(bound_row):
            row_reasons.append("row_hash_mismatch")
        expected_row_hashes_for_case = expected_row_hashes.get(case_index)
        if expected_row_hashes_for_case is None:
            row_reasons.append("case_index_out_of_range")
        else:
            expected_sides = _expected_sides(row_index, len(expected_row_hashes_for_case))
            if expected_sides is None:
                row_reasons.append("row_index_out_of_range")
            elif [step.get("side") for step in row_proof] != expected_sides:
                row_reasons.append("row_membership_shape_mismatch")
            elif not _verify_membership_hash(row_hash, row_proof, case_row_root):
                row_reasons.append("row_membership_hash_mismatch")
                row_membership_mismatch_count += 1

        expected_case_summary = expected_case_summary_by_index.get(case_index)
        if expected_case_summary is None:
            row_reasons.append("case_index_out_of_range")
        elif _case_leaf_hash(expected_case_summary) != case_hash:
            row_reasons.append("case_hash_mismatch")
        expected_case_sides = _expected_sides(case_index, len(expected_case_hashes))
        if expected_case_sides is None:
            row_reasons.append("case_index_out_of_range")
        elif [step.get("side") for step in case_proof] != expected_case_sides:
            row_reasons.append("case_membership_shape_mismatch")
        elif not _verify_membership_hash(case_hash, case_proof, expected_corpus_root):
            row_reasons.append("case_membership_hash_mismatch")
            corpus_root_mismatch_count += 1

        if row_reasons:
            invalid_receipt_count += 1
            reasons.extend(row_reasons)
            first_failure = _new_failure(
                first_failure,
                case_id=str(receipt.get("case_id", "")),
                mask_id=int(bound_row.get("child_mask_id", -1))
                if isinstance(bound_row, dict)
                else -1,
                reason=row_reasons[0],
                detail={"receipt_index": receipt_index},
            )

    missing_receipt_keys = expected_row_keys - seen_keys
    extra_receipt_keys = seen_keys - expected_row_keys
    if missing_receipt_keys:
        reasons.append("missing_row_receipt")
    if extra_receipt_keys:
        reasons.append("extra_row_receipt")
    if duplicate_receipt_count:
        reasons.append("duplicate_row_receipt")

    expected_summary = {
        "case_count": len(expected_case_summaries),
        "row_count": len(expected_rows),
        "case_root_count": len(expected_case_hashes),
        "corpus_root": expected_corpus_root,
        "case_summaries_digest": _sha256_json(expected_case_summaries),
        "row_receipts_digest": _sha256_json(
            [expected_rows[key] for key in sorted(expected_rows)]
        ),
        "max_case_row_count": max(
            (int(summary["row_count"]) for summary in expected_case_summaries),
            default=0,
        ),
    }
    if corpus_summary != expected_summary:
        reasons.append("corpus_summary_mismatch")

    reasons.extend(
        _linked_cross_binding_reasons(
            packet.get("linked_cross_binding_summary") if packet is not None else None
        )
    )

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "first_failure": first_failure,
        "case_count": len(case_summaries),
        "row_receipt_count": len(row_receipts),
        "expected_case_count": len(expected_case_summaries),
        "expected_row_receipt_count": len(expected_rows),
        "covered_row_receipt_count": len(seen_keys & expected_row_keys),
        "missing_row_receipt_count": len(missing_receipt_keys),
        "extra_row_receipt_count": len(extra_receipt_keys),
        "invalid_row_receipt_count": invalid_receipt_count,
        "duplicate_row_receipt_count": duplicate_receipt_count,
        "case_root_mismatch_count": case_root_mismatch_count,
        "corpus_root_mismatch_count": corpus_root_mismatch_count,
        "row_membership_mismatch_count": row_membership_mismatch_count,
        "corpus_root": corpus_summary.get("corpus_root"),
        "expected_corpus_root": expected_corpus_root,
        "case_summaries_digest": corpus_summary.get("case_summaries_digest"),
        "row_receipts_digest": corpus_summary.get("row_receipts_digest"),
        "max_case_row_count": corpus_summary.get("max_case_row_count"),
    }


def _negative_controls() -> list[dict[str, Any]]:
    base_packet = build_corpus_packet()
    controls: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    controls.append(("packet_hash_mismatch", bad_hash, "packet_hash_mismatch"))

    bad_row_hash = copy.deepcopy(base_packet)
    bad_row_hash["row_receipts"][0]["row_hash"] = "0" * 64
    bad_row_hash["corpus_summary"]["row_receipts_digest"] = _sha256_json(
        bad_row_hash["row_receipts"]
    )
    controls.append(
        (
            "row_hash_mismatch",
            _with_packet_hash(bad_row_hash),
            "row_hash_mismatch",
        )
    )

    bad_row_proof = copy.deepcopy(base_packet)
    target_index = next(
        index
        for index, row in enumerate(bad_row_proof["row_receipts"])
        if row["row_membership_proof"]
    )
    bad_row_proof["row_receipts"][target_index]["row_membership_proof"][0][
        "hash"
    ] = "0" * 64
    bad_row_proof["corpus_summary"]["row_receipts_digest"] = _sha256_json(
        bad_row_proof["row_receipts"]
    )
    controls.append(
        (
            "row_membership_hash_mismatch",
            _with_packet_hash(bad_row_proof),
            "row_membership_hash_mismatch",
        )
    )

    bad_case_root = copy.deepcopy(base_packet)
    bad_case_root["row_receipts"][0]["case_row_root"] = "0" * 64
    bad_case_root["corpus_summary"]["row_receipts_digest"] = _sha256_json(
        bad_case_root["row_receipts"]
    )
    controls.append(
        (
            "case_row_root_mismatch",
            _with_packet_hash(bad_case_root),
            "case_row_root_mismatch",
        )
    )

    bad_case_proof = copy.deepcopy(base_packet)
    target_case_index = next(
        index
        for index, row in enumerate(bad_case_proof["row_receipts"])
        if row["case_membership_proof"]
    )
    bad_case_proof["row_receipts"][target_case_index]["case_membership_proof"][0][
        "hash"
    ] = "0" * 64
    bad_case_proof["corpus_summary"]["row_receipts_digest"] = _sha256_json(
        bad_case_proof["row_receipts"]
    )
    controls.append(
        (
            "case_membership_hash_mismatch",
            _with_packet_hash(bad_case_proof),
            "case_membership_hash_mismatch",
        )
    )

    missing_row = copy.deepcopy(base_packet)
    missing_row["row_receipts"] = missing_row["row_receipts"][1:]
    missing_row["corpus_summary"]["row_count"] -= 1
    missing_row["corpus_summary"]["row_receipts_digest"] = _sha256_json(
        missing_row["row_receipts"]
    )
    controls.append(
        (
            "missing_row_receipt",
            _with_packet_hash(missing_row),
            "missing_row_receipt",
        )
    )

    duplicate_row = copy.deepcopy(base_packet)
    duplicate_row["row_receipts"].append(copy.deepcopy(duplicate_row["row_receipts"][0]))
    duplicate_row["corpus_summary"]["row_count"] += 1
    duplicate_row["corpus_summary"]["row_receipts_digest"] = _sha256_json(
        duplicate_row["row_receipts"]
    )
    controls.append(
        (
            "duplicate_row_receipt",
            _with_packet_hash(duplicate_row),
            "duplicate_row_receipt",
        )
    )

    bad_case_index = copy.deepcopy(base_packet)
    bad_case_index["row_receipts"][0]["case_index"] = 99
    bad_case_index["corpus_summary"]["row_receipts_digest"] = _sha256_json(
        bad_case_index["row_receipts"]
    )
    controls.append(
        (
            "case_index_out_of_range",
            _with_packet_hash(bad_case_index),
            "case_index_out_of_range",
        )
    )

    bad_link = copy.deepcopy(base_packet)
    bad_link["linked_cross_binding_summary"]["bound_row_count"] = 0
    controls.append(
        (
            "linked_cross_binding_bound_row_count_mismatch",
            _with_packet_hash(bad_link),
            "linked_cross_binding_bound_row_count_mismatch",
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
        verification = verify_corpus_packet(packet)
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
    packet = build_corpus_packet()
    verification = verify_corpus_packet(packet)
    negative_controls = _negative_controls()
    case_summaries = list(packet["case_summaries"])
    rows = [
        {
            "case_id": summary["case_id"],
            "bit_count": summary["bit_count"],
            "row_count": summary["row_count"],
        }
        for summary in case_summaries
    ]
    return {
        "schema": "zenodex/ab_reserve_state_child_frontier_corpus_root_search/v1",
        "source_seed": N7_SEED,
        "packet_hash": packet["packet_hash"],
        "corpus_root": verification["corpus_root"],
        "expected_corpus_root": verification["expected_corpus_root"],
        "corpus_root_matches": verification["corpus_root"]
        == verification["expected_corpus_root"],
        "case_count": verification["case_count"],
        "expected_case_count": verification["expected_case_count"],
        "row_receipt_count": verification["row_receipt_count"],
        "expected_row_receipt_count": verification["expected_row_receipt_count"],
        "covered_row_receipt_count": verification["covered_row_receipt_count"],
        "missing_row_receipt_count": verification["missing_row_receipt_count"],
        "extra_row_receipt_count": verification["extra_row_receipt_count"],
        "invalid_row_receipt_count": verification["invalid_row_receipt_count"],
        "duplicate_row_receipt_count": verification["duplicate_row_receipt_count"],
        "case_root_mismatch_count": verification["case_root_mismatch_count"],
        "corpus_root_mismatch_count": verification["corpus_root_mismatch_count"],
        "row_membership_mismatch_count": verification["row_membership_mismatch_count"],
        "case_summaries_digest": verification["case_summaries_digest"],
        "row_receipts_digest": verification["row_receipts_digest"],
        "max_case_row_count": verification["max_case_row_count"],
        "linked_cross_binding_summary": packet["linked_cross_binding_summary"],
        "coverage": {
            "n_counts": _histogram(rows, "bit_count"),
            "case_row_count_histogram": _histogram(rows, "row_count"),
            "reason_classes": sorted(
                {
                    reason
                    for control in negative_controls
                    for reason in control["reasons"]
                }
            ),
        },
        "verification": verification,
        "negative_control_count": len(negative_controls),
        "negative_control_accept_count": sum(
            1 for row in negative_controls if row["accepted"]
        ),
        "negative_controls": negative_controls,
        "case_summaries": case_summaries,
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
        search["verification"]["ok"]
        and search["corpus_root_matches"]
        and search["case_count"] == TARGET_CASE_COUNT
        and search["expected_case_count"] == TARGET_CASE_COUNT
        and search["row_receipt_count"] == 864
        and search["expected_row_receipt_count"] == 864
        and search["covered_row_receipt_count"] == 864
        and search["missing_row_receipt_count"] == 0
        and search["extra_row_receipt_count"] == 0
        and search["invalid_row_receipt_count"] == 0
        and search["duplicate_row_receipt_count"] == 0
        and search["case_root_mismatch_count"] == 0
        and search["corpus_root_mismatch_count"] == 0
        and search["row_membership_mismatch_count"] == 0
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and not _linked_cross_binding_reasons(search["linked_cross_binding_summary"])
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded n=7 host checker compresses 864 witness+Merkle "
            "cross-bound child-frontier row receipts into four case roots and "
            "one corpus root with fail-closed inclusion checks."
        ),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "search": search,
        "deterministic_replay": deterministic,
        "replay_command": (
            "python3 tools/check_ab_reserve_state_child_frontier_corpus_root_20260629.py"
        ),
        "hypothesis_card": {
            "hypothesis_id": "H-AB-N7-CORPUS-ROOT-20260629",
            "mechanism_change": (
                "Aggregate cross-bound child-frontier rows into case roots and "
                "one corpus root with row and case membership proofs."
            ),
            "representation_shift_used": "certificate_boundary",
            "expected_metric_delta": {
                "safety": "+single corpus commitment rejects stale or missing row receipts",
                "cap_efficiency": "0",
                "execution_quality": "0",
                "perf_cost": "+Merkle verification, -large receipt comparison surface",
                "determinism_simplicity": "+canonical corpus root for replay and audit",
            },
            "null_hypothesis": (
                "Adding a corpus root gives no extra falsifiable constraint beyond "
                "the row-level witness+Merkle report."
            ),
            "falsification_recipe": (
                "Mutate row hashes, row proofs, case roots, case proofs, row "
                "presence, duplicate indexes, case indexes, linked-report summary, "
                "packet hash, and authority rails."
            ),
            "support_recipe": (
                "Verify all 864 row receipts through case roots and the corpus root, "
                "assert the linked cross-binding report, and reject all mutation controls."
            ),
            "formal_obligations": (
                "A production-grade artifact would need a versioned verifier grammar "
                "and a Lean or Tau-level statement for the corpus-root membership relation."
            ),
            "risk_modes": [
                "row receipt omitted from corpus root",
                "case root stale or from a different case",
                "corpus root stale",
                "duplicate row index",
                "linked cross-binding report stale",
                "authority leakage",
            ],
            "status": "supported_bounded",
        },
        "non_claims": [
            "This corpus-root checker is bounded to the committed n=7 randomized corpus.",
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
        "# ZenoDEX AB Reserve-State Child-Frontier Corpus Root - 2026-06-29",
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
        "row_receipt -> case_root -> corpus_root",
        "```",
        "",
        "The checker accepts only when every cross-bound row receipt is included in its case root and every case root is included in the corpus root.",
        "",
        "## Evidence Summary",
        "",
        f"- Cases checked: `{search['case_count']}`",
        f"- Row receipts: `{search['row_receipt_count']}`",
        f"- Covered row receipts: `{search['covered_row_receipt_count']}`",
        f"- Missing row receipts: `{search['missing_row_receipt_count']}`",
        f"- Extra row receipts: `{search['extra_row_receipt_count']}`",
        f"- Invalid row receipts: `{search['invalid_row_receipt_count']}`",
        f"- Duplicate row receipts: `{search['duplicate_row_receipt_count']}`",
        f"- Case-root mismatches: `{search['case_root_mismatch_count']}`",
        f"- Corpus-root mismatches: `{search['corpus_root_mismatch_count']}`",
        f"- Row membership mismatches: `{search['row_membership_mismatch_count']}`",
        f"- Corpus root: `{search['corpus_root']}`",
        f"- Case summaries digest: `{search['case_summaries_digest']}`",
        f"- Row receipts digest: `{search['row_receipts_digest']}`",
        f"- Max rows per case: `{search['max_case_row_count']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Linked Cross-Binding Report",
        "",
        "```json",
        json.dumps(search["linked_cross_binding_summary"], indent=2, sort_keys=True),
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
    lines.extend(["| case | rows | row root |", "| --- | ---: | --- |"])
    for summary in search["case_summaries"]:
        lines.append(
            f"| `{summary['case_id']}` | `{summary['row_count']}` | `{summary['row_root']}` |"
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
