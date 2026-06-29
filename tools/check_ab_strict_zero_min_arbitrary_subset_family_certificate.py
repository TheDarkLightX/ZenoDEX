#!/usr/bin/env python3
"""Check arbitrary subset-family certificate packets for AB strict zero-min DP.

This research-only checker connects the concrete one-record min-reserve-out
compressed DP emitter to the Lean `StrictSubsetFamilyHostTable` endpoint.  For
each reachable subset mask and each completion suffix, it checks that a
singleton subset-family table has the rails and host premises required by the
Lean theorem:

* local mask pruning,
* selected-family winner membership,
* selected suffix executability,
* full-frontier suffix dominance by the selected representative.
"""

from __future__ import annotations

import argparse
import copy
import itertools
import json
import sys
import time
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

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
from tools.check_ab_strict_zero_min_subset_induction_witness import (  # noqa: E402
    _amount_sums,
    _clone_compressed_dp,
    _clone_full_dp,
    _record_identity,
    _record_json,
    _remaining_intents,
    _run_suffix,
)
from tools.check_ab_zero_min_economic_compression_certificate import _context, _short  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_arbitrary_subset_family_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_ARBITRARY_SUBSET_FAMILY_CERTIFICATE_20260629.md"
)

EXPECTED_NEGATIVE_CONTROL_COUNT = 12
PACKET_SCHEMA = "zenodex.ab_strict_zero_min_arbitrary_subset_family_certificate_packet.v1"
REPORT_SCHEMA = "zenodex.ab_strict_zero_min_arbitrary_subset_family_certificate_report.v1"
AUTHORITY_BOUNDARY = "research_only_no_settlement_or_state_authority"
SCOPE = "stress_same_pool_same_direction_exact_in_zero_min_strict_executable"


def _without_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in packet.items() if key != "packet_hash"}


def _packet_hash(packet: Mapping[str, Any]) -> str:
    return _sha256_json(_without_packet_hash(packet))


def _with_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    out = dict(packet)
    out["packet_hash"] = _packet_hash(out)
    return out


def _record_digest(record: _HostRecord) -> str:
    return _sha256_json(_record_json(record))


def _records_digest(records: list[_HostRecord]) -> str:
    return _sha256_json([_record_json(record) for record in records])


def _suffix_ids(suffix: tuple[Any, ...]) -> tuple[str, ...]:
    return tuple(intent.intent_id for intent in suffix)


def _suffix_json(suffix: tuple[Any, ...]) -> dict[str, Any]:
    ids = _suffix_ids(suffix)
    return {"order_ids": list(ids), "order_short": _short(ids)}


def _lean_contract() -> dict[str, str]:
    return {
        "structure": "StrictSubsetFamilyHostTable",
        "valid_predicate": "strictSubsetFamilyHostTableValid",
        "endpoint": "strictSubsetFamilyHostTable_validates",
        "witness": "witness_strictSubsetFamilyHostTable_validates",
        "family_shape": "singleton_per_reachable_mask_suffix",
    }


def _packet_min_amount_out_reasons(packet: Mapping[str, Any]) -> list[str]:
    raw_values = packet.get("min_amount_out")
    try:
        bit_count = int(packet.get("bit_count"))
    except (TypeError, ValueError):
        bit_count = -1
    if not isinstance(raw_values, list) or len(raw_values) != bit_count:
        return ["packet_min_amount_out_shape_mismatch"]
    try:
        if any(int(item) != 0 for item in raw_values):
            return ["packet_nonzero_min_amount_out_out_of_scope"]
    except (TypeError, ValueError):
        return ["packet_min_amount_out_shape_mismatch"]
    return []


def _case_has_zero_min_amount_out(case: _StressCase) -> bool:
    return all(int(intent.get_field("min_amount_out", 0)) == 0 for intent in case.intents)


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
    if packet.get("winner_membership_bound") is not True:
        reasons.append("winner_membership_bound_missing")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("lean_contract_mismatch")
    reasons.extend(_packet_min_amount_out_reasons(packet))
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    return reasons


def _case_context(case: _StressCase) -> Any:
    return _context(case.pool, case.intents, case.balances)


def _case_summary_inputs(case: _StressCase) -> dict[str, Any]:
    context = _case_context(case)
    return {
        "case_id": case.case_id,
        "scope": SCOPE,
        "bit_count": len(case.intents),
        "full_mask": (1 << len(case.intents)) - 1,
        "initial_reserve_in": int(context.r_in0),
        "initial_reserve_out": int(context.r_out0),
        "executed_input": int(sum(int(intent.get_field("amount_in")) for intent in case.intents)),
        "pool": {
            "reserve_in": int(context.r_in0),
            "reserve_out": int(context.r_out0),
            "fee_bps": int(context.pool_state.fee_bps),
        },
        "amounts": [int(intent.get_field("amount_in")) for intent in case.intents],
        "min_amount_out": [int(intent.get_field("min_amount_out", 0)) for intent in case.intents],
        "stress": {"seed": SEED, "pattern": case.pattern, "case_count": CASE_COUNT},
    }


def _mask_summary(
    *,
    mask_id: int,
    selected: _HostRecord,
    full_records: list[_HostRecord],
    suffix_count: int,
) -> dict[str, Any]:
    return {
        "mask_id": int(mask_id),
        "singleton_family_shape": True,
        "winner_member_of_family": True,
        "selected": _record_json(selected),
        "selected_digest": _record_digest(selected),
        "full_record_count": len(full_records),
        "full_records_digest": _records_digest(full_records),
        "suffix_count": int(suffix_count),
    }


def _new_failure(
    first_failure: dict[str, Any] | None,
    *,
    case: _StressCase,
    mask_id: int,
    reason: str,
    **details: Any,
) -> dict[str, Any] | None:
    if first_failure is not None:
        return first_failure
    return {"case_id": case.case_id, "mask_id": int(mask_id), "reason": reason, **details}


def _verify_case_arrays(
    case: _StressCase,
    *,
    full_dp: list[list[_HostRecord]],
    compressed_dp: list[_HostRecord | None],
    packet: Mapping[str, Any] | None,
) -> dict[str, Any]:
    context = _case_context(case)
    n = len(case.intents)
    full_mask = (1 << n) - 1
    reasons: list[str] = []
    reasons.extend(_packet_rail_reasons(packet))
    first_failure: dict[str, Any] | None = None
    if not _case_has_zero_min_amount_out(case):
        reasons.append("nonzero_min_amount_out_out_of_scope")
        first_failure = _new_failure(
            first_failure,
            case=case,
            mask_id=0,
            reason="nonzero_min_amount_out_out_of_scope",
        )
    amount_sums = _amount_sums(case.intents)
    mask_count = 0
    record_count = 0
    singleton_table_obligation_count = 0
    selected_suffix_executable_count = 0
    dominance_check_count = 0
    full_runtime_completion_count = 0
    max_records_per_mask = 0
    max_suffix_per_mask = 0
    mask_summaries: list[dict[str, Any]] = []
    obligation_digest_rows: list[dict[str, Any]] = []
    first_obligation: dict[str, Any] | None = None

    if compressed_dp[full_mask] is None:
        reasons.append("compressed_full_mask_not_executable")
        first_failure = _new_failure(
            first_failure,
            case=case,
            mask_id=full_mask,
            reason="compressed_full_mask_not_executable",
        )

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
            first_failure = _new_failure(
                first_failure,
                case=case,
                mask_id=mask_id,
                reason="compressed_record_missing",
            )
            continue

        selected_identity = _record_identity(selected)
        full_identities = {_record_identity(record) for record in full_records}
        if selected_identity not in full_identities:
            reasons.append("selected_record_not_in_full_state_records")
            first_failure = _new_failure(
                first_failure,
                case=case,
                mask_id=mask_id,
                reason="selected_record_not_in_full_state_records",
                selected=_record_json(selected),
            )

        if int(selected.processed_reserve_in) != expected_processed_reserve_in:
            reasons.append("mask_pruning_selected_processed_reserve_in_mismatch")
            first_failure = _new_failure(
                first_failure,
                case=case,
                mask_id=mask_id,
                reason="mask_pruning_selected_processed_reserve_in_mismatch",
                selected=_record_json(selected),
                expected_processed_reserve_in=expected_processed_reserve_in,
            )
        for record in full_records:
            if int(record.processed_reserve_in) != expected_processed_reserve_in:
                reasons.append("mask_pruning_full_record_processed_reserve_in_mismatch")
                first_failure = _new_failure(
                    first_failure,
                    case=case,
                    mask_id=mask_id,
                    reason="mask_pruning_full_record_processed_reserve_in_mismatch",
                    record=_record_json(record),
                    expected_processed_reserve_in=expected_processed_reserve_in,
                )

        min_reserve_out = min(int(record.reserve_out) for record in full_records)
        if int(selected.reserve_out) != min_reserve_out:
            reasons.append("mask_pruning_selected_reserve_out_not_min")
            first_failure = _new_failure(
                first_failure,
                case=case,
                mask_id=mask_id,
                reason="mask_pruning_selected_reserve_out_not_min",
                selected=_record_json(selected),
                min_reserve_out=min_reserve_out,
            )

        suffixes = tuple(itertools.permutations(_remaining_intents(mask_id, case.intents)))
        max_suffix_per_mask = max(max_suffix_per_mask, len(suffixes))
        mask_summaries.append(
            _mask_summary(
                mask_id=mask_id,
                selected=selected,
                full_records=full_records,
                suffix_count=len(suffixes),
            )
        )
        for suffix in suffixes:
            suffix_id_tuple = _suffix_ids(suffix)
            singleton_table_obligation_count += 1
            selected_result = _run_suffix(selected, suffix, context)
            if selected_result is None:
                reasons.append("singleton_table_suffix_not_executable")
                first_failure = _new_failure(
                    first_failure,
                    case=case,
                    mask_id=mask_id,
                    reason="singleton_table_suffix_not_executable",
                    selected=_record_json(selected),
                    suffix_short=_short(suffix_id_tuple),
                )
            else:
                selected_suffix_executable_count += 1

            obligation_row = {
                "mask_id": int(mask_id),
                "suffix_short": _short(suffix_id_tuple),
                "selected_digest": _record_digest(selected),
                "full_records_digest": _records_digest(full_records),
            }
            obligation_digest_rows.append(obligation_row)
            if first_obligation is None:
                first_obligation = {
                    "mask_id": int(mask_id),
                    "suffix": _suffix_json(suffix),
                    "singleton_family": [int(mask_id)],
                    "winner": _record_json(selected),
                    "full_record_count": len(full_records),
                    "full_records_digest": _records_digest(full_records),
                }

            for record in full_records:
                dominance_check_count += 1
                full_result = _run_suffix(record, suffix, context)
                if full_result is None:
                    reasons.append("full_suffix_not_executable")
                    first_failure = _new_failure(
                        first_failure,
                        case=case,
                        mask_id=mask_id,
                        reason="full_suffix_not_executable",
                        full_record=_record_json(record),
                        suffix_short=_short(suffix_id_tuple),
                    )
                    continue
                full_runtime_completion_count += 1
                if selected_result is None:
                    continue
                if int(selected_result.reserve_out) > int(full_result.reserve_out):
                    reasons.append("selected_final_reserve_dominance_failure")
                    first_failure = _new_failure(
                        first_failure,
                        case=case,
                        mask_id=mask_id,
                        reason="selected_final_reserve_dominance_failure",
                        full_final=_record_json(full_result),
                        selected_final=_record_json(selected_result),
                        suffix_short=_short(suffix_id_tuple),
                    )

    obligation_summary = {
        "mask_count": mask_count,
        "record_count": record_count,
        "singleton_table_obligation_count": singleton_table_obligation_count,
        "selected_suffix_executable_count": selected_suffix_executable_count,
        "dominance_check_count": dominance_check_count,
        "full_runtime_completion_count": full_runtime_completion_count,
        "max_records_per_mask": max_records_per_mask,
        "max_suffix_per_mask": max_suffix_per_mask,
        "obligation_digest": _sha256_json(obligation_digest_rows),
    }

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("full_mask") != full_mask:
            reasons.append("packet_full_mask_mismatch")
        if packet.get("obligation_summary") != obligation_summary:
            reasons.append("packet_obligation_summary_mismatch")
        if packet.get("mask_summaries") != mask_summaries:
            reasons.append("packet_mask_summaries_mismatch")
        if packet.get("first_obligation") != first_obligation:
            reasons.append("packet_first_obligation_mismatch")

    unique_reasons = list(dict.fromkeys(reasons))
    return {
        "case_id": case.case_id,
        "ok": not unique_reasons,
        "reasons": unique_reasons,
        "first_failure": first_failure,
        "bit_count": n,
        "fee_bps": int(case.pool.fee_bps),
        "pattern": case.pattern,
        "mask_summaries": mask_summaries,
        "first_obligation": first_obligation,
        **obligation_summary,
        "full_mask_selected": _record_json(compressed_dp[full_mask])
        if compressed_dp[full_mask] is not None
        else None,
    }


def build_case_packet(
    case: _StressCase,
    *,
    full_dp: list[list[_HostRecord]] | None = None,
    compressed_dp: list[_HostRecord | None] | None = None,
) -> dict[str, Any]:
    if not _case_has_zero_min_amount_out(case):
        raise ValueError("nonzero_min_amount_out_out_of_scope")
    context = _case_context(case)
    if full_dp is None:
        full_dp = _full_state_records(case.intents, context)
    if compressed_dp is None:
        compressed_dp = _compressed_records(case.intents, context)
    verification = _verify_case_arrays(case, full_dp=full_dp, compressed_dp=compressed_dp, packet=None)
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "winner_membership_bound": True,
        "lean_contract": _lean_contract(),
        "obligation_summary": {
            "mask_count": verification["mask_count"],
            "record_count": verification["record_count"],
            "singleton_table_obligation_count": verification["singleton_table_obligation_count"],
            "selected_suffix_executable_count": verification["selected_suffix_executable_count"],
            "dominance_check_count": verification["dominance_check_count"],
            "full_runtime_completion_count": verification["full_runtime_completion_count"],
            "max_records_per_mask": verification["max_records_per_mask"],
            "max_suffix_per_mask": verification["max_suffix_per_mask"],
            "obligation_digest": verification["obligation_digest"],
        },
        "mask_summaries": verification["mask_summaries"],
        "first_obligation": verification["first_obligation"],
    }
    return _with_packet_hash(packet)


def verify_case_packet(case: _StressCase, packet: Mapping[str, Any]) -> dict[str, Any]:
    context = _case_context(case)
    return _verify_case_arrays(
        case,
        full_dp=_full_state_records(case.intents, context),
        compressed_dp=_compressed_records(case.intents, context),
        packet=packet,
    )


def verify_case(case: _StressCase) -> dict[str, Any]:
    packet = build_case_packet(case)
    verification = verify_case_packet(case, packet)
    return {key: value for key, value in verification.items() if key != "mask_summaries"} | {
        "packet_hash": packet["packet_hash"],
    }


def _rehash_packet(packet: dict[str, Any]) -> dict[str, Any]:
    return _with_packet_hash(packet)


def _negative_controls(case: _StressCase) -> list[dict[str, Any]]:
    context = _case_context(case)
    base_full = _full_state_records(case.intents, context)
    base_compressed = _compressed_records(case.intents, context)
    base_packet = build_case_packet(case, full_dp=base_full, compressed_dp=base_compressed)

    rows: list[tuple[str, list[list[_HostRecord]], list[_HostRecord | None], dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    rows.append(
        (
            "packet_hash_mismatch",
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            bad_hash,
            "packet_hash_mismatch",
        )
    )

    bad_hash_bound = copy.deepcopy(base_packet)
    bad_hash_bound["packet_hash_bound"] = False
    rows.append(
        (
            "packet_hash_bound_missing",
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_hash_bound),
            "packet_hash_bound_missing",
        )
    )

    bad_authority = copy.deepcopy(base_packet)
    bad_authority["no_authority_effect"] = False
    rows.append(
        (
            "authority_effect_present",
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_authority),
            "authority_effect_present",
        )
    )

    bad_membership_bound = copy.deepcopy(base_packet)
    bad_membership_bound["winner_membership_bound"] = False
    rows.append(
        (
            "winner_membership_bound_missing",
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_membership_bound),
            "winner_membership_bound_missing",
        )
    )

    bad_nonzero_min_packet = copy.deepcopy(base_packet)
    bad_nonzero_min_packet["min_amount_out"] = [1, *bad_nonzero_min_packet["min_amount_out"][1:]]
    rows.append(
        (
            "packet_nonzero_min_amount_out_out_of_scope",
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_nonzero_min_packet),
            "packet_nonzero_min_amount_out_out_of_scope",
        )
    )

    bad_min_shape_packet = copy.deepcopy(base_packet)
    bad_min_shape_packet["min_amount_out"] = []
    rows.append(
        (
            "packet_min_amount_out_shape_mismatch",
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_min_shape_packet),
            "packet_min_amount_out_shape_mismatch",
        )
    )

    missing_compressed = _clone_compressed_dp(base_compressed)
    missing_compressed[0] = None
    rows.append(
        (
            "compressed_record_missing",
            _clone_full_dp(base_full),
            missing_compressed,
            base_packet,
            "compressed_record_missing",
        )
    )

    processed_mismatch_full = _clone_full_dp(base_full)
    processed_mismatch_full[0][0] = _HostRecord(
        int(processed_mismatch_full[0][0].processed_reserve_in) + 1,
        int(processed_mismatch_full[0][0].reserve_out),
        tuple(processed_mismatch_full[0][0].order_ids),
    )
    rows.append(
        (
            "mask_pruning_full_record_processed_reserve_in_mismatch",
            processed_mismatch_full,
            _clone_compressed_dp(base_compressed),
            base_packet,
            "mask_pruning_full_record_processed_reserve_in_mismatch",
        )
    )

    selected_not_min = _clone_compressed_dp(base_compressed)
    selected_not_min[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        int(base_full[0][0].reserve_out) + 1,
        tuple(base_compressed[0].order_ids),
    )
    rows.append(
        (
            "mask_pruning_selected_reserve_out_not_min",
            _clone_full_dp(base_full),
            selected_not_min,
            base_packet,
            "mask_pruning_selected_reserve_out_not_min",
        )
    )

    selected_not_member = _clone_compressed_dp(base_compressed)
    selected_not_member[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        int(base_compressed[0].reserve_out),
        ("mutated-order",),
    )
    rows.append(
        (
            "selected_record_not_in_full_state_records",
            _clone_full_dp(base_full),
            selected_not_member,
            base_packet,
            "selected_record_not_in_full_state_records",
        )
    )

    suffix_gap = _clone_compressed_dp(base_compressed)
    suffix_gap[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        1,
        tuple(base_compressed[0].order_ids),
    )
    rows.append(
        (
            "singleton_table_suffix_not_executable",
            _clone_full_dp(base_full),
            suffix_gap,
            base_packet,
            "singleton_table_suffix_not_executable",
        )
    )

    dominance_failure = _clone_compressed_dp(base_compressed)
    dominance_failure[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        int(base_full[0][0].reserve_out) + 1_000,
        tuple(base_compressed[0].order_ids),
    )
    rows.append(
        (
            "selected_final_reserve_dominance_failure",
            _clone_full_dp(base_full),
            dominance_failure,
            base_packet,
            "selected_final_reserve_dominance_failure",
        )
    )

    output: list[dict[str, Any]] = []
    for mutation_id, full_dp, compressed_dp, packet, expected_reason in rows:
        verification = _verify_case_arrays(case, full_dp=full_dp, compressed_dp=compressed_dp, packet=packet)
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
    rows: list[dict[str, Any]] = []
    first_case: _StressCase | None = None
    first_packet: dict[str, Any] | None = None
    for case in _iter_cases():
        if first_case is None:
            first_case = case
            first_packet = build_case_packet(case)
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
        "schema": "zenodex/ab_strict_zero_min_arbitrary_subset_family_certificate_search/v1",
        "seed": SEED,
        "case_count": CASE_COUNT,
        "strict_case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "mask_count": sum(int(row["mask_count"]) for row in rows),
        "record_count": sum(int(row["record_count"]) for row in rows),
        "singleton_table_obligation_count": sum(
            int(row["singleton_table_obligation_count"]) for row in rows
        ),
        "selected_suffix_executable_count": sum(
            int(row["selected_suffix_executable_count"]) for row in rows
        ),
        "dominance_check_count": sum(int(row["dominance_check_count"]) for row in rows),
        "full_runtime_completion_count": sum(
            int(row["full_runtime_completion_count"]) for row in rows
        ),
        "max_records_per_mask": max((int(row["max_records_per_mask"]) for row in rows), default=0),
        "max_suffix_per_mask": max((int(row["max_suffix_per_mask"]) for row in rows), default=0),
        "coverage": {
            "n_counts": dict(sorted(n_counts.items())),
            "fee_bps_counts": dict(sorted(fee_counts.items(), key=lambda item: int(item[0]))),
            "pattern_counts": dict(sorted(pattern_counts.items())),
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
        "first_packet": first_packet,
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
        and search["singleton_table_obligation_count"] == search["selected_suffix_executable_count"]
        and search["dominance_check_count"] == search["full_runtime_completion_count"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A bounded host certificate checker instantiates the Lean "
            "StrictSubsetFamilyHostTable shape as singleton subset-family "
            "obligations over every reachable mask and completion suffix in "
            "the strict zero-min stress corpus."
        ),
        "authority_boundary": (
            "Research-only certificate evidence; no settlement, state-root, production, "
            "or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_strict_zero_min_arbitrary_subset_family_certificate.py"
        ),
        "non_claims": [
            "This bounded checker is not a Lean proof of the concrete Python emitter.",
            "This checker does not prove Lean-to-Python refinement.",
            "This checker does not prove exhaustive coverage over all pool states.",
            "This checker does not define canonical tie order.",
            "Nonzero min_amount_out batches are outside this artifact.",
            "The singleton-family packet shape is a host certificate shape, not a production ABI.",
            "No settlement, state-root, production, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Arbitrary Subset-Family Certificate - 2026-06-29",
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
        f"- Singleton table obligations: `{search['singleton_table_obligation_count']}`",
        f"- Selected suffix executable checks: `{search['selected_suffix_executable_count']}`",
        f"- Dominance checks: `{search['dominance_check_count']}`",
        f"- Runtime-executable full completions: `{search['full_runtime_completion_count']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        "",
        "## Lean Shape Mirrored",
        "",
        "```text",
        "StrictSubsetFamilyHostTable:",
        "  masks = [mask]",
        "  winner = mask",
        "  suffix = fixed completion suffix",
        "  packetHashBound = true",
        "  noAuthorityEffect = true",
        "  winnerMembershipBound = true",
        "```",
        "",
        "For each singleton family, the checker validates local pruning, winner membership,",
        "selected suffix executability, and selected-final reserve dominance against all",
        "full-state records for the same mask and suffix.",
        "",
        "## Coverage",
        "",
        f"- `n` histogram: `{coverage['n_counts']}`",
        f"- Fee histogram: `{coverage['fee_bps_counts']}`",
        f"- Pattern histogram: `{coverage['pattern_counts']}`",
        f"- Max records per mask: `{search['max_records_per_mask']}`",
        f"- Max suffixes per mask: `{search['max_suffix_per_mask']}`",
        "",
        "## First Packet",
        "",
        "```json",
        json.dumps(search["first_packet"], indent=2, sort_keys=True),
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
            "| case | ok | n | masks | singleton tables | dominance checks |",
            "| --- | --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['bit_count']}` | "
            f"`{row['mask_count']}` | `{row['singleton_table_obligation_count']}` | "
            f"`{row['dominance_check_count']}` |"
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
