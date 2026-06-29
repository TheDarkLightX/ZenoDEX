#!/usr/bin/env python3
"""Bounded n=8 sample for AB strict zero-min reserve-state quotients.

This research-only checker extends the reserve-state quotient replay beyond the
committed n=7 corpus. It generates full reachable order-history records for a
small deterministic n=8 corpus, then checks selected reserve-state quotient
obligations over a deterministic mask and suffix sample.
"""

from __future__ import annotations

import argparse
import copy
import itertools
import json
import random
import sys
import time
from math import factorial
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_ab_strict_zero_min_arbitrary_subset_family_certificate import (  # noqa: E402
    AUTHORITY_BOUNDARY,
    _case_context,
    _case_has_zero_min_amount_out,
    _case_summary_inputs,
)
from tools.check_ab_strict_zero_min_arbitrary_subset_family_extended_stress import (  # noqa: E402
    _histogram,
)
from tools.check_ab_strict_zero_min_arbitrary_subset_family_n7_randomized import (  # noqa: E402
    _case_from_amounts,
)
from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _HostRecord,
    _compressed_records,
    _full_state_records,
    _sha256_json,
    _strip_timing,
)
from tools.check_ab_strict_zero_min_reserve_state_quotient_certificate import (  # noqa: E402
    _ReserveState,
    _packet_hash,
    _quotient_digest,
    _quotient_rows,
    _reserve_state,
    _run_suffix_from_state,
    _state_digest,
    _state_json,
    _suffix_ids,
    _with_packet_hash,
)
from tools.check_ab_strict_zero_min_subset_induction_witness import (  # noqa: E402
    _amount_sums,
    _clone_compressed_dp,
    _clone_full_dp,
    _remaining_intents,
)
from tools.check_ab_zero_min_economic_compression_certificate import _short  # noqa: E402

OUT_DIR = (
    REPO_ROOT
    / "generated"
    / "zenodex_ab_strict_zero_min_reserve_state_quotient_n8_sample_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_RESERVE_STATE_QUOTIENT_N8_SAMPLE_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_strict_zero_min_reserve_state_quotient_n8_sample_packet.v1"
REPORT_SCHEMA = "zenodex.ab_strict_zero_min_reserve_state_quotient_n8_sample_report.v1"
SEARCH_SCHEMA = "zenodex/ab_strict_zero_min_reserve_state_quotient_n8_sample_search/v1"
SCOPE = "n8_same_pool_same_direction_exact_in_zero_min_strict_executable_reserve_state_quotient_sample"
SEED = 2_026_062_908
BIT_COUNT = 8
TARGET_CASE_COUNT = 3
SUFFIX_SAMPLE_LIMIT = 24
EXPECTED_NEGATIVE_CONTROL_COUNT = 12


def _n8_cases() -> list[Any]:
    return [
        _case_from_amounts(
            case_no=8_800,
            case_id="n8_sample_000_thin_fee9000_stair",
            reserve_in=10_000,
            reserve_out=1_600,
            fee_bps=9_000,
            amounts=[100, 101, 102, 103, 104, 105, 106, 107],
            pattern="n8_thin_high_fee/stair",
        ),
        _case_from_amounts(
            case_no=8_801,
            case_id="n8_sample_001_deep_fee30_tie",
            reserve_in=85_000,
            reserve_out=1_400_000,
            fee_bps=30,
            amounts=[45, 45, 46, 46, 47, 47, 48, 48],
            pattern="n8_deep_low_fee/tie",
        ),
        _case_from_amounts(
            case_no=8_802,
            case_id="n8_sample_002_burst_fee2500",
            reserve_in=50_000,
            reserve_out=2_200_000,
            fee_bps=2_500,
            amounts=[520, 44, 48, 52, 56, 60, 64, 68],
            pattern="n8_deep_mid_fee/front_burst",
        ),
    ]


def _sample_mask_ids(n: int) -> list[int]:
    full_mask = (1 << n) - 1
    base = {
        0,
        full_mask,
        0x01,
        0x02,
        0x04,
        0x08,
        0x10,
        0x20,
        0x40,
        0x80,
        0x0F,
        0xF0,
        0x33,
        0xCC,
        0x55,
        0xAA,
        0x3C,
        0xC3,
    }
    return sorted(mask & full_mask for mask in base)


def _sample_plan(n: int) -> dict[str, Any]:
    return {
        "seed": SEED,
        "bit_count": int(n),
        "mask_ids": _sample_mask_ids(n),
        "suffix_sample_limit": SUFFIX_SAMPLE_LIMIT,
        "suffix_sampling": "all suffixes up to limit; otherwise first, last, and deterministic random indexes",
        "full_dp_generated_all_masks": True,
    }


def _lean_contract() -> dict[str, str]:
    return {
        "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
        "host_table": "ReserveStateQuotientHostTable",
        "summary_structure": "ReserveStateQuotientObservedSummary",
        "summary_valid_predicate": "reserveStateQuotientObservedSummaryValid",
        "summary_endpoint": "reserveStateQuotientObservedSummary_validates",
        "projection_shape": "one_digest_row_per_sampled_mask_sampled_suffix",
    }


def _lean_observed_summary_row(
    *,
    mask_id: int,
    suffix_ids: tuple[str, ...],
    state_count: int,
    selected_state: _ReserveState,
    quotient_digest: str,
    executed_input: int,
    initial_reserve_out: int,
) -> dict[str, Any]:
    return {
        "mask_id": int(mask_id),
        "suffix_order_ids": list(suffix_ids),
        "suffix_short": _short(suffix_ids),
        "lean_structure": "ReserveStateQuotientObservedSummary",
        "lean_endpoint": "reserveStateQuotientObservedSummary_validates",
        "observed_state_count": int(state_count),
        "observed_selected_reserve_in": int(selected_state.processed_reserve_in),
        "observed_selected_reserve_out": int(selected_state.reserve_out),
        "observed_executed_input": int(executed_input),
        "observed_initial_reserve_out": int(initial_reserve_out),
        "selected_state_digest": _state_digest(selected_state),
        "table_state_digest": quotient_digest,
    }


def _lean_observed_summary_digest(rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "contract": _lean_contract(),
        "row_count": len(rows),
        "digest": _sha256_json(rows),
        "first_row": rows[0] if rows else None,
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
    if packet.get("quotient_family_bound") is not True:
        reasons.append("quotient_family_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
    if packet.get("sampled_n8_bound") is not True:
        reasons.append("sampled_n8_bound_missing")
    if packet.get("sample_suffix_bound") is not True:
        reasons.append("sample_suffix_bound_missing")
    if packet.get("lean_contract") != _lean_contract():
        reasons.append("packet_lean_contract_mismatch")
    if packet.get("packet_hash") != _packet_hash(packet):
        reasons.append("packet_hash_mismatch")
    reasons.extend(_packet_min_amount_out_reasons(packet))
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


def _suffixes_for_mask(mask_id: int, case: Any, *, case_index: int) -> tuple[tuple[Any, ...], ...]:
    remaining = tuple(_remaining_intents(mask_id, case.intents))
    suffix_universe_count = factorial(len(remaining))
    suffixes = tuple(itertools.permutations(remaining))
    if suffix_universe_count <= SUFFIX_SAMPLE_LIMIT:
        return suffixes
    rng = random.Random(SEED + case_index * 10_007 + mask_id * 1_009)
    selected_indexes = {0, suffix_universe_count - 1}
    needed = SUFFIX_SAMPLE_LIMIT - len(selected_indexes)
    selected_indexes.update(rng.sample(range(1, suffix_universe_count - 1), needed))
    return tuple(suffixes[index] for index in sorted(selected_indexes))


def _mask_summary(
    *,
    mask_id: int,
    selected_state: _ReserveState,
    full_records: list[_HostRecord],
    suffix_sample_count: int,
    suffix_universe_count: int,
) -> dict[str, Any]:
    return {
        "mask_id": int(mask_id),
        "selected_state": _state_json(selected_state),
        "selected_state_digest": _state_digest(selected_state),
        "full_record_count": len(full_records),
        "quotient_state_count": len(_quotient_rows(full_records)),
        "quotient_digest": _quotient_digest(full_records),
        "suffix_sample_count": int(suffix_sample_count),
        "suffix_universe_count": int(suffix_universe_count),
    }


def _all_quotient_state_count(full_dp: list[list[_HostRecord]]) -> int:
    return sum(len(_quotient_rows(records)) for records in full_dp if records)


def _verify_case_arrays(
    case: Any,
    *,
    case_index: int,
    full_dp: list[list[_HostRecord]],
    compressed_dp: list[_HostRecord | None],
    packet: Mapping[str, Any] | None,
) -> dict[str, Any]:
    context = _case_context(case)
    n = len(case.intents)
    full_mask = (1 << n) - 1
    sampled_mask_ids = _sample_mask_ids(n)
    amount_sums = _amount_sums(case.intents)
    reasons: list[str] = []
    reasons.extend(_packet_rail_reasons(packet))
    first_failure: dict[str, Any] | None = None

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
    if compressed_dp[full_mask] is None:
        reasons.append("compressed_full_mask_not_executable")
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=full_mask,
            reason="compressed_full_mask_not_executable",
        )

    sampled_mask_count = 0
    sampled_full_record_count = 0
    sampled_quotient_state_count = 0
    sampled_suffix_count = 0
    suffix_universe_count = 0
    selected_suffix_executable_count = 0
    quotient_dominance_check_count = 0
    quotient_runtime_completion_count = 0
    baseline_full_dominance_check_count = 0
    max_full_records_per_sampled_mask = 0
    max_quotient_states_per_sampled_mask = 0
    max_suffix_sample_per_mask = 0
    max_suffix_universe_per_mask = 0
    sampled_remaining_counts: list[int] = []
    mask_summaries: list[dict[str, Any]] = []
    obligation_digest_rows: list[dict[str, Any]] = []
    lean_observed_summary_rows: list[dict[str, Any]] = []
    first_obligation: dict[str, Any] | None = None
    executed_input = int(amount_sums[full_mask])
    initial_reserve_out = int(context.r_out0)

    for mask_id in sampled_mask_ids:
        full_records = full_dp[mask_id]
        if not full_records:
            reasons.append("sampled_mask_not_reachable")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=mask_id,
                reason="sampled_mask_not_reachable",
            )
            continue
        sampled_mask_count += 1
        sampled_full_record_count += len(full_records)
        quotient_rows = _quotient_rows(full_records)
        quotient_digest = _quotient_digest(full_records)
        quotient_states = {
            _ReserveState(int(row["processed_reserve_in"]), int(row["reserve_out"]))
            for row in quotient_rows
        }
        sampled_quotient_state_count += len(quotient_states)
        max_full_records_per_sampled_mask = max(
            max_full_records_per_sampled_mask,
            len(full_records),
        )
        max_quotient_states_per_sampled_mask = max(
            max_quotient_states_per_sampled_mask,
            len(quotient_states),
        )

        selected = compressed_dp[mask_id]
        expected_processed_reserve_in = int(context.r_in0) + int(amount_sums[mask_id])
        if selected is None:
            reasons.append("compressed_record_missing")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=mask_id,
                reason="compressed_record_missing",
            )
            continue
        selected_state = _reserve_state(selected)
        if selected_state not in quotient_states:
            reasons.append("selected_state_not_in_quotient_family")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=mask_id,
                reason="selected_state_not_in_quotient_family",
                selected_state=_state_json(selected_state),
            )
        if int(selected_state.processed_reserve_in) != expected_processed_reserve_in:
            reasons.append("selected_processed_reserve_in_mismatch")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=mask_id,
                reason="selected_processed_reserve_in_mismatch",
                selected_state=_state_json(selected_state),
                expected_processed_reserve_in=expected_processed_reserve_in,
            )
        for state in quotient_states:
            if int(state.processed_reserve_in) != expected_processed_reserve_in:
                reasons.append("quotient_state_processed_reserve_in_mismatch")
                first_failure = _new_failure(
                    first_failure,
                    case_id=case.case_id,
                    mask_id=mask_id,
                    reason="quotient_state_processed_reserve_in_mismatch",
                    quotient_state=_state_json(state),
                    expected_processed_reserve_in=expected_processed_reserve_in,
                )

        min_reserve_out = min(int(state.reserve_out) for state in quotient_states)
        if int(selected_state.reserve_out) != min_reserve_out:
            reasons.append("selected_reserve_out_not_min")
            first_failure = _new_failure(
                first_failure,
                case_id=case.case_id,
                mask_id=mask_id,
                reason="selected_reserve_out_not_min",
                selected_state=_state_json(selected_state),
                min_reserve_out=min_reserve_out,
            )

        suffixes = _suffixes_for_mask(mask_id, case, case_index=case_index)
        suffix_sample_count = len(suffixes)
        remaining_count = len(_remaining_intents(mask_id, case.intents))
        this_suffix_universe_count = factorial(remaining_count)
        sampled_suffix_count += suffix_sample_count
        suffix_universe_count += this_suffix_universe_count
        max_suffix_sample_per_mask = max(max_suffix_sample_per_mask, suffix_sample_count)
        max_suffix_universe_per_mask = max(max_suffix_universe_per_mask, this_suffix_universe_count)
        sampled_remaining_counts.append(remaining_count)
        mask_summaries.append(
            _mask_summary(
                mask_id=mask_id,
                selected_state=selected_state,
                full_records=full_records,
                suffix_sample_count=suffix_sample_count,
                suffix_universe_count=this_suffix_universe_count,
            )
        )
        for suffix in suffixes:
            suffix_id_tuple = _suffix_ids(suffix)
            lean_observed_summary_rows.append(
                _lean_observed_summary_row(
                    mask_id=mask_id,
                    suffix_ids=suffix_id_tuple,
                    state_count=len(quotient_states),
                    selected_state=selected_state,
                    quotient_digest=quotient_digest,
                    executed_input=executed_input,
                    initial_reserve_out=initial_reserve_out,
                )
            )
            selected_result = _run_suffix_from_state(selected_state, suffix, context)
            if selected_result is None:
                reasons.append("selected_suffix_not_executable")
                first_failure = _new_failure(
                    first_failure,
                    case_id=case.case_id,
                    mask_id=mask_id,
                    reason="selected_suffix_not_executable",
                    selected_state=_state_json(selected_state),
                    suffix_short=_short(suffix_id_tuple),
                )
            else:
                selected_suffix_executable_count += 1

            obligation_row = {
                "mask_id": int(mask_id),
                "suffix_short": _short(suffix_id_tuple),
                "selected_state_digest": _state_digest(selected_state),
                "quotient_digest": quotient_digest,
            }
            obligation_digest_rows.append(obligation_row)
            if first_obligation is None:
                first_obligation = {
                    "mask_id": int(mask_id),
                    "suffix_short": _short(suffix_id_tuple),
                    "selected_state": _state_json(selected_state),
                    "quotient_state_count": len(quotient_states),
                    "quotient_digest": quotient_digest,
                }

            baseline_full_dominance_check_count += len(full_records)
            for state in quotient_states:
                quotient_dominance_check_count += 1
                quotient_result = _run_suffix_from_state(state, suffix, context)
                if quotient_result is None:
                    reasons.append("quotient_suffix_not_executable")
                    first_failure = _new_failure(
                        first_failure,
                        case_id=case.case_id,
                        mask_id=mask_id,
                        reason="quotient_suffix_not_executable",
                        quotient_state=_state_json(state),
                        suffix_short=_short(suffix_id_tuple),
                    )
                    continue
                quotient_runtime_completion_count += 1
                if selected_result is None:
                    continue
                if int(selected_result.reserve_out) > int(quotient_result.reserve_out):
                    reasons.append("selected_final_reserve_dominance_failure")
                    first_failure = _new_failure(
                        first_failure,
                        case_id=case.case_id,
                        mask_id=mask_id,
                        reason="selected_final_reserve_dominance_failure",
                        quotient_final=_state_json(quotient_result),
                        selected_final=_state_json(selected_result),
                        suffix_short=_short(suffix_id_tuple),
                    )

    quotient_summary = {
        "sampled_mask_count": sampled_mask_count,
        "sampled_full_record_count": sampled_full_record_count,
        "sampled_quotient_state_count": sampled_quotient_state_count,
        "sampled_record_compression_saved": sampled_full_record_count - sampled_quotient_state_count,
        "sampled_suffix_count": sampled_suffix_count,
        "suffix_universe_count": suffix_universe_count,
        "selected_suffix_executable_count": selected_suffix_executable_count,
        "quotient_dominance_check_count": quotient_dominance_check_count,
        "quotient_runtime_completion_count": quotient_runtime_completion_count,
        "baseline_full_dominance_check_count": baseline_full_dominance_check_count,
        "dominance_check_compression_saved": (
            baseline_full_dominance_check_count - quotient_dominance_check_count
        ),
        "max_full_records_per_sampled_mask": max_full_records_per_sampled_mask,
        "max_quotient_states_per_sampled_mask": max_quotient_states_per_sampled_mask,
        "max_suffix_sample_per_mask": max_suffix_sample_per_mask,
        "max_suffix_universe_per_mask": max_suffix_universe_per_mask,
        "quotient_obligation_digest": _sha256_json(obligation_digest_rows),
    }
    lean_observed_summary = _lean_observed_summary_digest(lean_observed_summary_rows)

    if packet is not None:
        if packet.get("case_id") != case.case_id:
            reasons.append("packet_case_id_mismatch")
        if packet.get("bit_count") != n:
            reasons.append("packet_bit_count_mismatch")
        if packet.get("full_mask") != full_mask:
            reasons.append("packet_full_mask_mismatch")
        if packet.get("sample_plan") != _sample_plan(n):
            reasons.append("packet_sample_plan_mismatch")
        if packet.get("quotient_summary") != quotient_summary:
            reasons.append("packet_quotient_summary_mismatch")
        if packet.get("lean_observed_summary") != lean_observed_summary:
            reasons.append("packet_lean_observed_summary_mismatch")
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
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "fee_bps": int(context.pool_state.fee_bps),
        "pattern": case.pattern,
        "stress": {"seed": SEED, "pattern": case.pattern, "case_count": TARGET_CASE_COUNT},
        "full_mask": full_mask,
        "mask_count_all": sum(1 for records in full_dp if records),
        "full_record_count_all": sum(len(records) for records in full_dp),
        "quotient_state_count_all": _all_quotient_state_count(full_dp),
        "sampled_remaining_counts": sampled_remaining_counts,
        "mask_summaries": mask_summaries,
        "first_obligation": first_obligation,
        "lean_observed_summary": lean_observed_summary,
        "full_mask_selected_state": _state_json(_reserve_state(compressed_dp[full_mask]))
        if compressed_dp[full_mask] is not None
        else None,
        **quotient_summary,
    }


def build_case_packet(
    case: Any,
    *,
    case_index: int,
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
    verification = _verify_case_arrays(
        case,
        case_index=case_index,
        full_dp=full_dp,
        compressed_dp=compressed_dp,
        packet=None,
    )
    packet = {
        "schema": PACKET_SCHEMA,
        **_case_summary_inputs(case),
        "scope": SCOPE,
        "stress": {"seed": SEED, "pattern": case.pattern, "case_count": TARGET_CASE_COUNT},
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "quotient_family_bound": True,
        "reserve_state_only_bound": True,
        "sampled_n8_bound": True,
        "sample_suffix_bound": True,
        "lean_contract": _lean_contract(),
        "sample_plan": _sample_plan(len(case.intents)),
        "quotient_contract": {
            "state": "processed_reserve_in,reserve_out",
            "objective": "sampled selected reserve_out is minimum per sampled reachable mask",
            "suffix_property": "sampled future exact-in CPMM behavior is reserve-state determined",
            "non_claim": "bounded n=8 sample; not exhaustive n=8 and not a production ABI",
        },
        "quotient_summary": {
            key: verification[key]
            for key in (
                "sampled_mask_count",
                "sampled_full_record_count",
                "sampled_quotient_state_count",
                "sampled_record_compression_saved",
                "sampled_suffix_count",
                "suffix_universe_count",
                "selected_suffix_executable_count",
                "quotient_dominance_check_count",
                "quotient_runtime_completion_count",
                "baseline_full_dominance_check_count",
                "dominance_check_compression_saved",
                "max_full_records_per_sampled_mask",
                "max_quotient_states_per_sampled_mask",
                "max_suffix_sample_per_mask",
                "max_suffix_universe_per_mask",
                "quotient_obligation_digest",
            )
        },
        "lean_observed_summary": verification["lean_observed_summary"],
        "mask_summaries": verification["mask_summaries"],
        "first_obligation": verification["first_obligation"],
    }
    return _with_packet_hash(packet)


def verify_case_packet(case: Any, *, case_index: int, packet: Mapping[str, Any]) -> dict[str, Any]:
    context = _case_context(case)
    return _verify_case_arrays(
        case,
        case_index=case_index,
        full_dp=_full_state_records(case.intents, context),
        compressed_dp=_compressed_records(case.intents, context),
        packet=packet,
    )


def verify_case(case: Any, *, case_index: int) -> dict[str, Any]:
    context = _case_context(case)
    full_dp = _full_state_records(case.intents, context)
    compressed_dp = _compressed_records(case.intents, context)
    packet = build_case_packet(
        case,
        case_index=case_index,
        full_dp=full_dp,
        compressed_dp=compressed_dp,
    )
    verification = _verify_case_arrays(
        case,
        case_index=case_index,
        full_dp=full_dp,
        compressed_dp=compressed_dp,
        packet=packet,
    )
    return {key: value for key, value in verification.items() if key != "mask_summaries"} | {
        "packet_hash": packet["packet_hash"],
    }


def _rehash_packet(packet: dict[str, Any]) -> dict[str, Any]:
    return _with_packet_hash(packet)


def _find_sampled_multistate_mask(full_dp: list[list[_HostRecord]]) -> int:
    for mask_id in _sample_mask_ids(BIT_COUNT):
        if len({_reserve_state(record) for record in full_dp[mask_id]}) > 1:
            return mask_id
    raise ValueError("no sampled multi-state mask available for negative control")


def _negative_controls(
    case: Any,
    *,
    case_index: int,
    multistate_case: Any,
    multistate_case_index: int,
) -> list[dict[str, Any]]:
    context = _case_context(case)
    base_full = _full_state_records(case.intents, context)
    base_compressed = _compressed_records(case.intents, context)
    base_packet = build_case_packet(
        case,
        case_index=case_index,
        full_dp=base_full,
        compressed_dp=base_compressed,
    )
    multi_context = _case_context(multistate_case)
    multi_full = _full_state_records(multistate_case.intents, multi_context)
    multi_compressed = _compressed_records(multistate_case.intents, multi_context)
    multi_packet = build_case_packet(
        multistate_case,
        case_index=multistate_case_index,
        full_dp=multi_full,
        compressed_dp=multi_compressed,
    )

    rows: list[
        tuple[str, Any, int, list[list[_HostRecord]], list[_HostRecord | None], dict[str, Any], str]
    ] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    rows.append(
        (
            "packet_hash_mismatch",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            bad_hash,
            "packet_hash_mismatch",
        )
    )

    bad_authority = copy.deepcopy(base_packet)
    bad_authority["no_authority_effect"] = False
    rows.append(
        (
            "authority_effect_present",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_authority),
            "authority_effect_present",
        )
    )

    bad_family = copy.deepcopy(base_packet)
    bad_family["quotient_family_bound"] = False
    rows.append(
        (
            "quotient_family_bound_missing",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_family),
            "quotient_family_bound_missing",
        )
    )

    bad_state_bound = copy.deepcopy(base_packet)
    bad_state_bound["reserve_state_only_bound"] = False
    rows.append(
        (
            "reserve_state_only_bound_missing",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_state_bound),
            "reserve_state_only_bound_missing",
        )
    )

    bad_sample_bound = copy.deepcopy(base_packet)
    bad_sample_bound["sampled_n8_bound"] = False
    rows.append(
        (
            "sampled_n8_bound_missing",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_sample_bound),
            "sampled_n8_bound_missing",
        )
    )

    bad_sample_plan = copy.deepcopy(base_packet)
    bad_sample_plan["sample_plan"]["suffix_sample_limit"] += 1
    rows.append(
        (
            "packet_sample_plan_mismatch",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_sample_plan),
            "packet_sample_plan_mismatch",
        )
    )

    bad_lean_contract = copy.deepcopy(base_packet)
    bad_lean_contract["lean_contract"]["summary_endpoint"] = "stale_endpoint"
    rows.append(
        (
            "packet_lean_contract_mismatch",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_lean_contract),
            "packet_lean_contract_mismatch",
        )
    )

    bad_lean_observed_summary = copy.deepcopy(base_packet)
    bad_lean_observed_summary["lean_observed_summary"]["row_count"] += 1
    rows.append(
        (
            "packet_lean_observed_summary_mismatch",
            case,
            case_index,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_lean_observed_summary),
            "packet_lean_observed_summary_mismatch",
        )
    )

    missing_compressed = _clone_compressed_dp(base_compressed)
    missing_compressed[0] = None
    rows.append(
        (
            "compressed_record_missing",
            case,
            case_index,
            _clone_full_dp(base_full),
            missing_compressed,
            base_packet,
            "compressed_record_missing",
        )
    )

    selected_not_member = _clone_compressed_dp(base_compressed)
    selected_not_member[0] = _HostRecord(
        int(base_compressed[0].processed_reserve_in),
        int(base_compressed[0].reserve_out) + 1,
        tuple(base_compressed[0].order_ids),
    )
    rows.append(
        (
            "selected_state_not_in_quotient_family",
            case,
            case_index,
            _clone_full_dp(base_full),
            selected_not_member,
            base_packet,
            "selected_state_not_in_quotient_family",
        )
    )

    multistate_mask = _find_sampled_multistate_mask(multi_full)
    non_min_state_record = max(multi_full[multistate_mask], key=lambda record: int(record.reserve_out))
    selected_not_min = _clone_compressed_dp(multi_compressed)
    selected_not_min[multistate_mask] = non_min_state_record
    rows.append(
        (
            "selected_reserve_out_not_min",
            multistate_case,
            multistate_case_index,
            _clone_full_dp(multi_full),
            selected_not_min,
            multi_packet,
            "selected_reserve_out_not_min",
        )
    )

    suffix_gap_full = _clone_full_dp(base_full)
    suffix_gap_compressed = _clone_compressed_dp(base_compressed)
    suffix_gap_full[0][0] = _HostRecord(
        int(suffix_gap_full[0][0].processed_reserve_in),
        1,
        tuple(suffix_gap_full[0][0].order_ids),
    )
    suffix_gap_compressed[0] = suffix_gap_full[0][0]
    rows.append(
        (
            "selected_suffix_not_executable",
            case,
            case_index,
            suffix_gap_full,
            suffix_gap_compressed,
            base_packet,
            "selected_suffix_not_executable",
        )
    )

    output: list[dict[str, Any]] = []
    for mutation_id, target_case, target_case_index, full_dp, compressed_dp, packet, expected_reason in rows:
        verification = _verify_case_arrays(
            target_case,
            case_index=target_case_index,
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
    cases = _n8_cases()
    rows = [verify_case(case, case_index=index) for index, case in enumerate(cases)]
    invalid_rows = [row for row in rows if not row["ok"]]
    negative_controls = _negative_controls(
        cases[0],
        case_index=0,
        multistate_case=cases[1],
        multistate_case_index=1,
    )
    all_full_records = sum(int(row["full_record_count_all"]) for row in rows)
    all_quotient_states = sum(int(row["quotient_state_count_all"]) for row in rows)
    sampled_full_records = sum(int(row["sampled_full_record_count"]) for row in rows)
    sampled_quotient_states = sum(int(row["sampled_quotient_state_count"]) for row in rows)
    baseline_dominance = sum(int(row["baseline_full_dominance_check_count"]) for row in rows)
    quotient_dominance = sum(int(row["quotient_dominance_check_count"]) for row in rows)
    lean_observed_summary_count = sum(
        int(row["lean_observed_summary"]["row_count"]) for row in rows
    )
    return {
        "schema": SEARCH_SCHEMA,
        "source_seed": SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "sample_plan": _sample_plan(BIT_COUNT),
        "mask_count_all": sum(int(row["mask_count_all"]) for row in rows),
        "full_record_count_all": all_full_records,
        "quotient_state_count_all": all_quotient_states,
        "all_record_compression_saved": all_full_records - all_quotient_states,
        "all_record_compression_ratio": round(all_full_records / max(1, all_quotient_states), 6),
        "sampled_mask_count": sum(int(row["sampled_mask_count"]) for row in rows),
        "sampled_full_record_count": sampled_full_records,
        "sampled_quotient_state_count": sampled_quotient_states,
        "sampled_record_compression_saved": sampled_full_records - sampled_quotient_states,
        "sampled_record_compression_ratio": round(
            sampled_full_records / max(1, sampled_quotient_states),
            6,
        ),
        "sampled_suffix_count": sum(int(row["sampled_suffix_count"]) for row in rows),
        "lean_observed_summary_count": lean_observed_summary_count,
        "lean_observed_summary_digest": _sha256_json(
            [row["lean_observed_summary"]["digest"] for row in rows]
        ),
        "suffix_universe_count": sum(int(row["suffix_universe_count"]) for row in rows),
        "selected_suffix_executable_count": sum(
            int(row["selected_suffix_executable_count"]) for row in rows
        ),
        "baseline_full_dominance_check_count": baseline_dominance,
        "quotient_dominance_check_count": quotient_dominance,
        "quotient_runtime_completion_count": sum(
            int(row["quotient_runtime_completion_count"]) for row in rows
        ),
        "dominance_check_compression_saved": baseline_dominance - quotient_dominance,
        "dominance_check_compression_ratio": round(baseline_dominance / max(1, quotient_dominance), 6),
        "max_full_records_per_sampled_mask": max(
            (int(row["max_full_records_per_sampled_mask"]) for row in rows),
            default=0,
        ),
        "max_quotient_states_per_sampled_mask": max(
            (int(row["max_quotient_states_per_sampled_mask"]) for row in rows),
            default=0,
        ),
        "max_suffix_sample_per_mask": max(
            (int(row["max_suffix_sample_per_mask"]) for row in rows),
            default=0,
        ),
        "max_suffix_universe_per_mask": max(
            (int(row["max_suffix_universe_per_mask"]) for row in rows),
            default=0,
        ),
        "coverage": {
            "n_counts": _histogram(rows, "bit_count"),
            "fee_bps_counts": _histogram(rows, "fee_bps"),
            "pattern_counts": _histogram(rows, "pattern"),
            "sampled_remaining_counts": {
                str(count): sum(
                    1
                    for row in rows
                    for item in row["sampled_remaining_counts"]
                    if int(item) == count
                )
                for count in range(BIT_COUNT + 1)
            },
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
        and search["full_record_count_all"] > search["quotient_state_count_all"]
        and search["sampled_full_record_count"] > search["sampled_quotient_state_count"]
        and search["sampled_suffix_count"] == search["selected_suffix_executable_count"]
        and search["lean_observed_summary_count"] == search["sampled_suffix_count"]
        and search["quotient_dominance_check_count"] == search["quotient_runtime_completion_count"]
        and search["negative_control_count"] == EXPECTED_NEGATIVE_CONTROL_COUNT
        and search["negative_control_accept_count"] == 0
        and deterministic["ok"]
    )
    return {
        "schema": REPORT_SCHEMA,
        "date": "2026-06-29",
        "ok": ok,
        "summary": (
            "A deterministic n=8 sample extends the reserve-state quotient replay "
            "beyond the n=7 certificate by generating full reachable records for "
            "all masks and checking sampled suffix obligations."
        ),
        "authority_boundary": (
            "Research-only quotient replay evidence; no settlement, state-root, "
            "production, routing, matching, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_strict_zero_min_reserve_state_quotient_n8_sample_20260629.py"
        ),
        "non_claims": [
            "This is a bounded deterministic n=8 sample, not exhaustive n=8 coverage.",
            "This checker does not prove Python-to-Lean refinement.",
            "This checker does not prove JSON canonicalization or packet-hash computation in Lean.",
            "This checker does not define canonical tie order or preserve order-id history.",
            "This checker is restricted to strict executable same-pool, same-direction, exact-in, zero-min batches.",
            "This checker does not cover nonzero min_amount_out behavior.",
            "This checker has no settlement, state-root, production, routing, matching, or governance authority.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# ZenoDEX AB Strict Zero-Min Reserve-State Quotient n=8 Sample",
        "",
        "## Summary",
        "",
        str(report["summary"]),
        "",
        str(report["authority_boundary"]),
        "",
        "## Metrics",
        "",
        f"- Cases checked: `{search['case_count']}`",
        f"- Valid cases: `{search['valid_case_count']}`",
        f"- Full records across all masks: `{search['full_record_count_all']}`",
        f"- Quotient states across all masks: `{search['quotient_state_count_all']}`",
        f"- All-mask record compression ratio: `{search['all_record_compression_ratio']}`",
        f"- Sampled masks: `{search['sampled_mask_count']}`",
        f"- Sampled suffix obligations: `{search['sampled_suffix_count']}`",
        f"- Lean observed-summary rows: `{search['lean_observed_summary_count']}`",
        f"- Sampled suffix universe: `{search['suffix_universe_count']}`",
        f"- Quotient dominance checks: `{search['quotient_dominance_check_count']}`",
        f"- Dominance check compression ratio: `{search['dominance_check_compression_ratio']}`",
        f"- Negative controls: `{search['negative_control_count']}`",
        f"- Negative control accepts: `{search['negative_control_accept_count']}`",
        f"- Deterministic replay ok: `{report['deterministic_replay']['ok']}`",
        f"- Lean observed-summary digest: `{search['lean_observed_summary_digest']}`",
        "",
        "## Lean Projection Shape",
        "",
        "```json",
        json.dumps(report["lean_contract"], indent=2, sort_keys=True),
        "```",
        "",
        "Each sampled digest row binds the observed summary fields used by",
        "`reserveStateQuotientObservedSummary_validates`: quotient-state count, selected",
        "reserve-in, selected reserve-out, completed gross input, initial output reserve,",
        "selected-state digest, quotient-state digest, and one sampled completion suffix.",
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
        "| --- | --- | --- |",
    ]
    for row in search["negative_controls"]:
        lines.append(
            f"| `{row['mutation_id']}` | `{row['accepted']}` | `{row['expected_reason']}` |"
        )
    lines.extend(
        [
            "",
            "## Case Summary",
            "",
            "| case | ok | all records | all quotient states | sampled suffixes | quotient checks |",
            "| --- | --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for row in search["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['full_record_count_all']}` | "
            f"`{row['quotient_state_count_all']}` | `{row['sampled_suffix_count']}` | "
            f"`{row['quotient_dominance_check_count']}` |"
        )
    lines.extend(["", "## Non-Claims", ""])
    lines.extend(f"- {item}" for item in report["non_claims"])
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="print full report JSON")
    parser.add_argument("--no-markdown", action="store_true", help="skip markdown report write")
    args = parser.parse_args()

    report = build_report()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if not args.no_markdown:
        _write_markdown(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({"ok": report["ok"], "report": str(REPORT_JSON.relative_to(REPO_ROOT))}, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
