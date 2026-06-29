#!/usr/bin/env python3
"""Check reserve-state quotient certificates for AB strict zero-min n=7 cases.

This research-only checker tests a quotient witness shape for the AB strict
zero-min subset-family certificate. It groups full-state order histories by the
reserve state `(processed_reserve_in, reserve_out)` and verifies suffix
dominance over quotient states instead of over every order-id sequence.
"""

from __future__ import annotations

import argparse
import copy
import itertools
import json
import random
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_in  # noqa: E402
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
    SEED as N7_SEED,
    _boundary_positive_case,
    _random_candidate,
)
from tools.check_ab_strict_zero_min_emitter_witness import (  # noqa: E402
    _HostRecord,
    _compressed_records,
    _full_state_records,
    _sha256_json,
    _strip_timing,
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
    / "zenodex_ab_strict_zero_min_reserve_state_quotient_certificate_20260629"
)
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = (
    REPO_ROOT
    / "docs"
    / "research"
    / "ZENODEX_AB_STRICT_ZERO_MIN_RESERVE_STATE_QUOTIENT_CERTIFICATE_20260629.md"
)

PACKET_SCHEMA = "zenodex.ab_strict_zero_min_reserve_state_quotient_certificate_packet.v1"
REPORT_SCHEMA = "zenodex.ab_strict_zero_min_reserve_state_quotient_certificate_report.v1"
SCOPE = "n7_same_pool_same_direction_exact_in_zero_min_strict_executable_reserve_state_quotient"
TARGET_CASE_COUNT = 4
EXPECTED_NEGATIVE_CONTROL_COUNT = 12


@dataclass(frozen=True)
class _ReserveState:
    processed_reserve_in: int
    reserve_out: int


def _reserve_state(record: _HostRecord) -> _ReserveState:
    return _ReserveState(int(record.processed_reserve_in), int(record.reserve_out))


def _state_json(state: _ReserveState) -> dict[str, int]:
    return {
        "processed_reserve_in": int(state.processed_reserve_in),
        "reserve_out": int(state.reserve_out),
    }


def _state_digest(state: _ReserveState) -> str:
    return _sha256_json(_state_json(state))


def _quotient_rows(records: Iterable[_HostRecord]) -> list[dict[str, Any]]:
    grouped: dict[_ReserveState, list[_HostRecord]] = {}
    for record in records:
        grouped.setdefault(_reserve_state(record), []).append(record)
    rows: list[dict[str, Any]] = []
    for state, state_records in sorted(
        grouped.items(),
        key=lambda item: (item[0].processed_reserve_in, item[0].reserve_out),
    ):
        representative = min(tuple(record.order_ids) for record in state_records)
        rows.append(
            {
                **_state_json(state),
                "multiplicity": len(state_records),
                "representative_order_short": _short(representative),
            }
        )
    return rows


def _quotient_digest(records: Iterable[_HostRecord]) -> str:
    return _sha256_json(_quotient_rows(records))


def _lean_contract() -> dict[str, str]:
    return {
        "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
        "host_table": "ReserveStateQuotientHostTable",
        "summary_structure": "ReserveStateQuotientObservedSummary",
        "summary_valid_predicate": "reserveStateQuotientObservedSummaryValid",
        "summary_endpoint": "reserveStateQuotientObservedSummary_validates",
        "projection_shape": "one_digest_row_per_reachable_mask_completion_suffix",
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


def _lean_observed_summary_digest(
    rows: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "contract": _lean_contract(),
        "row_count": len(rows),
        "digest": _sha256_json(rows),
        "first_row": rows[0] if rows else None,
    }


def _suffix_ids(suffix: tuple[Any, ...]) -> tuple[str, ...]:
    return tuple(intent.intent_id for intent in suffix)


def _run_suffix_from_state(
    state: _ReserveState,
    suffix: tuple[Any, ...],
    context: Any,
) -> _ReserveState | None:
    reserve_in = int(state.processed_reserve_in)
    reserve_out = int(state.reserve_out)
    for intent in suffix:
        try:
            quote = quote_cpmm_swap_exact_in(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=int(intent.get_field("amount_in")),
                fee_bps=int(context.pool_state.fee_bps),
            )
        except ValueError:
            return None
        if int(quote.amount_out) < int(intent.get_field("min_amount_out", 0)):
            return None
        reserve_in = int(quote.reserve_in_after)
        reserve_out = int(quote.reserve_out_after)
    return _ReserveState(reserve_in, reserve_out)


def _without_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in packet.items() if key != "packet_hash"}


def _packet_hash(packet: Mapping[str, Any]) -> str:
    return _sha256_json(_without_packet_hash(packet))


def _with_packet_hash(packet: Mapping[str, Any]) -> dict[str, Any]:
    out = dict(packet)
    out["packet_hash"] = _packet_hash(out)
    return out


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
    if packet.get("quotient_family_bound") is not True:
        reasons.append("quotient_family_bound_missing")
    if packet.get("reserve_state_only_bound") is not True:
        reasons.append("reserve_state_only_bound_missing")
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


def _first_n7_positive_cases() -> list[Any]:
    rng = random.Random(N7_SEED)
    return [
        _boundary_positive_case(),
        _random_candidate(0, rng),
        _random_candidate(1, rng),
        _random_candidate(2, rng),
    ]


def _mask_summary(
    *,
    mask_id: int,
    selected_state: _ReserveState,
    full_records: list[_HostRecord],
    suffix_count: int,
) -> dict[str, Any]:
    return {
        "mask_id": int(mask_id),
        "selected_state": _state_json(selected_state),
        "selected_state_digest": _state_digest(selected_state),
        "full_record_count": len(full_records),
        "quotient_state_count": len(_quotient_rows(full_records)),
        "quotient_digest": _quotient_digest(full_records),
        "suffix_count": int(suffix_count),
    }


def _verify_case_arrays(
    case: Any,
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
            case_id=case.case_id,
            mask_id=0,
            reason="nonzero_min_amount_out_out_of_scope",
        )

    amount_sums = _amount_sums(case.intents)
    mask_count = 0
    full_record_count = 0
    quotient_state_count = 0
    quotient_table_obligation_count = 0
    selected_suffix_executable_count = 0
    quotient_dominance_check_count = 0
    quotient_runtime_completion_count = 0
    baseline_full_dominance_check_count = 0
    max_full_records_per_mask = 0
    max_quotient_states_per_mask = 0
    max_suffix_per_mask = 0
    mask_summaries: list[dict[str, Any]] = []
    obligation_digest_rows: list[dict[str, Any]] = []
    lean_observed_summary_rows: list[dict[str, Any]] = []
    first_obligation: dict[str, Any] | None = None
    executed_input = int(amount_sums[full_mask])
    initial_reserve_out = int(context.r_out0)

    if compressed_dp[full_mask] is None:
        reasons.append("compressed_full_mask_not_executable")
        first_failure = _new_failure(
            first_failure,
            case_id=case.case_id,
            mask_id=full_mask,
            reason="compressed_full_mask_not_executable",
        )

    for mask_id, full_records in enumerate(full_dp):
        if not full_records:
            continue
        mask_count += 1
        full_record_count += len(full_records)
        quotient_rows = _quotient_rows(full_records)
        quotient_states = {
            _ReserveState(int(row["processed_reserve_in"]), int(row["reserve_out"]))
            for row in quotient_rows
        }
        quotient_state_count += len(quotient_states)
        max_full_records_per_mask = max(max_full_records_per_mask, len(full_records))
        max_quotient_states_per_mask = max(max_quotient_states_per_mask, len(quotient_states))
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

        suffixes = tuple(itertools.permutations(_remaining_intents(mask_id, case.intents)))
        quotient_digest = _quotient_digest(full_records)
        max_suffix_per_mask = max(max_suffix_per_mask, len(suffixes))
        mask_summaries.append(
            _mask_summary(
                mask_id=mask_id,
                selected_state=selected_state,
                full_records=full_records,
                suffix_count=len(suffixes),
            )
        )
        for suffix in suffixes:
            suffix_id_tuple = _suffix_ids(suffix)
            quotient_table_obligation_count += 1
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
        "mask_count": mask_count,
        "full_record_count": full_record_count,
        "quotient_state_count": quotient_state_count,
        "record_compression_saved": full_record_count - quotient_state_count,
        "quotient_table_obligation_count": quotient_table_obligation_count,
        "selected_suffix_executable_count": selected_suffix_executable_count,
        "quotient_dominance_check_count": quotient_dominance_check_count,
        "quotient_runtime_completion_count": quotient_runtime_completion_count,
        "baseline_full_dominance_check_count": baseline_full_dominance_check_count,
        "dominance_check_compression_saved": (
            baseline_full_dominance_check_count - quotient_dominance_check_count
        ),
        "max_full_records_per_mask": max_full_records_per_mask,
        "max_quotient_states_per_mask": max_quotient_states_per_mask,
        "max_suffix_per_mask": max_suffix_per_mask,
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
        "bit_count": n,
        "fee_bps": int(case.pool.fee_bps),
        "pattern": case.pattern,
        "mask_summaries": mask_summaries,
        "first_obligation": first_obligation,
        "lean_observed_summary": lean_observed_summary,
        **quotient_summary,
        "full_mask_selected_state": _state_json(_reserve_state(compressed_dp[full_mask]))
        if compressed_dp[full_mask] is not None
        else None,
    }


def build_case_packet(
    case: Any,
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
        "scope": SCOPE,
        "authority_boundary": AUTHORITY_BOUNDARY,
        "packet_hash_bound": True,
        "no_authority_effect": True,
        "quotient_family_bound": True,
        "reserve_state_only_bound": True,
        "lean_contract": _lean_contract(),
        "quotient_contract": {
            "state": "processed_reserve_in,reserve_out",
            "objective": "selected reserve_out is minimum per reachable mask",
            "suffix_property": "future exact-in CPMM behavior is reserve-state determined",
            "non_claim": "not a Lean endpoint or production ABI",
        },
        "quotient_summary": {
            key: verification[key]
            for key in (
                "mask_count",
                "full_record_count",
                "quotient_state_count",
                "record_compression_saved",
                "quotient_table_obligation_count",
                "selected_suffix_executable_count",
                "quotient_dominance_check_count",
                "quotient_runtime_completion_count",
                "baseline_full_dominance_check_count",
                "dominance_check_compression_saved",
                "max_full_records_per_mask",
                "max_quotient_states_per_mask",
                "max_suffix_per_mask",
                "quotient_obligation_digest",
            )
        },
        "lean_observed_summary": verification["lean_observed_summary"],
        "mask_summaries": verification["mask_summaries"],
        "first_obligation": verification["first_obligation"],
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
    packet = build_case_packet(case)
    verification = verify_case_packet(case, packet)
    return {key: value for key, value in verification.items() if key != "mask_summaries"} | {
        "packet_hash": packet["packet_hash"],
    }


def _rehash_packet(packet: dict[str, Any]) -> dict[str, Any]:
    return _with_packet_hash(packet)


def _find_multistate_mask(full_dp: list[list[_HostRecord]]) -> int:
    for mask_id, records in enumerate(full_dp):
        if len({_reserve_state(record) for record in records}) > 1:
            return mask_id
    raise ValueError("no multi-state mask available for negative control")


def _negative_controls(case: Any, multistate_case: Any) -> list[dict[str, Any]]:
    context = _case_context(case)
    base_full = _full_state_records(case.intents, context)
    base_compressed = _compressed_records(case.intents, context)
    base_packet = build_case_packet(case, full_dp=base_full, compressed_dp=base_compressed)

    multi_context = _case_context(multistate_case)
    multi_full = _full_state_records(multistate_case.intents, multi_context)
    multi_compressed = _compressed_records(multistate_case.intents, multi_context)
    multi_packet = build_case_packet(multistate_case, full_dp=multi_full, compressed_dp=multi_compressed)

    rows: list[
        tuple[str, Any, list[list[_HostRecord]], list[_HostRecord | None], dict[str, Any], str]
    ] = []

    bad_hash = copy.deepcopy(base_packet)
    bad_hash["packet_hash"] = "0" * 64
    rows.append(
        (
            "packet_hash_mismatch",
            case,
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
            case,
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
            case,
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
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_state_bound),
            "reserve_state_only_bound_missing",
        )
    )

    bad_lean_contract = copy.deepcopy(base_packet)
    bad_lean_contract["lean_contract"]["summary_endpoint"] = "stale_endpoint"
    rows.append(
        (
            "packet_lean_contract_mismatch",
            case,
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
            _clone_full_dp(base_full),
            selected_not_member,
            base_packet,
            "selected_state_not_in_quotient_family",
        )
    )

    multistate_mask = _find_multistate_mask(multi_full)
    non_min_state_record = max(multi_full[multistate_mask], key=lambda record: int(record.reserve_out))
    selected_not_min = _clone_compressed_dp(multi_compressed)
    selected_not_min[multistate_mask] = non_min_state_record
    rows.append(
        (
            "selected_reserve_out_not_min",
            multistate_case,
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
            suffix_gap_full,
            suffix_gap_compressed,
            base_packet,
            "selected_suffix_not_executable",
        )
    )

    bad_summary = copy.deepcopy(base_packet)
    bad_summary["quotient_summary"]["quotient_state_count"] += 1
    rows.append(
        (
            "packet_quotient_summary_mismatch",
            case,
            _clone_full_dp(base_full),
            _clone_compressed_dp(base_compressed),
            _rehash_packet(bad_summary),
            "packet_quotient_summary_mismatch",
        )
    )

    output: list[dict[str, Any]] = []
    for mutation_id, target_case, full_dp, compressed_dp, packet, expected_reason in rows:
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
    negative_controls = _negative_controls(cases[0], cases[1])
    full_record_count = sum(int(row["full_record_count"]) for row in rows)
    quotient_state_count = sum(int(row["quotient_state_count"]) for row in rows)
    baseline_dominance = sum(int(row["baseline_full_dominance_check_count"]) for row in rows)
    quotient_dominance = sum(int(row["quotient_dominance_check_count"]) for row in rows)
    lean_observed_summary_count = sum(
        int(row["lean_observed_summary"]["row_count"]) for row in rows
    )
    return {
        "schema": "zenodex/ab_strict_zero_min_reserve_state_quotient_certificate_search/v1",
        "source_seed": N7_SEED,
        "case_count": len(rows),
        "valid_case_count": sum(1 for row in rows if row["ok"]),
        "first_invalid_case": invalid_rows[0] if invalid_rows else None,
        "mask_count": sum(int(row["mask_count"]) for row in rows),
        "full_record_count": full_record_count,
        "quotient_state_count": quotient_state_count,
        "record_compression_saved": full_record_count - quotient_state_count,
        "record_compression_ratio": round(full_record_count / max(1, quotient_state_count), 6),
        "quotient_table_obligation_count": sum(
            int(row["quotient_table_obligation_count"]) for row in rows
        ),
        "lean_observed_summary_count": lean_observed_summary_count,
        "lean_observed_summary_digest": _sha256_json(
            [row["lean_observed_summary"]["digest"] for row in rows]
        ),
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
        "max_full_records_per_mask": max((int(row["max_full_records_per_mask"]) for row in rows), default=0),
        "max_quotient_states_per_mask": max(
            (int(row["max_quotient_states_per_mask"]) for row in rows),
            default=0,
        ),
        "max_suffix_per_mask": max((int(row["max_suffix_per_mask"]) for row in rows), default=0),
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
        and search["quotient_state_count"] < search["full_record_count"]
        and search["quotient_table_obligation_count"] == search["selected_suffix_executable_count"]
        and search["lean_observed_summary_count"] == search["quotient_table_obligation_count"]
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
            "A reserve-state quotient certificate checker supports a smaller host "
            "witness shape for the n=7 strict zero-min corpus by grouping full "
            "order histories by processed reserve-in and reserve-out."
        ),
        "authority_boundary": (
            "Research-only certificate-compression evidence; no settlement, state-root, "
            "production, or governance authority."
        ),
        "search": search,
        "deterministic_replay": deterministic,
        "lean_contract": _lean_contract(),
        "replay_command": (
            "python3 tools/check_ab_strict_zero_min_reserve_state_quotient_certificate.py"
        ),
        "non_claims": [
            "This quotient checker is bounded to the committed n=7 randomized corpus.",
            "This checker does not prove Lean-to-Python refinement.",
            "This checker does not define canonical tie order or preserve order-id history.",
            "This checker does not cover nonzero min_amount_out certificates.",
            "This checker is not a Lean endpoint or production ABI.",
            "No settlement, state-root, production, or governance authority is derived from this artifact.",
        ],
    }


def _write_markdown(report: Mapping[str, Any]) -> None:
    search = report["search"]
    coverage = search["coverage"]
    lines = [
        "# ZenoDEX AB Strict Zero-Min Reserve-State Quotient Certificate - 2026-06-29",
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
        f"- Full records: `{search['full_record_count']}`",
        f"- Quotient states: `{search['quotient_state_count']}`",
        f"- Record compression ratio: `{search['record_compression_ratio']}`",
        f"- Lean observed-summary rows: `{search['lean_observed_summary_count']}`",
        f"- Full dominance checks: `{search['baseline_full_dominance_check_count']}`",
        f"- Quotient dominance checks: `{search['quotient_dominance_check_count']}`",
        f"- Dominance-check compression ratio: `{search['dominance_check_compression_ratio']}`",
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
        f"- Max full records per mask: `{search['max_full_records_per_mask']}`",
        f"- Max quotient states per mask: `{search['max_quotient_states_per_mask']}`",
        f"- Max suffixes per mask: `{search['max_suffix_per_mask']}`",
        f"- Lean observed-summary digest: `{search['lean_observed_summary_digest']}`",
        "",
        "## Lean Projection Shape",
        "",
        "```json",
        json.dumps(report["lean_contract"], indent=2, sort_keys=True),
        "```",
        "",
        "Each digest row binds the observed summary fields used by",
        "`reserveStateQuotientObservedSummary_validates`: quotient-state count, selected",
        "reserve-in, selected reserve-out, completed gross input, initial output reserve,",
        "selected-state digest, quotient-state digest, and one fixed completion suffix.",
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
    for row in search["negative_controls"]:
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | `{row['expected_reason']}` |")
    lines.extend(
        [
            "",
            "## Case Summary",
            "",
            "| case | ok | full records | quotient states | record ratio | dominance ratio |",
            "| --- | --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for row in search["cases"]:
        record_ratio = round(int(row["full_record_count"]) / max(1, int(row["quotient_state_count"])), 6)
        dominance_ratio = round(
            int(row["baseline_full_dominance_check_count"])
            / max(1, int(row["quotient_dominance_check_count"])),
            6,
        )
        lines.append(
            f"| `{row['case_id']}` | `{row['ok']}` | `{row['full_record_count']}` | "
            f"`{row['quotient_state_count']}` | `{record_ratio}` | `{dominance_ratio}` |"
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
