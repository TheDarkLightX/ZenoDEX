"""Pure gate decisions for deterministic route quote receipts."""

from __future__ import annotations

from typing import Any, Dict

from ..core import quote_receipt_gate_contract as _quote_receipt_gate_contract
from ..core.quote_receipt_gate_contract import (
    QUOTE_RECEIPT_CERTIFICATE_AMOUNT_IN_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_AMOUNT_OUT_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_ASSET_IN_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_ASSET_OUT_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE,
    QUOTE_RECEIPT_CERTIFICATE_BAD_WINNER,
    QUOTE_RECEIPT_CERTIFICATE_LEGS_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_OK,
    QUOTE_RECEIPT_HOP_BAD_AMOUNTS,
    QUOTE_RECEIPT_HOP_BAD_ASSETS,
    QUOTE_RECEIPT_HOP_BAD_HOP,
    QUOTE_RECEIPT_HOP_BAD_POOL_ID,
    QUOTE_RECEIPT_HOP_CHAIN_MISMATCH,
    QUOTE_RECEIPT_HOP_HOP_ASSET_CHAIN_MISMATCH,
    QUOTE_RECEIPT_HOP_LEG_ASSET_IN_MISMATCH,
    QUOTE_RECEIPT_HOP_MISSING_POOL_FINGERPRINT,
    QUOTE_RECEIPT_HOP_MISSING_WORKING_POOL,
    QUOTE_RECEIPT_HOP_OK,
    QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_IN_MISMATCH,
    QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_OUT_MISMATCH,
    QUOTE_RECEIPT_LEG_SUMMARY_ASSET_OUT_MISMATCH,
    QUOTE_RECEIPT_LEG_SUMMARY_OK,
    QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT,
    QUOTE_RECEIPT_POOL_SNAPSHOT_MISMATCH,
    QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL,
    QUOTE_RECEIPT_POOL_SNAPSHOT_OK,
    QUOTE_RECEIPT_PRECHECK_BAD_BODY_ASSETS,
    QUOTE_RECEIPT_PRECHECK_BAD_KIND,
    QUOTE_RECEIPT_PRECHECK_BAD_LEGS,
    QUOTE_RECEIPT_PRECHECK_BAD_POOLS,
    QUOTE_RECEIPT_PRECHECK_BAD_QUOTE_EPOCH,
    QUOTE_RECEIPT_PRECHECK_BAD_SCHEMA,
    QUOTE_RECEIPT_PRECHECK_HASH_MISMATCH,
    QUOTE_RECEIPT_PRECHECK_MISSING_RECEIPT_HASH,
    QUOTE_RECEIPT_PRECHECK_OK,
    QUOTE_RECEIPT_PRECHECK_UNEXPECTED_CANONICAL_ROUTE_CERTIFICATE,
    QUOTE_RECEIPT_REPLAY_BAD_POOL_DIRECTION,
    QUOTE_RECEIPT_REPLAY_HOP_QUOTE_ERROR,
    QUOTE_RECEIPT_REPLAY_HOP_QUOTE_MISMATCH,
    QUOTE_RECEIPT_REPLAY_OK,
    QUOTE_RECEIPT_TOTALS_BAD_BODY_AMOUNTS,
    QUOTE_RECEIPT_TOTALS_MISMATCH,
    QUOTE_RECEIPT_TOTALS_OK,
    RouteQuoteReceiptCertificateOutcome,
    RouteQuoteReceiptHopReplayOutcome,
    RouteQuoteReceiptHopStructureOutcome,
    RouteQuoteReceiptLegSummaryOutcome,
    RouteQuoteReceiptPoolSnapshotOutcome,
    RouteQuoteReceiptPrecheckOutcome,
    RouteQuoteReceiptTotalsOutcome,
    _coerce_receipt_gate_checks,
    _first_failed_gate_code,
    _require_receipt_gate_flag,
    _require_receipt_int,
)


def __getattr__(name: str) -> object:
    """Compatibility re-export for quote receipt gate contract symbols."""
    try:
        return getattr(_quote_receipt_gate_contract, name)
    except AttributeError as exc:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}") from exc


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(dir(_quote_receipt_gate_contract)))


def evaluate_route_quote_receipt_precheck_gate(
    *,
    schema_ok: Any,
    receipt_hash_present: Any,
    hash_matches: Any,
    kind_ok: Any,
    canonical_certificate_allowed: Any,
    body_assets_ok: Any,
    quote_epoch_ok: Any,
    pools_object_ok: Any,
    legs_list_ok: Any,
) -> RouteQuoteReceiptPrecheckOutcome:
    checks = _coerce_receipt_gate_checks(
        (
            ("schema_ok", schema_ok),
            ("receipt_hash_present", receipt_hash_present),
            ("hash_matches", hash_matches),
            ("kind_ok", kind_ok),
            ("canonical_certificate_allowed", canonical_certificate_allowed),
            ("body_assets_ok", body_assets_ok),
            ("quote_epoch_ok", quote_epoch_ok),
            ("pools_object_ok", pools_object_ok),
            ("legs_list_ok", legs_list_ok),
        )
    )
    reject_code = _first_failed_gate_code(
        checks=checks,
        failures=(
            ("schema_ok", QUOTE_RECEIPT_PRECHECK_BAD_SCHEMA),
            ("receipt_hash_present", QUOTE_RECEIPT_PRECHECK_MISSING_RECEIPT_HASH),
            ("hash_matches", QUOTE_RECEIPT_PRECHECK_HASH_MISMATCH),
            ("kind_ok", QUOTE_RECEIPT_PRECHECK_BAD_KIND),
            (
                "canonical_certificate_allowed",
                QUOTE_RECEIPT_PRECHECK_UNEXPECTED_CANONICAL_ROUTE_CERTIFICATE,
            ),
            ("body_assets_ok", QUOTE_RECEIPT_PRECHECK_BAD_BODY_ASSETS),
            ("quote_epoch_ok", QUOTE_RECEIPT_PRECHECK_BAD_QUOTE_EPOCH),
            ("pools_object_ok", QUOTE_RECEIPT_PRECHECK_BAD_POOLS),
            ("legs_list_ok", QUOTE_RECEIPT_PRECHECK_BAD_LEGS),
        ),
        ok_code=QUOTE_RECEIPT_PRECHECK_OK,
    )
    return RouteQuoteReceiptPrecheckOutcome(
        precheck_ok=bool(reject_code == QUOTE_RECEIPT_PRECHECK_OK),
        reject_code=reject_code,
        checks=checks,
    )


def evaluate_route_quote_receipt_certificate_gate(
    *,
    cert_present: Any,
    cert_dict_ok: Any,
    winner_quote_dict_ok: Any,
    asset_in_match: Any,
    asset_out_match: Any,
    amount_in_match: Any,
    amount_out_match: Any,
    legs_match: Any,
) -> RouteQuoteReceiptCertificateOutcome:
    checks = _coerce_receipt_gate_checks(
        (
            ("cert_present", cert_present),
            ("cert_dict_ok", cert_dict_ok),
            ("winner_quote_dict_ok", winner_quote_dict_ok),
            ("asset_in_match", asset_in_match),
            ("asset_out_match", asset_out_match),
            ("amount_in_match", amount_in_match),
            ("amount_out_match", amount_out_match),
            ("legs_match", legs_match),
        )
    )
    reject_code = (
        QUOTE_RECEIPT_CERTIFICATE_OK
        if not checks["cert_present"]
        else _first_failed_gate_code(
            checks=checks,
            failures=(
                ("cert_dict_ok", QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE),
                ("winner_quote_dict_ok", QUOTE_RECEIPT_CERTIFICATE_BAD_WINNER),
                ("asset_in_match", QUOTE_RECEIPT_CERTIFICATE_ASSET_IN_MISMATCH),
                ("asset_out_match", QUOTE_RECEIPT_CERTIFICATE_ASSET_OUT_MISMATCH),
                ("amount_in_match", QUOTE_RECEIPT_CERTIFICATE_AMOUNT_IN_MISMATCH),
                ("amount_out_match", QUOTE_RECEIPT_CERTIFICATE_AMOUNT_OUT_MISMATCH),
                ("legs_match", QUOTE_RECEIPT_CERTIFICATE_LEGS_MISMATCH),
            ),
            ok_code=QUOTE_RECEIPT_CERTIFICATE_OK,
        )
    )
    return RouteQuoteReceiptCertificateOutcome(
        certificate_ok=bool(reject_code == QUOTE_RECEIPT_CERTIFICATE_OK),
        reject_code=reject_code,
        checks=checks,
    )


def evaluate_route_quote_receipt_pool_snapshot_gate(
    *,
    pool_entries_well_formed: Any,
    all_pools_present: Any,
    all_fingerprints_match: Any,
) -> RouteQuoteReceiptPoolSnapshotOutcome:
    checks = _coerce_receipt_gate_checks(
        (
            ("pool_entries_well_formed", pool_entries_well_formed),
            ("all_pools_present", all_pools_present),
            ("all_fingerprints_match", all_fingerprints_match),
        )
    )
    reject_code = _first_failed_gate_code(
        checks=checks,
        failures=(
            ("pool_entries_well_formed", QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT),
            ("all_pools_present", QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL),
            ("all_fingerprints_match", QUOTE_RECEIPT_POOL_SNAPSHOT_MISMATCH),
        ),
        ok_code=QUOTE_RECEIPT_POOL_SNAPSHOT_OK,
    )
    return RouteQuoteReceiptPoolSnapshotOutcome(
        snapshot_ok=bool(reject_code == QUOTE_RECEIPT_POOL_SNAPSHOT_OK),
        reject_code=reject_code,
        checks=checks,
    )


def evaluate_route_quote_receipt_hop_structure_gate(
    *,
    hop_dict_ok: Any,
    pool_id_ok: Any,
    snapshotted_pool_present: Any,
    working_pool_present: Any,
    assets_shaped_ok: Any,
    is_first_hop: Any,
    first_hop_asset_in_ok: Any,
    hop_asset_chain_ok: Any,
    hop_amounts_ok: Any,
    hop_amount_chain_ok: Any,
) -> RouteQuoteReceiptHopStructureOutcome:
    checks = _coerce_receipt_gate_checks(
        (
            ("hop_dict_ok", hop_dict_ok),
            ("pool_id_ok", pool_id_ok),
            ("snapshotted_pool_present", snapshotted_pool_present),
            ("working_pool_present", working_pool_present),
            ("assets_shaped_ok", assets_shaped_ok),
            ("is_first_hop", is_first_hop),
            ("first_hop_asset_in_ok", first_hop_asset_in_ok),
            ("hop_asset_chain_ok", hop_asset_chain_ok),
            ("hop_amounts_ok", hop_amounts_ok),
            ("hop_amount_chain_ok", hop_amount_chain_ok),
        )
    )
    reject_code = _route_quote_hop_structure_reject_code(checks)
    return RouteQuoteReceiptHopStructureOutcome(
        hop_ok=bool(reject_code == QUOTE_RECEIPT_HOP_OK),
        reject_code=reject_code,
        checks=checks,
    )


def _route_quote_hop_structure_reject_code(checks: Dict[str, bool]) -> str:
    first_failure = _first_failed_gate_code(
        checks=checks,
        failures=(
            ("hop_dict_ok", QUOTE_RECEIPT_HOP_BAD_HOP),
            ("pool_id_ok", QUOTE_RECEIPT_HOP_BAD_POOL_ID),
            ("snapshotted_pool_present", QUOTE_RECEIPT_HOP_MISSING_POOL_FINGERPRINT),
            ("working_pool_present", QUOTE_RECEIPT_HOP_MISSING_WORKING_POOL),
            ("assets_shaped_ok", QUOTE_RECEIPT_HOP_BAD_ASSETS),
        ),
        ok_code=QUOTE_RECEIPT_HOP_OK,
    )
    if first_failure != QUOTE_RECEIPT_HOP_OK:
        return first_failure
    if checks["is_first_hop"] and not checks["first_hop_asset_in_ok"]:
        return QUOTE_RECEIPT_HOP_LEG_ASSET_IN_MISMATCH
    if (not checks["is_first_hop"]) and not checks["hop_asset_chain_ok"]:
        return QUOTE_RECEIPT_HOP_HOP_ASSET_CHAIN_MISMATCH
    return _first_failed_gate_code(
        checks=checks,
        failures=(
            ("hop_amounts_ok", QUOTE_RECEIPT_HOP_BAD_AMOUNTS),
            ("hop_amount_chain_ok", QUOTE_RECEIPT_HOP_CHAIN_MISMATCH),
        ),
        ok_code=QUOTE_RECEIPT_HOP_OK,
    )


def evaluate_route_quote_receipt_leg_summary_gate(
    *,
    final_asset_out_ok: Any,
    first_hop_amount_in_ok: Any,
    last_hop_amount_out_ok: Any,
) -> RouteQuoteReceiptLegSummaryOutcome:
    final_asset_out_ok_v = _require_receipt_gate_flag(
        final_asset_out_ok,
        name="final_asset_out_ok",
    )
    first_hop_amount_in_ok_v = _require_receipt_gate_flag(
        first_hop_amount_in_ok,
        name="first_hop_amount_in_ok",
    )
    last_hop_amount_out_ok_v = _require_receipt_gate_flag(
        last_hop_amount_out_ok,
        name="last_hop_amount_out_ok",
    )

    checks = {
        "final_asset_out_ok": final_asset_out_ok_v,
        "first_hop_amount_in_ok": first_hop_amount_in_ok_v,
        "last_hop_amount_out_ok": last_hop_amount_out_ok_v,
    }
    if not final_asset_out_ok_v:
        reject_code = QUOTE_RECEIPT_LEG_SUMMARY_ASSET_OUT_MISMATCH
    elif not first_hop_amount_in_ok_v:
        reject_code = QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_IN_MISMATCH
    elif not last_hop_amount_out_ok_v:
        reject_code = QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_OUT_MISMATCH
    else:
        reject_code = QUOTE_RECEIPT_LEG_SUMMARY_OK
    return RouteQuoteReceiptLegSummaryOutcome(
        leg_ok=bool(reject_code == QUOTE_RECEIPT_LEG_SUMMARY_OK),
        reject_code=reject_code,
        checks=checks,
    )


def evaluate_route_quote_receipt_totals_gate(
    *,
    body_amounts_ok: Any,
    totals_match: Any,
) -> RouteQuoteReceiptTotalsOutcome:
    body_amounts_ok_v = _require_receipt_gate_flag(body_amounts_ok, name="body_amounts_ok")
    totals_match_v = _require_receipt_gate_flag(totals_match, name="totals_match")

    checks = {
        "body_amounts_ok": body_amounts_ok_v,
        "totals_match": totals_match_v,
    }
    if not body_amounts_ok_v:
        reject_code = QUOTE_RECEIPT_TOTALS_BAD_BODY_AMOUNTS
    elif not totals_match_v:
        reject_code = QUOTE_RECEIPT_TOTALS_MISMATCH
    else:
        reject_code = QUOTE_RECEIPT_TOTALS_OK
    return RouteQuoteReceiptTotalsOutcome(
        totals_ok=bool(reject_code == QUOTE_RECEIPT_TOTALS_OK),
        reject_code=reject_code,
        checks=checks,
    )


def evaluate_route_quote_receipt_hop_replay_gate(
    *,
    direction_ok: Any,
    forward_direction: Any,
    swap_ok: Any,
    quote_matches: Any,
    next_reserve_in: Any,
    next_reserve_out: Any,
) -> RouteQuoteReceiptHopReplayOutcome:
    direction_ok_v = _require_receipt_gate_flag(direction_ok, name="direction_ok")
    forward_direction_v = _require_receipt_gate_flag(forward_direction, name="forward_direction")
    swap_ok_v = _require_receipt_gate_flag(swap_ok, name="swap_ok")
    quote_matches_v = _require_receipt_gate_flag(quote_matches, name="quote_matches")
    next_reserve_in_v = _require_receipt_int(next_reserve_in)
    next_reserve_out_v = _require_receipt_int(next_reserve_out)
    if next_reserve_in_v is None or next_reserve_in_v < 0:
        raise ValueError("next_reserve_in must be a non-negative int")
    if next_reserve_out_v is None or next_reserve_out_v < 0:
        raise ValueError("next_reserve_out must be a non-negative int")

    checks = {
        "direction_ok": direction_ok_v,
        "forward_direction": forward_direction_v,
        "swap_ok": swap_ok_v,
        "quote_matches": quote_matches_v,
    }
    if not direction_ok_v:
        reject_code = QUOTE_RECEIPT_REPLAY_BAD_POOL_DIRECTION
    elif not swap_ok_v:
        reject_code = QUOTE_RECEIPT_REPLAY_HOP_QUOTE_ERROR
    elif not quote_matches_v:
        reject_code = QUOTE_RECEIPT_REPLAY_HOP_QUOTE_MISMATCH
    else:
        reject_code = QUOTE_RECEIPT_REPLAY_OK

    next_reserve0 = next_reserve_in_v if forward_direction_v else next_reserve_out_v
    next_reserve1 = next_reserve_out_v if forward_direction_v else next_reserve_in_v
    return RouteQuoteReceiptHopReplayOutcome(
        replay_ok=bool(reject_code == QUOTE_RECEIPT_REPLAY_OK),
        reject_code=reject_code,
        next_reserve0=int(next_reserve0),
        next_reserve1=int(next_reserve1),
        checks=checks,
    )
