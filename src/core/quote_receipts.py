"""
Deterministic quote receipts (UX + security + automation).

A *quote receipt* binds a proposed route quote to:
- the exact per-hop amounts,
- a snapshot fingerprint of the referenced pools,
- a deterministic receipt hash (canonical JSON + domain separation).

This supports:
- UI: show a quote that is replay/verifyable
- automation: deterministic agents can fail-closed if receipts don't verify
- security/audit: detect tampering or stale-state execution
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, Tuple

from ..core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from ..core.routing import RouteQuote
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.pools import PoolState


def _require_receipt_int(value: Any) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        return None
    return int(value)


def pool_state_fingerprint(pool: PoolState) -> str:
    """
    Deterministic pool fingerprint for receipts.

    Note: includes reserves so the receipt is only valid for a specific snapshot.
    """
    obj = {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": int(pool.reserve0),
        "reserve1": int(pool.reserve1),
        "fee_bps": int(pool.fee_bps),
        "curve_tag": str(pool.curve_tag),
        "curve_params": str(pool.curve_params),
        "lp_supply": int(pool.lp_supply),
        "status": str(pool.status.value),
        "created_at": int(pool.created_at),
    }
    return sha256_hex(domain_sep_bytes("zenodex.pool_state/v1") + canonical_json_bytes(obj))


def receipt_hash(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes("zenodex.route_quote_receipt/v1") + canonical_json_bytes(receipt_body))


def _require_receipt_gate_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and value in (0, 1):
        return bool(value)
    raise ValueError(f"{name} must be a bool or 0/1 int")


QUOTE_RECEIPT_PRECHECK_OK = "Ok"
QUOTE_RECEIPT_PRECHECK_BAD_SCHEMA = "BadSchema"
QUOTE_RECEIPT_PRECHECK_MISSING_RECEIPT_HASH = "MissingReceiptHash"
QUOTE_RECEIPT_PRECHECK_HASH_MISMATCH = "HashMismatch"
QUOTE_RECEIPT_PRECHECK_BAD_KIND = "BadKind"
QUOTE_RECEIPT_PRECHECK_UNEXPECTED_CANONICAL_ROUTE_CERTIFICATE = "UnexpectedCanonicalRouteCertificate"
QUOTE_RECEIPT_PRECHECK_BAD_BODY_ASSETS = "BadBodyAssets"
QUOTE_RECEIPT_PRECHECK_BAD_QUOTE_EPOCH = "BadQuoteEpoch"
QUOTE_RECEIPT_PRECHECK_BAD_POOLS = "BadPools"
QUOTE_RECEIPT_PRECHECK_BAD_LEGS = "BadLegs"
QUOTE_RECEIPT_CERTIFICATE_OK = "Ok"
QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE = "BadCertificateType"
QUOTE_RECEIPT_CERTIFICATE_BAD_WINNER = "BadWinnerQuote"
QUOTE_RECEIPT_CERTIFICATE_ASSET_IN_MISMATCH = "AssetInMismatch"
QUOTE_RECEIPT_CERTIFICATE_ASSET_OUT_MISMATCH = "AssetOutMismatch"
QUOTE_RECEIPT_CERTIFICATE_AMOUNT_IN_MISMATCH = "AmountInMismatch"
QUOTE_RECEIPT_CERTIFICATE_AMOUNT_OUT_MISMATCH = "AmountOutMismatch"
QUOTE_RECEIPT_CERTIFICATE_LEGS_MISMATCH = "LegsMismatch"
QUOTE_RECEIPT_POOL_SNAPSHOT_OK = "Ok"
QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT = "BadPoolFingerprint"
QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL = "MissingPool"
QUOTE_RECEIPT_POOL_SNAPSHOT_MISMATCH = "PoolSnapshotMismatch"
QUOTE_RECEIPT_HOP_OK = "Ok"
QUOTE_RECEIPT_HOP_BAD_HOP = "BadHop"
QUOTE_RECEIPT_HOP_BAD_POOL_ID = "BadPoolId"
QUOTE_RECEIPT_HOP_MISSING_POOL_FINGERPRINT = "MissingPoolFingerprint"
QUOTE_RECEIPT_HOP_MISSING_WORKING_POOL = "MissingWorkingPool"
QUOTE_RECEIPT_HOP_BAD_ASSETS = "BadAssets"
QUOTE_RECEIPT_HOP_LEG_ASSET_IN_MISMATCH = "LegAssetInMismatch"
QUOTE_RECEIPT_HOP_HOP_ASSET_CHAIN_MISMATCH = "HopAssetChainMismatch"
QUOTE_RECEIPT_HOP_BAD_AMOUNTS = "BadHopAmounts"
QUOTE_RECEIPT_HOP_CHAIN_MISMATCH = "HopChainMismatch"
QUOTE_RECEIPT_LEG_SUMMARY_OK = "Ok"
QUOTE_RECEIPT_LEG_SUMMARY_ASSET_OUT_MISMATCH = "LegAssetOutMismatch"
QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_IN_MISMATCH = "LegAmountInMismatch"
QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_OUT_MISMATCH = "LegAmountOutMismatch"
QUOTE_RECEIPT_TOTALS_OK = "Ok"
QUOTE_RECEIPT_TOTALS_BAD_BODY_AMOUNTS = "BadBodyAmounts"
QUOTE_RECEIPT_TOTALS_MISMATCH = "TotalsMismatch"
QUOTE_RECEIPT_REPLAY_OK = "Ok"
QUOTE_RECEIPT_REPLAY_BAD_POOL_DIRECTION = "BadPoolDirection"
QUOTE_RECEIPT_REPLAY_HOP_QUOTE_ERROR = "HopQuoteError"
QUOTE_RECEIPT_REPLAY_HOP_QUOTE_MISMATCH = "HopQuoteMismatch"


@dataclass(frozen=True)
class RouteQuoteReceiptPrecheckOutcome:
    precheck_ok: bool
    reject_code: str
    checks: Dict[str, bool]


@dataclass(frozen=True)
class RouteQuoteReceiptCertificateOutcome:
    certificate_ok: bool
    reject_code: str
    checks: Dict[str, bool]


@dataclass(frozen=True)
class RouteQuoteReceiptPoolSnapshotOutcome:
    snapshot_ok: bool
    reject_code: str
    checks: Dict[str, bool]


@dataclass(frozen=True)
class RouteQuoteReceiptHopStructureOutcome:
    hop_ok: bool
    reject_code: str
    checks: Dict[str, bool]


@dataclass(frozen=True)
class RouteQuoteReceiptLegSummaryOutcome:
    leg_ok: bool
    reject_code: str
    checks: Dict[str, bool]


@dataclass(frozen=True)
class RouteQuoteReceiptTotalsOutcome:
    totals_ok: bool
    reject_code: str
    checks: Dict[str, bool]


@dataclass(frozen=True)
class RouteQuoteReceiptHopReplayOutcome:
    replay_ok: bool
    reject_code: str
    next_reserve0: int
    next_reserve1: int
    checks: Dict[str, bool]


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
    schema_ok_v = _require_receipt_gate_flag(schema_ok, name="schema_ok")
    receipt_hash_present_v = _require_receipt_gate_flag(receipt_hash_present, name="receipt_hash_present")
    hash_matches_v = _require_receipt_gate_flag(hash_matches, name="hash_matches")
    kind_ok_v = _require_receipt_gate_flag(kind_ok, name="kind_ok")
    canonical_certificate_allowed_v = _require_receipt_gate_flag(
        canonical_certificate_allowed,
        name="canonical_certificate_allowed",
    )
    body_assets_ok_v = _require_receipt_gate_flag(body_assets_ok, name="body_assets_ok")
    quote_epoch_ok_v = _require_receipt_gate_flag(quote_epoch_ok, name="quote_epoch_ok")
    pools_object_ok_v = _require_receipt_gate_flag(pools_object_ok, name="pools_object_ok")
    legs_list_ok_v = _require_receipt_gate_flag(legs_list_ok, name="legs_list_ok")

    checks = {
        "schema_ok": schema_ok_v,
        "receipt_hash_present": receipt_hash_present_v,
        "hash_matches": hash_matches_v,
        "kind_ok": kind_ok_v,
        "canonical_certificate_allowed": canonical_certificate_allowed_v,
        "body_assets_ok": body_assets_ok_v,
        "quote_epoch_ok": quote_epoch_ok_v,
        "pools_object_ok": pools_object_ok_v,
        "legs_list_ok": legs_list_ok_v,
    }
    if not schema_ok_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_BAD_SCHEMA
    elif not receipt_hash_present_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_MISSING_RECEIPT_HASH
    elif not hash_matches_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_HASH_MISMATCH
    elif not kind_ok_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_BAD_KIND
    elif not canonical_certificate_allowed_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_UNEXPECTED_CANONICAL_ROUTE_CERTIFICATE
    elif not body_assets_ok_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_BAD_BODY_ASSETS
    elif not quote_epoch_ok_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_BAD_QUOTE_EPOCH
    elif not pools_object_ok_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_BAD_POOLS
    elif not legs_list_ok_v:
        reject_code = QUOTE_RECEIPT_PRECHECK_BAD_LEGS
    else:
        reject_code = QUOTE_RECEIPT_PRECHECK_OK
    return RouteQuoteReceiptPrecheckOutcome(
        precheck_ok=bool(reject_code == QUOTE_RECEIPT_PRECHECK_OK),
        reject_code=reject_code,
        checks=checks,
    )


def route_quote_receipt_precheck_error(outcome: RouteQuoteReceiptPrecheckOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_PRECHECK_BAD_SCHEMA: "bad_schema",
        QUOTE_RECEIPT_PRECHECK_MISSING_RECEIPT_HASH: "missing_receipt_hash",
        QUOTE_RECEIPT_PRECHECK_HASH_MISMATCH: "hash_mismatch",
        QUOTE_RECEIPT_PRECHECK_BAD_KIND: "bad_kind",
        QUOTE_RECEIPT_PRECHECK_UNEXPECTED_CANONICAL_ROUTE_CERTIFICATE: "unexpected_canonical_route_certificate",
        QUOTE_RECEIPT_PRECHECK_BAD_BODY_ASSETS: "bad_body_assets",
        QUOTE_RECEIPT_PRECHECK_BAD_QUOTE_EPOCH: "bad_quote_epoch",
        QUOTE_RECEIPT_PRECHECK_BAD_POOLS: "bad_pools",
        QUOTE_RECEIPT_PRECHECK_BAD_LEGS: "bad_legs",
    }
    return mapping.get(outcome.reject_code, "ok")


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
    cert_present_v = _require_receipt_gate_flag(cert_present, name="cert_present")
    cert_dict_ok_v = _require_receipt_gate_flag(cert_dict_ok, name="cert_dict_ok")
    winner_quote_dict_ok_v = _require_receipt_gate_flag(winner_quote_dict_ok, name="winner_quote_dict_ok")
    asset_in_match_v = _require_receipt_gate_flag(asset_in_match, name="asset_in_match")
    asset_out_match_v = _require_receipt_gate_flag(asset_out_match, name="asset_out_match")
    amount_in_match_v = _require_receipt_gate_flag(amount_in_match, name="amount_in_match")
    amount_out_match_v = _require_receipt_gate_flag(amount_out_match, name="amount_out_match")
    legs_match_v = _require_receipt_gate_flag(legs_match, name="legs_match")

    checks = {
        "cert_present": cert_present_v,
        "cert_dict_ok": cert_dict_ok_v,
        "winner_quote_dict_ok": winner_quote_dict_ok_v,
        "asset_in_match": asset_in_match_v,
        "asset_out_match": asset_out_match_v,
        "amount_in_match": amount_in_match_v,
        "amount_out_match": amount_out_match_v,
        "legs_match": legs_match_v,
    }
    if not cert_present_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_OK
    elif not cert_dict_ok_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE
    elif not winner_quote_dict_ok_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_BAD_WINNER
    elif not asset_in_match_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_ASSET_IN_MISMATCH
    elif not asset_out_match_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_ASSET_OUT_MISMATCH
    elif not amount_in_match_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_AMOUNT_IN_MISMATCH
    elif not amount_out_match_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_AMOUNT_OUT_MISMATCH
    elif not legs_match_v:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_LEGS_MISMATCH
    else:
        reject_code = QUOTE_RECEIPT_CERTIFICATE_OK
    return RouteQuoteReceiptCertificateOutcome(
        certificate_ok=bool(reject_code == QUOTE_RECEIPT_CERTIFICATE_OK),
        reject_code=reject_code,
        checks=checks,
    )


def route_quote_receipt_certificate_error(outcome: RouteQuoteReceiptCertificateOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE: "bad_canonical_route_certificate_type",
        QUOTE_RECEIPT_CERTIFICATE_BAD_WINNER: "bad_canonical_route_certificate_winner",
        QUOTE_RECEIPT_CERTIFICATE_ASSET_IN_MISMATCH: "canonical_route_certificate_asset_in_mismatch",
        QUOTE_RECEIPT_CERTIFICATE_ASSET_OUT_MISMATCH: "canonical_route_certificate_asset_out_mismatch",
        QUOTE_RECEIPT_CERTIFICATE_AMOUNT_IN_MISMATCH: "canonical_route_certificate_amount_in_mismatch",
        QUOTE_RECEIPT_CERTIFICATE_AMOUNT_OUT_MISMATCH: "canonical_route_certificate_amount_out_mismatch",
        QUOTE_RECEIPT_CERTIFICATE_LEGS_MISMATCH: "canonical_route_certificate_legs_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


def evaluate_route_quote_receipt_pool_snapshot_gate(
    *,
    pool_entries_well_formed: Any,
    all_pools_present: Any,
    all_fingerprints_match: Any,
) -> RouteQuoteReceiptPoolSnapshotOutcome:
    pool_entries_well_formed_v = _require_receipt_gate_flag(
        pool_entries_well_formed,
        name="pool_entries_well_formed",
    )
    all_pools_present_v = _require_receipt_gate_flag(
        all_pools_present,
        name="all_pools_present",
    )
    all_fingerprints_match_v = _require_receipt_gate_flag(
        all_fingerprints_match,
        name="all_fingerprints_match",
    )

    checks = {
        "pool_entries_well_formed": pool_entries_well_formed_v,
        "all_pools_present": all_pools_present_v,
        "all_fingerprints_match": all_fingerprints_match_v,
    }
    if not pool_entries_well_formed_v:
        reject_code = QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT
    elif not all_pools_present_v:
        reject_code = QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL
    elif not all_fingerprints_match_v:
        reject_code = QUOTE_RECEIPT_POOL_SNAPSHOT_MISMATCH
    else:
        reject_code = QUOTE_RECEIPT_POOL_SNAPSHOT_OK
    return RouteQuoteReceiptPoolSnapshotOutcome(
        snapshot_ok=bool(reject_code == QUOTE_RECEIPT_POOL_SNAPSHOT_OK),
        reject_code=reject_code,
        checks=checks,
    )


def route_quote_receipt_pool_snapshot_error(outcome: RouteQuoteReceiptPoolSnapshotOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT: "bad_pool_fingerprint",
        QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL: "missing_pool",
        QUOTE_RECEIPT_POOL_SNAPSHOT_MISMATCH: "pool_snapshot_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


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
    hop_dict_ok_v = _require_receipt_gate_flag(hop_dict_ok, name="hop_dict_ok")
    pool_id_ok_v = _require_receipt_gate_flag(pool_id_ok, name="pool_id_ok")
    snapshotted_pool_present_v = _require_receipt_gate_flag(
        snapshotted_pool_present,
        name="snapshotted_pool_present",
    )
    working_pool_present_v = _require_receipt_gate_flag(
        working_pool_present,
        name="working_pool_present",
    )
    assets_shaped_ok_v = _require_receipt_gate_flag(assets_shaped_ok, name="assets_shaped_ok")
    is_first_hop_v = _require_receipt_gate_flag(is_first_hop, name="is_first_hop")
    first_hop_asset_in_ok_v = _require_receipt_gate_flag(
        first_hop_asset_in_ok,
        name="first_hop_asset_in_ok",
    )
    hop_asset_chain_ok_v = _require_receipt_gate_flag(
        hop_asset_chain_ok,
        name="hop_asset_chain_ok",
    )
    hop_amounts_ok_v = _require_receipt_gate_flag(hop_amounts_ok, name="hop_amounts_ok")
    hop_amount_chain_ok_v = _require_receipt_gate_flag(
        hop_amount_chain_ok,
        name="hop_amount_chain_ok",
    )

    checks = {
        "hop_dict_ok": hop_dict_ok_v,
        "pool_id_ok": pool_id_ok_v,
        "snapshotted_pool_present": snapshotted_pool_present_v,
        "working_pool_present": working_pool_present_v,
        "assets_shaped_ok": assets_shaped_ok_v,
        "is_first_hop": is_first_hop_v,
        "first_hop_asset_in_ok": first_hop_asset_in_ok_v,
        "hop_asset_chain_ok": hop_asset_chain_ok_v,
        "hop_amounts_ok": hop_amounts_ok_v,
        "hop_amount_chain_ok": hop_amount_chain_ok_v,
    }
    if not hop_dict_ok_v:
        reject_code = QUOTE_RECEIPT_HOP_BAD_HOP
    elif not pool_id_ok_v:
        reject_code = QUOTE_RECEIPT_HOP_BAD_POOL_ID
    elif not snapshotted_pool_present_v:
        reject_code = QUOTE_RECEIPT_HOP_MISSING_POOL_FINGERPRINT
    elif not working_pool_present_v:
        reject_code = QUOTE_RECEIPT_HOP_MISSING_WORKING_POOL
    elif not assets_shaped_ok_v:
        reject_code = QUOTE_RECEIPT_HOP_BAD_ASSETS
    elif is_first_hop_v and not first_hop_asset_in_ok_v:
        reject_code = QUOTE_RECEIPT_HOP_LEG_ASSET_IN_MISMATCH
    elif (not is_first_hop_v) and not hop_asset_chain_ok_v:
        reject_code = QUOTE_RECEIPT_HOP_HOP_ASSET_CHAIN_MISMATCH
    elif not hop_amounts_ok_v:
        reject_code = QUOTE_RECEIPT_HOP_BAD_AMOUNTS
    elif not hop_amount_chain_ok_v:
        reject_code = QUOTE_RECEIPT_HOP_CHAIN_MISMATCH
    else:
        reject_code = QUOTE_RECEIPT_HOP_OK
    return RouteQuoteReceiptHopStructureOutcome(
        hop_ok=bool(reject_code == QUOTE_RECEIPT_HOP_OK),
        reject_code=reject_code,
        checks=checks,
    )


def route_quote_receipt_hop_structure_error(outcome: RouteQuoteReceiptHopStructureOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_HOP_BAD_HOP: "bad_hop",
        QUOTE_RECEIPT_HOP_BAD_POOL_ID: "bad_pool_id",
        QUOTE_RECEIPT_HOP_MISSING_POOL_FINGERPRINT: "missing_pool_fingerprint",
        QUOTE_RECEIPT_HOP_MISSING_WORKING_POOL: "missing_working_pool",
        QUOTE_RECEIPT_HOP_BAD_ASSETS: "bad_assets",
        QUOTE_RECEIPT_HOP_LEG_ASSET_IN_MISMATCH: "leg_asset_in_mismatch",
        QUOTE_RECEIPT_HOP_HOP_ASSET_CHAIN_MISMATCH: "hop_asset_chain_mismatch",
        QUOTE_RECEIPT_HOP_BAD_AMOUNTS: "bad_hop_amounts",
        QUOTE_RECEIPT_HOP_CHAIN_MISMATCH: "hop_chain_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


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


def route_quote_receipt_leg_summary_error(outcome: RouteQuoteReceiptLegSummaryOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_LEG_SUMMARY_ASSET_OUT_MISMATCH: "leg_asset_out_mismatch",
        QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_IN_MISMATCH: "leg_amount_in_mismatch",
        QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_OUT_MISMATCH: "leg_amount_out_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


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


def route_quote_receipt_totals_error(outcome: RouteQuoteReceiptTotalsOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_TOTALS_BAD_BODY_AMOUNTS: "bad_body_amounts",
        QUOTE_RECEIPT_TOTALS_MISMATCH: "totals_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


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


def route_quote_receipt_hop_replay_error(outcome: RouteQuoteReceiptHopReplayOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_REPLAY_BAD_POOL_DIRECTION: "bad_pool_direction",
        QUOTE_RECEIPT_REPLAY_HOP_QUOTE_ERROR: "hop_quote_error",
        QUOTE_RECEIPT_REPLAY_HOP_QUOTE_MISMATCH: "hop_quote_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


def make_route_quote_receipt(
    *,
    kind: str,
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
    quote_epoch: int | None = None,
) -> Dict[str, Any]:
    """
    Create a deterministic receipt for a RouteQuote.

    `kind` must be "exact_in" or "exact_out". (RouteQuote itself is type-agnostic.)
    """
    k = str(kind).strip().lower()
    if k not in {"exact_in", "exact_out"}:
        raise ValueError("kind must be 'exact_in' or 'exact_out'")

    if quote_epoch is not None:
        quote_epoch = _require_receipt_int(quote_epoch)
        if quote_epoch is None or quote_epoch < 0:
            raise ValueError("quote_epoch must be a non-negative int")

    # Receipt legs/hops are stored as plain dicts (canonical JSON friendly).
    legs = []
    pool_fps: Dict[str, str] = {}
    for leg in quote.legs:
        hops = []
        for hop in leg.hops:
            pool = pools_by_id.get(hop.pool_id)
            if pool is None:
                raise ValueError(f"missing pool for hop.pool_id={hop.pool_id!r}")
            if hop.pool_id not in pool_fps:
                pool_fps[hop.pool_id] = pool_state_fingerprint(pool)
            hops.append(
                {
                    "pool_id": hop.pool_id,
                    "asset_in": hop.asset_in,
                    "asset_out": hop.asset_out,
                    "amount_in": int(hop.amount_in),
                    "amount_out": int(hop.amount_out),
                }
            )
        legs.append(
            {
                "amount_in": int(leg.amount_in),
                "amount_out": int(leg.amount_out),
                "hops": hops,
            }
        )

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": k,
        "asset_in": quote.asset_in,
        "asset_out": quote.asset_out,
        "amount_in": int(quote.amount_in),
        "amount_out": int(quote.amount_out),
        "legs": legs,
        # Deterministic map of pool_id -> snapshot fingerprint.
        "pools": {pid: pool_fps[pid] for pid in sorted(pool_fps.keys())},
    }
    if quote_epoch is not None:
        body["quote_epoch"] = int(quote_epoch)
    if k == "exact_in":
        # Optional canonical-winner attachment: include it when the provided
        # quote is the actual canonical winner under the current router surface.
        from ..integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_canonical_certificate_for_pools,
        )

        certificate = build_exact_in_route_canonical_certificate_for_pools(
            pools_by_id=pools_by_id,
            asset_in=quote.asset_in,
            asset_out=quote.asset_out,
            amount_in=int(quote.amount_in),
        )
        if certificate is not None and certificate.winner_quote == quote:
            body["canonical_route_certificate"] = certificate.to_dict()
    return {
        "body": body,
        "receipt_hash": receipt_hash(body),
    }


def _pool_reserves_for_hop(pool: PoolState, *, asset_in: str, asset_out: str) -> Tuple[int, int] | None:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _replay_and_apply_hop(
    *,
    pool: PoolState,
    kind: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    amount_out: int,
) -> Tuple[bool, str, PoolState | None]:
    forward_direction = bool(asset_in == pool.asset0 and asset_out == pool.asset1)
    reverse_direction = bool(asset_in == pool.asset1 and asset_out == pool.asset0)
    direction_ok = bool(forward_direction or reverse_direction)
    reserves = _pool_reserves_for_hop(pool, asset_in=asset_in, asset_out=asset_out)
    if not direction_ok or reserves is None:
        direction_ok = False
        rin = 0
        rout = 0
    else:
        rin, rout = reserves

    swap_ok = False
    quote_matches = False
    next_rin = 0
    next_rout = 0
    if direction_ok:
        try:
            if kind == "exact_in":
                quoted_out, (next_rin, next_rout) = swap_exact_in_for_pool(
                    pool,
                    reserve_in=rin,
                    reserve_out=rout,
                    amount_in=int(amount_in),
                )
                swap_ok = True
                quote_matches = int(quoted_out) == int(amount_out)
            else:
                quoted_in, (next_rin, next_rout) = swap_exact_out_for_pool(
                    pool,
                    reserve_in=rin,
                    reserve_out=rout,
                    amount_out=int(amount_out),
                )
                swap_ok = True
                quote_matches = int(quoted_in) == int(amount_in)
        except ValueError:
            swap_ok = False

    replay = evaluate_route_quote_receipt_hop_replay_gate(
        direction_ok=direction_ok,
        forward_direction=forward_direction,
        swap_ok=swap_ok,
        quote_matches=quote_matches,
        next_reserve_in=next_rin,
        next_reserve_out=next_rout,
    )
    if not replay.replay_ok:
        return False, route_quote_receipt_hop_replay_error(replay), None
    return True, "ok", replace(pool, reserve0=int(replay.next_reserve0), reserve1=int(replay.next_reserve1))


def verify_route_quote_receipt(
    receipt: object,
    *,
    pools_by_id: Dict[str, PoolState],
    expected_quote_epoch: int | None = None,
) -> Tuple[bool, str]:
    """
    Verify a quote receipt against pool snapshots and AMM semantics.

    When `expected_quote_epoch` is supplied, the receipt must carry the same
    non-negative epoch. This lets callers bind a quote receipt to the current
    route/session context while preserving legacy verification for callers that
    do not use quote epochs.

    Returns (ok, error_code).
    """
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"

    want_hash = receipt.get("receipt_hash")
    schema_ok = body.get("schema") == "zenodex/route_quote_receipt/v1"
    receipt_hash_present = isinstance(want_hash, str) and bool(want_hash)
    hash_matches = bool(receipt_hash_present and receipt_hash(body) == want_hash)
    kind = str(body.get("kind", "")).strip().lower()
    canonical_route_certificate = body.get("canonical_route_certificate")
    body_asset_in = body.get("asset_in")
    body_asset_out = body.get("asset_out")
    body_assets_ok = (
        not isinstance(body_asset_in, str)
        or not isinstance(body_asset_out, str)
        or not body_asset_in
        or not body_asset_out
        or body_asset_in == body_asset_out
    )
    body_assets_ok = not body_assets_ok
    quote_epoch_ok = True
    quote_epoch_value: int | None = None
    if "quote_epoch" in body:
        quote_epoch_value = _require_receipt_int(body.get("quote_epoch"))
        quote_epoch_ok = quote_epoch_value is not None and quote_epoch_value >= 0
    pools = body.get("pools")
    pools_object_ok = isinstance(pools, dict)
    legs = body.get("legs")
    legs_list_ok = isinstance(legs, list) and bool(legs)
    precheck = evaluate_route_quote_receipt_precheck_gate(
        schema_ok=schema_ok,
        receipt_hash_present=receipt_hash_present,
        hash_matches=hash_matches,
        kind_ok=kind in {"exact_in", "exact_out"},
        canonical_certificate_allowed=canonical_route_certificate is None or kind == "exact_in",
        body_assets_ok=body_assets_ok,
        quote_epoch_ok=quote_epoch_ok,
        pools_object_ok=pools_object_ok,
        legs_list_ok=legs_list_ok,
    )
    if not precheck.precheck_ok:
        return False, route_quote_receipt_precheck_error(precheck)
    if expected_quote_epoch is not None:
        expected_quote_epoch_value = _require_receipt_int(expected_quote_epoch)
        if expected_quote_epoch_value is None or expected_quote_epoch_value < 0:
            return False, "bad_expected_quote_epoch"
        if quote_epoch_value is None:
            return False, "missing_quote_epoch"
        if quote_epoch_value != expected_quote_epoch_value:
            return False, "quote_epoch_mismatch"
    if not isinstance(pools, dict):
        return False, "bad_pools"
    if not isinstance(legs, list) or not legs:
        return False, "bad_legs"
    if not isinstance(body_asset_in, str) or not isinstance(body_asset_out, str):
        return False, "bad_body_assets"

    if canonical_route_certificate is not None:
        from ..integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_in_route_canonical_certificate_payload,
        )

        cert_ok, cert_err = verify_exact_in_route_canonical_certificate_payload(canonical_route_certificate)
        if not cert_ok:
            return False, f"bad_canonical_route_certificate:{cert_err}"
        winner_quote = canonical_route_certificate.get("winner_quote") if isinstance(canonical_route_certificate, dict) else None
        cert_gate = evaluate_route_quote_receipt_certificate_gate(
            cert_present=True,
            cert_dict_ok=isinstance(canonical_route_certificate, dict),
            winner_quote_dict_ok=isinstance(winner_quote, dict),
            asset_in_match=isinstance(winner_quote, dict) and winner_quote.get("asset_in") == body.get("asset_in"),
            asset_out_match=isinstance(winner_quote, dict) and winner_quote.get("asset_out") == body.get("asset_out"),
            amount_in_match=isinstance(winner_quote, dict) and winner_quote.get("amount_in") == body.get("amount_in"),
            amount_out_match=isinstance(winner_quote, dict) and winner_quote.get("amount_out") == body.get("amount_out"),
            legs_match=isinstance(winner_quote, dict) and winner_quote.get("legs") == body.get("legs"),
        )
        if not cert_gate.certificate_ok:
            return False, route_quote_receipt_certificate_error(cert_gate)

    # Verify pool snapshot fingerprints.
    pool_entries_well_formed = True
    all_pools_present = True
    all_fingerprints_match = True
    for pid, fp in pools.items():
        if not isinstance(pid, str) or not isinstance(fp, str):
            pool_entries_well_formed = False
            break
        pool = pools_by_id.get(pid)
        if pool is None:
            all_pools_present = False
            break
        if pool_state_fingerprint(pool) != fp:
            all_fingerprints_match = False
            break
    pool_snapshot = evaluate_route_quote_receipt_pool_snapshot_gate(
        pool_entries_well_formed=pool_entries_well_formed,
        all_pools_present=all_pools_present,
        all_fingerprints_match=all_fingerprints_match,
    )
    if not pool_snapshot.snapshot_ok:
        return False, route_quote_receipt_pool_snapshot_error(pool_snapshot)
    working_pools = {pid: replace(pools_by_id[pid]) for pid in pools}

    # Verify hop-by-hop quote semantics.
    total_in = 0
    total_out = 0
    for leg in legs:
        if not isinstance(leg, dict):
            return False, "bad_leg"
        hops = leg.get("hops")
        if not isinstance(hops, list) or not hops:
            return False, "bad_hops"

        leg_in = _require_receipt_int(leg.get("amount_in"))
        leg_out = _require_receipt_int(leg.get("amount_out"))
        if leg_in is None or leg_out is None or leg_in <= 0 or leg_out <= 0:
            return False, "bad_leg_amounts"

        prev_out: int | None = None
        prev_asset_out: str | None = None
        for hop_index, hop in enumerate(hops):
            hop_dict_ok = isinstance(hop, dict)
            pid = hop.get("pool_id") if hop_dict_ok else None
            pool_id_ok = isinstance(pid, str) and bool(pid)
            snapshotted_pool_present = bool(pool_id_ok and pid in pools)
            pool = working_pools.get(pid) if pool_id_ok else None
            working_pool_present = bool(pool is not None)

            asset_in = hop.get("asset_in") if hop_dict_ok else None
            asset_out = hop.get("asset_out") if hop_dict_ok else None
            assets_shaped_ok = isinstance(asset_in, str) and isinstance(asset_out, str)
            is_first_hop = hop_index == 0
            first_hop_asset_in_ok = bool((not is_first_hop) or asset_in == body_asset_in)
            hop_asset_chain_ok = bool(is_first_hop or asset_in == prev_asset_out)

            amt_in = _require_receipt_int(hop.get("amount_in")) if hop_dict_ok else None
            amt_out = _require_receipt_int(hop.get("amount_out")) if hop_dict_ok else None
            hop_amounts_ok = (
                amt_in is not None and amt_out is not None and amt_in > 0 and amt_out > 0
            )
            hop_amount_chain_ok = bool(prev_out is None or amt_in == prev_out)

            hop_gate = evaluate_route_quote_receipt_hop_structure_gate(
                hop_dict_ok=hop_dict_ok,
                pool_id_ok=pool_id_ok,
                snapshotted_pool_present=snapshotted_pool_present,
                working_pool_present=working_pool_present,
                assets_shaped_ok=assets_shaped_ok,
                is_first_hop=is_first_hop,
                first_hop_asset_in_ok=first_hop_asset_in_ok,
                hop_asset_chain_ok=hop_asset_chain_ok,
                hop_amounts_ok=hop_amounts_ok,
                hop_amount_chain_ok=hop_amount_chain_ok,
            )
            if not hop_gate.hop_ok:
                return False, route_quote_receipt_hop_structure_error(hop_gate)
            if (
                not isinstance(pid, str)
                or pool is None
                or not isinstance(asset_in, str)
                or not isinstance(asset_out, str)
                or amt_in is None
                or amt_out is None
            ):
                return False, route_quote_receipt_hop_structure_error(hop_gate)

            ok, err, next_pool = _replay_and_apply_hop(
                pool=pool,
                kind=kind,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amt_in,
                amount_out=amt_out,
            )
            if not ok or next_pool is None:
                return False, err
            working_pools[pid] = next_pool

            prev_out = amt_out
            prev_asset_out = str(asset_out)

        first_hop_amount_in = _require_receipt_int(hops[0].get("amount_in"))
        last_hop_amount_out = _require_receipt_int(hops[-1].get("amount_out"))
        leg_summary = evaluate_route_quote_receipt_leg_summary_gate(
            final_asset_out_ok=prev_asset_out == body_asset_out,
            first_hop_amount_in_ok=first_hop_amount_in is not None and first_hop_amount_in == leg_in,
            last_hop_amount_out_ok=last_hop_amount_out is not None and last_hop_amount_out == leg_out,
        )
        if not leg_summary.leg_ok:
            return False, route_quote_receipt_leg_summary_error(leg_summary)

        total_in += leg_in
        total_out += leg_out

    body_amount_in = _require_receipt_int(body.get("amount_in"))
    body_amount_out = _require_receipt_int(body.get("amount_out"))
    body_amounts_ok = body_amount_in is not None and body_amount_out is not None
    totals_gate = evaluate_route_quote_receipt_totals_gate(
        body_amounts_ok=body_amounts_ok,
        totals_match=body_amounts_ok and total_in == body_amount_in and total_out == body_amount_out,
    )
    if not totals_gate.totals_ok:
        return False, route_quote_receipt_totals_error(totals_gate)

    return True, "ok"
