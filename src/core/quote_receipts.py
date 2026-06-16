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


GateFlagSpec = tuple[str, Any]
GateFailureSpec = tuple[str, str]


def _coerce_receipt_gate_checks(specs: tuple[GateFlagSpec, ...]) -> Dict[str, bool]:
    return {
        name: _require_receipt_gate_flag(value, name=name)
        for name, value in specs
    }


def _first_failed_gate_code(
    *,
    checks: Dict[str, bool],
    failures: tuple[GateFailureSpec, ...],
    ok_code: str,
) -> str:
    for check_name, reject_code in failures:
        if not checks[check_name]:
            return reject_code
    return ok_code


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


@dataclass(frozen=True)
class _ReceiptBodyContext:
    body: Dict[str, Any]
    kind: str
    canonical_route_certificate: object
    body_asset_in: str
    body_asset_out: str
    quote_epoch_value: int | None
    pools: Dict[str, Any]
    legs: list[Any]


@dataclass(frozen=True)
class _ReceiptHopContext:
    kind: str
    hop: object
    hop_index: int
    prev_out: int | None
    prev_asset_out: str | None
    body_asset_in: str
    working_pools: Dict[str, PoolState]
    snapshotted_pools: Dict[str, Any]


@dataclass(frozen=True)
class _ReceiptHopData:
    pool_id: str
    pool: PoolState
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int


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


def _normalize_route_quote_receipt_kind(kind: str) -> str:
    normalized = str(kind).strip().lower()
    if normalized not in {"exact_in", "exact_out"}:
        raise ValueError("kind must be 'exact_in' or 'exact_out'")
    return normalized


def _normalize_route_quote_epoch(quote_epoch: int | None) -> int | None:
    if quote_epoch is None:
        return None
    normalized = _require_receipt_int(quote_epoch)
    if normalized is None or normalized < 0:
        raise ValueError("quote_epoch must be a non-negative int")
    return int(normalized)


def _route_quote_receipt_hop_payload(
    *,
    hop: Any,
    pools_by_id: Dict[str, PoolState],
    pool_fps: Dict[str, str],
) -> Dict[str, Any]:
    pool = pools_by_id.get(hop.pool_id)
    if pool is None:
        raise ValueError(f"missing pool for hop.pool_id={hop.pool_id!r}")
    if hop.pool_id not in pool_fps:
        pool_fps[hop.pool_id] = pool_state_fingerprint(pool)
    return {
        "pool_id": hop.pool_id,
        "asset_in": hop.asset_in,
        "asset_out": hop.asset_out,
        "amount_in": int(hop.amount_in),
        "amount_out": int(hop.amount_out),
    }


def _route_quote_receipt_legs_and_pool_fingerprints(
    *,
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
) -> Tuple[list[Dict[str, Any]], Dict[str, str]]:
    legs: list[Dict[str, Any]] = []
    pool_fps: Dict[str, str] = {}
    for leg in quote.legs:
        hops = [
            _route_quote_receipt_hop_payload(
                hop=hop,
                pools_by_id=pools_by_id,
                pool_fps=pool_fps,
            )
            for hop in leg.hops
        ]
        legs.append(
            {
                "amount_in": int(leg.amount_in),
                "amount_out": int(leg.amount_out),
                "hops": hops,
            }
        )
    return legs, pool_fps


def _attach_exact_in_canonical_route_certificate(
    *,
    body: Dict[str, Any],
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
) -> None:
    # Optional canonical-winner attachment: include it when the provided quote is
    # the actual canonical winner under the current router surface.
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
    k = _normalize_route_quote_receipt_kind(kind)
    quote_epoch = _normalize_route_quote_epoch(quote_epoch)
    legs, pool_fps = _route_quote_receipt_legs_and_pool_fingerprints(
        quote=quote,
        pools_by_id=pools_by_id,
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
        _attach_exact_in_canonical_route_certificate(
            body=body,
            quote=quote,
            pools_by_id=pools_by_id,
        )
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
        except (TypeError, ValueError, OverflowError):
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


def _verify_expected_quote_epoch(
    *,
    quote_epoch_value: int | None,
    expected_quote_epoch: int | None,
) -> Tuple[bool, str]:
    if expected_quote_epoch is None:
        return True, "ok"
    expected_quote_epoch_value = _require_receipt_int(expected_quote_epoch)
    if expected_quote_epoch_value is None or expected_quote_epoch_value < 0:
        return False, "bad_expected_quote_epoch"
    if quote_epoch_value is None:
        return False, "missing_quote_epoch"
    if quote_epoch_value != expected_quote_epoch_value:
        return False, "quote_epoch_mismatch"
    return True, "ok"


def _verify_canonical_route_certificate(
    *,
    canonical_route_certificate: object,
    body: Dict[str, Any],
) -> Tuple[bool, str]:
    if canonical_route_certificate is None:
        return True, "ok"
    from ..integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
        verify_exact_in_route_canonical_certificate_payload,
    )

    cert_ok, cert_err = verify_exact_in_route_canonical_certificate_payload(canonical_route_certificate)
    if not cert_ok:
        return False, f"bad_canonical_route_certificate:{cert_err}"
    winner_quote = (
        canonical_route_certificate.get("winner_quote")
        if isinstance(canonical_route_certificate, dict)
        else None
    )
    winner_is_dict = isinstance(winner_quote, dict)
    cert_gate = evaluate_route_quote_receipt_certificate_gate(
        cert_present=True,
        cert_dict_ok=isinstance(canonical_route_certificate, dict),
        winner_quote_dict_ok=winner_is_dict,
        asset_in_match=winner_is_dict and winner_quote.get("asset_in") == body.get("asset_in"),
        asset_out_match=winner_is_dict and winner_quote.get("asset_out") == body.get("asset_out"),
        amount_in_match=winner_is_dict and winner_quote.get("amount_in") == body.get("amount_in"),
        amount_out_match=winner_is_dict and winner_quote.get("amount_out") == body.get("amount_out"),
        legs_match=winner_is_dict and winner_quote.get("legs") == body.get("legs"),
    )
    if not cert_gate.certificate_ok:
        return False, route_quote_receipt_certificate_error(cert_gate)
    return True, "ok"


def _verify_pool_snapshots(
    *,
    pools: Dict[str, Any],
    pools_by_id: Dict[str, PoolState],
) -> Tuple[bool, str, Dict[str, PoolState] | None]:
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
        return False, route_quote_receipt_pool_snapshot_error(pool_snapshot), None
    return True, "ok", {pid: replace(pools_by_id[pid]) for pid in pools}


def _parse_receipt_hop_structure(
    ctx: _ReceiptHopContext,
) -> Tuple[bool, str, _ReceiptHopData | None]:
    hop_dict_ok = isinstance(ctx.hop, dict)
    pid = ctx.hop.get("pool_id") if hop_dict_ok else None
    pool_id_ok = isinstance(pid, str) and bool(pid)
    snapshotted_pool_present = bool(pool_id_ok and pid in ctx.snapshotted_pools)
    pool = ctx.working_pools.get(pid) if pool_id_ok else None
    working_pool_present = bool(pool is not None)

    asset_in = ctx.hop.get("asset_in") if hop_dict_ok else None
    asset_out = ctx.hop.get("asset_out") if hop_dict_ok else None
    assets_shaped_ok = isinstance(asset_in, str) and isinstance(asset_out, str)
    is_first_hop = ctx.hop_index == 0
    first_hop_asset_in_ok = bool((not is_first_hop) or asset_in == ctx.body_asset_in)
    hop_asset_chain_ok = bool(is_first_hop or asset_in == ctx.prev_asset_out)

    amt_in = _require_receipt_int(ctx.hop.get("amount_in")) if hop_dict_ok else None
    amt_out = _require_receipt_int(ctx.hop.get("amount_out")) if hop_dict_ok else None
    hop_amounts_ok = amt_in is not None and amt_out is not None and amt_in > 0 and amt_out > 0
    hop_amount_chain_ok = bool(ctx.prev_out is None or amt_in == ctx.prev_out)

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
        return False, route_quote_receipt_hop_structure_error(hop_gate), None
    if (
        not isinstance(pid, str)
        or pool is None
        or not isinstance(asset_in, str)
        or not isinstance(asset_out, str)
        or amt_in is None
        or amt_out is None
    ):
        return False, route_quote_receipt_hop_structure_error(hop_gate), None
    return True, "ok", _ReceiptHopData(
        pool_id=pid,
        pool=pool,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amt_in,
        amount_out=amt_out,
    )


def _verify_receipt_hop(
    ctx: _ReceiptHopContext,
) -> Tuple[bool, str, str | None, int | None, str | None, PoolState | None]:
    structure_ok, structure_err, hop_data = _parse_receipt_hop_structure(ctx)
    if not structure_ok or hop_data is None:
        return False, structure_err, None, None, None, None
    ok, err, next_pool = _replay_and_apply_hop(
        pool=hop_data.pool,
        kind=ctx.kind,
        asset_in=hop_data.asset_in,
        asset_out=hop_data.asset_out,
        amount_in=hop_data.amount_in,
        amount_out=hop_data.amount_out,
    )
    if not ok or next_pool is None:
        return False, err, None, None, None, None
    return True, "ok", hop_data.pool_id, hop_data.amount_out, hop_data.asset_out, next_pool


def _verify_receipt_leg(
    *,
    kind: str,
    leg: object,
    body_asset_in: str,
    body_asset_out: str,
    working_pools: Dict[str, PoolState],
    snapshotted_pools: Dict[str, Any],
) -> Tuple[bool, str, int, int]:
    if not isinstance(leg, dict):
        return False, "bad_leg", 0, 0
    hops = leg.get("hops")
    if not isinstance(hops, list) or not hops:
        return False, "bad_hops", 0, 0

    leg_in = _require_receipt_int(leg.get("amount_in"))
    leg_out = _require_receipt_int(leg.get("amount_out"))
    if leg_in is None or leg_out is None or leg_in <= 0 or leg_out <= 0:
        return False, "bad_leg_amounts", 0, 0

    prev_out: int | None = None
    prev_asset_out: str | None = None
    for hop_index, hop in enumerate(hops):
        hop_ctx = _ReceiptHopContext(
            kind=kind,
            hop=hop,
            hop_index=hop_index,
            prev_out=prev_out,
            prev_asset_out=prev_asset_out,
            body_asset_in=body_asset_in,
            working_pools=working_pools,
            snapshotted_pools=snapshotted_pools,
        )
        ok, err, pid, amt_out, asset_out, next_pool = _verify_receipt_hop(hop_ctx)
        if not ok or pid is None or amt_out is None or asset_out is None or next_pool is None:
            return False, err, 0, 0
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
        return False, route_quote_receipt_leg_summary_error(leg_summary), 0, 0
    return True, "ok", int(leg_in), int(leg_out)


def _verify_receipt_legs_and_totals(
    *,
    kind: str,
    legs: list[Any],
    body: Dict[str, Any],
    body_asset_in: str,
    body_asset_out: str,
    working_pools: Dict[str, PoolState],
    snapshotted_pools: Dict[str, Any],
) -> Tuple[bool, str]:
    total_in = 0
    total_out = 0
    for leg in legs:
        ok, err, leg_in, leg_out = _verify_receipt_leg(
            kind=kind,
            leg=leg,
            body_asset_in=body_asset_in,
            body_asset_out=body_asset_out,
            working_pools=working_pools,
            snapshotted_pools=snapshotted_pools,
        )
        if not ok:
            return False, err
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


def _precheck_receipt_body(
    *,
    body: Dict[str, Any],
    want_hash: object,
) -> Tuple[bool, str, _ReceiptBodyContext | None]:
    schema_ok = body.get("schema") == "zenodex/route_quote_receipt/v1"
    receipt_hash_present = isinstance(want_hash, str) and bool(want_hash)
    hash_matches = bool(receipt_hash_present and receipt_hash(body) == want_hash)
    kind = str(body.get("kind", "")).strip().lower()
    canonical_route_certificate = body.get("canonical_route_certificate")
    body_asset_in = body.get("asset_in")
    body_asset_out = body.get("asset_out")
    body_assets_ok = (
        isinstance(body_asset_in, str)
        and isinstance(body_asset_out, str)
        and bool(body_asset_in)
        and bool(body_asset_out)
        and body_asset_in != body_asset_out
    )
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
        return False, route_quote_receipt_precheck_error(precheck), None
    if not isinstance(pools, dict):
        return False, "bad_pools", None
    if not isinstance(legs, list) or not legs:
        return False, "bad_legs", None
    if not isinstance(body_asset_in, str) or not isinstance(body_asset_out, str):
        return False, "bad_body_assets", None
    return True, "ok", _ReceiptBodyContext(
        body=body,
        kind=kind,
        canonical_route_certificate=canonical_route_certificate,
        body_asset_in=body_asset_in,
        body_asset_out=body_asset_out,
        quote_epoch_value=quote_epoch_value,
        pools=pools,
        legs=legs,
    )


def _verify_prechecked_route_quote_receipt(
    *,
    ctx: _ReceiptBodyContext,
    pools_by_id: Dict[str, PoolState],
    expected_quote_epoch: int | None,
) -> Tuple[bool, str]:
    epoch_ok, epoch_err = _verify_expected_quote_epoch(
        quote_epoch_value=ctx.quote_epoch_value,
        expected_quote_epoch=expected_quote_epoch,
    )
    if not epoch_ok:
        return False, epoch_err

    certificate_ok, certificate_err = _verify_canonical_route_certificate(
        canonical_route_certificate=ctx.canonical_route_certificate,
        body=ctx.body,
    )
    if not certificate_ok:
        return False, certificate_err

    snapshot_ok, snapshot_err, working_pools = _verify_pool_snapshots(
        pools=ctx.pools,
        pools_by_id=pools_by_id,
    )
    if not snapshot_ok or working_pools is None:
        return False, snapshot_err

    legs_ok, legs_err = _verify_receipt_legs_and_totals(
        kind=ctx.kind,
        legs=ctx.legs,
        body=ctx.body,
        body_asset_in=ctx.body_asset_in,
        body_asset_out=ctx.body_asset_out,
        working_pools=working_pools,
        snapshotted_pools=ctx.pools,
    )
    if not legs_ok:
        return False, legs_err
    return True, "ok"


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
    precheck_ok, precheck_err, ctx = _precheck_receipt_body(
        body=body,
        want_hash=want_hash,
    )
    if not precheck_ok or ctx is None:
        return False, precheck_err
    return _verify_prechecked_route_quote_receipt(
        ctx=ctx,
        pools_by_id=pools_by_id,
        expected_quote_epoch=expected_quote_epoch,
    )
