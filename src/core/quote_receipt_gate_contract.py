"""Stable reject codes, primitives, and outcomes for quote receipt gates."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict


def _require_receipt_int(value: Any) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        return None
    return int(value)


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


def route_quote_receipt_pool_snapshot_error(outcome: RouteQuoteReceiptPoolSnapshotOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT: "bad_pool_fingerprint",
        QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL: "missing_pool",
        QUOTE_RECEIPT_POOL_SNAPSHOT_MISMATCH: "pool_snapshot_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


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


def route_quote_receipt_leg_summary_error(outcome: RouteQuoteReceiptLegSummaryOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_LEG_SUMMARY_ASSET_OUT_MISMATCH: "leg_asset_out_mismatch",
        QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_IN_MISMATCH: "leg_amount_in_mismatch",
        QUOTE_RECEIPT_LEG_SUMMARY_AMOUNT_OUT_MISMATCH: "leg_amount_out_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


def route_quote_receipt_totals_error(outcome: RouteQuoteReceiptTotalsOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_TOTALS_BAD_BODY_AMOUNTS: "bad_body_amounts",
        QUOTE_RECEIPT_TOTALS_MISMATCH: "totals_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")


def route_quote_receipt_hop_replay_error(outcome: RouteQuoteReceiptHopReplayOutcome) -> str:
    mapping = {
        QUOTE_RECEIPT_REPLAY_BAD_POOL_DIRECTION: "bad_pool_direction",
        QUOTE_RECEIPT_REPLAY_HOP_QUOTE_ERROR: "hop_quote_error",
        QUOTE_RECEIPT_REPLAY_HOP_QUOTE_MISMATCH: "hop_quote_mismatch",
    }
    return mapping.get(outcome.reject_code, "ok")
