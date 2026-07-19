"""Body-level checks for route quote receipt verification."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, replace
from typing import Any, Dict, Tuple

from ..core.quote_receipt_building import pool_state_fingerprint, receipt_hash
from ..core.quote_receipt_gate_contract import (
    route_quote_receipt_certificate_error,
    route_quote_receipt_pool_snapshot_error,
    route_quote_receipt_precheck_error,
)
from ..core.quote_receipt_gates import (
    _require_receipt_int,
    evaluate_route_quote_receipt_certificate_gate,
    evaluate_route_quote_receipt_pool_snapshot_gate,
    evaluate_route_quote_receipt_precheck_gate,
)
from ..core.quote_receipt_limits import (
    ROUTE_QUOTE_RECEIPT_MAX_LEGS,
    ROUTE_QUOTE_RECEIPT_MAX_POOLS,
)
from ..state.pools import PoolState


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
    pools_by_id: Mapping[str, PoolState],
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
    pools_object_ok = isinstance(pools, dict) and len(pools) <= ROUTE_QUOTE_RECEIPT_MAX_POOLS
    legs = body.get("legs")
    legs_list_ok = isinstance(legs, list) and 0 < len(legs) <= ROUTE_QUOTE_RECEIPT_MAX_LEGS
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
