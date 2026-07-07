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

from dataclasses import dataclass
from typing import Any, Dict, Tuple

from ..core import quote_receipt_gates as _quote_receipt_gates
from ..core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from ..core.frontier_signature_root import (
    FrontierSignatureCertificatesRootBinding,
    normalize_frontier_signature_binding,
)
from ..core.quote_receipt_body_verification import (
    _precheck_receipt_body,
    _ReceiptBodyContext,
    _verify_canonical_route_certificate,
    _verify_expected_quote_epoch,
    _verify_pool_snapshots,
)
from ..core.quote_receipt_building import (
    attach_frontier_signature_binding_to_route_quote_receipt,
    make_risc0_route_quote_receipt_binding_hash,
    make_risc0_route_quote_receipt_binding_hash_from_body,
    make_route_quote_receipt,
    pool_state_fingerprint,
    receipt_hash,
)
from ..core.quote_receipt_gate_contract import (
    route_quote_receipt_hop_structure_error,
    route_quote_receipt_leg_summary_error,
    route_quote_receipt_totals_error,
)
from ..core.quote_receipt_gates import (
    _require_receipt_int,
    evaluate_route_quote_receipt_hop_structure_gate,
    evaluate_route_quote_receipt_leg_summary_gate,
    evaluate_route_quote_receipt_totals_gate,
)
from ..core.quote_receipt_hop_replay import _ReceiptHopData
from ..core.quote_receipt_hop_replay import (
    replay_and_apply_hop as _replay_and_apply_hop_with_reserve_lookup,
)
from ..core.quote_receipt_limits import ROUTE_QUOTE_RECEIPT_MAX_HOPS_PER_LEG
from ..state.pools import PoolState

__all__ = [
    "attach_frontier_signature_binding_to_route_quote_receipt",
    "make_route_quote_receipt",
    "make_risc0_route_quote_receipt_binding_hash",
    "make_risc0_route_quote_receipt_binding_hash_from_body",
    "pool_state_fingerprint",
    "receipt_hash",
    "verify_route_quote_receipt",
]


def __getattr__(name: str) -> object:
    """Compatibility re-export for quote receipt gate constants and outcomes."""
    try:
        return getattr(_quote_receipt_gates, name)
    except AttributeError as exc:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}") from exc


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(dir(_quote_receipt_gates)))


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
class _ReceiptLegContext:
    kind: str
    body_asset_in: str
    body_asset_out: str
    working_pools: Dict[str, PoolState]
    snapshotted_pools: Dict[str, Any]


@dataclass(frozen=True)
class _ReceiptLegsContext:
    kind: str
    legs: list[Any]
    body: Dict[str, Any]
    body_asset_in: str
    body_asset_out: str
    working_pools: Dict[str, PoolState]
    snapshotted_pools: Dict[str, Any]


@dataclass(frozen=True)
class _ReceiptHopFields:
    hop_dict_ok: bool
    pool_id: object
    pool: PoolState | None
    asset_in: object
    asset_out: object
    amount_in: int | None
    amount_out: int | None


def _pool_reserves_for_hop(pool: PoolState, *, asset_in: str, asset_out: str) -> Tuple[int, int] | None:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _replay_and_apply_hop(
    *,
    kind: str,
    hop_data: _ReceiptHopData,
) -> Tuple[bool, str, PoolState | None]:
    return _replay_and_apply_hop_with_reserve_lookup(
        kind=kind,
        hop_data=hop_data,
        reserve_lookup=_pool_reserves_for_hop,
        swap_exact_in=swap_exact_in_for_pool,
        swap_exact_out=swap_exact_out_for_pool,
    )


def _hop_field(hop: object, key: str) -> object:
    if not isinstance(hop, dict):
        return None
    return hop.get(key)


def _extract_receipt_hop_fields(ctx: _ReceiptHopContext) -> _ReceiptHopFields:
    hop_dict_ok = isinstance(ctx.hop, dict)
    pid = _hop_field(ctx.hop, "pool_id")
    pid_str = pid if isinstance(pid, str) and bool(pid) else None
    pool = ctx.working_pools.get(pid_str) if pid_str is not None else None
    return _ReceiptHopFields(
        hop_dict_ok=hop_dict_ok,
        pool_id=pid,
        pool=pool,
        asset_in=_hop_field(ctx.hop, "asset_in"),
        asset_out=_hop_field(ctx.hop, "asset_out"),
        amount_in=_require_receipt_int(_hop_field(ctx.hop, "amount_in")),
        amount_out=_require_receipt_int(_hop_field(ctx.hop, "amount_out")),
    )


def _evaluate_receipt_hop_structure(ctx: _ReceiptHopContext, fields: _ReceiptHopFields):
    pool_id_ok = isinstance(fields.pool_id, str) and bool(fields.pool_id)
    assets_shaped_ok = isinstance(fields.asset_in, str) and isinstance(fields.asset_out, str)
    is_first_hop = ctx.hop_index == 0
    hop_amounts_ok = (
        fields.amount_in is not None
        and fields.amount_out is not None
        and fields.amount_in > 0
        and fields.amount_out > 0
    )
    return evaluate_route_quote_receipt_hop_structure_gate(
        hop_dict_ok=fields.hop_dict_ok,
        pool_id_ok=pool_id_ok,
        snapshotted_pool_present=bool(pool_id_ok and fields.pool_id in ctx.snapshotted_pools),
        working_pool_present=bool(fields.pool is not None),
        assets_shaped_ok=assets_shaped_ok,
        is_first_hop=is_first_hop,
        first_hop_asset_in_ok=bool((not is_first_hop) or fields.asset_in == ctx.body_asset_in),
        hop_asset_chain_ok=bool(is_first_hop or fields.asset_in == ctx.prev_asset_out),
        hop_amounts_ok=hop_amounts_ok,
        hop_amount_chain_ok=bool(ctx.prev_out is None or fields.amount_in == ctx.prev_out),
    )


def _receipt_hop_data_from_fields(fields: _ReceiptHopFields) -> _ReceiptHopData | None:
    if (
        not isinstance(fields.pool_id, str)
        or fields.pool is None
        or not isinstance(fields.asset_in, str)
        or not isinstance(fields.asset_out, str)
        or fields.amount_in is None
        or fields.amount_out is None
    ):
        return None
    return _ReceiptHopData(
        pool_id=fields.pool_id,
        pool=fields.pool,
        asset_in=fields.asset_in,
        asset_out=fields.asset_out,
        amount_in=fields.amount_in,
        amount_out=fields.amount_out,
    )


def _parse_receipt_hop_structure(
    ctx: _ReceiptHopContext,
) -> Tuple[bool, str, _ReceiptHopData | None]:
    fields = _extract_receipt_hop_fields(ctx)
    hop_gate = _evaluate_receipt_hop_structure(ctx, fields)
    if not hop_gate.hop_ok:
        return False, route_quote_receipt_hop_structure_error(hop_gate), None
    hop_data = _receipt_hop_data_from_fields(fields)
    if hop_data is None:
        return False, route_quote_receipt_hop_structure_error(hop_gate), None
    return True, "ok", hop_data


def _verify_receipt_hop(
    ctx: _ReceiptHopContext,
) -> Tuple[bool, str, str | None, int | None, str | None, PoolState | None]:
    structure_ok, structure_err, hop_data = _parse_receipt_hop_structure(ctx)
    if not structure_ok or hop_data is None:
        return False, structure_err, None, None, None, None
    ok, err, next_pool = _replay_and_apply_hop(
        kind=ctx.kind,
        hop_data=hop_data,
    )
    if not ok or next_pool is None:
        return False, err, None, None, None, None
    return True, "ok", hop_data.pool_id, hop_data.amount_out, hop_data.asset_out, next_pool


def _verify_receipt_leg(ctx: _ReceiptLegContext, leg: object) -> Tuple[bool, str, int, int]:
    if not isinstance(leg, dict):
        return False, "bad_leg", 0, 0
    hops = leg.get("hops")
    if not isinstance(hops, list) or not hops or len(hops) > ROUTE_QUOTE_RECEIPT_MAX_HOPS_PER_LEG:
        return False, "bad_hops", 0, 0

    leg_in = _require_receipt_int(leg.get("amount_in"))
    leg_out = _require_receipt_int(leg.get("amount_out"))
    if leg_in is None or leg_out is None or leg_in <= 0 or leg_out <= 0:
        return False, "bad_leg_amounts", 0, 0

    prev_out: int | None = None
    prev_asset_out: str | None = None
    for hop_index, hop in enumerate(hops):
        hop_ctx = _ReceiptHopContext(
            kind=ctx.kind,
            hop=hop,
            hop_index=hop_index,
            prev_out=prev_out,
            prev_asset_out=prev_asset_out,
            body_asset_in=ctx.body_asset_in,
            working_pools=ctx.working_pools,
            snapshotted_pools=ctx.snapshotted_pools,
        )
        ok, err, pid, amt_out, asset_out, next_pool = _verify_receipt_hop(hop_ctx)
        if not ok or pid is None or amt_out is None or asset_out is None or next_pool is None:
            return False, err, 0, 0
        ctx.working_pools[pid] = next_pool
        prev_out = amt_out
        prev_asset_out = str(asset_out)

    first_hop_amount_in = _require_receipt_int(hops[0].get("amount_in"))
    last_hop_amount_out = _require_receipt_int(hops[-1].get("amount_out"))
    leg_summary = evaluate_route_quote_receipt_leg_summary_gate(
        final_asset_out_ok=prev_asset_out == ctx.body_asset_out,
        first_hop_amount_in_ok=first_hop_amount_in is not None and first_hop_amount_in == leg_in,
        last_hop_amount_out_ok=last_hop_amount_out is not None and last_hop_amount_out == leg_out,
    )
    if not leg_summary.leg_ok:
        return False, route_quote_receipt_leg_summary_error(leg_summary), 0, 0
    return True, "ok", int(leg_in), int(leg_out)


def _verify_receipt_legs_and_totals(ctx: _ReceiptLegsContext) -> Tuple[bool, str]:
    total_in = 0
    total_out = 0
    leg_ctx = _ReceiptLegContext(
        kind=ctx.kind,
        body_asset_in=ctx.body_asset_in,
        body_asset_out=ctx.body_asset_out,
        working_pools=ctx.working_pools,
        snapshotted_pools=ctx.snapshotted_pools,
    )
    for leg in ctx.legs:
        ok, err, leg_in, leg_out = _verify_receipt_leg(leg_ctx, leg)
        if not ok:
            return False, err
        total_in += leg_in
        total_out += leg_out

    body_amount_in = _require_receipt_int(ctx.body.get("amount_in"))
    body_amount_out = _require_receipt_int(ctx.body.get("amount_out"))
    body_amounts_ok = body_amount_in is not None and body_amount_out is not None
    totals_gate = evaluate_route_quote_receipt_totals_gate(
        body_amounts_ok=body_amounts_ok,
        totals_match=body_amounts_ok and total_in == body_amount_in and total_out == body_amount_out,
    )
    if not totals_gate.totals_ok:
        return False, route_quote_receipt_totals_error(totals_gate)
    return True, "ok"


def _verify_expected_frontier_signature_binding(
    *,
    body: Dict[str, Any],
    expected_binding: FrontierSignatureCertificatesRootBinding | None,
) -> Tuple[bool, str]:
    body_count = body.get("shared_pool_frontier_signature_certificate_count")
    body_root = body.get("shared_pool_frontier_signature_certificates_root")
    body_has_count = "shared_pool_frontier_signature_certificate_count" in body
    body_has_root = "shared_pool_frontier_signature_certificates_root" in body

    if body_has_count != body_has_root:
        return False, "frontier_signature_binding_partial"

    body_binding: tuple[int, str] | None = None
    if body_has_count and body_has_root:
        try:
            body_binding = normalize_frontier_signature_binding(
                count=body_count,
                root=body_root,
                count_name="shared_pool_frontier_signature_certificate_count",
                root_name="shared_pool_frontier_signature_certificates_root",
            )
        except (TypeError, ValueError):
            return False, "bad_frontier_signature_binding"

    if expected_binding is None:
        return True, "ok"

    if body_binding is None:
        return False, "missing_frontier_signature_binding"
    if body_binding[0] != expected_binding.certificate_count:
        return False, "frontier_signature_count_mismatch"
    if body_binding[1] != expected_binding.certificates_root:
        return False, "frontier_signature_root_mismatch"
    return True, "ok"


def _verify_prechecked_route_quote_receipt(
    *,
    ctx: _ReceiptBodyContext,
    pools_by_id: Dict[str, PoolState],
    expected_quote_epoch: int | None,
    expected_frontier_signature_binding: FrontierSignatureCertificatesRootBinding | None,
) -> Tuple[bool, str]:
    epoch_ok, epoch_err = _verify_expected_quote_epoch(
        quote_epoch_value=ctx.quote_epoch_value,
        expected_quote_epoch=expected_quote_epoch,
    )
    if not epoch_ok:
        return False, epoch_err

    frontier_ok, frontier_err = _verify_expected_frontier_signature_binding(
        body=ctx.body,
        expected_binding=expected_frontier_signature_binding,
    )
    if not frontier_ok:
        return False, frontier_err

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
        _ReceiptLegsContext(
            kind=ctx.kind,
            legs=ctx.legs,
            body=ctx.body,
            body_asset_in=ctx.body_asset_in,
            body_asset_out=ctx.body_asset_out,
            working_pools=working_pools,
            snapshotted_pools=ctx.pools,
        )
    )
    if not legs_ok:
        return False, legs_err
    return True, "ok"


def verify_route_quote_receipt(
    receipt: object,
    *,
    pools_by_id: Dict[str, PoolState],
    expected_quote_epoch: int | None = None,
    expected_frontier_signature_binding: FrontierSignatureCertificatesRootBinding | None = None,
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
        expected_frontier_signature_binding=expected_frontier_signature_binding,
    )
