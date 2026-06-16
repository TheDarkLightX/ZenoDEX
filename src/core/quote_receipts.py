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

from ..core import quote_receipt_gates as _quote_receipt_gates
from ..core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from ..core.quote_receipt_building import (
    make_route_quote_receipt,
    pool_state_fingerprint,
    receipt_hash,
)
from ..core.quote_receipt_gate_contract import (
    route_quote_receipt_certificate_error,
    route_quote_receipt_hop_replay_error,
    route_quote_receipt_hop_structure_error,
    route_quote_receipt_leg_summary_error,
    route_quote_receipt_pool_snapshot_error,
    route_quote_receipt_precheck_error,
    route_quote_receipt_totals_error,
)
from ..core.quote_receipt_gates import (
    _require_receipt_int,
    evaluate_route_quote_receipt_certificate_gate,
    evaluate_route_quote_receipt_hop_replay_gate,
    evaluate_route_quote_receipt_hop_structure_gate,
    evaluate_route_quote_receipt_leg_summary_gate,
    evaluate_route_quote_receipt_pool_snapshot_gate,
    evaluate_route_quote_receipt_precheck_gate,
    evaluate_route_quote_receipt_totals_gate,
)
from ..state.pools import PoolState

__all__ = [
    "make_route_quote_receipt",
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
class _ReceiptHopData:
    pool_id: str
    pool: PoolState
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int


@dataclass(frozen=True)
class _HopDirection:
    forward_direction: bool
    direction_ok: bool
    reserve_in: int
    reserve_out: int


@dataclass(frozen=True)
class _HopSwapReplay:
    swap_ok: bool
    quote_matches: bool
    next_reserve_in: int
    next_reserve_out: int


def _pool_reserves_for_hop(pool: PoolState, *, asset_in: str, asset_out: str) -> Tuple[int, int] | None:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _resolve_hop_direction(hop_data: _ReceiptHopData) -> _HopDirection:
    pool = hop_data.pool
    forward_direction = bool(hop_data.asset_in == pool.asset0 and hop_data.asset_out == pool.asset1)
    reverse_direction = bool(hop_data.asset_in == pool.asset1 and hop_data.asset_out == pool.asset0)
    reserves = _pool_reserves_for_hop(pool, asset_in=hop_data.asset_in, asset_out=hop_data.asset_out)
    if not (forward_direction or reverse_direction) or reserves is None:
        return _HopDirection(
            forward_direction=forward_direction,
            direction_ok=False,
            reserve_in=0,
            reserve_out=0,
        )
    reserve_in, reserve_out = reserves
    return _HopDirection(
        forward_direction=forward_direction,
        direction_ok=True,
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
    )


def _replay_hop_swap(
    *,
    kind: str,
    direction: _HopDirection,
    hop_data: _ReceiptHopData,
) -> _HopSwapReplay:
    if not direction.direction_ok:
        return _HopSwapReplay(
            swap_ok=False,
            quote_matches=False,
            next_reserve_in=0,
            next_reserve_out=0,
        )
    try:
        if kind == "exact_in":
            quoted_out, next_reserves = swap_exact_in_for_pool(
                hop_data.pool,
                reserve_in=int(direction.reserve_in),
                reserve_out=int(direction.reserve_out),
                amount_in=int(hop_data.amount_in),
            )
            quote_matches = int(quoted_out) == int(hop_data.amount_out)
        else:
            quoted_in, next_reserves = swap_exact_out_for_pool(
                hop_data.pool,
                reserve_in=int(direction.reserve_in),
                reserve_out=int(direction.reserve_out),
                amount_out=int(hop_data.amount_out),
            )
            quote_matches = int(quoted_in) == int(hop_data.amount_in)
    except (TypeError, ValueError, OverflowError):
        return _HopSwapReplay(
            swap_ok=False,
            quote_matches=False,
            next_reserve_in=0,
            next_reserve_out=0,
        )
    next_reserve_in, next_reserve_out = next_reserves
    return _HopSwapReplay(
        swap_ok=True,
        quote_matches=bool(quote_matches),
        next_reserve_in=int(next_reserve_in),
        next_reserve_out=int(next_reserve_out),
    )


def _replay_and_apply_hop(
    *,
    kind: str,
    hop_data: _ReceiptHopData,
) -> Tuple[bool, str, PoolState | None]:
    direction = _resolve_hop_direction(hop_data)
    swap = _replay_hop_swap(
        kind=kind,
        direction=direction,
        hop_data=hop_data,
    )

    replay = evaluate_route_quote_receipt_hop_replay_gate(
        direction_ok=direction.direction_ok,
        forward_direction=direction.forward_direction,
        swap_ok=swap.swap_ok,
        quote_matches=swap.quote_matches,
        next_reserve_in=swap.next_reserve_in,
        next_reserve_out=swap.next_reserve_out,
    )
    if not replay.replay_ok:
        return False, route_quote_receipt_hop_replay_error(replay), None
    return True, "ok", replace(hop_data.pool, reserve0=int(replay.next_reserve0), reserve1=int(replay.next_reserve1))


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
