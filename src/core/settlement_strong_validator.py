"""
Strong settlement validation (proof-carrying friendly).

The legacy validator in `src/core/batch_clearing.py` checks conservation and
non-negativity of the *net* deltas, but it does not bind those deltas to:
  - the user intents (min_out / max_in constraints, recipient rules, etc.)
  - the verified swap kernels (no "k decreases" / free value leaks)

This module treats the settlement as an *untrusted certificate* and replay-
verifies the batch by re-executing each filled intent against local copies of
state using the verified kernels (`amm_dispatch`, `lp_math_v7`, etc). It then
recomputes canonical deltas/events and requires exact match.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, List, Optional, Tuple, cast

from ..kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_out
from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.lp import LPTable
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus
from .amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from .batch_clearing import validate_settlement as validate_settlement_legacy
from .cpmm import MIN_LP_LOCK, compute_fee_total, swap_exact_in_with_protocol_fee
from .domain_limits import is_strict_int
from .liquidity import add_liquidity, create_pool, remove_liquidity
from .quote_receipts import pool_state_fingerprint
from .settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48

_MODE_STRONG_REPLAY = "strong_replay"
_MODE_STRONG_PROOF_CARRYING = "strong_proof_carrying"
_VALIDATION_MODES = frozenset({_MODE_STRONG_REPLAY, _MODE_STRONG_PROOF_CARRYING})


def _format_error_details(**kwargs: object) -> str:
    parts: list[str] = []
    for key, value in kwargs.items():
        if value is None:
            continue
        parts.append(f"{key}={value!r}")
    return ", ".join(parts)


def _quote_binding_error(reason: str, **kwargs: object) -> str:
    details = _format_error_details(**kwargs)
    if not details:
        return reason
    return f"{reason}: {details}"


def _quote_binding_context(intent: Intent) -> dict[str, object]:
    return {
        "intent_id": intent.intent_id,
        "quote_hash": intent.get_field("quote_receipt_hash"),
        "quote_pool_fingerprint": intent.get_field("quote_pool_fingerprint"),
        "leg_index": intent.get_field("quote_receipt_leg_index"),
        "pool_id": intent.get_field("pool_id"),
    }


@dataclass(frozen=True)
class _CowPairEntry:
    intent_id: str
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in_filled: int
    amount_out_filled: int


@dataclass(frozen=True)
class _QuoteBindingFields:
    receipt_hash: object
    pool_fingerprint: object
    leg_index: object


@dataclass(frozen=True)
class _CreatePoolFields:
    asset0: object
    asset1: object
    fee_bps: object
    amount0: object
    amount1: object
    created_at: object
    curve_tag: object
    curve_params: object


@dataclass(frozen=True)
class _ValidatedCreatePoolFields:
    asset0: AssetId
    asset1: AssetId
    fee_bps: int
    amount0: int
    amount1: int
    created_at: int
    curve_tag: Optional[str]
    curve_params: object


@dataclass(frozen=True)
class _CreatePoolReplay:
    fields: _ValidatedCreatePoolFields
    pool_id: str
    created_pool: PoolState
    lp_minted: int


@dataclass(frozen=True)
class _ReplayPool:
    pool_id: str
    pool: PoolState


@dataclass(frozen=True)
class _SwapMetadata:
    asset_in: AssetId
    asset_out: AssetId


@dataclass(frozen=True)
class _SwapReserves:
    reserve_in: int
    reserve_out: int
    dir_is_0_to_1: bool


@dataclass(frozen=True)
class _ExactInSwapInputs:
    amount_in: int
    min_out: int


def _validate_strong_config(
    *,
    mode: str,
    protocol_fee_share_bps: object,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> Optional[str]:
    if mode not in _VALIDATION_MODES:
        return f"unsupported validation mode: {mode!r}"
    protocol_fee_share = _protocol_fee_share_value(protocol_fee_share_bps)
    if protocol_fee_share is None:
        return "protocol_fee_share_bps must be an int in [0, 10000]"
    if protocol_fee_share > 0 and not protocol_fee_recipient_pubkey:
        return "protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0"
    return None


def _protocol_fee_share_value(protocol_fee_share_bps: object) -> Optional[int]:
    if not is_strict_int(protocol_fee_share_bps):
        return None
    if not (0 <= protocol_fee_share_bps <= 10000):
        return None
    return protocol_fee_share_bps


def _build_replay_index(
    *,
    settlement: Settlement,
    intents: List[Intent],
    allow_cow_netting: bool,
) -> Tuple[bool, Optional[str], Dict[str, Intent], Dict[str, Fill]]:
    ok_base, err_base, intents_by_id, fill_by_id = _build_base_replay_index(
        settlement=settlement,
        intents=intents,
    )
    if not ok_base:
        return False, err_base, {}, {}

    ok_cow, err_cow = _validate_cow_pair_index(
        settlement=settlement,
        intents_by_id=intents_by_id,
        fill_by_id=fill_by_id,
        allow_cow_netting=allow_cow_netting,
    )
    if not ok_cow:
        return False, err_cow, {}, {}

    return True, None, intents_by_id, fill_by_id


def _build_base_replay_index(
    *,
    settlement: Settlement,
    intents: List[Intent],
) -> Tuple[bool, Optional[str], Dict[str, Intent], Dict[str, Fill]]:
    ok_intents, err_intents, intent_ids, intents_by_id = _index_intents_by_id(intents)
    if not ok_intents:
        return False, err_intents, {}, {}

    included_error = _validate_included_intent_ids(settlement=settlement, intent_ids=intent_ids)
    if included_error is not None:
        return False, included_error, {}, {}

    ok_fills, err_fills, fill_by_id = _index_fills_by_id(settlement=settlement, intent_ids=intent_ids)
    if not ok_fills:
        return False, err_fills, {}, {}

    fill_action_error = _validate_fill_actions(settlement=settlement, fill_by_id=fill_by_id)
    if fill_action_error is not None:
        return False, fill_action_error, {}, {}

    return True, None, intents_by_id, fill_by_id


def _index_intents_by_id(
    intents: List[Intent],
) -> Tuple[bool, Optional[str], List[str], Dict[str, Intent]]:
    # Intents must have unique ids (otherwise settlement semantics are ambiguous).
    intent_ids = [it.intent_id for it in intents]
    if len(intent_ids) != len(set(intent_ids)):
        return False, "duplicate intent_id in input intents", [], {}
    return True, None, intent_ids, {it.intent_id: it for it in intents}


def _validate_included_intent_ids(*, settlement: Settlement, intent_ids: List[str]) -> Optional[str]:
    included_ids = [intent_id for intent_id, _action in settlement.included_intents]
    if set(included_ids) != set(intent_ids):
        missing = sorted(set(intent_ids) - set(included_ids))
        extra = sorted(set(included_ids) - set(intent_ids))
        return f"settlement included_intents mismatch: missing={missing} extra={extra}"
    if len(included_ids) != len(set(included_ids)):
        return "settlement included_intents contains duplicate intent_id entries"
    return None


def _index_fills_by_id(
    *,
    settlement: Settlement,
    intent_ids: List[str],
) -> Tuple[bool, Optional[str], Dict[str, Fill]]:
    # Reject actions are allowed to omit fill details.
    fill_ids = [f.intent_id for f in settlement.fills]
    if len(fill_ids) != len(set(fill_ids)):
        return False, "settlement fills contains duplicate intent_id entries", {}
    extra_fill_ids = sorted(set(fill_ids) - set(intent_ids))
    if extra_fill_ids:
        return False, f"settlement fills contains intent_ids not in input intents: {extra_fill_ids}", {}
    return True, None, {f.intent_id: f for f in settlement.fills}


def _validate_fill_actions(*, settlement: Settlement, fill_by_id: Dict[str, Fill]) -> Optional[str]:
    for intent_id, action in settlement.included_intents:
        f = fill_by_id.get(intent_id)
        if f is None:
            if action == FillAction.FILL:
                return f"missing Fill for filled intent_id: {intent_id}"
            continue
        if f.action != action:
            return f"Fill.action mismatch for intent_id={intent_id}: {f.action} != {action}"
    return None


def _quote_binding_fields(intent: Intent) -> _QuoteBindingFields:
    return _QuoteBindingFields(
        receipt_hash=intent.get_field("quote_receipt_hash"),
        pool_fingerprint=intent.get_field("quote_pool_fingerprint"),
        leg_index=intent.get_field("quote_receipt_leg_index"),
    )


def _quote_binding_metadata_error(
    *,
    intent: Intent,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    fields = _quote_binding_fields(intent)
    for check in (
        _quote_binding_kind_error,
        _invalid_quote_leg_index_error,
        _quote_leg_transport_error,
        _quote_hash_metadata_error,
        _quote_pool_fingerprint_metadata_error,
    ):
        error = check(intent, fields, allow_snapshot_bound_quote_bindings)
        if error is not None:
            return error
    return None


def _has_quote_binding(fields: _QuoteBindingFields) -> bool:
    return fields.receipt_hash is not None or fields.pool_fingerprint is not None or fields.leg_index is not None


def _quote_binding_kind_error(
    intent: Intent,
    fields: _QuoteBindingFields,
    _allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    if _has_quote_binding(fields) and intent.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return _quote_binding_error(
            "quote receipt binding only supported for swap intents",
            **_quote_binding_context(intent),
            intent_kind=intent.kind.value,
        )
    return None


def _invalid_quote_leg_index_error(
    intent: Intent,
    fields: _QuoteBindingFields,
    _allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    leg_index = fields.leg_index
    if leg_index is not None and (not is_strict_int(leg_index) or leg_index < 0):
        return _quote_binding_error("invalid quote_receipt_leg_index", **_quote_binding_context(intent))
    return None


def _quote_leg_transport_error(
    intent: Intent,
    fields: _QuoteBindingFields,
    _allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    if fields.leg_index is not None:
        return _quote_transport_metadata_error(intent)
    return None


def _quote_hash_metadata_error(
    intent: Intent,
    fields: _QuoteBindingFields,
    _allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    if fields.receipt_hash is None:
        return None
    if not isinstance(fields.receipt_hash, str) or not fields.receipt_hash:
        return _quote_binding_error("invalid quote_receipt_hash", **_quote_binding_context(intent))
    return _quote_transport_metadata_error(intent)


def _quote_pool_fingerprint_metadata_error(
    intent: Intent,
    fields: _QuoteBindingFields,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    if fields.pool_fingerprint is None:
        return None
    if not isinstance(fields.pool_fingerprint, str) or not fields.pool_fingerprint:
        return _quote_binding_error("missing quote_pool_fingerprint", **_quote_binding_context(intent))
    if not allow_snapshot_bound_quote_bindings:
        return _quote_binding_error(
            "quote receipt snapshot binding requires validated engine witness",
            **_quote_binding_context(intent),
            guidance="only pass sanitized quote_pool_fingerprint through the validated engine path",
        )
    return None


def _quote_transport_metadata_error(intent: Intent) -> str:
    return _quote_binding_error(
        "quote receipt transport metadata requires validated engine witness",
        **_quote_binding_context(intent),
        guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
    )


def _create_pool_fields(intent: Intent) -> _CreatePoolFields:
    return _CreatePoolFields(
        asset0=intent.get_field("asset0"),
        asset1=intent.get_field("asset1"),
        fee_bps=intent.get_field("fee_bps"),
        amount0=intent.get_field("amount0"),
        amount1=intent.get_field("amount1"),
        created_at=intent.get_field("created_at", 0),
        curve_tag=intent.get_field("curve_tag", None),
        curve_params=intent.get_field("curve_params", None),
    )


def _create_pool_field_error(intent_id: str, fields: _CreatePoolFields) -> Optional[str]:
    for check in (
        _missing_create_pool_fields_error,
        _invalid_create_pool_asset_ids_error,
        _invalid_create_pool_fee_bps_error,
        _invalid_create_pool_amount0_error,
        _invalid_create_pool_amount1_error,
        _invalid_create_pool_created_at_error,
    ):
        error = check(intent_id, fields)
        if error is not None:
            return error
    return None


def _missing_create_pool_fields_error(intent_id: str, fields: _CreatePoolFields) -> Optional[str]:
    if any(v is None for v in (fields.asset0, fields.asset1, fields.fee_bps, fields.amount0, fields.amount1)):
        return f"missing CREATE_POOL fields for intent_id={intent_id}"
    return None


def _invalid_create_pool_asset_ids_error(intent_id: str, fields: _CreatePoolFields) -> Optional[str]:
    if not isinstance(fields.asset0, str) or not isinstance(fields.asset1, str):
        return f"invalid CREATE_POOL asset ids for intent_id={intent_id}"
    return None


def _invalid_create_pool_fee_bps_error(intent_id: str, fields: _CreatePoolFields) -> Optional[str]:
    fee_bps = fields.fee_bps
    if not is_strict_int(fee_bps):
        return f"invalid CREATE_POOL fee_bps for intent_id={intent_id}"
    if not (0 <= fee_bps <= 10000):
        return f"invalid CREATE_POOL fee_bps for intent_id={intent_id}"
    return None


def _invalid_create_pool_amount0_error(intent_id: str, fields: _CreatePoolFields) -> Optional[str]:
    amount0 = fields.amount0
    if not is_strict_int(amount0):
        return f"invalid CREATE_POOL amount0 for intent_id={intent_id}"
    if amount0 <= 0:
        return f"invalid CREATE_POOL amount0 for intent_id={intent_id}"
    return None


def _invalid_create_pool_amount1_error(intent_id: str, fields: _CreatePoolFields) -> Optional[str]:
    amount1 = fields.amount1
    if not is_strict_int(amount1):
        return f"invalid CREATE_POOL amount1 for intent_id={intent_id}"
    if amount1 <= 0:
        return f"invalid CREATE_POOL amount1 for intent_id={intent_id}"
    return None


def _invalid_create_pool_created_at_error(intent_id: str, fields: _CreatePoolFields) -> Optional[str]:
    created_at = fields.created_at
    if created_at is None:
        return None
    if not is_strict_int(created_at):
        return f"invalid CREATE_POOL created_at for intent_id={intent_id}"
    if created_at < 0:
        return f"invalid CREATE_POOL created_at for intent_id={intent_id}"
    return None


def _create_pool_created_at_value(fields: _CreatePoolFields) -> int:
    created_at = fields.created_at
    if created_at is None:
        return 0
    if not is_strict_int(created_at):
        raise TypeError("CREATE_POOL created_at was not validated")
    return created_at


def _validated_create_pool_fields(fields: _CreatePoolFields) -> _ValidatedCreatePoolFields:
    return _ValidatedCreatePoolFields(
        asset0=cast(AssetId, fields.asset0),
        asset1=cast(AssetId, fields.asset1),
        fee_bps=cast(int, fields.fee_bps),
        amount0=cast(int, fields.amount0),
        amount1=cast(int, fields.amount1),
        created_at=_create_pool_created_at_value(fields),
        curve_tag=cast(Optional[str], fields.curve_tag),
        curve_params=fields.curve_params,
    )


def _create_pool_replay(
    *,
    intent_id: str,
    sender: PubKey,
    fields: _ValidatedCreatePoolFields,
    pools: Dict[str, PoolState],
) -> Tuple[Optional[_CreatePoolReplay], Optional[str]]:
    try:
        pool_id, created_pool, lp_minted = create_pool(
            asset0=fields.asset0,
            asset1=fields.asset1,
            amount0=fields.amount0,
            amount1=fields.amount1,
            fee_bps=fields.fee_bps,
            creator_pubkey=sender,
            created_at=fields.created_at,
            curve_tag=fields.curve_tag,
            curve_params=fields.curve_params,
        )
    except Exception as exc:
        return None, f"CREATE_POOL computation error for intent_id={intent_id}: {exc}"

    if pool_id in pools:
        return None, f"CREATE_POOL duplicates existing pool_id={pool_id}"
    return _CreatePoolReplay(fields=fields, pool_id=pool_id, created_pool=created_pool, lp_minted=lp_minted), None


def _create_pool_fill_match_error(intent_id: str, fill: Fill, replay: _CreatePoolReplay) -> Optional[str]:
    fields = replay.fields
    checks = (
        ("amount0_used", _fill_value_or_zero(fill.amount0_used), fields.amount0),
        ("amount1_used", _fill_value_or_zero(fill.amount1_used), fields.amount1),
        ("lp_minted", _fill_value_or_zero(fill.lp_minted), replay.lp_minted),
    )
    for field_name, actual, expected in checks:
        if actual != expected:
            return f"CREATE_POOL fill.{field_name} mismatch for intent_id={intent_id}"
    return None


def _fill_value_or_zero(value: object) -> int:
    if value:
        # Preserve legacy fill coercion; the public wrapper fails closed on bad truthy scalars.
        return int(cast(Any, value))
    return 0


def _apply_create_pool_replay(
    *,
    intent_id: str,
    sender: PubKey,
    replay: _CreatePoolReplay,
    balances: BalanceTable,
    lp: LPTable,
    pools: Dict[str, PoolState],
) -> Optional[str]:
    fields = replay.fields
    try:
        balances.subtract(sender, fields.asset0, fields.amount0)
        balances.subtract(sender, fields.asset1, fields.amount1)
        lp.add(sender, replay.pool_id, replay.lp_minted)
        lp.add(LP_LOCK_PUBKEY, replay.pool_id, int(MIN_LP_LOCK))
    except Exception as exc:
        return f"CREATE_POOL balance/LP apply error for intent_id={intent_id}: {exc}"

    pools[replay.pool_id] = replay.created_pool
    return None


def _append_create_pool_expected_event(expected_events: List[dict], replay: _CreatePoolReplay) -> None:
    fields = replay.fields
    expected_events.append(
        {
            "type": "CREATE_POOL",
            "pool_id": replay.pool_id,
            "asset0": fields.asset0,
            "asset1": fields.asset1,
            "fee_bps": fields.fee_bps,
            "curve_tag": replay.created_pool.curve_tag,
            "curve_params": replay.created_pool.curve_params,
            "status": PoolStatus.ACTIVE.value,
            "created_at": int(replay.created_pool.created_at),
        }
    )


def _append_create_pool_deltas(
    *,
    sender: PubKey,
    replay: _CreatePoolReplay,
    bal_deltas: List[BalanceDelta],
    res_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
) -> None:
    fields = replay.fields
    bal_deltas.append(BalanceDelta(pubkey=sender, asset=fields.asset0, delta_add=0, delta_sub=fields.amount0))
    bal_deltas.append(BalanceDelta(pubkey=sender, asset=fields.asset1, delta_add=0, delta_sub=fields.amount1))
    res_deltas.append(ReserveDelta(pool_id=replay.pool_id, asset=fields.asset0, delta_add=fields.amount0, delta_sub=0))
    res_deltas.append(ReserveDelta(pool_id=replay.pool_id, asset=fields.asset1, delta_add=fields.amount1, delta_sub=0))
    lp_deltas.append(LPDelta(pubkey=sender, pool_id=replay.pool_id, delta_add=replay.lp_minted, delta_sub=0))
    lp_deltas.append(LPDelta(pubkey=LP_LOCK_PUBKEY, pool_id=replay.pool_id, delta_add=int(MIN_LP_LOCK), delta_sub=0))


def _lookup_replay_pool(
    *,
    intent_id: str,
    intent: Intent,
    pools: Dict[str, PoolState],
) -> Tuple[Optional[_ReplayPool], Optional[str]]:
    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        return None, f"missing pool_id for intent_id={intent_id}"
    if pool_id not in pools:
        return None, f"pool not found for intent_id={intent_id}: {pool_id}"
    return _ReplayPool(pool_id=pool_id, pool=pools[pool_id]), None


def _swap_metadata(
    *,
    intent_id: str,
    intent: Intent,
    pool: PoolState,
    quote_pool_fp: object,
) -> Tuple[Optional[_SwapMetadata], Optional[str]]:
    metadata, error = _swap_asset_metadata(intent_id=intent_id, intent=intent)
    if error is not None:
        return None, error
    return _swap_metadata_after_asset(
        intent_id=intent_id,
        intent=intent,
        pool=pool,
        metadata=metadata,
        quote_pool_fp=quote_pool_fp,
    )


def _swap_metadata_after_asset(
    *,
    intent_id: str,
    intent: Intent,
    pool: PoolState,
    metadata: Optional[_SwapMetadata],
    quote_pool_fp: object,
) -> Tuple[Optional[_SwapMetadata], Optional[str]]:
    if metadata is None:
        return None, f"swap metadata missing result for intent_id={intent_id}"
    error = _swap_pool_status_error(intent_id=intent_id, pool=pool)
    if error is not None:
        return None, error
    error = _swap_asset_pair_error(intent_id=intent_id, pool=pool, metadata=metadata)
    if error is not None:
        return None, error
    snapshot_error = _quote_pool_snapshot_error(intent=intent, pool=pool, quote_pool_fp=quote_pool_fp)
    if snapshot_error is not None:
        return None, snapshot_error
    return metadata, None


def _swap_asset_metadata(*, intent_id: str, intent: Intent) -> Tuple[Optional[_SwapMetadata], Optional[str]]:
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return None, f"invalid asset_in/out for intent_id={intent_id}"
    return _SwapMetadata(asset_in=asset_in, asset_out=asset_out), None


def _swap_pool_status_error(*, intent_id: str, pool: PoolState) -> Optional[str]:
    if pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent_id}: {pool.status}"
    return None


def _swap_asset_pair_error(*, intent_id: str, pool: PoolState, metadata: _SwapMetadata) -> Optional[str]:
    if {metadata.asset_in, metadata.asset_out} != {pool.asset0, pool.asset1} or metadata.asset_in == metadata.asset_out:
        return f"swap asset mismatch for intent_id={intent_id}"
    return None


def _quote_pool_snapshot_error(*, intent: Intent, pool: PoolState, quote_pool_fp: object) -> Optional[str]:
    if quote_pool_fp is None:
        return None
    actual_pool_fp = pool_state_fingerprint(pool)
    if actual_pool_fp == quote_pool_fp:
        return None
    return _quote_binding_error(
        "quote receipt pool snapshot mismatch",
        **_quote_binding_context(intent),
        actual_pool_fingerprint=actual_pool_fp,
    )


def _swap_reserves(
    *,
    intent_id: str,
    pool: PoolState,
    metadata: _SwapMetadata,
) -> Tuple[Optional[_SwapReserves], Optional[str]]:
    if metadata.asset_in == pool.asset0 and metadata.asset_out == pool.asset1:
        return _SwapReserves(reserve_in=int(pool.reserve0), reserve_out=int(pool.reserve1), dir_is_0_to_1=True), None
    if metadata.asset_in == pool.asset1 and metadata.asset_out == pool.asset0:
        return _SwapReserves(reserve_in=int(pool.reserve1), reserve_out=int(pool.reserve0), dir_is_0_to_1=False), None
    return None, f"swap asset mismatch for intent_id={intent_id}"


def _swap_reserves_for_replay(
    *,
    intent_id: str,
    pool: PoolState,
    metadata: _SwapMetadata,
    fill: Fill,
    mode: str,
) -> Tuple[Optional[_SwapReserves], Optional[str]]:
    reserves, reserve_error = _swap_reserves(intent_id=intent_id, pool=pool, metadata=metadata)
    if reserve_error is not None:
        return None, reserve_error
    if reserves is None:
        return None, f"swap reserves missing result for intent_id={intent_id}"
    witness_error = _swap_reserve_witness_error(intent_id=intent_id, fill=fill, mode=mode, reserves=reserves)
    if witness_error is not None:
        return None, witness_error
    return reserves, None


def _swap_reserve_witness_error(
    *,
    intent_id: str,
    fill: Fill,
    mode: str,
    reserves: _SwapReserves,
) -> Optional[str]:
    if mode != _MODE_STRONG_PROOF_CARRYING:
        return None
    if _swap_witness_reserves_missing(fill):
        return f"missing swap witness reserves for intent_id={intent_id}"
    if not _swap_witness_reserves_match(fill, reserves):
        return f"swap witness reserve mismatch for intent_id={intent_id}"
    return None


def _swap_witness_reserves_missing(fill: Fill) -> bool:
    return fill.reserve_in_before is None or fill.reserve_out_before is None


def _swap_witness_reserves_match(fill: Fill, reserves: _SwapReserves) -> bool:
    reserve_in_before = fill.reserve_in_before
    reserve_out_before = fill.reserve_out_before
    if reserve_in_before is None or reserve_out_before is None:
        return False
    return int(reserve_in_before) == int(reserves.reserve_in) and int(reserve_out_before) == int(reserves.reserve_out)


def _exact_in_swap_inputs(
    *,
    intent_id: str,
    intent: Intent,
) -> Tuple[Optional[_ExactInSwapInputs], Optional[str]]:
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not is_strict_int(amount_in):
        return None, f"invalid amount_in for intent_id={intent_id}"
    if int(amount_in) <= 0:
        return None, f"invalid amount_in for intent_id={intent_id}"
    if not is_strict_int(min_out):
        return None, f"invalid min_amount_out for intent_id={intent_id}"
    if int(min_out) < 0:
        return None, f"invalid min_amount_out for intent_id={intent_id}"
    return _ExactInSwapInputs(amount_in=int(amount_in), min_out=int(min_out)), None


def _exact_in_preflight_error(*, intent_id: str, fill: Fill, inputs: _ExactInSwapInputs) -> Optional[str]:
    if int(fill.amount_in_filled or 0) != int(inputs.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={intent_id}"
    return None


def _protocol_fee_curve_error(
    *,
    intent_id: str,
    pool: PoolState,
    protocol_fee_share_bps: int,
) -> Optional[str]:
    if int(protocol_fee_share_bps) and pool.curve_tag != CURVE_TAG_CPMM:
        return f"protocol fee unsupported for curve intent_id={intent_id}"
    return None


def _validate_cow_pair_index(
    *,
    settlement: Settlement,
    intents_by_id: Dict[str, Intent],
    fill_by_id: Dict[str, Fill],
    allow_cow_netting: bool,
) -> Tuple[bool, Optional[str]]:
    cow_ids = [fill.intent_id for fill in settlement.fills if fill.reason == "COW_NETTED"]
    if not cow_ids:
        return True, None
    if not allow_cow_netting:
        return False, f"COW_NETTED not allowed for intent_id={cow_ids[0]}"

    entries: Dict[str, _CowPairEntry] = {}
    for intent_id in cow_ids:
        it = intents_by_id[intent_id]
        f = fill_by_id[intent_id]
        if f.action != FillAction.FILL:
            return False, f"COW_NETTED requires filled action: intent_id={intent_id}"
        if it.kind != IntentKind.SWAP_EXACT_IN:
            return False, f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}"

        pool_id = it.get_field("pool_id")
        if not isinstance(pool_id, str) or not pool_id:
            return False, f"missing pool_id for intent_id={intent_id}"
        asset_in = it.get_field("asset_in")
        asset_out = it.get_field("asset_out")
        if not isinstance(asset_in, str) or not isinstance(asset_out, str):
            return False, f"invalid asset_in/out for intent_id={intent_id}"
        amount_in = it.get_field("amount_in")
        min_out = it.get_field("min_amount_out", 0)
        if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
            return False, f"invalid amount_in for intent_id={intent_id}"
        if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
            return False, f"invalid min_amount_out for intent_id={intent_id}"
        if int(f.fee_paid or 0) != 0:
            return False, f"COW_NETTED fee_paid must be 0: intent_id={intent_id}"
        if not is_strict_int(f.amount_in_filled) or int(f.amount_in_filled or 0) != int(amount_in):
            return False, f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}"
        if not is_strict_int(f.amount_out_filled):
            return False, f"COW_NETTED amount_out_filled invalid: intent_id={intent_id}"
        out_amt = int(f.amount_out_filled or 0)
        if out_amt < int(min_out):
            return False, f"COW_NETTED slippage: intent_id={intent_id}"
        entries[intent_id] = _CowPairEntry(
            intent_id=intent_id,
            pool_id=pool_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_filled=int(f.amount_in_filled or 0),
            amount_out_filled=out_amt,
        )

    pair_for: Dict[str, str] = {}
    for intent_id, entry in entries.items():
        matches = [
            other_id
            for other_id, other in entries.items()
            if other_id != intent_id
            and other.pool_id == entry.pool_id
            and other.asset_in == entry.asset_out
            and other.asset_out == entry.asset_in
            and other.amount_in_filled == entry.amount_out_filled
            and other.amount_out_filled == entry.amount_in_filled
        ]
        if len(matches) != 1:
            return (
                False,
                f"COW_NETTED fill requires exactly one reciprocal counterparty: intent_id={intent_id} matches={matches}",
            )
        pair_for[intent_id] = matches[0]

    for intent_id, counterparty_id in pair_for.items():
        if pair_for.get(counterparty_id) != intent_id:
            return False, f"COW_NETTED reciprocal pair is not symmetric: intent_id={intent_id}"
    return True, None


def validate_settlement_strong(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Fail-closed wrapper around the strong validator implementation.

    This validator is used on untrusted settlement proposals; it must return `(False, reason)`
    rather than crash on malformed inputs.
    """
    try:
        return _validate_settlement_strong_impl(
            settlement=settlement,
            intents=intents,
            pre_balances=pre_balances,
            pre_pools=pre_pools,
            pre_lp_balances=pre_lp_balances,
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )
    except Exception as exc:
        detail = str(exc).strip()
        if "\n" in detail or "\r" in detail:
            detail = " ".join(detail.split())
        if len(detail) > 200:
            detail = detail[:200]
        if detail:
            return False, f"strong validator crashed: {type(exc).__name__}: {detail}"
        return False, f"strong validator crashed: {type(exc).__name__}"


def _validate_settlement_strong_impl(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Strong settlement validation.

    This is intended to be used in `dex.step` as a fail-closed acceptance gate.
    """
    config_error = _validate_strong_config(
        mode=mode,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    if config_error is not None:
        return False, config_error

    ok_index, err_index, intents_by_id, fill_by_id = _build_replay_index(
        settlement=settlement,
        intents=intents,
        allow_cow_netting=allow_cow_netting,
    )
    if not ok_index:
        return False, err_index

    # Replay state (pure local copies).
    balances = _copy_balance_table(pre_balances)
    pools: Dict[str, PoolState] = {pool_id: replace(pool) for pool_id, pool in pre_pools.items()}
    lp = _copy_lp_table(pre_lp_balances) if pre_lp_balances is not None else LPTable()

    expected_events: List[dict] = []
    bal_deltas: List[BalanceDelta] = []
    res_deltas: List[ReserveDelta] = []
    lp_deltas: List[LPDelta] = []

    def fail(msg: str) -> Tuple[bool, Optional[str]]:
        return False, msg

    for intent_id, action in settlement.included_intents:
        it = intents_by_id[intent_id]
        quote_binding_error = _quote_binding_metadata_error(
            intent=it,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        )
        if quote_binding_error is not None:
            return fail(quote_binding_error)
        quote_pool_fp = it.get_field("quote_pool_fingerprint")

        if action == FillAction.REJECT:
            continue

        f = fill_by_id[intent_id]

        sender: PubKey = it.sender_pubkey
        recipient: PubKey = it.get_field("recipient", sender)
        if not isinstance(recipient, str) or not recipient:
            return fail(f"invalid recipient for intent_id={intent_id}")

        if it.kind == IntentKind.CREATE_POOL:
            create_pool_fields = _create_pool_fields(it)
            create_pool_error = _create_pool_field_error(intent_id, create_pool_fields)
            if create_pool_error is not None:
                return fail(create_pool_error)
            replay, replay_error = _create_pool_replay(
                intent_id=intent_id,
                sender=sender,
                fields=_validated_create_pool_fields(create_pool_fields),
                pools=pools,
            )
            if replay_error is not None:
                return fail(replay_error)
            if replay is None:
                return fail(f"CREATE_POOL replay missing result for intent_id={intent_id}")

            fill_error = _create_pool_fill_match_error(intent_id, f, replay)
            if fill_error is not None:
                return fail(fill_error)

            apply_error = _apply_create_pool_replay(
                intent_id=intent_id,
                sender=sender,
                replay=replay,
                balances=balances,
                lp=lp,
                pools=pools,
            )
            if apply_error is not None:
                return fail(apply_error)

            _append_create_pool_expected_event(expected_events, replay)
            _append_create_pool_deltas(
                sender=sender,
                replay=replay,
                bal_deltas=bal_deltas,
                res_deltas=res_deltas,
                lp_deltas=lp_deltas,
            )
            continue

        replay_pool, pool_error = _lookup_replay_pool(intent_id=intent_id, intent=it, pools=pools)
        if pool_error is not None:
            return fail(pool_error)
        if replay_pool is None:
            return fail(f"pool lookup missing result for intent_id={intent_id}")
        pool_id = replay_pool.pool_id
        pool = replay_pool.pool

        if it.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            swap_metadata, swap_metadata_error = _swap_metadata(
                intent_id=intent_id,
                intent=it,
                pool=pool,
                quote_pool_fp=quote_pool_fp,
            )
            if swap_metadata_error is not None:
                return fail(swap_metadata_error)
            if swap_metadata is None:
                return fail(f"swap metadata missing result for intent_id={intent_id}")
            asset_in = swap_metadata.asset_in
            asset_out = swap_metadata.asset_out

            # CoW netting semantics (optional): direct user-to-user swap, no pool reserve changes.
            if f.reason == "COW_NETTED":
                if not allow_cow_netting:
                    return fail(f"COW_NETTED not allowed for intent_id={intent_id}")
                if it.kind != IntentKind.SWAP_EXACT_IN:
                    return fail(f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}")
                amount_in = it.get_field("amount_in")
                min_out = it.get_field("min_amount_out", 0)
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    return fail(f"invalid amount_in for intent_id={intent_id}")
                if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
                    return fail(f"invalid min_amount_out for intent_id={intent_id}")
                if int(f.fee_paid or 0) != 0:
                    return fail(f"COW_NETTED fee_paid must be 0: intent_id={intent_id}")
                if int(f.amount_in_filled or 0) != int(amount_in):
                    return fail(f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}")
                out_amt = int(f.amount_out_filled or 0)
                if out_amt < int(min_out):
                    return fail(f"COW_NETTED slippage: intent_id={intent_id}")
                try:
                    balances.subtract(sender, asset_in, int(amount_in))
                    balances.add(recipient, asset_out, out_amt)
                except Exception as exc:
                    return fail(f"COW_NETTED apply error for intent_id={intent_id}: {exc}")

                bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in)))
                bal_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=out_amt, delta_sub=0))
                continue

            swap_reserves, swap_reserve_error = _swap_reserves_for_replay(
                intent_id=intent_id,
                pool=pool,
                metadata=swap_metadata,
                fill=f,
                mode=mode,
            )
            if swap_reserve_error is not None:
                return fail(swap_reserve_error)
            if swap_reserves is None:
                return fail(f"swap reserves missing result for intent_id={intent_id}")
            reserve_in = swap_reserves.reserve_in
            reserve_out = swap_reserves.reserve_out
            dir_is_0_to_1 = swap_reserves.dir_is_0_to_1

            if it.kind == IntentKind.SWAP_EXACT_IN:
                exact_in_inputs, exact_in_input_error = _exact_in_swap_inputs(intent_id=intent_id, intent=it)
                if exact_in_input_error is not None:
                    return fail(exact_in_input_error)
                if exact_in_inputs is None:
                    return fail(f"exact-in swap inputs missing result for intent_id={intent_id}")
                exact_in_error = _exact_in_preflight_error(intent_id=intent_id, fill=f, inputs=exact_in_inputs)
                if exact_in_error is not None:
                    return fail(exact_in_error)
                amount_in = exact_in_inputs.amount_in
                min_out = exact_in_inputs.min_out
                protocol_fee_curve_error = _protocol_fee_curve_error(
                    intent_id=intent_id,
                    pool=pool,
                    protocol_fee_share_bps=protocol_fee_share_bps,
                )
                if protocol_fee_curve_error is not None:
                    return fail(protocol_fee_curve_error)

                try:
                    if int(protocol_fee_share_bps):
                        quote = swap_exact_in_with_protocol_fee(
                            reserve_in=int(reserve_in),
                            reserve_out=int(reserve_out),
                            amount_in=int(amount_in),
                            fee_bps=int(pool.fee_bps),
                            protocol_fee_share_bps=int(protocol_fee_share_bps),
                        )
                        amount_out = int(quote.amount_out)
                        new_in = int(quote.new_reserve_in)
                        new_out = int(quote.new_reserve_out)
                        protocol_fee = int(quote.protocol_fee)
                    else:
                        amount_out, (new_in, new_out) = swap_exact_in_for_pool(
                            pool,
                            reserve_in=int(reserve_in),
                            reserve_out=int(reserve_out),
                            amount_in=int(amount_in),
                        )
                        protocol_fee = 0
                except Exception as exc:
                    return fail(f"swap_exact_in kernel error for intent_id={intent_id}: {exc}")

                if int(f.amount_out_filled or 0) != int(amount_out):
                    return fail(f"swap amount_out_filled mismatch for intent_id={intent_id}")
                if int(amount_out) < int(min_out):
                    return fail(f"swap slippage for intent_id={intent_id}")

                fee = compute_fee_total(int(amount_in), int(pool.fee_bps))
                if int(f.fee_paid or 0) != int(fee):
                    return fail(f"swap fee_paid mismatch for intent_id={intent_id}")
                if int(f.protocol_fee_paid or 0) != int(protocol_fee):
                    return fail(f"swap protocol_fee_paid mismatch for intent_id={intent_id}")

                try:
                    balances.subtract(sender, asset_in, int(amount_in))
                    balances.add(recipient, asset_out, int(amount_out))
                    if protocol_fee:
                        assert protocol_fee_recipient_pubkey is not None
                        balances.add(protocol_fee_recipient_pubkey, asset_in, int(protocol_fee))
                except Exception as exc:
                    return fail(f"swap apply error for intent_id={intent_id}: {exc}")

                # Apply reserve updates.
                if dir_is_0_to_1:
                    pool.reserve0 = int(new_in)
                    pool.reserve1 = int(new_out)
                else:
                    pool.reserve1 = int(new_in)
                    pool.reserve0 = int(new_out)

                bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in)))
                bal_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=int(amount_out), delta_sub=0))
                if protocol_fee:
                    assert protocol_fee_recipient_pubkey is not None
                    bal_deltas.append(
                        BalanceDelta(
                            pubkey=protocol_fee_recipient_pubkey,
                            asset=asset_in,
                            delta_add=int(protocol_fee),
                            delta_sub=0,
                        )
                    )
                res_deltas.append(
                    ReserveDelta(
                        pool_id=pool_id,
                        asset=asset_in,
                        delta_add=int(amount_in) - int(protocol_fee),
                        delta_sub=0,
                    )
                )
                res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=int(amount_out)))
                continue

            # SWAP_EXACT_OUT
            amount_out_req = it.get_field("amount_out")
            max_in = it.get_field("max_amount_in")
            if not isinstance(amount_out_req, int) or isinstance(amount_out_req, bool) or amount_out_req <= 0:
                return fail(f"invalid amount_out for intent_id={intent_id}")
            if not isinstance(max_in, int) or isinstance(max_in, bool) or max_in < 0:
                return fail(f"invalid max_amount_in for intent_id={intent_id}")

            if int(f.amount_out_filled or 0) != int(amount_out_req):
                return fail(f"swap amount_out_filled mismatch for intent_id={intent_id}")

            try:
                if int(protocol_fee_share_bps):
                    if pool.curve_tag != CURVE_TAG_CPMM:
                        return fail(f"protocol fee unsupported for curve intent_id={intent_id}")
                    quote = quote_cpmm_swap_exact_out(
                        reserve_in=int(reserve_in),
                        reserve_out=int(reserve_out),
                        amount_out=int(amount_out_req),
                        fee_bps=int(pool.fee_bps),
                        protocol_fee_share_bps=int(protocol_fee_share_bps),
                    )
                    amount_in_req = int(quote.amount_in)
                    new_in = int(quote.reserve_in_after)
                    new_out = int(quote.reserve_out_after)
                    protocol_fee = int(quote.protocol_fee_paid)
                else:
                    amount_in_req, (new_in, new_out) = swap_exact_out_for_pool(
                        pool,
                        reserve_in=int(reserve_in),
                        reserve_out=int(reserve_out),
                        amount_out=int(amount_out_req),
                    )
                    protocol_fee = 0
            except Exception as exc:
                return fail(f"swap_exact_out kernel error for intent_id={intent_id}: {exc}")

            if int(f.amount_in_filled or 0) != int(amount_in_req):
                return fail(f"swap amount_in_filled mismatch for intent_id={intent_id}")
            if int(amount_in_req) > int(max_in):
                return fail(f"swap slippage for intent_id={intent_id}")

            fee = compute_fee_total(int(amount_in_req), int(pool.fee_bps))
            if int(f.fee_paid or 0) != int(fee):
                return fail(f"swap fee_paid mismatch for intent_id={intent_id}")
            if int(f.protocol_fee_paid or 0) != int(protocol_fee):
                return fail(f"swap protocol_fee_paid mismatch for intent_id={intent_id}")

            try:
                balances.subtract(sender, asset_in, int(amount_in_req))
                balances.add(recipient, asset_out, int(amount_out_req))
                if protocol_fee:
                    assert protocol_fee_recipient_pubkey is not None
                    balances.add(protocol_fee_recipient_pubkey, asset_in, int(protocol_fee))
            except Exception as exc:
                return fail(f"swap apply error for intent_id={intent_id}: {exc}")

            if dir_is_0_to_1:
                pool.reserve0 = int(new_in)
                pool.reserve1 = int(new_out)
            else:
                pool.reserve1 = int(new_in)
                pool.reserve0 = int(new_out)

            bal_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in_req)))
            bal_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=int(amount_out_req), delta_sub=0))
            if protocol_fee:
                assert protocol_fee_recipient_pubkey is not None
                bal_deltas.append(
                    BalanceDelta(
                        pubkey=protocol_fee_recipient_pubkey,
                        asset=asset_in,
                        delta_add=int(protocol_fee),
                        delta_sub=0,
                    )
                )
            res_deltas.append(
                ReserveDelta(
                    pool_id=pool_id,
                    asset=asset_in,
                    delta_add=int(amount_in_req) - int(protocol_fee),
                    delta_sub=0,
                )
            )
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=int(amount_out_req)))
            continue

        if it.kind == IntentKind.ADD_LIQUIDITY:
            if pool.status != PoolStatus.ACTIVE:
                return fail(f"pool not active for intent_id={intent_id}: {pool.status}")
            amount0_desired = it.get_field("amount0_desired")
            amount1_desired = it.get_field("amount1_desired")
            amount0_min = it.get_field("amount0_min", 0)
            amount1_min = it.get_field("amount1_min", 0)
            if any(v is None for v in (amount0_desired, amount1_desired)):
                return fail(f"missing ADD_LIQUIDITY fields for intent_id={intent_id}")
            if not is_strict_int(amount0_desired) or amount0_desired <= 0:
                return fail(f"invalid amount0_desired for intent_id={intent_id}")
            if not is_strict_int(amount1_desired) or amount1_desired <= 0:
                return fail(f"invalid amount1_desired for intent_id={intent_id}")
            if not is_strict_int(amount0_min) or amount0_min < 0:
                return fail(f"invalid amount0_min for intent_id={intent_id}")
            if not is_strict_int(amount1_min) or amount1_min < 0:
                return fail(f"invalid amount1_min for intent_id={intent_id}")

            try:
                amount0_used, amount1_used, lp_minted = add_liquidity(
                    pool_state=pool,
                    amount0_desired=amount0_desired,
                    amount1_desired=amount1_desired,
                    amount0_min=amount0_min,
                    amount1_min=amount1_min,
                )
            except Exception as exc:
                return fail(f"ADD_LIQUIDITY computation error for intent_id={intent_id}: {exc}")

            if int(f.amount0_used or 0) != int(amount0_used):
                return fail(f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={intent_id}")
            if int(f.amount1_used or 0) != int(amount1_used):
                return fail(f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={intent_id}")
            if int(f.lp_minted or 0) != int(lp_minted):
                return fail(f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={intent_id}")

            try:
                balances.subtract(sender, pool.asset0, int(amount0_used))
                balances.subtract(sender, pool.asset1, int(amount1_used))
                lp.add(recipient, pool_id, int(lp_minted))
            except Exception as exc:
                return fail(f"ADD_LIQUIDITY apply error for intent_id={intent_id}: {exc}")

            pool.reserve0 += int(amount0_used)
            pool.reserve1 += int(amount1_used)
            pool.lp_supply += int(lp_minted)

            bal_deltas.append(BalanceDelta(pubkey=sender, asset=pool.asset0, delta_add=0, delta_sub=int(amount0_used)))
            bal_deltas.append(BalanceDelta(pubkey=sender, asset=pool.asset1, delta_add=0, delta_sub=int(amount1_used)))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=int(amount0_used), delta_sub=0))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset1, delta_add=int(amount1_used), delta_sub=0))
            lp_deltas.append(LPDelta(pubkey=recipient, pool_id=pool_id, delta_add=int(lp_minted), delta_sub=0))
            continue

        if it.kind == IntentKind.REMOVE_LIQUIDITY:
            if pool.status != PoolStatus.ACTIVE:
                return fail(f"pool not active for intent_id={intent_id}: {pool.status}")
            lp_amount = it.get_field("lp_amount")
            amount0_min = it.get_field("amount0_min", 0)
            amount1_min = it.get_field("amount1_min", 0)
            if lp_amount is None:
                return fail(f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent_id}")
            if not is_strict_int(lp_amount) or lp_amount <= 0:
                return fail(f"invalid lp_amount for intent_id={intent_id}")
            if not is_strict_int(amount0_min) or amount0_min < 0:
                return fail(f"invalid amount0_min for intent_id={intent_id}")
            if not is_strict_int(amount1_min) or amount1_min < 0:
                return fail(f"invalid amount1_min for intent_id={intent_id}")

            try:
                amount0_out, amount1_out = remove_liquidity(
                    pool_state=pool,
                    lp_amount=lp_amount,
                    amount0_min=amount0_min,
                    amount1_min=amount1_min,
                )
            except Exception as exc:
                return fail(f"REMOVE_LIQUIDITY computation error for intent_id={intent_id}: {exc}")

            if int(f.lp_burned or 0) != int(lp_amount):
                return fail(f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={intent_id}")
            if int(f.amount0_out or 0) != int(amount0_out):
                return fail(f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={intent_id}")
            if int(f.amount1_out or 0) != int(amount1_out):
                return fail(f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={intent_id}")

            try:
                lp.subtract(sender, pool_id, int(lp_amount))
                balances.add(recipient, pool.asset0, int(amount0_out))
                balances.add(recipient, pool.asset1, int(amount1_out))
            except Exception as exc:
                return fail(f"REMOVE_LIQUIDITY apply error for intent_id={intent_id}: {exc}")

            pool.reserve0 -= int(amount0_out)
            pool.reserve1 -= int(amount1_out)
            pool.lp_supply -= int(lp_amount)

            lp_deltas.append(LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=int(lp_amount)))
            bal_deltas.append(BalanceDelta(pubkey=recipient, asset=pool.asset0, delta_add=int(amount0_out), delta_sub=0))
            bal_deltas.append(BalanceDelta(pubkey=recipient, asset=pool.asset1, delta_add=int(amount1_out), delta_sub=0))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=0, delta_sub=int(amount0_out)))
            res_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset1, delta_add=0, delta_sub=int(amount1_out)))
            continue

        return fail(f"unsupported intent kind for strong validation: {it.kind}")

    # Canonicalize and compare the settlement payloads.
    expected_balance = _aggregate_balance_deltas(bal_deltas)
    expected_reserve = _aggregate_reserve_deltas(res_deltas)
    expected_lp = _aggregate_lp_deltas(lp_deltas)

    ok, err = _check_canonical_deltas(settlement)
    if not ok:
        return False, err

    if settlement.balance_deltas != expected_balance:
        return False, "balance_deltas mismatch vs replay"
    if settlement.reserve_deltas != expected_reserve:
        return False, "reserve_deltas mismatch vs replay"
    if settlement.lp_deltas != expected_lp:
        return False, "lp_deltas mismatch vs replay"

    exp_events_norm = expected_events
    got_events_norm = settlement.events or []
    if got_events_norm != exp_events_norm:
        return False, "events mismatch vs replay"

    # Defense-in-depth: ensure basic conservation/non-negativity in addition to replay checks.
    # This is essential when a fill type does not touch pool reserves (e.g. COW_NETTED),
    # where conservation must be enforced globally across balance deltas.
    ok_legacy, err_legacy = validate_settlement_legacy(
        settlement=settlement,
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp_balances,
    )
    if not ok_legacy:
        return False, f"legacy validation failed: {err_legacy}"

    return True, None


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, amount)
    return copied


def _copy_lp_table(lp_balances: LPTable) -> LPTable:
    copied = LPTable()
    for (pubkey, pool_id), amount in lp_balances.get_all_balances().items():
        copied.set(pubkey, pool_id, amount)
    for (pubkey, pool_id), timestamp in lp_balances.get_all_last_mint_timestamps().items():
        if copied.get(pubkey, pool_id) > 0:
            copied.set_last_mint_timestamp(pubkey, pool_id, timestamp)
    return copied


def _aggregate_balance_deltas(deltas: List[BalanceDelta]) -> List[BalanceDelta]:
    acc: Dict[Tuple[PubKey, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[BalanceDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(BalanceDelta(pubkey=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_reserve_deltas(deltas: List[ReserveDelta]) -> List[ReserveDelta]:
    acc: Dict[Tuple[str, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pool_id, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[ReserveDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(ReserveDelta(pool_id=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_lp_deltas(deltas: List[LPDelta]) -> List[LPDelta]:
    acc: Dict[Tuple[PubKey, str], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.pool_id)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[LPDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(LPDelta(pubkey=key[0], pool_id=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _check_canonical_deltas(settlement: Settlement) -> Tuple[bool, Optional[str]]:
    # Ensure deltas are canonical (one entry per key, sorted, and with non-negative fields).
    def _check_unique_sorted(keys: List[Tuple], what: str) -> Tuple[bool, Optional[str]]:
        if keys != sorted(keys):
            return False, f"{what} not sorted canonically"
        if len(keys) != len(set(keys)):
            return False, f"{what} contains duplicate keys"
        return True, None

    # Balance deltas
    bal_keys: List[Tuple[PubKey, AssetId]] = []
    for balance_delta in settlement.balance_deltas:
        if (
            not isinstance(balance_delta.delta_add, int)
            or isinstance(balance_delta.delta_add, bool)
            or balance_delta.delta_add < 0
        ):
            return False, "balance_deltas contains invalid delta_add"
        if (
            not isinstance(balance_delta.delta_sub, int)
            or isinstance(balance_delta.delta_sub, bool)
            or balance_delta.delta_sub < 0
        ):
            return False, "balance_deltas contains invalid delta_sub"
        if balance_delta.delta_add == 0 and balance_delta.delta_sub == 0:
            return False, "balance_deltas contains a zero entry"
        bal_keys.append((balance_delta.pubkey, balance_delta.asset))
    ok, err = _check_unique_sorted(bal_keys, "balance_deltas")
    if not ok:
        return ok, err

    # Reserve deltas
    res_keys: List[Tuple[str, AssetId]] = []
    for reserve_delta in settlement.reserve_deltas:
        if (
            not isinstance(reserve_delta.delta_add, int)
            or isinstance(reserve_delta.delta_add, bool)
            or reserve_delta.delta_add < 0
        ):
            return False, "reserve_deltas contains invalid delta_add"
        if (
            not isinstance(reserve_delta.delta_sub, int)
            or isinstance(reserve_delta.delta_sub, bool)
            or reserve_delta.delta_sub < 0
        ):
            return False, "reserve_deltas contains invalid delta_sub"
        if reserve_delta.delta_add == 0 and reserve_delta.delta_sub == 0:
            return False, "reserve_deltas contains a zero entry"
        res_keys.append((reserve_delta.pool_id, reserve_delta.asset))
    ok, err = _check_unique_sorted(res_keys, "reserve_deltas")
    if not ok:
        return ok, err

    # LP deltas
    lp_keys: List[Tuple[PubKey, str]] = []
    for lp_delta in settlement.lp_deltas:
        if (
            not isinstance(lp_delta.delta_add, int)
            or isinstance(lp_delta.delta_add, bool)
            or lp_delta.delta_add < 0
        ):
            return False, "lp_deltas contains invalid delta_add"
        if (
            not isinstance(lp_delta.delta_sub, int)
            or isinstance(lp_delta.delta_sub, bool)
            or lp_delta.delta_sub < 0
        ):
            return False, "lp_deltas contains invalid delta_sub"
        if lp_delta.delta_add == 0 and lp_delta.delta_sub == 0:
            return False, "lp_deltas contains a zero entry"
        lp_keys.append((lp_delta.pubkey, lp_delta.pool_id))
    ok, err = _check_unique_sorted(lp_keys, "lp_deltas")
    if not ok:
        return ok, err

    return True, None
