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
from typing import Dict, List, Optional, Tuple

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
_FAIL_CLOSED_VALIDATOR_ERRORS = (
    TypeError,
    ValueError,
    ArithmeticError,
    LookupError,
    AttributeError,
    RuntimeError,
    AssertionError,
)


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
class _QuoteBindingFields:
    receipt_hash: object
    pool_fingerprint: object
    leg_index: object


def _quote_binding_fields(intent: Intent) -> _QuoteBindingFields:
    return _QuoteBindingFields(
        receipt_hash=intent.get_field("quote_receipt_hash"),
        pool_fingerprint=intent.get_field("quote_pool_fingerprint"),
        leg_index=intent.get_field("quote_receipt_leg_index"),
    )


def _has_quote_binding(fields: _QuoteBindingFields) -> bool:
    return fields.receipt_hash is not None or fields.pool_fingerprint is not None or fields.leg_index is not None


def _validate_quote_binding_kind(intent: Intent, fields: _QuoteBindingFields) -> Optional[str]:
    if not _has_quote_binding(fields) or intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return None
    return _quote_binding_error(
        "quote receipt binding only supported for swap intents",
        **_quote_binding_context(intent),
        intent_kind=intent.kind.value,
    )


def _validate_quote_leg_index_transport(intent: Intent, fields: _QuoteBindingFields) -> Optional[str]:
    if fields.leg_index is None:
        return None
    if not is_strict_int(fields.leg_index) or int(fields.leg_index) < 0:
        return _quote_binding_error("invalid quote_receipt_leg_index", **_quote_binding_context(intent))
    return _quote_binding_error(
        "quote receipt transport metadata requires validated engine witness",
        **_quote_binding_context(intent),
        guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
    )


def _validate_quote_receipt_hash_transport(intent: Intent, fields: _QuoteBindingFields) -> Optional[str]:
    if fields.receipt_hash is None:
        return None
    if not isinstance(fields.receipt_hash, str) or not fields.receipt_hash:
        return _quote_binding_error("invalid quote_receipt_hash", **_quote_binding_context(intent))
    return _quote_binding_error(
        "quote receipt transport metadata requires validated engine witness",
        **_quote_binding_context(intent),
        guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
    )


def _validate_quote_pool_fingerprint_transport(
    intent: Intent,
    fields: _QuoteBindingFields,
    *,
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


def _validate_quote_binding_transport(
    intent: Intent,
    *,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    fields = _quote_binding_fields(intent)
    for validator in (
        _validate_quote_binding_kind,
        _validate_quote_leg_index_transport,
        _validate_quote_receipt_hash_transport,
    ):
        error = validator(intent, fields)
        if error is not None:
            return error
    error = _validate_quote_pool_fingerprint_transport(
        intent,
        fields,
        allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
    )
    if error is not None:
        return error
    return None


@dataclass(frozen=True)
class _CowPairEntry:
    intent_id: str
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in_filled: int
    amount_out_filled: int


@dataclass(frozen=True)
class _CowPairIntentFields:
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _CowPairFillAmounts:
    amount_in_filled: int
    amount_out_filled: int


_CowPairKey = Tuple[str, AssetId, AssetId, int, int]


@dataclass(frozen=True)
class _SettlementIndex:
    intents_by_id: Dict[str, Intent]
    fill_by_id: Dict[str, Fill]


@dataclass
class _ReplayContext:
    balances: BalanceTable
    pools: Dict[str, PoolState]
    lp: LPTable
    expected_events: List[dict]
    bal_deltas: List[BalanceDelta]
    res_deltas: List[ReserveDelta]
    lp_deltas: List[LPDelta]


@dataclass(frozen=True)
class _SettlementPreState:
    balances: BalanceTable
    pools: Dict[str, PoolState]
    lp_balances: Optional[LPTable]


@dataclass(frozen=True)
class _CreatePoolIntentFields:
    asset0: object
    asset1: object
    fee_bps: object
    amount0: object
    amount1: object
    created_at: object
    curve_tag: object
    curve_params: object


@dataclass(frozen=True)
class _CreatePoolAssetIds:
    asset0: AssetId
    asset1: AssetId


@dataclass(frozen=True)
class _CreatePoolScalars:
    fee_bps: int
    amount0: int
    amount1: int
    created_at: int


@dataclass(frozen=True)
class _CreatePoolReplayInput:
    intent_id: str
    sender: PubKey
    asset0: AssetId
    asset1: AssetId
    fee_bps: int
    amount0: int
    amount1: int
    created_at: int
    curve_tag: object
    curve_params: object


@dataclass(frozen=True)
class _CreatePoolReplayResult:
    pool_id: str
    created_pool: PoolState
    lp_minted: int


@dataclass(frozen=True)
class _AddLiquidityReplayInput:
    intent_id: str
    sender: PubKey
    recipient: PubKey
    pool_id: str
    amount0_desired: int
    amount1_desired: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _AddLiquidityIntentFields:
    amount0_desired: object
    amount1_desired: object
    amount0_min: object
    amount1_min: object


@dataclass(frozen=True)
class _AddLiquidityAmounts:
    amount0_desired: int
    amount1_desired: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _AddLiquidityReplayResult:
    amount0_used: int
    amount1_used: int
    lp_minted: int


@dataclass(frozen=True)
class _RemoveLiquidityReplayInput:
    intent_id: str
    sender: PubKey
    recipient: PubKey
    pool_id: str
    lp_amount: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _RemoveLiquidityReplayResult:
    amount0_out: int
    amount1_out: int


@dataclass(frozen=True)
class _SwapReplayTarget:
    intent_id: str
    sender: PubKey
    recipient: PubKey
    pool_id: str
    pool: PoolState
    asset_in: AssetId
    asset_out: AssetId
    reserve_in: int
    reserve_out: int
    dir_is_0_to_1: bool


@dataclass(frozen=True)
class _CowNettingReplayRequest:
    intent: Intent
    fill: Fill
    target: _SwapReplayTarget
    allow_cow_netting: bool


@dataclass(frozen=True)
class _CowNettingReplayAmounts:
    amount_in: int
    amount_out: int


@dataclass(frozen=True)
class _CowNettingIntentAmounts:
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _ProtocolFeeReplayConfig:
    share_bps: int
    recipient_pubkey: Optional[PubKey]


@dataclass(frozen=True)
class _StrongValidationRequest:
    settlement: Settlement
    intents: List[Intent]
    pre_state: _SettlementPreState
    mode: str
    allow_cow_netting: bool
    allow_snapshot_bound_quote_bindings: bool
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: Optional[PubKey]


@dataclass(frozen=True)
class _IntentReplayEnvironment:
    request: _StrongValidationRequest
    settlement_index: _SettlementIndex
    replay: _ReplayContext
    protocol_fee: _ProtocolFeeReplayConfig


@dataclass(frozen=True)
class _PoolIntentReplayRequest:
    intent: Intent
    fill: Fill
    pool_target: _PoolReplayTarget
    quote_pool_fp: object
    env: _IntentReplayEnvironment


@dataclass(frozen=True)
class _SwapReplayRequest:
    intent: Intent
    fill: Fill
    target: _SwapReplayTarget
    protocol_fee: _ProtocolFeeReplayConfig


@dataclass(frozen=True)
class _SwapExactInReplayInput:
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _SwapExactOutReplayInput:
    amount_out: int
    max_in: int


@dataclass(frozen=True)
class _SwapReplayAmounts:
    amount_in: int
    amount_out: int
    new_reserve_in: int
    new_reserve_out: int
    protocol_fee: int


@dataclass(frozen=True)
class _PoolReplayTarget:
    pool_id: str
    pool: PoolState
    recipient: PubKey


def _build_replay_context(
    *,
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable],
) -> _ReplayContext:
    return _ReplayContext(
        balances=_copy_balance_table(pre_balances),
        pools={pool_id: replace(pool) for pool_id, pool in pre_pools.items()},
        lp=_copy_lp_table(pre_lp_balances) if pre_lp_balances is not None else LPTable(),
        expected_events=[],
        bal_deltas=[],
        res_deltas=[],
        lp_deltas=[],
    )


def _build_intents_by_id(intents: List[Intent]) -> Tuple[Optional[Dict[str, Intent]], Optional[str]]:
    intent_ids = [it.intent_id for it in intents]
    if len(intent_ids) != len(set(intent_ids)):
        return None, "duplicate intent_id in input intents"
    return {it.intent_id: it for it in intents}, None


def _validate_included_intent_ids(
    *,
    settlement: Settlement,
    intent_ids: List[str],
) -> Optional[str]:
    included_ids = [intent_id for intent_id, _action in settlement.included_intents]
    if set(included_ids) != set(intent_ids):
        missing = sorted(set(intent_ids) - set(included_ids))
        extra = sorted(set(included_ids) - set(intent_ids))
        return f"settlement included_intents mismatch: missing={missing} extra={extra}"
    if len(included_ids) != len(set(included_ids)):
        return "settlement included_intents contains duplicate intent_id entries"
    return None


def _build_fill_by_id(
    *,
    settlement: Settlement,
    intent_ids: List[str],
) -> Tuple[Optional[Dict[str, Fill]], Optional[str]]:
    fill_ids = [f.intent_id for f in settlement.fills]
    if len(fill_ids) != len(set(fill_ids)):
        return None, "settlement fills contains duplicate intent_id entries"
    extra_fill_ids = sorted(set(fill_ids) - set(intent_ids))
    if extra_fill_ids:
        return None, f"settlement fills contains intent_ids not in input intents: {extra_fill_ids}"
    return {f.intent_id: f for f in settlement.fills}, None


def _validate_included_fill_actions(
    *,
    settlement: Settlement,
    fill_by_id: Dict[str, Fill],
) -> Optional[str]:
    for intent_id, action in settlement.included_intents:
        fill = fill_by_id.get(intent_id)
        if fill is None:
            if action == FillAction.FILL:
                return f"missing Fill for filled intent_id: {intent_id}"
            continue
        if fill.action != action:
            return f"Fill.action mismatch for intent_id={intent_id}: {fill.action} != {action}"
    return None


def _build_settlement_index(
    *,
    settlement: Settlement,
    intents: List[Intent],
) -> Tuple[Optional[_SettlementIndex], Optional[str]]:
    intent_ids = [it.intent_id for it in intents]
    intents_by_id, err = _build_intents_by_id(intents)
    if intents_by_id is None:
        return None, err
    err = _validate_included_intent_ids(settlement=settlement, intent_ids=intent_ids)
    if err is not None:
        return None, err
    fill_by_id, err = _build_fill_by_id(settlement=settlement, intent_ids=intent_ids)
    if fill_by_id is None:
        return None, err
    err = _validate_included_fill_actions(settlement=settlement, fill_by_id=fill_by_id)
    if err is not None:
        return None, err
    return _SettlementIndex(intents_by_id=intents_by_id, fill_by_id=fill_by_id), None


def _cow_pair_key(entry: _CowPairEntry) -> _CowPairKey:
    return (
        entry.pool_id,
        entry.asset_in,
        entry.asset_out,
        entry.amount_in_filled,
        entry.amount_out_filled,
    )


def _cow_pair_reciprocal_key(entry: _CowPairEntry) -> _CowPairKey:
    return (
        entry.pool_id,
        entry.asset_out,
        entry.asset_in,
        entry.amount_out_filled,
        entry.amount_in_filled,
    )


def _validate_cow_pair_shape(*, intent_id: str, intent: Intent, fill: Fill) -> Optional[str]:
    if fill.action != FillAction.FILL:
        return f"COW_NETTED requires filled action: intent_id={intent_id}"
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}"
    return None


def _parse_cow_pair_intent_fields(
    *,
    intent_id: str,
    intent: Intent,
) -> Tuple[Optional[_CowPairIntentFields], Optional[str]]:
    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        return None, f"missing pool_id for intent_id={intent_id}"
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return None, f"invalid asset_in/out for intent_id={intent_id}"
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not is_strict_int(amount_in) or int(amount_in) <= 0:
        return None, f"invalid amount_in for intent_id={intent_id}"
    if not is_strict_int(min_out) or int(min_out) < 0:
        return None, f"invalid min_amount_out for intent_id={intent_id}"
    return (
        _CowPairIntentFields(
            pool_id=pool_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=int(amount_in),
            min_out=int(min_out),
        ),
        None,
    )


def _parse_cow_pair_fill_amounts(
    *,
    intent_id: str,
    fill: Fill,
    fields: _CowPairIntentFields,
) -> Tuple[Optional[_CowPairFillAmounts], Optional[str]]:
    if int(fill.fee_paid or 0) != 0:
        return None, f"COW_NETTED fee_paid must be 0: intent_id={intent_id}"
    if not is_strict_int(fill.amount_in_filled) or int(fill.amount_in_filled or 0) != fields.amount_in:
        return None, f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}"
    if not is_strict_int(fill.amount_out_filled):
        return None, f"COW_NETTED amount_out_filled invalid: intent_id={intent_id}"
    out_amt = int(fill.amount_out_filled or 0)
    if out_amt < fields.min_out:
        return None, f"COW_NETTED slippage: intent_id={intent_id}"
    return _CowPairFillAmounts(amount_in_filled=int(fill.amount_in_filled or 0), amount_out_filled=out_amt), None


def _parse_cow_pair_entry(
    *,
    intent_id: str,
    intent: Intent,
    fill: Fill,
) -> Tuple[Optional[_CowPairEntry], Optional[str]]:
    shape_error = _validate_cow_pair_shape(intent_id=intent_id, intent=intent, fill=fill)
    if shape_error is not None:
        return None, shape_error
    fields, field_error = _parse_cow_pair_intent_fields(intent_id=intent_id, intent=intent)
    if fields is None:
        return None, field_error
    amounts, amount_error = _parse_cow_pair_fill_amounts(intent_id=intent_id, fill=fill, fields=fields)
    if amounts is None:
        return None, amount_error
    return (
        _CowPairEntry(
            intent_id=intent_id,
            pool_id=fields.pool_id,
            asset_in=fields.asset_in,
            asset_out=fields.asset_out,
            amount_in_filled=amounts.amount_in_filled,
            amount_out_filled=amounts.amount_out_filled,
        ),
        None,
    )


def _build_cow_pair_entries(
    *,
    cow_ids: List[str],
    intents_by_id: Dict[str, Intent],
    fill_by_id: Dict[str, Fill],
) -> Tuple[Optional[Dict[str, _CowPairEntry]], Optional[str]]:
    entries: Dict[str, _CowPairEntry] = {}
    for intent_id in cow_ids:
        entry, err = _parse_cow_pair_entry(
            intent_id=intent_id,
            intent=intents_by_id[intent_id],
            fill=fill_by_id[intent_id],
        )
        if entry is None:
            return None, err or f"COW_NETTED amount_out_filled invalid: intent_id={intent_id}"
        entries[intent_id] = entry
    return entries, None


def _index_cow_pair_entries(entries: Dict[str, _CowPairEntry]) -> Dict[_CowPairKey, List[str]]:
    indexed: Dict[_CowPairKey, List[str]] = {}
    for intent_id, entry in entries.items():
        indexed.setdefault(_cow_pair_key(entry), []).append(intent_id)
    return indexed


def _validate_cow_pair_reciprocity(entries: Dict[str, _CowPairEntry]) -> Tuple[bool, Optional[str]]:
    # Indexed reciprocal lookup preserves the prior match list order while making
    # matching linear in the number of COW fills instead of quadratic.
    indexed = _index_cow_pair_entries(entries)
    pair_for: Dict[str, str] = {}
    for intent_id, entry in entries.items():
        matches = [other_id for other_id in indexed.get(_cow_pair_reciprocal_key(entry), []) if other_id != intent_id]
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

    entries, err = _build_cow_pair_entries(
        cow_ids=cow_ids,
        intents_by_id=intents_by_id,
        fill_by_id=fill_by_id,
    )
    if entries is None:
        return False, err
    return _validate_cow_pair_reciprocity(entries)


def _create_pool_intent_fields(intent: Intent) -> _CreatePoolIntentFields:
    return _CreatePoolIntentFields(
        asset0=intent.get_field("asset0"),
        asset1=intent.get_field("asset1"),
        fee_bps=intent.get_field("fee_bps"),
        amount0=intent.get_field("amount0"),
        amount1=intent.get_field("amount1"),
        created_at=intent.get_field("created_at", 0),
        curve_tag=intent.get_field("curve_tag", None),
        curve_params=intent.get_field("curve_params", None),
    )


def _validate_create_pool_required_fields(
    *,
    intent_id: str,
    fields: _CreatePoolIntentFields,
) -> Optional[str]:
    if any(v is None for v in (fields.asset0, fields.asset1, fields.fee_bps, fields.amount0, fields.amount1)):
        return f"missing CREATE_POOL fields for intent_id={intent_id}"
    return None


def _parse_create_pool_asset_ids(
    *,
    intent_id: str,
    fields: _CreatePoolIntentFields,
) -> Tuple[Optional[_CreatePoolAssetIds], Optional[str]]:
    if not isinstance(fields.asset0, str) or not isinstance(fields.asset1, str):
        return None, f"invalid CREATE_POOL asset ids for intent_id={intent_id}"
    return _CreatePoolAssetIds(asset0=fields.asset0, asset1=fields.asset1), None


def _parse_create_pool_fee_bps(*, intent_id: str, value: object) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or not (0 <= value <= 10000):
        return None, f"invalid CREATE_POOL fee_bps for intent_id={intent_id}"
    return value, None


def _parse_create_pool_positive_amount(
    *,
    intent_id: str,
    field_name: str,
    value: object,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or value <= 0:
        return None, f"invalid CREATE_POOL {field_name} for intent_id={intent_id}"
    return value, None


def _parse_create_pool_created_at(*, intent_id: str, value: object) -> Tuple[Optional[int], Optional[str]]:
    if value is not None and (not is_strict_int(value) or value < 0):
        return None, f"invalid CREATE_POOL created_at for intent_id={intent_id}"
    return 0 if value is None else value, None


def _parse_create_pool_scalars(
    *,
    intent_id: str,
    fields: _CreatePoolIntentFields,
) -> Tuple[Optional[_CreatePoolScalars], Optional[str]]:
    fee_bps, err = _parse_create_pool_fee_bps(intent_id=intent_id, value=fields.fee_bps)
    if fee_bps is None:
        return None, err
    amount0, err = _parse_create_pool_positive_amount(intent_id=intent_id, field_name="amount0", value=fields.amount0)
    if amount0 is None:
        return None, err
    amount1, err = _parse_create_pool_positive_amount(intent_id=intent_id, field_name="amount1", value=fields.amount1)
    if amount1 is None:
        return None, err
    created_at, err = _parse_create_pool_created_at(intent_id=intent_id, value=fields.created_at)
    if created_at is None:
        return None, err
    return (
        _CreatePoolScalars(
            fee_bps=fee_bps,
            amount0=amount0,
            amount1=amount1,
            created_at=created_at,
        ),
        None,
    )


def _parse_create_pool_replay_input(
    intent: Intent,
) -> Tuple[Optional[_CreatePoolReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    fields = _create_pool_intent_fields(intent)
    err = _validate_create_pool_required_fields(intent_id=intent_id, fields=fields)
    if err is not None:
        return None, err
    asset_ids, err = _parse_create_pool_asset_ids(intent_id=intent_id, fields=fields)
    if asset_ids is None:
        return None, err
    scalars, err = _parse_create_pool_scalars(intent_id=intent_id, fields=fields)
    if scalars is None:
        return None, err
    return (
        _CreatePoolReplayInput(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            asset0=asset_ids.asset0,
            asset1=asset_ids.asset1,
            fee_bps=scalars.fee_bps,
            amount0=scalars.amount0,
            amount1=scalars.amount1,
            created_at=scalars.created_at,
            curve_tag=fields.curve_tag,
            curve_params=fields.curve_params,
        ),
        None,
    )


def _check_create_pool_fill(
    *,
    fill: Fill,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> Optional[str]:
    if int(fill.amount0_used or 0) != int(replay_input.amount0):
        return f"CREATE_POOL fill.amount0_used mismatch for intent_id={replay_input.intent_id}"
    if int(fill.amount1_used or 0) != int(replay_input.amount1):
        return f"CREATE_POOL fill.amount1_used mismatch for intent_id={replay_input.intent_id}"
    if int(fill.lp_minted or 0) != int(replay_result.lp_minted):
        return f"CREATE_POOL fill.lp_minted mismatch for intent_id={replay_input.intent_id}"
    return None


def _apply_create_pool_replay(
    *,
    replay: _ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> Optional[str]:
    try:
        replay.balances.subtract(replay_input.sender, replay_input.asset0, int(replay_input.amount0))
        replay.balances.subtract(replay_input.sender, replay_input.asset1, int(replay_input.amount1))
        replay.lp.add(replay_input.sender, replay_result.pool_id, int(replay_result.lp_minted))
        replay.lp.add(LP_LOCK_PUBKEY, replay_result.pool_id, int(MIN_LP_LOCK))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"CREATE_POOL balance/LP apply error for intent_id={replay_input.intent_id}: {exc}"
    return None


def _record_create_pool_replay(
    *,
    replay: _ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> None:
    replay.pools[replay_result.pool_id] = replay_result.created_pool
    _record_create_pool_event(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    _record_create_pool_deltas(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )


def _record_create_pool_event(
    *,
    replay: _ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> None:
    replay.expected_events.append(
        {
            "type": "CREATE_POOL",
            "pool_id": replay_result.pool_id,
            "asset0": replay_input.asset0,
            "asset1": replay_input.asset1,
            "fee_bps": int(replay_input.fee_bps),
            "curve_tag": replay_result.created_pool.curve_tag,
            "curve_params": replay_result.created_pool.curve_params,
            "status": PoolStatus.ACTIVE.value,
            "created_at": int(replay_result.created_pool.created_at),
        }
    )


def _record_create_pool_deltas(
    *,
    replay: _ReplayContext,
    replay_input: _CreatePoolReplayInput,
    replay_result: _CreatePoolReplayResult,
) -> None:
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=replay_input.asset0,
            delta_add=0,
            delta_sub=int(replay_input.amount0),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=replay_input.asset1,
            delta_add=0,
            delta_sub=int(replay_input.amount1),
        )
    )

    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_result.pool_id,
            asset=replay_input.asset0,
            delta_add=int(replay_input.amount0),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_result.pool_id,
            asset=replay_input.asset1,
            delta_add=int(replay_input.amount1),
            delta_sub=0,
        )
    )

    replay.lp_deltas.append(
        LPDelta(
            pubkey=replay_input.sender,
            pool_id=replay_result.pool_id,
            delta_add=int(replay_result.lp_minted),
            delta_sub=0,
        )
    )
    replay.lp_deltas.append(
        LPDelta(
            pubkey=LP_LOCK_PUBKEY,
            pool_id=replay_result.pool_id,
            delta_add=int(MIN_LP_LOCK),
            delta_sub=0,
        )
    )


def _replay_create_pool_fill(
    *,
    intent: Intent,
    fill: Fill,
    replay: _ReplayContext,
) -> Optional[str]:
    intent_id = intent.intent_id

    replay_input, err = _parse_create_pool_replay_input(intent)
    if replay_input is None:
        return err or f"missing CREATE_POOL fields for intent_id={intent_id}"

    try:
        pool_id, created_pool, lp_minted = create_pool(
            asset0=replay_input.asset0,
            asset1=replay_input.asset1,
            amount0=replay_input.amount0,
            amount1=replay_input.amount1,
            fee_bps=replay_input.fee_bps,
            creator_pubkey=replay_input.sender,
            created_at=replay_input.created_at,
            curve_tag=replay_input.curve_tag,
            curve_params=replay_input.curve_params,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"CREATE_POOL computation error for intent_id={intent_id}: {exc}"

    if pool_id in replay.pools:
        return f"CREATE_POOL duplicates existing pool_id={pool_id}"

    replay_result = _CreatePoolReplayResult(
        pool_id=pool_id,
        created_pool=created_pool,
        lp_minted=lp_minted,
    )
    err = _check_create_pool_fill(
        fill=fill,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    err = _apply_create_pool_replay(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_create_pool_replay(
        replay=replay,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None


def _add_liquidity_intent_fields(intent: Intent) -> _AddLiquidityIntentFields:
    return _AddLiquidityIntentFields(
        amount0_desired=intent.get_field("amount0_desired"),
        amount1_desired=intent.get_field("amount1_desired"),
        amount0_min=intent.get_field("amount0_min", 0),
        amount1_min=intent.get_field("amount1_min", 0),
    )


def _validate_add_liquidity_required_fields(
    *,
    intent_id: str,
    fields: _AddLiquidityIntentFields,
) -> Optional[str]:
    if any(v is None for v in (fields.amount0_desired, fields.amount1_desired)):
        return f"missing ADD_LIQUIDITY fields for intent_id={intent_id}"
    return None


def _parse_add_liquidity_positive_amount(
    *,
    intent_id: str,
    field_name: str,
    value: object,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or value <= 0:
        return None, f"invalid {field_name} for intent_id={intent_id}"
    return value, None


def _parse_add_liquidity_min_amount(
    *,
    intent_id: str,
    field_name: str,
    value: object,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(value) or value < 0:
        return None, f"invalid {field_name} for intent_id={intent_id}"
    return value, None


def _parse_add_liquidity_amounts(
    *,
    intent_id: str,
    fields: _AddLiquidityIntentFields,
) -> Tuple[Optional[_AddLiquidityAmounts], Optional[str]]:
    amount0_desired, err = _parse_add_liquidity_positive_amount(
        intent_id=intent_id,
        field_name="amount0_desired",
        value=fields.amount0_desired,
    )
    if amount0_desired is None:
        return None, err
    amount1_desired, err = _parse_add_liquidity_positive_amount(
        intent_id=intent_id,
        field_name="amount1_desired",
        value=fields.amount1_desired,
    )
    if amount1_desired is None:
        return None, err
    amount0_min, err = _parse_add_liquidity_min_amount(
        intent_id=intent_id,
        field_name="amount0_min",
        value=fields.amount0_min,
    )
    if amount0_min is None:
        return None, err
    amount1_min, err = _parse_add_liquidity_min_amount(
        intent_id=intent_id,
        field_name="amount1_min",
        value=fields.amount1_min,
    )
    if amount1_min is None:
        return None, err
    return (
        _AddLiquidityAmounts(
            amount0_desired=amount0_desired,
            amount1_desired=amount1_desired,
            amount0_min=amount0_min,
            amount1_min=amount1_min,
        ),
        None,
    )


def _parse_add_liquidity_replay_input(
    *,
    intent: Intent,
    recipient: PubKey,
    pool_id: str,
) -> Tuple[Optional[_AddLiquidityReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    fields = _add_liquidity_intent_fields(intent)
    err = _validate_add_liquidity_required_fields(intent_id=intent_id, fields=fields)
    if err is not None:
        return None, err
    amounts, err = _parse_add_liquidity_amounts(intent_id=intent_id, fields=fields)
    if amounts is None:
        return None, err
    return (
        _AddLiquidityReplayInput(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            recipient=recipient,
            pool_id=pool_id,
            amount0_desired=amounts.amount0_desired,
            amount1_desired=amounts.amount1_desired,
            amount0_min=amounts.amount0_min,
            amount1_min=amounts.amount1_min,
        ),
        None,
    )


def _check_add_liquidity_fill(
    *,
    fill: Fill,
    replay_input: _AddLiquidityReplayInput,
    replay_result: _AddLiquidityReplayResult,
) -> Optional[str]:
    if int(fill.amount0_used or 0) != int(replay_result.amount0_used):
        return f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={replay_input.intent_id}"
    if int(fill.amount1_used or 0) != int(replay_result.amount1_used):
        return f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={replay_input.intent_id}"
    if int(fill.lp_minted or 0) != int(replay_result.lp_minted):
        return f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={replay_input.intent_id}"
    return None


def _apply_add_liquidity_replay(
    *,
    replay: _ReplayContext,
    pool: PoolState,
    replay_input: _AddLiquidityReplayInput,
    replay_result: _AddLiquidityReplayResult,
) -> Optional[str]:
    try:
        replay.balances.subtract(replay_input.sender, pool.asset0, int(replay_result.amount0_used))
        replay.balances.subtract(replay_input.sender, pool.asset1, int(replay_result.amount1_used))
        replay.lp.add(replay_input.recipient, replay_input.pool_id, int(replay_result.lp_minted))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"ADD_LIQUIDITY apply error for intent_id={replay_input.intent_id}: {exc}"

    pool.reserve0 += int(replay_result.amount0_used)
    pool.reserve1 += int(replay_result.amount1_used)
    pool.lp_supply += int(replay_result.lp_minted)
    return None


def _record_add_liquidity_deltas(
    *,
    replay: _ReplayContext,
    pool: PoolState,
    replay_input: _AddLiquidityReplayInput,
    replay_result: _AddLiquidityReplayResult,
) -> None:
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=pool.asset0,
            delta_add=0,
            delta_sub=int(replay_result.amount0_used),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.sender,
            asset=pool.asset1,
            delta_add=0,
            delta_sub=int(replay_result.amount1_used),
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset0,
            delta_add=int(replay_result.amount0_used),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset1,
            delta_add=int(replay_result.amount1_used),
            delta_sub=0,
        )
    )
    replay.lp_deltas.append(
        LPDelta(
            pubkey=replay_input.recipient,
            pool_id=replay_input.pool_id,
            delta_add=int(replay_result.lp_minted),
            delta_sub=0,
        )
    )


def _replay_add_liquidity_fill(
    *,
    intent: Intent,
    fill: Fill,
    target: _PoolReplayTarget,
    replay: _ReplayContext,
) -> Optional[str]:
    if target.pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent.intent_id}: {target.pool.status}"

    replay_input, err = _parse_add_liquidity_replay_input(
        intent=intent,
        recipient=target.recipient,
        pool_id=target.pool_id,
    )
    if replay_input is None:
        return err or f"missing ADD_LIQUIDITY fields for intent_id={intent.intent_id}"

    try:
        amount0_used, amount1_used, lp_minted = add_liquidity(
            pool_state=target.pool,
            amount0_desired=replay_input.amount0_desired,
            amount1_desired=replay_input.amount1_desired,
            amount0_min=replay_input.amount0_min,
            amount1_min=replay_input.amount1_min,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"ADD_LIQUIDITY computation error for intent_id={replay_input.intent_id}: {exc}"

    replay_result = _AddLiquidityReplayResult(
        amount0_used=amount0_used,
        amount1_used=amount1_used,
        lp_minted=lp_minted,
    )
    err = _check_add_liquidity_fill(
        fill=fill,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    err = _apply_add_liquidity_replay(
        replay=replay,
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_add_liquidity_deltas(
        replay=replay,
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None


def _parse_remove_liquidity_replay_input(
    *,
    intent: Intent,
    recipient: PubKey,
    pool_id: str,
) -> Tuple[Optional[_RemoveLiquidityReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    lp_amount = intent.get_field("lp_amount")
    amount0_min = intent.get_field("amount0_min", 0)
    amount1_min = intent.get_field("amount1_min", 0)
    if lp_amount is None:
        return None, f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent_id}"
    if not is_strict_int(lp_amount) or lp_amount <= 0:
        return None, f"invalid lp_amount for intent_id={intent_id}"
    if not is_strict_int(amount0_min) or amount0_min < 0:
        return None, f"invalid amount0_min for intent_id={intent_id}"
    if not is_strict_int(amount1_min) or amount1_min < 0:
        return None, f"invalid amount1_min for intent_id={intent_id}"
    return (
        _RemoveLiquidityReplayInput(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            recipient=recipient,
            pool_id=pool_id,
            lp_amount=lp_amount,
            amount0_min=amount0_min,
            amount1_min=amount1_min,
        ),
        None,
    )


def _check_remove_liquidity_fill(
    *,
    fill: Fill,
    replay_input: _RemoveLiquidityReplayInput,
    replay_result: _RemoveLiquidityReplayResult,
) -> Optional[str]:
    if int(fill.lp_burned or 0) != int(replay_input.lp_amount):
        return f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={replay_input.intent_id}"
    if int(fill.amount0_out or 0) != int(replay_result.amount0_out):
        return f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={replay_input.intent_id}"
    if int(fill.amount1_out or 0) != int(replay_result.amount1_out):
        return f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={replay_input.intent_id}"
    return None


def _apply_remove_liquidity_replay(
    *,
    replay: _ReplayContext,
    pool: PoolState,
    replay_input: _RemoveLiquidityReplayInput,
    replay_result: _RemoveLiquidityReplayResult,
) -> Optional[str]:
    try:
        replay.lp.subtract(replay_input.sender, replay_input.pool_id, int(replay_input.lp_amount))
        replay.balances.add(replay_input.recipient, pool.asset0, int(replay_result.amount0_out))
        replay.balances.add(replay_input.recipient, pool.asset1, int(replay_result.amount1_out))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"REMOVE_LIQUIDITY apply error for intent_id={replay_input.intent_id}: {exc}"

    pool.reserve0 -= int(replay_result.amount0_out)
    pool.reserve1 -= int(replay_result.amount1_out)
    pool.lp_supply -= int(replay_input.lp_amount)
    return None


def _record_remove_liquidity_deltas(
    *,
    replay: _ReplayContext,
    pool: PoolState,
    replay_input: _RemoveLiquidityReplayInput,
    replay_result: _RemoveLiquidityReplayResult,
) -> None:
    replay.lp_deltas.append(
        LPDelta(
            pubkey=replay_input.sender,
            pool_id=replay_input.pool_id,
            delta_add=0,
            delta_sub=int(replay_input.lp_amount),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.recipient,
            asset=pool.asset0,
            delta_add=int(replay_result.amount0_out),
            delta_sub=0,
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=replay_input.recipient,
            asset=pool.asset1,
            delta_add=int(replay_result.amount1_out),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset0,
            delta_add=0,
            delta_sub=int(replay_result.amount0_out),
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=replay_input.pool_id,
            asset=pool.asset1,
            delta_add=0,
            delta_sub=int(replay_result.amount1_out),
        )
    )


def _replay_remove_liquidity_fill(
    *,
    intent: Intent,
    fill: Fill,
    target: _PoolReplayTarget,
    replay: _ReplayContext,
) -> Optional[str]:
    if target.pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent.intent_id}: {target.pool.status}"

    replay_input, err = _parse_remove_liquidity_replay_input(
        intent=intent,
        recipient=target.recipient,
        pool_id=target.pool_id,
    )
    if replay_input is None:
        return err or f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent.intent_id}"

    try:
        amount0_out, amount1_out = remove_liquidity(
            pool_state=target.pool,
            lp_amount=replay_input.lp_amount,
            amount0_min=replay_input.amount0_min,
            amount1_min=replay_input.amount1_min,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"REMOVE_LIQUIDITY computation error for intent_id={replay_input.intent_id}: {exc}"

    replay_result = _RemoveLiquidityReplayResult(amount0_out=amount0_out, amount1_out=amount1_out)
    err = _check_remove_liquidity_fill(
        fill=fill,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    err = _apply_remove_liquidity_replay(
        replay=replay,
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    if err is not None:
        return err

    _record_remove_liquidity_deltas(
        replay=replay,
        pool=target.pool,
        replay_input=replay_input,
        replay_result=replay_result,
    )
    return None


def _build_swap_replay_target(
    *,
    intent: Intent,
    target: _PoolReplayTarget,
    quote_pool_fp: object,
) -> Tuple[Optional[_SwapReplayTarget], Optional[str]]:
    intent_id = intent.intent_id
    pool = target.pool
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return None, f"invalid asset_in/out for intent_id={intent_id}"
    if pool.status != PoolStatus.ACTIVE:
        return None, f"pool not active for intent_id={intent_id}: {pool.status}"
    if {asset_in, asset_out} != {pool.asset0, pool.asset1} or asset_in == asset_out:
        return None, f"swap asset mismatch for intent_id={intent_id}"
    if quote_pool_fp is not None:
        actual_pool_fp = pool_state_fingerprint(pool)
        if actual_pool_fp != quote_pool_fp:
            return (
                None,
                _quote_binding_error(
                    "quote receipt pool snapshot mismatch",
                    **_quote_binding_context(intent),
                    actual_pool_fingerprint=actual_pool_fp,
                ),
            )

    if asset_in == pool.asset0 and asset_out == pool.asset1:
        reserve_in = int(pool.reserve0)
        reserve_out = int(pool.reserve1)
        dir_is_0_to_1 = True
    else:
        reserve_in = int(pool.reserve1)
        reserve_out = int(pool.reserve0)
        dir_is_0_to_1 = False

    return (
        _SwapReplayTarget(
            intent_id=intent_id,
            sender=intent.sender_pubkey,
            recipient=target.recipient,
            pool_id=target.pool_id,
            pool=pool,
            asset_in=asset_in,
            asset_out=asset_out,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            dir_is_0_to_1=dir_is_0_to_1,
        ),
        None,
    )


def _check_swap_reserve_witness(
    *,
    fill: Fill,
    target: _SwapReplayTarget,
    mode: str,
) -> Optional[str]:
    if mode != _MODE_STRONG_PROOF_CARRYING:
        return None
    if fill.reserve_in_before is None or fill.reserve_out_before is None:
        return f"missing swap witness reserves for intent_id={target.intent_id}"
    if int(fill.reserve_in_before) != int(target.reserve_in) or int(fill.reserve_out_before) != int(target.reserve_out):
        return f"swap witness reserve mismatch for intent_id={target.intent_id}"
    return None


def _replay_cow_netted_fill(
    *,
    request: _CowNettingReplayRequest,
    replay: _ReplayContext,
) -> Optional[str]:
    err = _validate_cow_netted_replay_preconditions(request)
    if err is not None:
        return err
    amounts, err = _parse_cow_netted_replay_amounts(request)
    if amounts is None:
        return err
    err = _apply_cow_netted_balance_replay(replay=replay, target=request.target, amounts=amounts)
    if err is not None:
        return err
    _record_cow_netted_balance_deltas(replay=replay, target=request.target, amounts=amounts)
    return None


def _validate_cow_netted_replay_preconditions(request: _CowNettingReplayRequest) -> Optional[str]:
    target = request.target
    if not request.allow_cow_netting:
        return f"COW_NETTED not allowed for intent_id={target.intent_id}"
    if request.intent.kind != IntentKind.SWAP_EXACT_IN:
        return f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={target.intent_id}"
    return None


def _parse_cow_netted_replay_amounts(
    request: _CowNettingReplayRequest,
) -> Tuple[Optional[_CowNettingReplayAmounts], Optional[str]]:
    intent_amounts, err = _parse_cow_netted_intent_amounts(request)
    if intent_amounts is None:
        return None, err
    return _parse_cow_netted_fill_amounts(request=request, intent_amounts=intent_amounts)


def _parse_cow_netted_intent_amounts(
    request: _CowNettingReplayRequest,
) -> Tuple[Optional[_CowNettingIntentAmounts], Optional[str]]:
    intent = request.intent
    target = request.target
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None, f"invalid amount_in for intent_id={target.intent_id}"
    if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
        return None, f"invalid min_amount_out for intent_id={target.intent_id}"
    return _CowNettingIntentAmounts(amount_in=int(amount_in), min_out=int(min_out)), None


def _parse_cow_netted_fill_amounts(
    *,
    request: _CowNettingReplayRequest,
    intent_amounts: _CowNettingIntentAmounts,
) -> Tuple[Optional[_CowNettingReplayAmounts], Optional[str]]:
    fill = request.fill
    target = request.target
    if int(fill.fee_paid or 0) != 0:
        return None, f"COW_NETTED fee_paid must be 0: intent_id={target.intent_id}"
    if int(fill.amount_in_filled or 0) != intent_amounts.amount_in:
        return None, f"COW_NETTED amount_in_filled mismatch: intent_id={target.intent_id}"
    out_amt = int(fill.amount_out_filled or 0)
    if out_amt < intent_amounts.min_out:
        return None, f"COW_NETTED slippage: intent_id={target.intent_id}"
    return _CowNettingReplayAmounts(amount_in=intent_amounts.amount_in, amount_out=out_amt), None


def _apply_cow_netted_balance_replay(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    amounts: _CowNettingReplayAmounts,
) -> Optional[str]:
    try:
        replay.balances.subtract(target.sender, target.asset_in, amounts.amount_in)
        replay.balances.add(target.recipient, target.asset_out, amounts.amount_out)
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"COW_NETTED apply error for intent_id={target.intent_id}: {exc}"
    return None


def _record_cow_netted_balance_deltas(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    amounts: _CowNettingReplayAmounts,
) -> None:
    replay.bal_deltas.append(
        BalanceDelta(pubkey=target.sender, asset=target.asset_in, delta_add=0, delta_sub=amounts.amount_in)
    )
    replay.bal_deltas.append(
        BalanceDelta(pubkey=target.recipient, asset=target.asset_out, delta_add=amounts.amount_out, delta_sub=0)
    )


def _parse_swap_exact_in_replay_input(intent: Intent) -> Tuple[Optional[_SwapExactInReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        return None, f"invalid amount_in for intent_id={intent_id}"
    if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
        return None, f"invalid min_amount_out for intent_id={intent_id}"
    return _SwapExactInReplayInput(amount_in=amount_in, min_out=min_out), None


def _quote_swap_exact_in_replay(
    *,
    target: _SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Tuple[Optional[_SwapReplayAmounts], Optional[str]]:
    try:
        if int(protocol_fee.share_bps):
            if target.pool.curve_tag != CURVE_TAG_CPMM:
                return None, f"protocol fee unsupported for curve intent_id={target.intent_id}"
            quote = swap_exact_in_with_protocol_fee(
                reserve_in=int(target.reserve_in),
                reserve_out=int(target.reserve_out),
                amount_in=int(replay_input.amount_in),
                fee_bps=int(target.pool.fee_bps),
                protocol_fee_share_bps=int(protocol_fee.share_bps),
            )
            return (
                _SwapReplayAmounts(
                    amount_in=int(replay_input.amount_in),
                    amount_out=int(quote.amount_out),
                    new_reserve_in=int(quote.new_reserve_in),
                    new_reserve_out=int(quote.new_reserve_out),
                    protocol_fee=int(quote.protocol_fee),
                ),
                None,
            )

        amount_out, (new_in, new_out) = swap_exact_in_for_pool(
            target.pool,
            reserve_in=int(target.reserve_in),
            reserve_out=int(target.reserve_out),
            amount_in=int(replay_input.amount_in),
        )
        return (
            _SwapReplayAmounts(
                amount_in=int(replay_input.amount_in),
                amount_out=int(amount_out),
                new_reserve_in=int(new_in),
                new_reserve_out=int(new_out),
                protocol_fee=0,
            ),
            None,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return None, f"swap_exact_in kernel error for intent_id={target.intent_id}: {exc}"


def _check_swap_exact_in_fill(
    *,
    fill: Fill,
    target: _SwapReplayTarget,
    replay_input: _SwapExactInReplayInput,
    replay_amounts: _SwapReplayAmounts,
) -> Optional[str]:
    if int(fill.amount_in_filled or 0) != int(replay_input.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={target.intent_id}"
    if int(fill.amount_out_filled or 0) != int(replay_amounts.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={target.intent_id}"
    if int(replay_amounts.amount_out) < int(replay_input.min_out):
        return f"swap slippage for intent_id={target.intent_id}"

    fee = compute_fee_total(int(replay_input.amount_in), int(target.pool.fee_bps))
    if int(fill.fee_paid or 0) != int(fee):
        return f"swap fee_paid mismatch for intent_id={target.intent_id}"
    if int(fill.protocol_fee_paid or 0) != int(replay_amounts.protocol_fee):
        return f"swap protocol_fee_paid mismatch for intent_id={target.intent_id}"
    return None


def _apply_swap_replay(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    replay_amounts: _SwapReplayAmounts,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Optional[str]:
    try:
        replay.balances.subtract(target.sender, target.asset_in, int(replay_amounts.amount_in))
        replay.balances.add(target.recipient, target.asset_out, int(replay_amounts.amount_out))
        if replay_amounts.protocol_fee:
            if protocol_fee.recipient_pubkey is None:
                return f"protocol fee recipient missing during replay for intent_id={target.intent_id}"
            replay.balances.add(protocol_fee.recipient_pubkey, target.asset_in, int(replay_amounts.protocol_fee))
    except (TypeError, ValueError, ArithmeticError) as exc:
        return f"swap apply error for intent_id={target.intent_id}: {exc}"

    if target.dir_is_0_to_1:
        target.pool.reserve0 = int(replay_amounts.new_reserve_in)
        target.pool.reserve1 = int(replay_amounts.new_reserve_out)
    else:
        target.pool.reserve1 = int(replay_amounts.new_reserve_in)
        target.pool.reserve0 = int(replay_amounts.new_reserve_out)
    return None


def _record_swap_replay_deltas(
    *,
    replay: _ReplayContext,
    target: _SwapReplayTarget,
    replay_amounts: _SwapReplayAmounts,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Optional[str]:
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=target.sender,
            asset=target.asset_in,
            delta_add=0,
            delta_sub=int(replay_amounts.amount_in),
        )
    )
    replay.bal_deltas.append(
        BalanceDelta(
            pubkey=target.recipient,
            asset=target.asset_out,
            delta_add=int(replay_amounts.amount_out),
            delta_sub=0,
        )
    )
    if replay_amounts.protocol_fee:
        if protocol_fee.recipient_pubkey is None:
            return f"protocol fee recipient missing during replay for intent_id={target.intent_id}"
        replay.bal_deltas.append(
            BalanceDelta(
                pubkey=protocol_fee.recipient_pubkey,
                asset=target.asset_in,
                delta_add=int(replay_amounts.protocol_fee),
                delta_sub=0,
            )
        )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=target.pool_id,
            asset=target.asset_in,
            delta_add=int(replay_amounts.amount_in) - int(replay_amounts.protocol_fee),
            delta_sub=0,
        )
    )
    replay.res_deltas.append(
        ReserveDelta(
            pool_id=target.pool_id,
            asset=target.asset_out,
            delta_add=0,
            delta_sub=int(replay_amounts.amount_out),
        )
    )
    return None


def _replay_swap_exact_in_fill(
    *,
    request: _SwapReplayRequest,
    replay: _ReplayContext,
) -> Optional[str]:
    replay_input, err = _parse_swap_exact_in_replay_input(request.intent)
    if replay_input is None:
        return err or f"invalid amount_in for intent_id={request.target.intent_id}"
    if int(request.fill.amount_in_filled or 0) != int(replay_input.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={request.target.intent_id}"

    replay_amounts, err = _quote_swap_exact_in_replay(
        target=request.target,
        replay_input=replay_input,
        protocol_fee=request.protocol_fee,
    )
    if replay_amounts is None:
        return err or f"swap_exact_in kernel error for intent_id={request.target.intent_id}"

    err = _check_swap_exact_in_fill(
        fill=request.fill,
        target=request.target,
        replay_input=replay_input,
        replay_amounts=replay_amounts,
    )
    if err is not None:
        return err

    err = _apply_swap_replay(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )
    if err is not None:
        return err

    return _record_swap_replay_deltas(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )


def _parse_swap_exact_out_replay_input(intent: Intent) -> Tuple[Optional[_SwapExactOutReplayInput], Optional[str]]:
    intent_id = intent.intent_id
    amount_out = intent.get_field("amount_out")
    max_in = intent.get_field("max_amount_in")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        return None, f"invalid amount_out for intent_id={intent_id}"
    if not isinstance(max_in, int) or isinstance(max_in, bool) or max_in < 0:
        return None, f"invalid max_amount_in for intent_id={intent_id}"
    return _SwapExactOutReplayInput(amount_out=amount_out, max_in=max_in), None


def _quote_swap_exact_out_replay(
    *,
    target: _SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    protocol_fee: _ProtocolFeeReplayConfig,
) -> Tuple[Optional[_SwapReplayAmounts], Optional[str]]:
    try:
        if int(protocol_fee.share_bps):
            if target.pool.curve_tag != CURVE_TAG_CPMM:
                return None, f"protocol fee unsupported for curve intent_id={target.intent_id}"
            quote = quote_cpmm_swap_exact_out(
                reserve_in=int(target.reserve_in),
                reserve_out=int(target.reserve_out),
                amount_out=int(replay_input.amount_out),
                fee_bps=int(target.pool.fee_bps),
                protocol_fee_share_bps=int(protocol_fee.share_bps),
            )
            return (
                _SwapReplayAmounts(
                    amount_in=int(quote.amount_in),
                    amount_out=int(replay_input.amount_out),
                    new_reserve_in=int(quote.reserve_in_after),
                    new_reserve_out=int(quote.reserve_out_after),
                    protocol_fee=int(quote.protocol_fee_paid),
                ),
                None,
            )

        amount_in, (new_in, new_out) = swap_exact_out_for_pool(
            target.pool,
            reserve_in=int(target.reserve_in),
            reserve_out=int(target.reserve_out),
            amount_out=int(replay_input.amount_out),
        )
        return (
            _SwapReplayAmounts(
                amount_in=int(amount_in),
                amount_out=int(replay_input.amount_out),
                new_reserve_in=int(new_in),
                new_reserve_out=int(new_out),
                protocol_fee=0,
            ),
            None,
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return None, f"swap_exact_out kernel error for intent_id={target.intent_id}: {exc}"


def _check_swap_exact_out_fill(
    *,
    fill: Fill,
    target: _SwapReplayTarget,
    replay_input: _SwapExactOutReplayInput,
    replay_amounts: _SwapReplayAmounts,
) -> Optional[str]:
    if int(fill.amount_out_filled or 0) != int(replay_input.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={target.intent_id}"
    if int(fill.amount_in_filled or 0) != int(replay_amounts.amount_in):
        return f"swap amount_in_filled mismatch for intent_id={target.intent_id}"
    if int(replay_amounts.amount_in) > int(replay_input.max_in):
        return f"swap slippage for intent_id={target.intent_id}"

    fee = compute_fee_total(int(replay_amounts.amount_in), int(target.pool.fee_bps))
    if int(fill.fee_paid or 0) != int(fee):
        return f"swap fee_paid mismatch for intent_id={target.intent_id}"
    if int(fill.protocol_fee_paid or 0) != int(replay_amounts.protocol_fee):
        return f"swap protocol_fee_paid mismatch for intent_id={target.intent_id}"
    return None


def _replay_swap_exact_out_fill(
    *,
    request: _SwapReplayRequest,
    replay: _ReplayContext,
) -> Optional[str]:
    replay_input, err = _parse_swap_exact_out_replay_input(request.intent)
    if replay_input is None:
        return err or f"invalid amount_out for intent_id={request.target.intent_id}"
    if int(request.fill.amount_out_filled or 0) != int(replay_input.amount_out):
        return f"swap amount_out_filled mismatch for intent_id={request.target.intent_id}"

    replay_amounts, err = _quote_swap_exact_out_replay(
        target=request.target,
        replay_input=replay_input,
        protocol_fee=request.protocol_fee,
    )
    if replay_amounts is None:
        return err or f"swap_exact_out kernel error for intent_id={request.target.intent_id}"

    err = _check_swap_exact_out_fill(
        fill=request.fill,
        target=request.target,
        replay_input=replay_input,
        replay_amounts=replay_amounts,
    )
    if err is not None:
        return err

    err = _apply_swap_replay(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )
    if err is not None:
        return err

    return _record_swap_replay_deltas(
        replay=replay,
        target=request.target,
        replay_amounts=replay_amounts,
        protocol_fee=request.protocol_fee,
    )


def _validate_replayed_payload(
    *,
    settlement: Settlement,
    replay: _ReplayContext,
    pre_state: _SettlementPreState,
) -> Tuple[bool, Optional[str]]:
    expected_balance = _aggregate_balance_deltas(replay.bal_deltas)
    expected_reserve = _aggregate_reserve_deltas(replay.res_deltas)
    expected_lp = _aggregate_lp_deltas(replay.lp_deltas)

    ok, err = _check_canonical_deltas(settlement)
    if not ok:
        return False, err

    if settlement.balance_deltas != expected_balance:
        return False, "balance_deltas mismatch vs replay"
    if settlement.reserve_deltas != expected_reserve:
        return False, "reserve_deltas mismatch vs replay"
    if settlement.lp_deltas != expected_lp:
        return False, "lp_deltas mismatch vs replay"

    got_events_norm = settlement.events or []
    if got_events_norm != replay.expected_events:
        return False, "events mismatch vs replay"

    # Defense-in-depth: ensure basic conservation/non-negativity in addition to replay checks.
    # This is essential when a fill type does not touch pool reserves (e.g. COW_NETTED),
    # where conservation must be enforced globally across balance deltas.
    ok_legacy, err_legacy = validate_settlement_legacy(
        settlement=settlement,
        pre_balances=pre_state.balances,
        pre_pools=pre_state.pools,
        pre_lp_balances=pre_state.lp_balances,
    )
    if not ok_legacy:
        return False, f"legacy validation failed: {err_legacy}"

    return True, None


def _replay_included_intents(env: _IntentReplayEnvironment) -> Tuple[bool, Optional[str]]:
    for intent_id, action in env.request.settlement.included_intents:
        err = _replay_included_intent(intent_id=intent_id, action=action, env=env)
        if err is not None:
            return False, err
    return True, None


def _replay_included_intent(
    *,
    intent_id: str,
    action: FillAction,
    env: _IntentReplayEnvironment,
) -> Optional[str]:
    intent = env.settlement_index.intents_by_id[intent_id]
    quote_binding_error = _validate_quote_binding_transport(
        intent,
        allow_snapshot_bound_quote_bindings=env.request.allow_snapshot_bound_quote_bindings,
    )
    if quote_binding_error is not None:
        return quote_binding_error
    if action == FillAction.REJECT:
        return None

    fill = env.settlement_index.fill_by_id[intent_id]
    recipient: PubKey = intent.get_field("recipient", intent.sender_pubkey)
    if not isinstance(recipient, str) or not recipient:
        return f"invalid recipient for intent_id={intent_id}"

    if intent.kind == IntentKind.CREATE_POOL:
        return _replay_create_pool_fill(intent=intent, fill=fill, replay=env.replay)

    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        return f"missing pool_id for intent_id={intent_id}"
    if pool_id not in env.replay.pools:
        return f"pool not found for intent_id={intent_id}: {pool_id}"

    pool_target = _PoolReplayTarget(pool_id=pool_id, pool=env.replay.pools[pool_id], recipient=recipient)
    return _replay_pool_intent(
        request=_PoolIntentReplayRequest(
            intent=intent,
            fill=fill,
            pool_target=pool_target,
            quote_pool_fp=intent.get_field("quote_pool_fingerprint"),
            env=env,
        ),
    )


def _replay_pool_intent(*, request: _PoolIntentReplayRequest) -> Optional[str]:
    if request.intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return _replay_swap_intent(request=request)
    if request.intent.kind == IntentKind.ADD_LIQUIDITY:
        return _replay_add_liquidity_fill(
            intent=request.intent,
            fill=request.fill,
            target=request.pool_target,
            replay=request.env.replay,
        )
    if request.intent.kind == IntentKind.REMOVE_LIQUIDITY:
        return _replay_remove_liquidity_fill(
            intent=request.intent,
            fill=request.fill,
            target=request.pool_target,
            replay=request.env.replay,
        )
    return f"unsupported intent kind for strong validation: {request.intent.kind}"


def _replay_swap_intent(*, request: _PoolIntentReplayRequest) -> Optional[str]:
    swap_target, err = _build_swap_replay_target(
        intent=request.intent,
        target=request.pool_target,
        quote_pool_fp=request.quote_pool_fp,
    )
    if swap_target is None:
        return err or f"invalid asset_in/out for intent_id={request.intent.intent_id}"

    if request.fill.reason == "COW_NETTED":
        return _replay_cow_netted_fill(
            request=_CowNettingReplayRequest(
                intent=request.intent,
                fill=request.fill,
                target=swap_target,
                allow_cow_netting=request.env.request.allow_cow_netting,
            ),
            replay=request.env.replay,
        )

    err = _check_swap_reserve_witness(fill=request.fill, target=swap_target, mode=request.env.request.mode)
    if err is not None:
        return err
    swap_request = _SwapReplayRequest(
        intent=request.intent,
        fill=request.fill,
        target=swap_target,
        protocol_fee=request.env.protocol_fee,
    )
    if request.intent.kind == IntentKind.SWAP_EXACT_IN:
        return _replay_swap_exact_in_fill(request=swap_request, replay=request.env.replay)
    return _replay_swap_exact_out_fill(request=swap_request, replay=request.env.replay)


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
        request = _StrongValidationRequest(
            settlement=settlement,
            intents=intents,
            pre_state=_SettlementPreState(
                balances=pre_balances,
                pools=pre_pools,
                lp_balances=pre_lp_balances,
            ),
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )
        return _validate_settlement_strong_impl(request=request)
    except _FAIL_CLOSED_VALIDATOR_ERRORS as exc:
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
    request: _StrongValidationRequest,
) -> Tuple[bool, Optional[str]]:
    """
    Strong settlement validation.

    This is intended to be used in `dex.step` as a fail-closed acceptance gate.
    """
    if request.mode not in _VALIDATION_MODES:
        return False, f"unsupported validation mode: {request.mode!r}"
    if not is_strict_int(request.protocol_fee_share_bps) or not (0 <= request.protocol_fee_share_bps <= 10000):
        return False, "protocol_fee_share_bps must be an int in [0, 10000]"
    if request.protocol_fee_share_bps > 0 and not request.protocol_fee_recipient_pubkey:
        return False, "protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0"

    settlement_index, err_index = _build_settlement_index(
        settlement=request.settlement,
        intents=request.intents,
    )
    if settlement_index is None:
        return False, err_index or "settlement index construction failed"

    ok_cow, err_cow = _validate_cow_pair_index(
        settlement=request.settlement,
        intents_by_id=settlement_index.intents_by_id,
        fill_by_id=settlement_index.fill_by_id,
        allow_cow_netting=request.allow_cow_netting,
    )
    if not ok_cow:
        return False, err_cow

    # Replay state (pure local copies).
    replay = _build_replay_context(
        pre_balances=request.pre_state.balances,
        pre_pools=request.pre_state.pools,
        pre_lp_balances=request.pre_state.lp_balances,
    )
    env = _IntentReplayEnvironment(
        request=request,
        settlement_index=settlement_index,
        replay=replay,
        protocol_fee=_ProtocolFeeReplayConfig(
            share_bps=int(request.protocol_fee_share_bps),
            recipient_pubkey=request.protocol_fee_recipient_pubkey,
        ),
    )
    ok_replay, err_replay = _replay_included_intents(env)
    if not ok_replay:
        return False, err_replay

    return _validate_replayed_payload(
        settlement=request.settlement,
        replay=replay,
        pre_state=request.pre_state,
    )


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


def _check_unique_sorted_delta_keys(keys: List[Tuple], what: str) -> Tuple[bool, Optional[str]]:
    if keys != sorted(keys):
        return False, f"{what} not sorted canonically"
    if len(keys) != len(set(keys)):
        return False, f"{what} contains duplicate keys"
    return True, None


def _check_canonical_balance_deltas(deltas: List[BalanceDelta]) -> Tuple[bool, Optional[str]]:
    bal_keys: List[Tuple[PubKey, AssetId]] = []
    for balance_delta in deltas:
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
    return _check_unique_sorted_delta_keys(bal_keys, "balance_deltas")


def _check_canonical_reserve_deltas(deltas: List[ReserveDelta]) -> Tuple[bool, Optional[str]]:
    res_keys: List[Tuple[str, AssetId]] = []
    for reserve_delta in deltas:
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
    return _check_unique_sorted_delta_keys(res_keys, "reserve_deltas")


def _check_canonical_lp_deltas(deltas: List[LPDelta]) -> Tuple[bool, Optional[str]]:
    lp_keys: List[Tuple[PubKey, str]] = []
    for lp_delta in deltas:
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
    return _check_unique_sorted_delta_keys(lp_keys, "lp_deltas")


def _check_canonical_deltas(settlement: Settlement) -> Tuple[bool, Optional[str]]:
    # Ensure deltas are canonical (one entry per key, sorted, and with non-negative fields).
    ok, err = _check_canonical_balance_deltas(settlement.balance_deltas)
    if not ok:
        return ok, err
    ok, err = _check_canonical_reserve_deltas(settlement.reserve_deltas)
    if not ok:
        return ok, err
    ok, err = _check_canonical_lp_deltas(settlement.lp_deltas)
    if not ok:
        return ok, err
    return True, None
