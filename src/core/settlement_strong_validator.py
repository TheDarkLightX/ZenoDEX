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
from typing import Any, Callable, Dict, List, Optional, Tuple, cast

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
# Inner replay catches are for malformed certificates and bounded arithmetic
# rejects. Unexpected implementation faults fall through to the public
# fail-closed crash wrapper with their exception class preserved.
_STRONG_REPLAY_DOMAIN_ERRORS = (ArithmeticError, TypeError, ValueError)


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
    quote_receipt_hash: object
    quote_pool_fingerprint: object
    quote_receipt_leg_index: object


def _quote_binding_fields(intent: Intent) -> _QuoteBindingFields:
    return _QuoteBindingFields(
        quote_receipt_hash=intent.get_field("quote_receipt_hash"),
        quote_pool_fingerprint=intent.get_field("quote_pool_fingerprint"),
        quote_receipt_leg_index=intent.get_field("quote_receipt_leg_index"),
    )


def _has_quote_binding(binding: _QuoteBindingFields) -> bool:
    return (
        binding.quote_receipt_hash is not None
        or binding.quote_pool_fingerprint is not None
        or binding.quote_receipt_leg_index is not None
    )


def _quote_transport_metadata_error(intent: Intent) -> str:
    return _quote_binding_error(
        "quote receipt transport metadata requires validated engine witness",
        **_quote_binding_context(intent),
        guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
    )


def _validate_quote_leg_index(intent: Intent, quote_leg_index: object) -> Optional[str]:
    if quote_leg_index is None:
        return None
    if not is_strict_int(quote_leg_index) or int(quote_leg_index) < 0:
        return _quote_binding_error("invalid quote_receipt_leg_index", **_quote_binding_context(intent))
    return _quote_transport_metadata_error(intent)


def _validate_quote_receipt_hash(intent: Intent, quote_receipt_hash: object) -> Optional[str]:
    if quote_receipt_hash is None:
        return None
    if not isinstance(quote_receipt_hash, str) or not quote_receipt_hash:
        return _quote_binding_error("invalid quote_receipt_hash", **_quote_binding_context(intent))
    return _quote_transport_metadata_error(intent)


def _validate_quote_pool_fingerprint(
    intent: Intent,
    *,
    quote_pool_fingerprint: object,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    if quote_pool_fingerprint is None:
        return None
    if not isinstance(quote_pool_fingerprint, str) or not quote_pool_fingerprint:
        return _quote_binding_error("missing quote_pool_fingerprint", **_quote_binding_context(intent))
    if not allow_snapshot_bound_quote_bindings:
        return _quote_binding_error(
            "quote receipt snapshot binding requires validated engine witness",
            **_quote_binding_context(intent),
            guidance="only pass sanitized quote_pool_fingerprint through the validated engine path",
        )
    return None


def _validate_quote_binding_for_intent(
    intent: Intent,
    *,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    binding = _quote_binding_fields(intent)
    if _has_quote_binding(binding) and intent.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return _quote_binding_error(
            "quote receipt binding only supported for swap intents",
            **_quote_binding_context(intent),
            intent_kind=intent.kind.value,
        )
    for err in (
        _validate_quote_leg_index(intent, binding.quote_receipt_leg_index),
        _validate_quote_receipt_hash(intent, binding.quote_receipt_hash),
        _validate_quote_pool_fingerprint(
            intent,
            quote_pool_fingerprint=binding.quote_pool_fingerprint,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        ),
    ):
        if err is not None:
            return err
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
class _CowIntentFields:
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _CreatePoolFields:
    asset0: AssetId
    asset1: AssetId
    fee_bps: int
    amount0: int
    amount1: int
    created_at: int
    curve_tag: Any
    curve_params: Any


@dataclass(frozen=True)
class _CreatePoolRawFields:
    asset0: Any
    asset1: Any
    fee_bps: Any
    amount0: Any
    amount1: Any
    created_at: Any
    curve_tag: Any
    curve_params: Any


@dataclass(frozen=True)
class _CreatePoolNumericFields:
    fee_bps: int
    amount0: int
    amount1: int
    created_at: int


@dataclass(frozen=True)
class _CreatePoolArtifacts:
    pool_id: str
    created_pool: PoolState
    lp_minted: int


@dataclass(frozen=True)
class _CreatePoolReplayPlan:
    fields: _CreatePoolFields
    artifacts: _CreatePoolArtifacts


@dataclass(frozen=True)
class _AddLiquidityFields:
    amount0_desired: int
    amount1_desired: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _LiquidityAmounts:
    amount0: int
    amount1: int
    lp_minted: int


@dataclass(frozen=True)
class _RemoveLiquidityFields:
    lp_amount: int
    amount0_min: int
    amount1_min: int


@dataclass(frozen=True)
class _RemoveLiquidityAmounts:
    amount0_out: int
    amount1_out: int
    lp_burned: int


@dataclass(frozen=True)
class _SwapReplayContext:
    asset_in: AssetId
    asset_out: AssetId
    reserve_in: int
    reserve_out: int
    dir_is_0_to_1: bool


@dataclass(frozen=True)
class _SwapExactInFields:
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _SwapKernelResult:
    amount_in: int
    amount_out: int
    new_reserve_in: int
    new_reserve_out: int
    protocol_fee: int


@dataclass(frozen=True)
class _FillAmounts:
    amount_in_filled: int
    amount_out_filled: int
    fee_paid: int
    protocol_fee_paid: int
    amount0_used: int
    amount1_used: int
    lp_minted: int
    amount0_out: int
    amount1_out: int
    lp_burned: int
    reserve_in_before: int
    reserve_out_before: int


@dataclass(frozen=True)
class _SettlementIntentIndex:
    intents_by_id: Dict[str, Intent]
    fill_by_id: Dict[str, Fill]


_FILL_AMOUNT_FIELDS = (
    "amount_in_filled",
    "amount_out_filled",
    "fee_paid",
    "protocol_fee_paid",
    "amount0_used",
    "amount1_used",
    "lp_minted",
    "amount0_out",
    "amount1_out",
    "lp_burned",
    "reserve_in_before",
    "reserve_out_before",
)


def _validate_fill_amount_fields(fill: Fill, intent_id: str) -> Tuple[bool, Optional[_FillAmounts], Optional[str]]:
    """Reject untrusted fill amounts that rely on Python coercion.

    Strong settlement validation replays certificate fields from an untrusted
    proposal. Numeric-looking strings and bools must not satisfy the replay by
    passing through ``int(...)`` at the comparison site.
    """
    values: dict[str, int] = {}
    for field_name in _FILL_AMOUNT_FIELDS:
        value = getattr(fill, field_name)
        if value is None:
            values[field_name] = 0
            continue
        if not is_strict_int(value) or int(value) < 0:
            return False, None, f"invalid fill.{field_name} for intent_id={intent_id}"
        values[field_name] = int(value)
    return True, _FillAmounts(**values), None


def _validate_strong_config(
    *,
    mode: str,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> Optional[str]:
    if mode not in _VALIDATION_MODES:
        return f"unsupported validation mode: {mode!r}"
    if not is_strict_int(protocol_fee_share_bps) or not (0 <= protocol_fee_share_bps <= 10000):
        return "protocol_fee_share_bps must be an int in [0, 10000]"
    if protocol_fee_share_bps > 0 and not protocol_fee_recipient_pubkey:
        return "protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0"
    return None


def _validate_cow_fill_shape(fill: Fill, intent_id: str) -> Tuple[bool, Optional[_FillAmounts], Optional[str]]:
    ok_amounts, amounts, err_amounts = _validate_fill_amount_fields(fill, intent_id)
    if not ok_amounts:
        return False, None, err_amounts
    if amounts is None:
        return False, None, f"invalid fill amounts for intent_id={intent_id}"
    if fill.action != FillAction.FILL:
        return False, None, f"COW_NETTED requires filled action: intent_id={intent_id}"
    return True, amounts, None


def _validate_cow_pool_id(intent_id: str, intent: Intent) -> Tuple[bool, Optional[str], Optional[str]]:
    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        return False, None, f"missing pool_id for intent_id={intent_id}"
    return True, pool_id, None


def _validate_cow_asset_pair(intent_id: str, intent: Intent) -> Tuple[bool, Optional[Tuple[AssetId, AssetId]], Optional[str]]:
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return False, None, f"invalid asset_in/out for intent_id={intent_id}"
    return True, (asset_in, asset_out), None


def _validate_cow_intent_amounts(intent_id: str, intent: Intent) -> Tuple[bool, Optional[Tuple[int, int]], Optional[str]]:
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not is_strict_int(amount_in) or int(amount_in) <= 0:
        return False, None, f"invalid amount_in for intent_id={intent_id}"
    if not is_strict_int(min_out) or int(min_out) < 0:
        return False, None, f"invalid min_amount_out for intent_id={intent_id}"
    return True, (int(amount_in), int(min_out)), None


def _validate_cow_intent_fields(
    *,
    intent_id: str,
    intent: Intent,
) -> Tuple[bool, Optional[_CowIntentFields], Optional[str]]:
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return False, None, f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}"
    ok_pool, pool_id, err_pool = _validate_cow_pool_id(intent_id, intent)
    if not ok_pool:
        return False, None, err_pool
    ok_assets, assets, err_assets = _validate_cow_asset_pair(intent_id, intent)
    if not ok_assets:
        return False, None, err_assets
    ok_amounts, amounts, err_amounts = _validate_cow_intent_amounts(intent_id, intent)
    if not ok_amounts:
        return False, None, err_amounts
    if pool_id is None or assets is None or amounts is None:
        return False, None, f"invalid COW_NETTED intent fields for intent_id={intent_id}"
    asset_in, asset_out = assets
    amount_in, min_out = amounts
    return True, _CowIntentFields(pool_id, asset_in, asset_out, amount_in, min_out), None


def _validated_cow_pair_entry(
    *,
    intent_id: str,
    intent: Intent,
    fill: Fill,
) -> Tuple[bool, Optional[_CowPairEntry], Optional[str]]:
    ok_amounts, amounts, err_amounts = _validate_cow_fill_shape(fill, intent_id)
    if not ok_amounts:
        return False, None, err_amounts
    ok_fields, fields, err_fields = _validate_cow_intent_fields(intent_id=intent_id, intent=intent)
    if not ok_fields:
        return False, None, err_fields
    if amounts is None or fields is None:
        return False, None, f"invalid COW_NETTED entry for intent_id={intent_id}"
    if amounts.fee_paid != 0:
        return False, None, f"COW_NETTED fee_paid must be 0: intent_id={intent_id}"
    if amounts.amount_in_filled != fields.amount_in:
        return False, None, f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}"
    out_amt = amounts.amount_out_filled
    if out_amt < fields.min_out:
        return False, None, f"COW_NETTED slippage: intent_id={intent_id}"
    return (
        True,
        _CowPairEntry(
            intent_id=intent_id,
            pool_id=fields.pool_id,
            asset_in=fields.asset_in,
            asset_out=fields.asset_out,
            amount_in_filled=amounts.amount_in_filled,
            amount_out_filled=out_amt,
        ),
        None,
    )


def _cow_reciprocal_matches(intent_id: str, entry: _CowPairEntry, entries: Dict[str, _CowPairEntry]) -> List[str]:
    return [
        other_id
        for other_id, other in entries.items()
        if other_id != intent_id
        and other.pool_id == entry.pool_id
        and other.asset_in == entry.asset_out
        and other.asset_out == entry.asset_in
        and other.amount_in_filled == entry.amount_out_filled
        and other.amount_out_filled == entry.amount_in_filled
    ]


def _validate_cow_reciprocal_pairs(entries: Dict[str, _CowPairEntry]) -> Tuple[bool, Optional[str]]:
    pair_for: Dict[str, str] = {}
    for intent_id, entry in entries.items():
        matches = _cow_reciprocal_matches(intent_id, entry, entries)
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

    entries: Dict[str, _CowPairEntry] = {}
    for intent_id in cow_ids:
        ok, entry, err = _validated_cow_pair_entry(
            intent_id=intent_id,
            intent=intents_by_id[intent_id],
            fill=fill_by_id[intent_id],
        )
        if not ok:
            return False, err
        if entry is None:
            return False, f"invalid COW_NETTED entry for intent_id={intent_id}"
        entries[intent_id] = entry
    return _validate_cow_reciprocal_pairs(entries)


def _build_input_intent_index(intents: List[Intent]) -> Tuple[bool, Optional[Dict[str, Intent]], Optional[str]]:
    intent_ids = [it.intent_id for it in intents]
    if len(intent_ids) != len(set(intent_ids)):
        return False, None, "duplicate intent_id in input intents"
    return True, {it.intent_id: it for it in intents}, None


def _validate_included_intent_ids(
    *,
    included_ids: List[str],
    intent_ids: List[str],
) -> Optional[str]:
    if set(included_ids) != set(intent_ids):
        missing = sorted(set(intent_ids) - set(included_ids))
        extra = sorted(set(included_ids) - set(intent_ids))
        return f"settlement included_intents mismatch: missing={missing} extra={extra}"
    if len(included_ids) != len(set(included_ids)):
        return "settlement included_intents contains duplicate intent_id entries"
    return None


def _build_fill_index(
    *,
    settlement: Settlement,
    intent_ids: List[str],
) -> Tuple[bool, Optional[Dict[str, Fill]], Optional[str]]:
    fill_ids = [fill.intent_id for fill in settlement.fills]
    if len(fill_ids) != len(set(fill_ids)):
        return False, None, "settlement fills contains duplicate intent_id entries"
    extra_fill_ids = sorted(set(fill_ids) - set(intent_ids))
    if extra_fill_ids:
        return False, None, f"settlement fills contains intent_ids not in input intents: {extra_fill_ids}"
    return True, {fill.intent_id: fill for fill in settlement.fills}, None


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


def _build_validated_intent_index(
    *,
    settlement: Settlement,
    intents: List[Intent],
    allow_cow_netting: bool,
) -> Tuple[bool, Optional[_SettlementIntentIndex], Optional[str]]:
    ok_intents, intents_by_id, err_intents = _build_input_intent_index(intents)
    if not ok_intents:
        return False, None, err_intents
    if intents_by_id is None:
        return False, None, "validated input intent index missing"
    intent_ids = list(intents_by_id)

    included_ids = [intent_id for intent_id, _action in settlement.included_intents]
    err_included = _validate_included_intent_ids(included_ids=included_ids, intent_ids=intent_ids)
    if err_included is not None:
        return False, None, err_included

    ok_fills, fill_by_id, err_fills = _build_fill_index(settlement=settlement, intent_ids=intent_ids)
    if not ok_fills:
        return False, None, err_fills
    if fill_by_id is None:
        return False, None, "validated settlement fill index missing"

    err_actions = _validate_included_fill_actions(settlement=settlement, fill_by_id=fill_by_id)
    if err_actions is not None:
        return False, None, err_actions

    ok_cow, err_cow = _validate_cow_pair_index(
        settlement=settlement,
        intents_by_id=intents_by_id,
        fill_by_id=fill_by_id,
        allow_cow_netting=allow_cow_netting,
    )
    if not ok_cow:
        return False, None, err_cow

    return True, _SettlementIntentIndex(intents_by_id=intents_by_id, fill_by_id=fill_by_id), None


def _create_pool_raw_fields(intent: Intent) -> _CreatePoolRawFields:
    return _CreatePoolRawFields(
        asset0=intent.get_field("asset0"),
        asset1=intent.get_field("asset1"),
        fee_bps=intent.get_field("fee_bps"),
        amount0=intent.get_field("amount0"),
        amount1=intent.get_field("amount1"),
        created_at=intent.get_field("created_at", 0),
        curve_tag=intent.get_field("curve_tag", None),
        curve_params=intent.get_field("curve_params", None),
    )


def _create_pool_missing_fields_error(intent_id: str, raw: _CreatePoolRawFields) -> Optional[str]:
    if any(v is None for v in (raw.asset0, raw.asset1, raw.fee_bps, raw.amount0, raw.amount1)):
        return f"missing CREATE_POOL fields for intent_id={intent_id}"
    return None


def _parse_create_pool_assets(
    *, intent_id: str, raw: _CreatePoolRawFields
) -> Tuple[Optional[Tuple[AssetId, AssetId]], Optional[str]]:
    if not isinstance(raw.asset0, str) or not isinstance(raw.asset1, str):
        return None, f"invalid CREATE_POOL asset ids for intent_id={intent_id}"
    return (raw.asset0, raw.asset1), None


def _parse_create_pool_fee_bps(*, intent_id: str, raw_fee_bps: Any) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(raw_fee_bps) or not (0 <= raw_fee_bps <= 10000):
        return None, f"invalid CREATE_POOL fee_bps for intent_id={intent_id}"
    return int(raw_fee_bps), None


def _parse_create_pool_positive_amount(
    *, intent_id: str, field_name: str, raw_amount: Any
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(raw_amount) or raw_amount <= 0:
        return None, f"invalid CREATE_POOL {field_name} for intent_id={intent_id}"
    return int(raw_amount), None


def _parse_create_pool_created_at(*, intent_id: str, raw_created_at: Any) -> Tuple[Optional[int], Optional[str]]:
    if raw_created_at is not None and (not is_strict_int(raw_created_at) or raw_created_at < 0):
        return None, f"invalid CREATE_POOL created_at for intent_id={intent_id}"
    return (0 if raw_created_at is None else int(raw_created_at)), None


def _parse_create_pool_numeric_fields(
    *, intent_id: str, raw: _CreatePoolRawFields
) -> Tuple[Optional[_CreatePoolNumericFields], Optional[str]]:
    parsed = (
        ("fee_bps", _parse_create_pool_fee_bps(intent_id=intent_id, raw_fee_bps=raw.fee_bps)),
        (
            "amount0",
            _parse_create_pool_positive_amount(intent_id=intent_id, field_name="amount0", raw_amount=raw.amount0),
        ),
        (
            "amount1",
            _parse_create_pool_positive_amount(intent_id=intent_id, field_name="amount1", raw_amount=raw.amount1),
        ),
        (
            "created_at",
            _parse_create_pool_created_at(intent_id=intent_id, raw_created_at=raw.created_at),
        ),
    )
    values: dict[str, int] = {}
    for name, (value, err) in parsed:
        if err is not None:
            return None, err
        if value is None:
            return None, f"invalid CREATE_POOL {name} for intent_id={intent_id}"
        values[name] = value
    return _CreatePoolNumericFields(**values), None


def _validate_create_pool_fields(intent: Intent) -> Tuple[Optional[_CreatePoolFields], Optional[str]]:
    intent_id = intent.intent_id
    raw = _create_pool_raw_fields(intent)
    missing_err = _create_pool_missing_fields_error(intent_id, raw)
    if missing_err is not None:
        return None, missing_err
    assets, assets_err = _parse_create_pool_assets(intent_id=intent_id, raw=raw)
    if assets_err is not None:
        return None, assets_err
    numeric, numeric_err = _parse_create_pool_numeric_fields(intent_id=intent_id, raw=raw)
    if numeric_err is not None:
        return None, numeric_err
    asset0, asset1 = cast(Tuple[AssetId, AssetId], assets)
    numeric_fields = cast(_CreatePoolNumericFields, numeric)
    return _CreatePoolFields(
        asset0=asset0,
        asset1=asset1,
        fee_bps=numeric_fields.fee_bps,
        amount0=numeric_fields.amount0,
        amount1=numeric_fields.amount1,
        created_at=numeric_fields.created_at,
        curve_tag=raw.curve_tag,
        curve_params=raw.curve_params,
    ), None


def _create_pool_fields_or_error(intent: Intent) -> Tuple[Optional[_CreatePoolFields], Optional[str]]:
    fields, err = _validate_create_pool_fields(intent)
    if err is not None:
        return None, err
    if fields is None:
        return None, f"invalid CREATE_POOL fields for intent_id={intent.intent_id}"
    return fields, None


def _create_pool_artifacts_or_error(
    *, intent_id: str, sender: PubKey, fields: _CreatePoolFields
) -> Tuple[Optional[_CreatePoolArtifacts], Optional[str]]:
    ok, artifacts, err = _compute_create_pool_artifacts(intent_id=intent_id, sender=sender, fields=fields)
    if not ok:
        return None, err
    if artifacts is None:
        return None, f"missing CREATE_POOL artifacts for intent_id={intent_id}"
    return artifacts, None


def _validate_create_pool_plan_bindings(
    *,
    intent_id: str,
    amounts: _FillAmounts,
    pools: Dict[str, PoolState],
    fields: _CreatePoolFields,
    artifacts: _CreatePoolArtifacts,
) -> Optional[str]:
    if artifacts.pool_id in pools:
        return f"CREATE_POOL duplicates existing pool_id={artifacts.pool_id}"
    return _validate_create_pool_fill_amounts(
        intent_id=intent_id,
        amounts=amounts,
        fields=fields,
        artifacts=artifacts,
    )


def _prepare_create_pool_replay_plan(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    pools: Dict[str, PoolState],
) -> Tuple[Optional[_CreatePoolReplayPlan], Optional[str]]:
    intent_id = intent.intent_id
    fields, fields_err = _create_pool_fields_or_error(intent)
    if fields_err is not None:
        return None, fields_err
    fields_value = cast(_CreatePoolFields, fields)
    artifacts, artifacts_err = _create_pool_artifacts_or_error(
        intent_id=intent_id,
        sender=intent.sender_pubkey,
        fields=fields_value,
    )
    if artifacts_err is not None:
        return None, artifacts_err
    artifacts_value = cast(_CreatePoolArtifacts, artifacts)
    plan_err = _validate_create_pool_plan_bindings(
        intent_id=intent_id,
        amounts=amounts,
        pools=pools,
        fields=fields_value,
        artifacts=artifacts_value,
    )
    if plan_err is not None:
        return None, plan_err
    return _CreatePoolReplayPlan(fields=fields_value, artifacts=artifacts_value), None


def _compute_create_pool_artifacts(
    *,
    intent_id: str,
    sender: PubKey,
    fields: _CreatePoolFields,
) -> Tuple[bool, Optional[_CreatePoolArtifacts], Optional[str]]:
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
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return False, None, f"CREATE_POOL computation error for intent_id={intent_id}: {exc}"
    return True, _CreatePoolArtifacts(pool_id=pool_id, created_pool=created_pool, lp_minted=int(lp_minted)), None


def _validate_create_pool_fill_amounts(
    *,
    intent_id: str,
    amounts: _FillAmounts,
    fields: _CreatePoolFields,
    artifacts: _CreatePoolArtifacts,
) -> Optional[str]:
    if amounts.amount0_used != fields.amount0:
        return f"CREATE_POOL fill.amount0_used mismatch for intent_id={intent_id}"
    if amounts.amount1_used != fields.amount1:
        return f"CREATE_POOL fill.amount1_used mismatch for intent_id={intent_id}"
    if amounts.lp_minted != artifacts.lp_minted:
        return f"CREATE_POOL fill.lp_minted mismatch for intent_id={intent_id}"
    return None


def _apply_create_pool_state_effects(
    *,
    intent_id: str,
    sender: PubKey,
    fields: _CreatePoolFields,
    artifacts: _CreatePoolArtifacts,
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    lp: LPTable,
) -> Tuple[bool, Optional[str]]:
    try:
        balances.subtract(sender, fields.asset0, fields.amount0)
        balances.subtract(sender, fields.asset1, fields.amount1)
        lp.add(sender, artifacts.pool_id, artifacts.lp_minted)
        lp.add(LP_LOCK_PUBKEY, artifacts.pool_id, int(MIN_LP_LOCK))
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return False, f"CREATE_POOL balance/LP apply error for intent_id={intent_id}: {exc}"
    pools[artifacts.pool_id] = artifacts.created_pool
    return True, None


def _emit_create_pool_replay_effects(
    *,
    sender: PubKey,
    fields: _CreatePoolFields,
    artifacts: _CreatePoolArtifacts,
    expected_events: List[dict],
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
) -> None:
    pool_id = artifacts.pool_id
    created_pool = artifacts.created_pool
    expected_events.append(
        {
            "type": "CREATE_POOL",
            "pool_id": pool_id,
            "asset0": fields.asset0,
            "asset1": fields.asset1,
            "fee_bps": fields.fee_bps,
            "curve_tag": created_pool.curve_tag,
            "curve_params": created_pool.curve_params,
            "status": PoolStatus.ACTIVE.value,
            "created_at": int(created_pool.created_at),
        }
    )
    balance_deltas.append(BalanceDelta(pubkey=sender, asset=fields.asset0, delta_add=0, delta_sub=fields.amount0))
    balance_deltas.append(BalanceDelta(pubkey=sender, asset=fields.asset1, delta_add=0, delta_sub=fields.amount1))
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=fields.asset0, delta_add=fields.amount0, delta_sub=0))
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=fields.asset1, delta_add=fields.amount1, delta_sub=0))
    lp_deltas.append(LPDelta(pubkey=sender, pool_id=pool_id, delta_add=artifacts.lp_minted, delta_sub=0))
    lp_deltas.append(LPDelta(pubkey=LP_LOCK_PUBKEY, pool_id=pool_id, delta_add=int(MIN_LP_LOCK), delta_sub=0))


def _replay_create_pool_fill(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    pools: Dict[str, PoolState],
    balances: BalanceTable,
    lp: LPTable,
    expected_events: List[dict],
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    sender = intent.sender_pubkey
    plan, plan_err = _prepare_create_pool_replay_plan(intent=intent, amounts=amounts, pools=pools)
    if plan_err is not None:
        return False, plan_err
    if plan is None:
        return False, f"invalid CREATE_POOL replay plan for intent_id={intent_id}"
    ok_apply, err_apply = _apply_create_pool_state_effects(
        intent_id=intent_id,
        sender=sender,
        fields=plan.fields,
        artifacts=plan.artifacts,
        pools=pools,
        balances=balances,
        lp=lp,
    )
    if not ok_apply:
        return False, err_apply
    _emit_create_pool_replay_effects(
        sender=sender,
        fields=plan.fields,
        artifacts=plan.artifacts,
        expected_events=expected_events,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        lp_deltas=lp_deltas,
    )
    return True, None


def _parse_add_liquidity_int(
    *, intent_id: str, field_name: str, raw_value: Any, positive: bool
) -> Tuple[Optional[int], Optional[str]]:
    lower_bound = 1 if positive else 0
    if not is_strict_int(raw_value) or raw_value < lower_bound:
        return None, f"invalid {field_name} for intent_id={intent_id}"
    return int(raw_value), None


def _parse_add_liquidity_fields(intent: Intent) -> Tuple[Optional[_AddLiquidityFields], Optional[str]]:
    intent_id = intent.intent_id
    amount0_desired = intent.get_field("amount0_desired")
    amount1_desired = intent.get_field("amount1_desired")
    if any(v is None for v in (amount0_desired, amount1_desired)):
        return None, f"missing ADD_LIQUIDITY fields for intent_id={intent_id}"
    parsed = (
        (
            "amount0_desired",
            _parse_add_liquidity_int(
                intent_id=intent_id, field_name="amount0_desired", raw_value=amount0_desired, positive=True
            ),
        ),
        (
            "amount1_desired",
            _parse_add_liquidity_int(
                intent_id=intent_id, field_name="amount1_desired", raw_value=amount1_desired, positive=True
            ),
        ),
        (
            "amount0_min",
            _parse_add_liquidity_int(
                intent_id=intent_id,
                field_name="amount0_min",
                raw_value=intent.get_field("amount0_min", 0),
                positive=False,
            ),
        ),
        (
            "amount1_min",
            _parse_add_liquidity_int(
                intent_id=intent_id,
                field_name="amount1_min",
                raw_value=intent.get_field("amount1_min", 0),
                positive=False,
            ),
        ),
    )
    values: dict[str, int] = {}
    for name, (value, err) in parsed:
        if err is not None:
            return None, err
        values[name] = cast(int, value)
    return _AddLiquidityFields(**values), None


def _compute_add_liquidity_amounts(
    *, intent_id: str, pool: PoolState, fields: _AddLiquidityFields
) -> Tuple[Optional[_LiquidityAmounts], Optional[str]]:
    try:
        amount0_used, amount1_used, lp_minted = add_liquidity(
            pool_state=pool,
            amount0_desired=fields.amount0_desired,
            amount1_desired=fields.amount1_desired,
            amount0_min=fields.amount0_min,
            amount1_min=fields.amount1_min,
        )
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return None, f"ADD_LIQUIDITY computation error for intent_id={intent_id}: {exc}"
    return _LiquidityAmounts(amount0=int(amount0_used), amount1=int(amount1_used), lp_minted=int(lp_minted)), None


def _validate_add_liquidity_fill_amounts(
    *, intent_id: str, fill_amounts: _FillAmounts, computed: _LiquidityAmounts
) -> Optional[str]:
    if fill_amounts.amount0_used != computed.amount0:
        return f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={intent_id}"
    if fill_amounts.amount1_used != computed.amount1:
        return f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={intent_id}"
    if fill_amounts.lp_minted != computed.lp_minted:
        return f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={intent_id}"
    return None


def _apply_add_liquidity_state_effects(
    *,
    intent_id: str,
    sender: PubKey,
    recipient: PubKey,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    lp: LPTable,
    computed: _LiquidityAmounts,
) -> Tuple[bool, Optional[str]]:
    try:
        balances.subtract(sender, pool.asset0, computed.amount0)
        balances.subtract(sender, pool.asset1, computed.amount1)
        lp.add(recipient, pool_id, computed.lp_minted)
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return False, f"ADD_LIQUIDITY apply error for intent_id={intent_id}: {exc}"

    pool.reserve0 += computed.amount0
    pool.reserve1 += computed.amount1
    pool.lp_supply += computed.lp_minted
    return True, None


def _emit_add_liquidity_replay_effects(
    *,
    sender: PubKey,
    recipient: PubKey,
    pool_id: str,
    pool: PoolState,
    computed: _LiquidityAmounts,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
) -> None:
    balance_deltas.append(BalanceDelta(pubkey=sender, asset=pool.asset0, delta_add=0, delta_sub=computed.amount0))
    balance_deltas.append(BalanceDelta(pubkey=sender, asset=pool.asset1, delta_add=0, delta_sub=computed.amount1))
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=computed.amount0, delta_sub=0))
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset1, delta_add=computed.amount1, delta_sub=0))
    lp_deltas.append(LPDelta(pubkey=recipient, pool_id=pool_id, delta_add=computed.lp_minted, delta_sub=0))


def _prepare_add_liquidity_replay_amounts(
    *, intent: Intent, amounts: _FillAmounts, pool: PoolState
) -> Tuple[Optional[_LiquidityAmounts], Optional[str]]:
    intent_id = intent.intent_id
    fields, fields_err = _parse_add_liquidity_fields(intent)
    if fields_err is not None:
        return None, fields_err
    computed, computed_err = _compute_add_liquidity_amounts(
        intent_id=intent_id,
        pool=pool,
        fields=cast(_AddLiquidityFields, fields),
    )
    if computed_err is not None:
        return None, computed_err
    computed_value = cast(_LiquidityAmounts, computed)
    fill_err = _validate_add_liquidity_fill_amounts(
        intent_id=intent_id,
        fill_amounts=amounts,
        computed=computed_value,
    )
    if fill_err is not None:
        return None, fill_err
    return computed_value, None


def _replay_add_liquidity_fill(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    lp: LPTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    sender = intent.sender_pubkey
    if pool.status != PoolStatus.ACTIVE:
        return False, f"pool not active for intent_id={intent_id}: {pool.status}"
    computed, computed_err = _prepare_add_liquidity_replay_amounts(
        intent=intent,
        amounts=amounts,
        pool=pool,
    )
    if computed_err is not None:
        return False, computed_err
    computed_value = cast(_LiquidityAmounts, computed)
    ok_apply, err_apply = _apply_add_liquidity_state_effects(
        intent_id=intent_id,
        sender=sender,
        recipient=recipient,
        pool_id=pool_id,
        pool=pool,
        balances=balances,
        lp=lp,
        computed=computed_value,
    )
    if not ok_apply:
        return False, err_apply
    _emit_add_liquidity_replay_effects(
        sender=sender,
        recipient=recipient,
        pool_id=pool_id,
        pool=pool,
        computed=computed_value,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        lp_deltas=lp_deltas,
    )
    return True, None


def _parse_remove_liquidity_fields(intent: Intent) -> Tuple[Optional[_RemoveLiquidityFields], Optional[str]]:
    intent_id = intent.intent_id
    lp_amount = intent.get_field("lp_amount")
    if lp_amount is None:
        return None, f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent_id}"
    parsed = (
        (
            "lp_amount",
            _parse_add_liquidity_int(
                intent_id=intent_id,
                field_name="lp_amount",
                raw_value=lp_amount,
                positive=True,
            ),
        ),
        (
            "amount0_min",
            _parse_add_liquidity_int(
                intent_id=intent_id,
                field_name="amount0_min",
                raw_value=intent.get_field("amount0_min", 0),
                positive=False,
            ),
        ),
        (
            "amount1_min",
            _parse_add_liquidity_int(
                intent_id=intent_id,
                field_name="amount1_min",
                raw_value=intent.get_field("amount1_min", 0),
                positive=False,
            ),
        ),
    )
    values: dict[str, int] = {}
    for name, (value, err) in parsed:
        if err is not None:
            return None, err
        values[name] = cast(int, value)
    return _RemoveLiquidityFields(**values), None


def _compute_remove_liquidity_amounts(
    *, intent_id: str, pool: PoolState, fields: _RemoveLiquidityFields
) -> Tuple[Optional[_RemoveLiquidityAmounts], Optional[str]]:
    try:
        amount0_out, amount1_out = remove_liquidity(
            pool_state=pool,
            lp_amount=fields.lp_amount,
            amount0_min=fields.amount0_min,
            amount1_min=fields.amount1_min,
        )
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return None, f"REMOVE_LIQUIDITY computation error for intent_id={intent_id}: {exc}"
    return (
        _RemoveLiquidityAmounts(
            amount0_out=int(amount0_out),
            amount1_out=int(amount1_out),
            lp_burned=fields.lp_amount,
        ),
        None,
    )


def _validate_remove_liquidity_fill_amounts(
    *, intent_id: str, fill_amounts: _FillAmounts, computed: _RemoveLiquidityAmounts
) -> Optional[str]:
    if fill_amounts.lp_burned != computed.lp_burned:
        return f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={intent_id}"
    if fill_amounts.amount0_out != computed.amount0_out:
        return f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={intent_id}"
    if fill_amounts.amount1_out != computed.amount1_out:
        return f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={intent_id}"
    return None


def _prepare_remove_liquidity_replay_amounts(
    *, intent: Intent, amounts: _FillAmounts, pool: PoolState
) -> Tuple[Optional[_RemoveLiquidityAmounts], Optional[str]]:
    intent_id = intent.intent_id
    fields, fields_err = _parse_remove_liquidity_fields(intent)
    if fields_err is not None:
        return None, fields_err
    computed, computed_err = _compute_remove_liquidity_amounts(
        intent_id=intent_id,
        pool=pool,
        fields=cast(_RemoveLiquidityFields, fields),
    )
    if computed_err is not None:
        return None, computed_err
    computed_value = cast(_RemoveLiquidityAmounts, computed)
    fill_err = _validate_remove_liquidity_fill_amounts(
        intent_id=intent_id,
        fill_amounts=amounts,
        computed=computed_value,
    )
    if fill_err is not None:
        return None, fill_err
    return computed_value, None


def _apply_remove_liquidity_state_effects(
    *,
    intent_id: str,
    sender: PubKey,
    recipient: PubKey,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    lp: LPTable,
    computed: _RemoveLiquidityAmounts,
) -> Tuple[bool, Optional[str]]:
    try:
        lp.subtract(sender, pool_id, computed.lp_burned)
        balances.add(recipient, pool.asset0, computed.amount0_out)
        balances.add(recipient, pool.asset1, computed.amount1_out)
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return False, f"REMOVE_LIQUIDITY apply error for intent_id={intent_id}: {exc}"

    pool.reserve0 -= computed.amount0_out
    pool.reserve1 -= computed.amount1_out
    pool.lp_supply -= computed.lp_burned
    return True, None


def _emit_remove_liquidity_replay_effects(
    *,
    sender: PubKey,
    recipient: PubKey,
    pool_id: str,
    pool: PoolState,
    computed: _RemoveLiquidityAmounts,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
) -> None:
    lp_deltas.append(LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=computed.lp_burned))
    balance_deltas.append(BalanceDelta(pubkey=recipient, asset=pool.asset0, delta_add=computed.amount0_out, delta_sub=0))
    balance_deltas.append(BalanceDelta(pubkey=recipient, asset=pool.asset1, delta_add=computed.amount1_out, delta_sub=0))
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=0, delta_sub=computed.amount0_out))
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=pool.asset1, delta_add=0, delta_sub=computed.amount1_out))


def _replay_remove_liquidity_fill(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    lp: LPTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    sender = intent.sender_pubkey
    if pool.status != PoolStatus.ACTIVE:
        return False, f"pool not active for intent_id={intent_id}: {pool.status}"
    computed, computed_err = _prepare_remove_liquidity_replay_amounts(intent=intent, amounts=amounts, pool=pool)
    if computed_err is not None:
        return False, computed_err
    computed_value = cast(_RemoveLiquidityAmounts, computed)
    ok_apply, err_apply = _apply_remove_liquidity_state_effects(
        intent_id=intent_id,
        sender=sender,
        recipient=recipient,
        pool_id=pool_id,
        pool=pool,
        balances=balances,
        lp=lp,
        computed=computed_value,
    )
    if not ok_apply:
        return False, err_apply
    _emit_remove_liquidity_replay_effects(
        sender=sender,
        recipient=recipient,
        pool_id=pool_id,
        pool=pool,
        computed=computed_value,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        lp_deltas=lp_deltas,
    )
    return True, None


def _parse_swap_assets(intent: Intent) -> Tuple[Optional[Tuple[AssetId, AssetId]], Optional[str]]:
    intent_id = intent.intent_id
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return None, f"invalid asset_in/out for intent_id={intent_id}"
    return (asset_in, asset_out), None


def _validate_swap_pool_membership(
    *, intent_id: str, asset_in: AssetId, asset_out: AssetId, pool: PoolState
) -> Optional[str]:
    if pool.status != PoolStatus.ACTIVE:
        return f"pool not active for intent_id={intent_id}: {pool.status}"
    if {asset_in, asset_out} != {pool.asset0, pool.asset1} or asset_in == asset_out:
        return f"swap asset mismatch for intent_id={intent_id}"
    return None


def _validate_quote_pool_snapshot(intent: Intent, pool: PoolState, quote_pool_fp: Optional[str]) -> Optional[str]:
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


def _swap_replay_direction_context(*, asset_in: AssetId, asset_out: AssetId, pool: PoolState) -> _SwapReplayContext:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return _SwapReplayContext(
            asset_in=asset_in,
            asset_out=asset_out,
            reserve_in=int(pool.reserve0),
            reserve_out=int(pool.reserve1),
            dir_is_0_to_1=True,
        )
    return _SwapReplayContext(
        asset_in=asset_in,
        asset_out=asset_out,
        reserve_in=int(pool.reserve1),
        reserve_out=int(pool.reserve0),
        dir_is_0_to_1=False,
    )


def _prepare_swap_replay_context(
    *, intent: Intent, pool: PoolState, quote_pool_fp: Optional[str]
) -> Tuple[Optional[_SwapReplayContext], Optional[str]]:
    intent_id = intent.intent_id
    assets, assets_err = _parse_swap_assets(intent)
    if assets_err is not None:
        return None, assets_err
    asset_in, asset_out = cast(Tuple[AssetId, AssetId], assets)
    membership_err = _validate_swap_pool_membership(
        intent_id=intent_id,
        asset_in=asset_in,
        asset_out=asset_out,
        pool=pool,
    )
    if membership_err is not None:
        return None, membership_err
    quote_err = _validate_quote_pool_snapshot(intent, pool, quote_pool_fp)
    if quote_err is not None:
        return None, quote_err
    return _swap_replay_direction_context(asset_in=asset_in, asset_out=asset_out, pool=pool), None


def _swap_witness_reserves_missing(fill: Fill) -> bool:
    return fill.reserve_in_before is None or fill.reserve_out_before is None


def _swap_witness_reserves_mismatch(amounts: _FillAmounts, context: _SwapReplayContext) -> bool:
    return amounts.reserve_in_before != context.reserve_in or amounts.reserve_out_before != context.reserve_out


def _validate_swap_witness_reserves(
    *, intent_id: str, fill: Fill, amounts: _FillAmounts, context: _SwapReplayContext, mode: str
) -> Optional[str]:
    if mode != _MODE_STRONG_PROOF_CARRYING:
        return None
    if _swap_witness_reserves_missing(fill):
        return f"missing swap witness reserves for intent_id={intent_id}"
    if _swap_witness_reserves_mismatch(amounts, context):
        return f"swap witness reserve mismatch for intent_id={intent_id}"
    return None


def _replay_swap_fill(
    *,
    intent: Intent,
    fill: Fill,
    amounts: _FillAmounts,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    mode: str,
    allow_cow_netting: bool,
    quote_pool_fp: Optional[str],
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    context, context_err = _prepare_swap_replay_context(intent=intent, pool=pool, quote_pool_fp=quote_pool_fp)
    if context_err is not None:
        return False, context_err
    context_value = cast(_SwapReplayContext, context)

    if fill.reason == "COW_NETTED":
        return _replay_cow_netted_swap_fill(
            intent=intent,
            amounts=amounts,
            balances=balances,
            recipient=recipient,
            balance_deltas=balance_deltas,
            allow_cow_netting=allow_cow_netting,
            asset_in=context_value.asset_in,
            asset_out=context_value.asset_out,
        )

    witness_err = _validate_swap_witness_reserves(
        intent_id=intent_id,
        fill=fill,
        amounts=amounts,
        context=context_value,
        mode=mode,
    )
    if witness_err is not None:
        return False, witness_err

    if intent.kind == IntentKind.SWAP_EXACT_IN:
        return _replay_swap_exact_in_fill(
            intent=intent,
            amounts=amounts,
            pool_id=pool_id,
            pool=pool,
            balances=balances,
            recipient=recipient,
            balance_deltas=balance_deltas,
            reserve_deltas=reserve_deltas,
            asset_in=context_value.asset_in,
            asset_out=context_value.asset_out,
            reserve_in=context_value.reserve_in,
            reserve_out=context_value.reserve_out,
            dir_is_0_to_1=context_value.dir_is_0_to_1,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )

    return _replay_swap_exact_out_fill(
        intent=intent,
        amounts=amounts,
        pool_id=pool_id,
        pool=pool,
        balances=balances,
        recipient=recipient,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        asset_in=context_value.asset_in,
        asset_out=context_value.asset_out,
        reserve_in=context_value.reserve_in,
        reserve_out=context_value.reserve_out,
        dir_is_0_to_1=context_value.dir_is_0_to_1,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )


def _replay_cow_netted_swap_fill(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    balances: BalanceTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    allow_cow_netting: bool,
    asset_in: AssetId,
    asset_out: AssetId,
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    if not allow_cow_netting:
        return False, f"COW_NETTED not allowed for intent_id={intent_id}"
    ok_amounts, amount_in, out_amt, err_amounts = _validate_cow_replay_amounts(intent=intent, amounts=amounts)
    if not ok_amounts:
        return False, err_amounts
    if amount_in is None or out_amt is None:
        return False, f"invalid COW_NETTED replay amounts for intent_id={intent_id}"
    return _apply_cow_netted_balance_effects(
        intent=intent,
        balances=balances,
        recipient=recipient,
        balance_deltas=balance_deltas,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        out_amt=out_amt,
    )


def _validate_cow_replay_amounts(
    *,
    intent: Intent,
    amounts: _FillAmounts,
) -> Tuple[bool, Optional[int], Optional[int], Optional[str]]:
    intent_id = intent.intent_id
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return False, None, None, f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}"
    ok_intent_amounts, intent_amounts, err_intent_amounts = _validate_cow_intent_amounts(intent_id, intent)
    if not ok_intent_amounts:
        return False, None, None, err_intent_amounts
    if intent_amounts is None:
        return False, None, None, f"invalid COW_NETTED replay amounts for intent_id={intent_id}"
    amount_in, min_out = intent_amounts
    if amounts.fee_paid != 0:
        return False, None, None, f"COW_NETTED fee_paid must be 0: intent_id={intent_id}"
    if amounts.amount_in_filled != amount_in:
        return False, None, None, f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}"
    out_amt = amounts.amount_out_filled
    if out_amt < min_out:
        return False, None, None, f"COW_NETTED slippage: intent_id={intent_id}"
    return True, amount_in, out_amt, None


def _apply_cow_netted_balance_effects(
    *,
    intent: Intent,
    balances: BalanceTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
    out_amt: int,
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    try:
        balances.subtract(intent.sender_pubkey, asset_in, amount_in)
        balances.add(recipient, asset_out, out_amt)
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return False, f"COW_NETTED apply error for intent_id={intent_id}: {exc}"

    balance_deltas.append(BalanceDelta(pubkey=intent.sender_pubkey, asset=asset_in, delta_add=0, delta_sub=amount_in))
    balance_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=out_amt, delta_sub=0))
    return True, None


def _apply_swap_replay_effects(
    *,
    intent_id: str,
    sender: PubKey,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
    dir_is_0_to_1: bool,
    protocol_fee: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> Tuple[bool, Optional[str]]:
    try:
        balances.subtract(sender, asset_in, int(amount_in))
        balances.add(recipient, asset_out, int(amount_out))
        if protocol_fee:
            if not protocol_fee_recipient_pubkey:
                return False, f"protocol fee recipient missing after validation for intent_id={intent_id}"
            balances.add(protocol_fee_recipient_pubkey, asset_in, int(protocol_fee))
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return False, f"swap apply error for intent_id={intent_id}: {exc}"

    if dir_is_0_to_1:
        pool.reserve0 = int(new_reserve_in)
        pool.reserve1 = int(new_reserve_out)
    else:
        pool.reserve1 = int(new_reserve_in)
        pool.reserve0 = int(new_reserve_out)

    balance_deltas.append(BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in)))
    balance_deltas.append(BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=int(amount_out), delta_sub=0))
    if protocol_fee:
        if not protocol_fee_recipient_pubkey:
            return False, f"protocol fee recipient missing after validation for intent_id={intent_id}"
        balance_deltas.append(
            BalanceDelta(
                pubkey=protocol_fee_recipient_pubkey,
                asset=asset_in,
                delta_add=int(protocol_fee),
                delta_sub=0,
            )
        )
    reserve_deltas.append(
        ReserveDelta(
            pool_id=pool_id,
            asset=asset_in,
            delta_add=int(amount_in) - int(protocol_fee),
            delta_sub=0,
        )
    )
    reserve_deltas.append(ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=int(amount_out)))
    return True, None


def _invalid_swap_int(raw_value: Any, *, positive: bool) -> bool:
    if not isinstance(raw_value, int) or isinstance(raw_value, bool):
        return True
    return raw_value <= 0 if positive else raw_value < 0


def _parse_swap_exact_in_fields(intent: Intent) -> Tuple[Optional[_SwapExactInFields], Optional[str]]:
    intent_id = intent.intent_id
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if _invalid_swap_int(amount_in, positive=True):
        return None, f"invalid amount_in for intent_id={intent_id}"
    if _invalid_swap_int(min_out, positive=False):
        return None, f"invalid min_amount_out for intent_id={intent_id}"
    return _SwapExactInFields(amount_in=int(amount_in), min_out=int(min_out)), None


def _compute_swap_exact_in_result(
    *,
    intent_id: str,
    pool: PoolState,
    reserve_in: int,
    reserve_out: int,
    fields: _SwapExactInFields,
    protocol_fee_share_bps: int,
) -> Tuple[Optional[_SwapKernelResult], Optional[str]]:
    try:
        if int(protocol_fee_share_bps):
            if pool.curve_tag != CURVE_TAG_CPMM:
                return None, f"protocol fee unsupported for curve intent_id={intent_id}"
            quote = swap_exact_in_with_protocol_fee(
                reserve_in=int(reserve_in),
                reserve_out=int(reserve_out),
                amount_in=fields.amount_in,
                fee_bps=int(pool.fee_bps),
                protocol_fee_share_bps=int(protocol_fee_share_bps),
            )
            return (
                _SwapKernelResult(
                    amount_in=fields.amount_in,
                    amount_out=int(quote.amount_out),
                    new_reserve_in=int(quote.new_reserve_in),
                    new_reserve_out=int(quote.new_reserve_out),
                    protocol_fee=int(quote.protocol_fee),
                ),
                None,
            )
        amount_out, (new_in, new_out) = swap_exact_in_for_pool(
            pool,
            reserve_in=int(reserve_in),
            reserve_out=int(reserve_out),
            amount_in=fields.amount_in,
        )
        return (
            _SwapKernelResult(
                amount_in=fields.amount_in,
                amount_out=int(amount_out),
                new_reserve_in=int(new_in),
                new_reserve_out=int(new_out),
                protocol_fee=0,
            ),
            None,
        )
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return None, f"swap_exact_in kernel error for intent_id={intent_id}: {exc}"


def _validate_swap_exact_in_fill_amounts(
    *,
    intent_id: str,
    amounts: _FillAmounts,
    fields: _SwapExactInFields,
    result: _SwapKernelResult,
    pool: PoolState,
) -> Optional[str]:
    if amounts.amount_in_filled != fields.amount_in:
        return f"swap amount_in_filled mismatch for intent_id={intent_id}"
    if amounts.amount_out_filled != result.amount_out:
        return f"swap amount_out_filled mismatch for intent_id={intent_id}"
    if result.amount_out < fields.min_out:
        return f"swap slippage for intent_id={intent_id}"
    return _validate_swap_fee_fields(
        intent_id=intent_id,
        amounts=amounts,
        amount_in=result.amount_in,
        protocol_fee=result.protocol_fee,
        pool=pool,
    )


def _validate_swap_fee_fields(
    *,
    intent_id: str,
    amounts: _FillAmounts,
    amount_in: int,
    protocol_fee: int,
    pool: PoolState,
) -> Optional[str]:
    fee = compute_fee_total(amount_in, int(pool.fee_bps))
    if amounts.fee_paid != int(fee):
        return f"swap fee_paid mismatch for intent_id={intent_id}"
    if amounts.protocol_fee_paid != protocol_fee:
        return f"swap protocol_fee_paid mismatch for intent_id={intent_id}"
    return None


def _prepare_swap_exact_in_replay_result(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    pool: PoolState,
    reserve_in: int,
    reserve_out: int,
    protocol_fee_share_bps: int,
) -> Tuple[Optional[_SwapKernelResult], Optional[str]]:
    intent_id = intent.intent_id
    fields, fields_err = _parse_swap_exact_in_fields(intent)
    if fields_err is not None:
        return None, fields_err
    fields_value = cast(_SwapExactInFields, fields)
    result, result_err = _compute_swap_exact_in_result(
        intent_id=intent_id,
        pool=pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fields=fields_value,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    if result_err is not None:
        return None, result_err
    result_value = cast(_SwapKernelResult, result)
    fill_err = _validate_swap_exact_in_fill_amounts(
        intent_id=intent_id,
        amounts=amounts,
        fields=fields_value,
        result=result_value,
        pool=pool,
    )
    if fill_err is not None:
        return None, fill_err
    return result_value, None


def _replay_swap_exact_in_fill(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    asset_in: AssetId,
    asset_out: AssetId,
    reserve_in: int,
    reserve_out: int,
    dir_is_0_to_1: bool,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    sender = intent.sender_pubkey
    result, result_err = _prepare_swap_exact_in_replay_result(
        intent=intent,
        amounts=amounts,
        pool=pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    if result_err is not None:
        return False, result_err
    result_value = cast(_SwapKernelResult, result)
    return _apply_swap_replay_effects(
        intent_id=intent_id,
        sender=sender,
        pool_id=pool_id,
        pool=pool,
        balances=balances,
        recipient=recipient,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=result_value.amount_in,
        amount_out=result_value.amount_out,
        new_reserve_in=result_value.new_reserve_in,
        new_reserve_out=result_value.new_reserve_out,
        dir_is_0_to_1=dir_is_0_to_1,
        protocol_fee=result_value.protocol_fee,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )


def _replay_swap_exact_out_fill(
    *,
    intent: Intent,
    amounts: _FillAmounts,
    pool_id: str,
    pool: PoolState,
    balances: BalanceTable,
    recipient: PubKey,
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    asset_in: AssetId,
    asset_out: AssetId,
    reserve_in: int,
    reserve_out: int,
    dir_is_0_to_1: bool,
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> Tuple[bool, Optional[str]]:
    intent_id = intent.intent_id
    sender = intent.sender_pubkey
    amount_out_req = intent.get_field("amount_out")
    max_in = intent.get_field("max_amount_in")
    if not isinstance(amount_out_req, int) or isinstance(amount_out_req, bool) or amount_out_req <= 0:
        return False, f"invalid amount_out for intent_id={intent_id}"
    if not isinstance(max_in, int) or isinstance(max_in, bool) or max_in < 0:
        return False, f"invalid max_amount_in for intent_id={intent_id}"

    if amounts.amount_out_filled != int(amount_out_req):
        return False, f"swap amount_out_filled mismatch for intent_id={intent_id}"

    try:
        if int(protocol_fee_share_bps):
            if pool.curve_tag != CURVE_TAG_CPMM:
                return False, f"protocol fee unsupported for curve intent_id={intent_id}"
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
    except _STRONG_REPLAY_DOMAIN_ERRORS as exc:
        return False, f"swap_exact_out kernel error for intent_id={intent_id}: {exc}"

    if amounts.amount_in_filled != int(amount_in_req):
        return False, f"swap amount_in_filled mismatch for intent_id={intent_id}"
    if int(amount_in_req) > int(max_in):
        return False, f"swap slippage for intent_id={intent_id}"

    fee = compute_fee_total(int(amount_in_req), int(pool.fee_bps))
    if amounts.fee_paid != int(fee):
        return False, f"swap fee_paid mismatch for intent_id={intent_id}"
    if amounts.protocol_fee_paid != int(protocol_fee):
        return False, f"swap protocol_fee_paid mismatch for intent_id={intent_id}"

    return _apply_swap_replay_effects(
        intent_id=intent_id,
        sender=sender,
        pool_id=pool_id,
        pool=pool,
        balances=balances,
        recipient=recipient,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(amount_in_req),
        amount_out=int(amount_out_req),
        new_reserve_in=int(new_in),
        new_reserve_out=int(new_out),
        dir_is_0_to_1=dir_is_0_to_1,
        protocol_fee=int(protocol_fee),
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )


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
    config_err = _validate_strong_config(
        mode=mode,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    if config_err is not None:
        return False, config_err

    ok_index, intent_index, err_index = _build_validated_intent_index(
        settlement=settlement,
        allow_cow_netting=allow_cow_netting,
        intents=intents,
    )
    if not ok_index:
        return False, err_index
    if intent_index is None:
        raise RuntimeError("validated settlement intent index missing")
    intents_by_id = intent_index.intents_by_id
    fill_by_id = intent_index.fill_by_id

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
        quote_binding_err = _validate_quote_binding_for_intent(
            it,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        )
        if quote_binding_err is not None:
            return fail(quote_binding_err)
        quote_pool_fp = it.get_field("quote_pool_fingerprint")

        if action == FillAction.REJECT:
            continue

        f = fill_by_id[intent_id]
        ok_amounts, amounts, err_amounts = _validate_fill_amount_fields(f, intent_id)
        if not ok_amounts:
            return fail(str(err_amounts))
        if amounts is None:
            return fail(f"invalid fill amounts for intent_id={intent_id}")

        sender: PubKey = it.sender_pubkey
        recipient: PubKey = it.get_field("recipient", sender)
        if not isinstance(recipient, str) or not recipient:
            return fail(f"invalid recipient for intent_id={intent_id}")

        if it.kind == IntentKind.CREATE_POOL:
            ok_create, err_create = _replay_create_pool_fill(
                intent=it,
                amounts=amounts,
                pools=pools,
                balances=balances,
                lp=lp,
                expected_events=expected_events,
                balance_deltas=bal_deltas,
                reserve_deltas=res_deltas,
                lp_deltas=lp_deltas,
            )
            if not ok_create:
                return fail(str(err_create))
            continue

        pool_id = it.get_field("pool_id")
        if not isinstance(pool_id, str) or not pool_id:
            return fail(f"missing pool_id for intent_id={intent_id}")
        if pool_id not in pools:
            return fail(f"pool not found for intent_id={intent_id}: {pool_id}")
        pool = pools[pool_id]

        if it.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            ok_swap, err_swap = _replay_swap_fill(
                intent=it,
                fill=f,
                amounts=amounts,
                pool_id=pool_id,
                pool=pool,
                balances=balances,
                recipient=recipient,
                balance_deltas=bal_deltas,
                reserve_deltas=res_deltas,
                mode=mode,
                allow_cow_netting=allow_cow_netting,
                quote_pool_fp=quote_pool_fp,
                protocol_fee_share_bps=protocol_fee_share_bps,
                protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
            )
            if not ok_swap:
                return fail(str(err_swap))
            continue

        if it.kind == IntentKind.ADD_LIQUIDITY:
            ok_add, err_add = _replay_add_liquidity_fill(
                intent=it,
                amounts=amounts,
                pool_id=pool_id,
                pool=pool,
                balances=balances,
                lp=lp,
                recipient=recipient,
                balance_deltas=bal_deltas,
                reserve_deltas=res_deltas,
                lp_deltas=lp_deltas,
            )
            if not ok_add:
                return fail(str(err_add))
            continue

        if it.kind == IntentKind.REMOVE_LIQUIDITY:
            ok_remove, err_remove = _replay_remove_liquidity_fill(
                intent=it,
                amounts=amounts,
                pool_id=pool_id,
                pool=pool,
                balances=balances,
                lp=lp,
                recipient=recipient,
                balance_deltas=bal_deltas,
                reserve_deltas=res_deltas,
                lp_deltas=lp_deltas,
            )
            if not ok_remove:
                return fail(str(err_remove))
            continue

        return fail(f"unsupported intent kind for strong validation: {it.kind}")

    return _validate_replay_payload(
        settlement=settlement,
        expected_balance=_aggregate_balance_deltas(bal_deltas),
        expected_reserve=_aggregate_reserve_deltas(res_deltas),
        expected_lp=_aggregate_lp_deltas(lp_deltas),
        expected_events=expected_events,
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp_balances,
    )


def _validate_replay_payload(
    *,
    settlement: Settlement,
    expected_balance: List[BalanceDelta],
    expected_reserve: List[ReserveDelta],
    expected_lp: List[LPDelta],
    expected_events: List[dict],
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable],
) -> Tuple[bool, Optional[str]]:
    ok, err = _check_canonical_deltas(settlement)
    if not ok:
        return False, err
    replay_err = _replay_delta_payload_error(
        settlement=settlement,
        expected_balance=expected_balance,
        expected_reserve=expected_reserve,
        expected_lp=expected_lp,
        expected_events=expected_events,
    )
    if replay_err is not None:
        return False, replay_err
    return _validate_legacy_conservation(
        settlement=settlement,
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp_balances,
    )


def _replay_delta_payload_error(
    *,
    settlement: Settlement,
    expected_balance: List[BalanceDelta],
    expected_reserve: List[ReserveDelta],
    expected_lp: List[LPDelta],
    expected_events: List[dict],
) -> Optional[str]:
    if settlement.balance_deltas != expected_balance:
        return "balance_deltas mismatch vs replay"
    if settlement.reserve_deltas != expected_reserve:
        return "reserve_deltas mismatch vs replay"
    if settlement.lp_deltas != expected_lp:
        return "lp_deltas mismatch vs replay"
    if (settlement.events or []) != expected_events:
        return "events mismatch vs replay"
    return None


def _validate_legacy_conservation(
    *,
    settlement: Settlement,
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable],
) -> Tuple[bool, Optional[str]]:
    # Defense-in-depth for fill types that do not touch pool reserves, such as
    # COW_NETTED, where conservation must be enforced across balance deltas.
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


def _delta_scalar_is_nonnegative_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _check_unique_sorted(keys: List[Tuple], what: str) -> Tuple[bool, Optional[str]]:
    if keys != sorted(keys):
        return False, f"{what} not sorted canonically"
    if len(keys) != len(set(keys)):
        return False, f"{what} contains duplicate keys"
    return True, None


def _check_canonical_delta_group(
    deltas: List[Any],
    *,
    what: str,
    key_fn: Callable[[Any], Tuple],
) -> Tuple[bool, Optional[str]]:
    keys: List[Tuple] = []
    for delta in deltas:
        if not _delta_scalar_is_nonnegative_int(delta.delta_add):
            return False, f"{what} contains invalid delta_add"
        if not _delta_scalar_is_nonnegative_int(delta.delta_sub):
            return False, f"{what} contains invalid delta_sub"
        if delta.delta_add == 0 and delta.delta_sub == 0:
            return False, f"{what} contains a zero entry"
        keys.append(key_fn(delta))
    return _check_unique_sorted(keys, what)


def _check_canonical_deltas(settlement: Settlement) -> Tuple[bool, Optional[str]]:
    # Ensure deltas are canonical (one entry per key, sorted, and with non-negative fields).
    ok, err = _check_canonical_delta_group(
        list(settlement.balance_deltas),
        what="balance_deltas",
        key_fn=lambda delta: (delta.pubkey, delta.asset),
    )
    if not ok:
        return ok, err

    ok, err = _check_canonical_delta_group(
        list(settlement.reserve_deltas),
        what="reserve_deltas",
        key_fn=lambda delta: (delta.pool_id, delta.asset),
    )
    if not ok:
        return ok, err

    ok, err = _check_canonical_delta_group(
        list(settlement.lp_deltas),
        what="lp_deltas",
        key_fn=lambda delta: (delta.pubkey, delta.pool_id),
    )
    if not ok:
        return ok, err

    return True, None
