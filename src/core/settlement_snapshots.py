"""Immutable owned normal form for accepted settlements and effect plans."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, field
from typing import NoReturn

from ..state.immutable_collections import FrozenList, deep_freeze
from .settlement import BalanceDelta, Fill, LPDelta, ReserveDelta, Settlement


def _immutable_settlement(*_args: object, **_kwargs: object) -> NoReturn:
    raise TypeError("accepted settlement snapshot is immutable")


class _SealedSettlementValue:
    """Reject attribute writes after a dataclass snapshot finishes construction."""

    __slots__ = ()

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_snapshot_sealed", False):
            _immutable_settlement(name, value)
        object.__setattr__(self, name, value)

    def _seal(self) -> None:
        object.__setattr__(self, "_snapshot_sealed", True)


@dataclass(slots=True)
class FrozenFill(_SealedSettlementValue, Fill):
    _snapshot_sealed: bool = field(init=False, repr=False, compare=False, default=False)

    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenFill:
        return self


@dataclass(slots=True)
class FrozenBalanceDelta(_SealedSettlementValue, BalanceDelta):
    _snapshot_sealed: bool = field(init=False, repr=False, compare=False, default=False)

    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenBalanceDelta:
        return self


@dataclass(slots=True)
class FrozenReserveDelta(_SealedSettlementValue, ReserveDelta):
    _snapshot_sealed: bool = field(init=False, repr=False, compare=False, default=False)

    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenReserveDelta:
        return self


@dataclass(slots=True)
class FrozenLPDelta(_SealedSettlementValue, LPDelta):
    _snapshot_sealed: bool = field(init=False, repr=False, compare=False, default=False)

    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenLPDelta:
        return self


@dataclass(slots=True)
class FrozenSettlement(_SealedSettlementValue, Settlement):
    """A recursively immutable settlement with the historical read schema."""

    _snapshot_sealed: bool = field(init=False, repr=False, compare=False, default=False)

    def __post_init__(self) -> None:
        Settlement.__post_init__(self)
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenSettlement:
        return self


def _freeze_fill(fill: Fill) -> FrozenFill:
    if type(fill) is not Fill:
        raise TypeError("settlement fills must contain exact Fill values")
    return FrozenFill(
        intent_id=fill.intent_id,
        action=fill.action,
        reason=fill.reason,
        amount_in_filled=fill.amount_in_filled,
        amount_out_filled=fill.amount_out_filled,
        fee_paid=fill.fee_paid,
        protocol_fee_paid=fill.protocol_fee_paid,
        amount0_used=fill.amount0_used,
        amount1_used=fill.amount1_used,
        lp_minted=fill.lp_minted,
        amount0_out=fill.amount0_out,
        amount1_out=fill.amount1_out,
        lp_burned=fill.lp_burned,
        reserve_in_before=fill.reserve_in_before,
        reserve_out_before=fill.reserve_out_before,
    )


def _freeze_balance_delta(delta: BalanceDelta) -> FrozenBalanceDelta:
    if type(delta) is not BalanceDelta:
        raise TypeError("balance_deltas must contain exact BalanceDelta values")
    return FrozenBalanceDelta(
        pubkey=delta.pubkey,
        asset=delta.asset,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _freeze_reserve_delta(delta: ReserveDelta) -> FrozenReserveDelta:
    if type(delta) is not ReserveDelta:
        raise TypeError("reserve_deltas must contain exact ReserveDelta values")
    return FrozenReserveDelta(
        pool_id=delta.pool_id,
        asset=delta.asset,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _freeze_lp_delta(delta: LPDelta) -> FrozenLPDelta:
    if type(delta) is not LPDelta:
        raise TypeError("lp_deltas must contain exact LPDelta values")
    return FrozenLPDelta(
        pubkey=delta.pubkey,
        pool_id=delta.pool_id,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def freeze_settlement(settlement: Settlement) -> Settlement:
    """Detach a settlement and recursively seal every accepted child value."""

    if type(settlement) is FrozenSettlement:
        return settlement
    if type(settlement) is not Settlement:
        raise TypeError("settlement must be an exact Settlement")

    events: FrozenList | None = None
    if settlement.events is not None:
        events = FrozenList(deep_freeze(event) for event in settlement.events)

    return FrozenSettlement(
        module=settlement.module,
        version=settlement.version,
        batch_ref=settlement.batch_ref,
        included_intents=FrozenList(
            (deep_freeze(intent_id), action) for intent_id, action in settlement.included_intents
        ),
        fills=FrozenList(_freeze_fill(fill) for fill in settlement.fills),
        balance_deltas=FrozenList(
            _freeze_balance_delta(delta) for delta in settlement.balance_deltas
        ),
        reserve_deltas=FrozenList(
            _freeze_reserve_delta(delta) for delta in settlement.reserve_deltas
        ),
        lp_deltas=FrozenList(_freeze_lp_delta(delta) for delta in settlement.lp_deltas),
        events=events,
    )


def _copy_fill(fill: Fill) -> Fill:
    if type(fill) not in (Fill, FrozenFill):
        raise TypeError("settlement fills must contain exact Fill values")
    return Fill(
        intent_id=deepcopy(fill.intent_id),
        action=fill.action,
        reason=deepcopy(fill.reason),
        amount_in_filled=fill.amount_in_filled,
        amount_out_filled=fill.amount_out_filled,
        fee_paid=fill.fee_paid,
        protocol_fee_paid=fill.protocol_fee_paid,
        amount0_used=fill.amount0_used,
        amount1_used=fill.amount1_used,
        lp_minted=fill.lp_minted,
        amount0_out=fill.amount0_out,
        amount1_out=fill.amount1_out,
        lp_burned=fill.lp_burned,
        reserve_in_before=fill.reserve_in_before,
        reserve_out_before=fill.reserve_out_before,
    )


def _copy_balance_delta(delta: BalanceDelta) -> BalanceDelta:
    if type(delta) not in (BalanceDelta, FrozenBalanceDelta):
        raise TypeError("balance_deltas must contain exact BalanceDelta values")
    return BalanceDelta(
        pubkey=deepcopy(delta.pubkey),
        asset=deepcopy(delta.asset),
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _copy_reserve_delta(delta: ReserveDelta) -> ReserveDelta:
    if type(delta) not in (ReserveDelta, FrozenReserveDelta):
        raise TypeError("reserve_deltas must contain exact ReserveDelta values")
    return ReserveDelta(
        pool_id=deepcopy(delta.pool_id),
        asset=deepcopy(delta.asset),
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _copy_lp_delta(delta: LPDelta) -> LPDelta:
    if type(delta) not in (LPDelta, FrozenLPDelta):
        raise TypeError("lp_deltas must contain exact LPDelta values")
    return LPDelta(
        pubkey=deepcopy(delta.pubkey),
        pool_id=deepcopy(delta.pool_id),
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def snapshot_settlement(settlement: Settlement) -> Settlement:
    """Return an exact owned scratch copy for deterministic validation.

    The scratch value is never exposed as authoritative state or an accepted
    effect. It preserves the exact mutable base schema expected by replay
    validators while detaching every value from the caller's proposal. Accepted
    effects cross the separate freeze_settlement boundary.
    """

    if type(settlement) not in (Settlement, FrozenSettlement):
        raise TypeError("settlement must be an exact Settlement")

    events = None
    if settlement.events is not None:
        events = deepcopy(list(settlement.events))

    return Settlement(
        module=deepcopy(settlement.module),
        version=deepcopy(settlement.version),
        batch_ref=deepcopy(settlement.batch_ref),
        included_intents=[
            (deepcopy(intent_id), action) for intent_id, action in settlement.included_intents
        ],
        fills=[_copy_fill(fill) for fill in settlement.fills],
        balance_deltas=[_copy_balance_delta(delta) for delta in settlement.balance_deltas],
        reserve_deltas=[_copy_reserve_delta(delta) for delta in settlement.reserve_deltas],
        lp_deltas=[_copy_lp_delta(delta) for delta in settlement.lp_deltas],
        events=events,
    )
