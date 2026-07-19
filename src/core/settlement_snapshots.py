"""Immutable owned normal form for accepted settlements and effect plans."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, NoReturn

from ..state.immutable_collections import FrozenList, deep_freeze
from .settlement import BalanceDelta, Fill, LPDelta, ReserveDelta, Settlement


def _immutable_settlement(*_args: object, **_kwargs: object) -> NoReturn:
    raise TypeError("accepted settlement snapshot is immutable")


class _SealedSettlementValue:
    """Reject attribute writes after a dataclass snapshot finishes construction."""

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            _immutable_settlement(name, value)
        object.__setattr__(self, name, value)

    def _seal(self) -> None:
        object.__setattr__(self, "_snapshot_sealed", True)


@dataclass
class FrozenFill(_SealedSettlementValue, Fill):
    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenFill:
        return self


@dataclass
class FrozenBalanceDelta(_SealedSettlementValue, BalanceDelta):
    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenBalanceDelta:
        return self


@dataclass
class FrozenReserveDelta(_SealedSettlementValue, ReserveDelta):
    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenReserveDelta:
        return self


@dataclass
class FrozenLPDelta(_SealedSettlementValue, LPDelta):
    def __post_init__(self) -> None:
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenLPDelta:
        return self


@dataclass
class FrozenSettlement(_SealedSettlementValue, Settlement):
    """A recursively immutable settlement with the historical read schema."""

    def __post_init__(self) -> None:
        Settlement.__post_init__(self)
        self._seal()

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenSettlement:
        return self


def _freeze_fill(fill: Fill) -> FrozenFill:
    if not isinstance(fill, Fill):
        raise TypeError("settlement fills must contain Fill values")
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
    if not isinstance(delta, BalanceDelta):
        raise TypeError("balance_deltas must contain BalanceDelta values")
    return FrozenBalanceDelta(
        pubkey=delta.pubkey,
        asset=delta.asset,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _freeze_reserve_delta(delta: ReserveDelta) -> FrozenReserveDelta:
    if not isinstance(delta, ReserveDelta):
        raise TypeError("reserve_deltas must contain ReserveDelta values")
    return FrozenReserveDelta(
        pool_id=delta.pool_id,
        asset=delta.asset,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _freeze_lp_delta(delta: LPDelta) -> FrozenLPDelta:
    if not isinstance(delta, LPDelta):
        raise TypeError("lp_deltas must contain LPDelta values")
    return FrozenLPDelta(
        pubkey=delta.pubkey,
        pool_id=delta.pool_id,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def freeze_settlement(settlement: Settlement) -> Settlement:
    """Detach a settlement and recursively seal every accepted child value."""

    if not isinstance(settlement, Settlement):
        raise TypeError("settlement must be a Settlement")
    if isinstance(settlement, FrozenSettlement):
        return settlement

    events: FrozenList | None = None
    if settlement.events is not None:
        events = FrozenList(deep_freeze(event) for event in settlement.events)

    return FrozenSettlement(
        module=settlement.module,
        version=settlement.version,
        batch_ref=settlement.batch_ref,
        included_intents=FrozenList(
            (deep_freeze(intent_id), action)
            for intent_id, action in settlement.included_intents
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


def settlement_effect_fingerprint_payload(settlement: Settlement) -> dict[str, Any]:
    """Stable plain-data projection used by regressions and downstream hashing."""

    frozen = freeze_settlement(settlement)
    return {
        "module": frozen.module,
        "version": frozen.version,
        "batch_ref": frozen.batch_ref,
        "included_intents": [
            [intent_id, action.value]
            for intent_id, action in frozen.included_intents
        ],
        "fills": [dict(vars(fill)) for fill in frozen.fills],
        "balance_deltas": [dict(vars(delta)) for delta in frozen.balance_deltas],
        "reserve_deltas": [dict(vars(delta)) for delta in frozen.reserve_deltas],
        "lp_deltas": [dict(vars(delta)) for delta in frozen.lp_deltas],
        "events": deep_freeze(frozen.events),
    }
