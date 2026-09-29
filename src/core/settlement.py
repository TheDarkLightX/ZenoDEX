"""
Settlement data structures for batch clearing.

A settlement represents a proposed execution of a set of intents in a batch.

Two phases share one field layout:

- ``Settlement``, ``Fill`` and the delta records are mutable builders assembled
  by the clearing kernels (and tampered with freely by negative tests).
- ``SettlementSnapshot`` and its row snapshots are the immutable owned values
  returned inside ``DexEffects`` once a settlement has been validated and
  applied. ``SettlementSnapshot.to_settlement()`` returns a fresh builder.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass, fields
from enum import Enum
from typing import Any, Dict, List, Optional, TypeAlias, TypeGuard

from ..state.balances import Amount, AssetId, PubKey
from .domain_limits import is_strict_int

# Type alias
PoolId = str  # 32-byte hex string

SETTLEMENT_MODULE = "TauSwap"


def _require_non_negative_delta_limb(value: Any, *, name: str) -> int:
    if not is_strict_int(value):
        raise TypeError(f"{name} must be a non-negative int")
    if value < 0:
        raise TypeError(f"{name} must be a non-negative int")
    return int(value)


class FillAction(Enum):
    """Action taken on an intent."""
    FILL = "FILL"
    REJECT = "REJECT"


@dataclass
class Fill:
    """
    Represents a filled intent.
    
    Attributes:
        intent_id: Intent identifier
        action: FILL or REJECT
        reason: Optional rejection reason
        # Swap-specific fields
        amount_in_filled: Optional amount in (for swaps)
        amount_out_filled: Optional amount out (for swaps)
        fee_paid: Optional fee paid (for swaps)
        protocol_fee_paid: Optional protocol fee removed from pool reserves
        # Liquidity-specific fields
        amount0_used: Optional amount0 used (for add liquidity)
        amount1_used: Optional amount1 used (for add liquidity)
        lp_minted: Optional LP minted (for add liquidity)
        amount0_out: Optional amount0 out (for remove liquidity)
        amount1_out: Optional amount1 out (for remove liquidity)
        lp_burned: Optional LP burned (for remove liquidity)
        # Optional proof-carrying witnesses (for strong settlement validation)
        reserve_in_before: Optional reserve of input asset before a pool swap
        reserve_out_before: Optional reserve of output asset before a pool swap
    """
    intent_id: str
    action: FillAction
    reason: Optional[str] = None
    
    # Swap fields
    amount_in_filled: Optional[Amount] = None
    amount_out_filled: Optional[Amount] = None
    fee_paid: Optional[Amount] = None
    protocol_fee_paid: Optional[Amount] = None
    
    # Liquidity fields
    amount0_used: Optional[Amount] = None
    amount1_used: Optional[Amount] = None
    lp_minted: Optional[Amount] = None
    amount0_out: Optional[Amount] = None
    amount1_out: Optional[Amount] = None
    lp_burned: Optional[Amount] = None

    # Proof-carrying witnesses (optional; required only in strict modes).
    reserve_in_before: Optional[Amount] = None
    reserve_out_before: Optional[Amount] = None


@dataclass
class BalanceDelta:
    """
    Balance delta for a (pubkey, asset) pair.
    
    Attributes:
        pubkey: Public key
        asset: Asset identifier
        delta_add: Amount to add
        delta_sub: Amount to subtract
    """
    pubkey: PubKey
    asset: AssetId
    delta_add: Amount
    delta_sub: Amount
    
    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        delta_add = _require_non_negative_delta_limb(self.delta_add, name="balance_delta.delta_add")
        delta_sub = _require_non_negative_delta_limb(self.delta_sub, name="balance_delta.delta_sub")
        return delta_add - delta_sub


@dataclass
class ReserveDelta:
    """
    Reserve delta for a (pool_id, asset) pair.
    
    Attributes:
        pool_id: Pool identifier
        asset: Asset identifier
        delta_add: Amount to add
        delta_sub: Amount to subtract
    """
    pool_id: PoolId
    asset: AssetId
    delta_add: Amount
    delta_sub: Amount
    
    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        delta_add = _require_non_negative_delta_limb(self.delta_add, name="reserve_delta.delta_add")
        delta_sub = _require_non_negative_delta_limb(self.delta_sub, name="reserve_delta.delta_sub")
        return delta_add - delta_sub


@dataclass
class LPDelta:
    """
    LP balance delta for a (pubkey, pool_id) pair.
    
    Attributes:
        pubkey: Public key
        pool_id: Pool identifier
        delta_add: Amount to add
        delta_sub: Amount to subtract
    """
    pubkey: PubKey
    pool_id: PoolId
    delta_add: Amount
    delta_sub: Amount
    
    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        delta_add = _require_non_negative_delta_limb(self.delta_add, name="lp_delta.delta_add")
        delta_sub = _require_non_negative_delta_limb(self.delta_sub, name="lp_delta.delta_sub")
        return delta_add - delta_sub


@dataclass
class Settlement:
    """
    Batch settlement proposal.
    
    Attributes:
        module: Must be "TauSwap"
        version: Protocol version
        batch_ref: Reference to block height/hash
        included_intents: List of (intent_id, action) pairs
        fills: List of fill details
        balance_deltas: List of balance deltas
        reserve_deltas: List of reserve deltas
        lp_deltas: List of LP deltas
        events: Optional list of events for indexing
    """
    module: str
    version: str
    batch_ref: str
    included_intents: List[tuple[str, FillAction]]
    fills: List[Fill]
    balance_deltas: List[BalanceDelta]
    reserve_deltas: List[ReserveDelta]
    lp_deltas: List[LPDelta]
    events: Optional[List[Dict[str, Any]]] = None
    
    def __post_init__(self):
        """Validate settlement structure."""
        _validate_settlement_shape(
            module=self.module,
            included_intents=self.included_intents,
            fills=self.fills,
        )


def _validate_settlement_shape(
    *,
    module: object,
    included_intents: Sequence[Any],
    fills: Sequence[Any],
) -> None:
    """Structural settlement rules shared by the builder and the owned snapshot."""
    if module != SETTLEMENT_MODULE:
        raise ValueError(f"Invalid module: {module}")

    # Reject duplicate intent ids (ambiguous semantics).
    included_ids = [intent_id for intent_id, _action in included_intents]
    if len(included_ids) != len(set(included_ids)):
        raise ValueError("included_intents contains duplicate intent_id entries")

    # Reject duplicate fill ids (ambiguous semantics).
    fill_ids = [fill.intent_id for fill in fills]
    if len(fill_ids) != len(set(fill_ids)):
        raise ValueError("fills contains duplicate intent_id entries")

    # Any fill record must correspond to an included intent.
    included_set = set(included_ids)
    extra_fills = set(fill_ids) - included_set
    if extra_fills:
        raise ValueError(f"fills contains intent_ids not in included_intents: {sorted(extra_fills)}")

    # Verify all filled intents have corresponding fill details
    # Only check FILL actions; REJECT actions don't need fill details
    filled_intent_ids = {
        intent_id for intent_id, action in included_intents
        if action == FillAction.FILL
    }
    fill_intent_ids = {fill.intent_id for fill in fills if fill.action == FillAction.FILL}

    if filled_intent_ids != fill_intent_ids:
        missing = filled_intent_ids - fill_intent_ids
        extra = fill_intent_ids - filled_intent_ids
        raise ValueError(
            f"Fill mismatch: missing {missing}, extra {extra}"
        )


# ---------------------------------------------------------------------------
# Owned immutable settlement values (returned inside DexEffects)
# ---------------------------------------------------------------------------

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
_EVENT_SCALAR_TYPES = (bool, int, str)
SettlementEventScalar: TypeAlias = None | bool | int | str


def _is_settlement_event_scalar(value: object) -> TypeGuard[SettlementEventScalar]:
    return value is None or type(value) in _EVENT_SCALAR_TYPES


def _is_settlement_event_array(value: object) -> TypeGuard[list[object]]:
    return type(value) is list


def _is_settlement_event_object(value: object) -> TypeGuard[dict[object, object]]:
    return type(value) is dict


def _require_str(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    return value


def _require_optional_fill_int(value: object, *, name: str) -> int | None:
    if value is None:
        return None
    if not is_strict_int(value):
        raise TypeError(f"{name} must be an int or None")
    return int(value)


def _require_rows(rows: object, *, name: str) -> Sequence[Any]:
    if type(rows) is not list and type(rows) is not tuple:
        raise TypeError(f"settlement.{name} must be a list or tuple")
    return rows


def _owned_rows(rows: object, row_type: type, *, name: str) -> tuple[Any, ...]:
    owned = _require_rows(rows, name=name)
    for row in owned:
        if type(row) is not row_type:
            raise TypeError(f"settlement.{name} entries must be {row_type.__name__}")
    return tuple(owned)


def _owned_included_intents(entries: object) -> tuple[tuple[str, FillAction], ...]:
    owned: list[tuple[str, FillAction]] = []
    for entry in _require_rows(entries, name="included_intents"):
        if (type(entry) is not tuple and type(entry) is not list) or len(entry) != 2:
            raise TypeError("included_intents entries must be (intent_id, action) pairs")
        intent_id, action = entry
        _require_str(intent_id, name="included_intents.intent_id")
        if type(action) is not FillAction:
            raise TypeError("included_intents.action must be a FillAction")
        owned.append((intent_id, action))
    return tuple(owned)


@dataclass(frozen=True, slots=True)
class FillSnapshot:
    """Immutable owned copy of a ``Fill`` record (same fields, exact types)."""

    intent_id: str
    action: FillAction
    reason: str | None = None

    # Swap fields
    amount_in_filled: Amount | None = None
    amount_out_filled: Amount | None = None
    fee_paid: Amount | None = None
    protocol_fee_paid: Amount | None = None

    # Liquidity fields
    amount0_used: Amount | None = None
    amount1_used: Amount | None = None
    lp_minted: Amount | None = None
    amount0_out: Amount | None = None
    amount1_out: Amount | None = None
    lp_burned: Amount | None = None

    # Proof-carrying witnesses (optional; required only in strict modes).
    reserve_in_before: Amount | None = None
    reserve_out_before: Amount | None = None

    def __post_init__(self) -> None:
        _require_str(self.intent_id, name="fill.intent_id")
        if type(self.action) is not FillAction:
            raise TypeError("fill.action must be a FillAction")
        if self.reason is not None:
            _require_str(self.reason, name="fill.reason")
        for name in _FILL_AMOUNT_FIELDS:
            object.__setattr__(
                self,
                name,
                _require_optional_fill_int(getattr(self, name), name=f"fill.{name}"),
            )

    def to_fill(self) -> Fill:
        """Return a fresh mutable ``Fill`` builder with the same values."""
        return Fill(**{field.name: getattr(self, field.name) for field in fields(self)})


@dataclass(frozen=True, slots=True)
class BalanceDeltaSnapshot:
    """Immutable owned copy of a ``BalanceDelta`` record."""

    pubkey: PubKey
    asset: AssetId
    delta_add: Amount
    delta_sub: Amount

    def __post_init__(self) -> None:
        _require_str(self.pubkey, name="balance_delta.pubkey")
        _require_str(self.asset, name="balance_delta.asset")
        object.__setattr__(
            self,
            "delta_add",
            _require_non_negative_delta_limb(self.delta_add, name="balance_delta.delta_add"),
        )
        object.__setattr__(
            self,
            "delta_sub",
            _require_non_negative_delta_limb(self.delta_sub, name="balance_delta.delta_sub"),
        )

    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        return self.delta_add - self.delta_sub

    def to_balance_delta(self) -> BalanceDelta:
        return BalanceDelta(
            pubkey=self.pubkey,
            asset=self.asset,
            delta_add=self.delta_add,
            delta_sub=self.delta_sub,
        )


@dataclass(frozen=True, slots=True)
class ReserveDeltaSnapshot:
    """Immutable owned copy of a ``ReserveDelta`` record."""

    pool_id: PoolId
    asset: AssetId
    delta_add: Amount
    delta_sub: Amount

    def __post_init__(self) -> None:
        _require_str(self.pool_id, name="reserve_delta.pool_id")
        _require_str(self.asset, name="reserve_delta.asset")
        object.__setattr__(
            self,
            "delta_add",
            _require_non_negative_delta_limb(self.delta_add, name="reserve_delta.delta_add"),
        )
        object.__setattr__(
            self,
            "delta_sub",
            _require_non_negative_delta_limb(self.delta_sub, name="reserve_delta.delta_sub"),
        )

    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        return self.delta_add - self.delta_sub

    def to_reserve_delta(self) -> ReserveDelta:
        return ReserveDelta(
            pool_id=self.pool_id,
            asset=self.asset,
            delta_add=self.delta_add,
            delta_sub=self.delta_sub,
        )


@dataclass(frozen=True, slots=True)
class LPDeltaSnapshot:
    """Immutable owned copy of an ``LPDelta`` record."""

    pubkey: PubKey
    pool_id: PoolId
    delta_add: Amount
    delta_sub: Amount

    def __post_init__(self) -> None:
        _require_str(self.pubkey, name="lp_delta.pubkey")
        _require_str(self.pool_id, name="lp_delta.pool_id")
        object.__setattr__(
            self,
            "delta_add",
            _require_non_negative_delta_limb(self.delta_add, name="lp_delta.delta_add"),
        )
        object.__setattr__(
            self,
            "delta_sub",
            _require_non_negative_delta_limb(self.delta_sub, name="lp_delta.delta_sub"),
        )

    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        return self.delta_add - self.delta_sub

    def to_lp_delta(self) -> LPDelta:
        return LPDelta(
            pubkey=self.pubkey,
            pool_id=self.pool_id,
            delta_add=self.delta_add,
            delta_sub=self.delta_sub,
        )


class SettlementEventSnapshot(Mapping[str, "SettlementEventValue"]):
    """
    Read-only settlement event with recursively owned JSON metadata.

    Raw objects and arrays enter only as exact ``dict`` and ``list`` values.
    The snapshot owns immutable tuple/object equivalents, then reconstructs
    detached ordinary JSON containers through ``to_dict()``.
    """

    __slots__ = ("_keys", "_values")
    _keys: tuple[str, ...]
    _values: tuple[SettlementEventValue, ...]

    def __init__(self, event: dict[object, object]) -> None:
        if not _is_settlement_event_object(event):
            raise TypeError("settlement event must be an exact dict")
        items: list[tuple[str, SettlementEventValue]] = []
        for key, value in event.items():
            if type(key) is not str:
                raise TypeError("settlement event keys must be str")
            items.append((key, _snapshot_settlement_event_value(value)))
        object.__setattr__(self, "_keys", tuple(key for key, _value in items))
        object.__setattr__(self, "_values", tuple(value for _key, value in items))

    def __setattr__(self, name: str, value: object) -> None:
        del name, value
        raise TypeError("settlement event snapshot is immutable")

    def __delattr__(self, name: str) -> None:
        del name
        raise TypeError("settlement event snapshot is immutable")

    def __copy__(self) -> SettlementEventSnapshot:
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> SettlementEventSnapshot:
        memo[id(self)] = self
        return self

    def __getitem__(self, key: str) -> SettlementEventValue:
        if type(key) is not str:
            raise KeyError(key)
        for stored_key, stored_value in zip(self._keys, self._values, strict=True):
            if stored_key == key:
                return stored_value
        raise KeyError(key)

    def __iter__(self) -> Iterator[str]:
        return iter(self._keys)

    def __len__(self) -> int:
        return len(self._keys)

    def __eq__(self, other: object) -> bool:
        if type(other) is SettlementEventSnapshot:
            return self.to_dict() == other.to_dict()
        if isinstance(other, Mapping):
            return self.to_dict() == dict(other.items())
        return NotImplemented

    def __repr__(self) -> str:
        return f"SettlementEventSnapshot({self.to_dict()!r})"

    def to_dict(self) -> dict[str, SettlementEventJsonValue]:
        """Return a fresh, recursively detached JSON event dict."""
        output: dict[str, SettlementEventJsonValue] = {}
        for key, value in zip(self._keys, self._values, strict=True):
            output[key] = _settlement_event_value_to_json(value)
        return output


SettlementEventJsonValue: TypeAlias = (
    SettlementEventScalar | list["SettlementEventJsonValue"] | dict[str, "SettlementEventJsonValue"]
)
SettlementEventValue: TypeAlias = (
    SettlementEventScalar | tuple["SettlementEventValue", ...] | SettlementEventSnapshot
)


def _is_owned_settlement_event_array(
    value: SettlementEventValue,
) -> TypeGuard[tuple[SettlementEventValue, ...]]:
    return type(value) is tuple


def _is_owned_settlement_event_object(value: SettlementEventValue) -> TypeGuard[SettlementEventSnapshot]:
    return type(value) is SettlementEventSnapshot


def _snapshot_settlement_event_value(value: object) -> SettlementEventValue:
    """Own one value admitted by the settlement-event JSON algebra."""
    if _is_settlement_event_scalar(value):
        return value
    if _is_settlement_event_array(value):
        return tuple(_snapshot_settlement_event_value(item) for item in value)
    if _is_settlement_event_object(value):
        return SettlementEventSnapshot(value)
    raise TypeError("settlement event values must be JSON scalars, exact lists, or exact dicts")


def _settlement_event_value_to_json(value: SettlementEventValue) -> SettlementEventJsonValue:
    """Rebuild one owned event value as detached ordinary JSON containers."""
    if _is_settlement_event_scalar(value):
        return value
    if _is_owned_settlement_event_array(value):
        return [_settlement_event_value_to_json(item) for item in value]
    if _is_owned_settlement_event_object(value):
        return value.to_dict()
    raise TypeError("settlement event snapshot contains an unsupported value")


@dataclass(frozen=True, slots=True)
class SettlementSnapshot:
    """
    Immutable owned settlement graph: tuples of exact-typed row snapshots.

    The structural rules of ``Settlement`` (module, unique ids, fill/intent
    consistency) are re-checked on construction.

    Proposal validators consume mutable ``Settlement`` values. Use
    ``to_settlement()`` when intentionally revalidating a returned snapshot.
    """

    module: str
    version: str
    batch_ref: str
    included_intents: tuple[tuple[str, FillAction], ...]
    fills: tuple[FillSnapshot, ...]
    balance_deltas: tuple[BalanceDeltaSnapshot, ...]
    reserve_deltas: tuple[ReserveDeltaSnapshot, ...]
    lp_deltas: tuple[LPDeltaSnapshot, ...]
    events: tuple[SettlementEventSnapshot, ...] | None = None

    def __post_init__(self) -> None:
        for name in ("module", "version", "batch_ref"):
            _require_str(getattr(self, name), name=f"settlement.{name}")
        object.__setattr__(self, "included_intents", _owned_included_intents(self.included_intents))
        object.__setattr__(self, "fills", _owned_rows(self.fills, FillSnapshot, name="fills"))
        object.__setattr__(
            self,
            "balance_deltas",
            _owned_rows(self.balance_deltas, BalanceDeltaSnapshot, name="balance_deltas"),
        )
        object.__setattr__(
            self,
            "reserve_deltas",
            _owned_rows(self.reserve_deltas, ReserveDeltaSnapshot, name="reserve_deltas"),
        )
        object.__setattr__(self, "lp_deltas", _owned_rows(self.lp_deltas, LPDeltaSnapshot, name="lp_deltas"))
        if self.events is not None:
            object.__setattr__(
                self,
                "events",
                _owned_rows(self.events, SettlementEventSnapshot, name="events"),
            )
        _validate_settlement_shape(
            module=self.module,
            included_intents=self.included_intents,
            fills=self.fills,
        )

    def to_settlement(self) -> Settlement:
        """Return a fresh mutable ``Settlement`` builder with the same content."""
        return Settlement(
            module=self.module,
            version=self.version,
            batch_ref=self.batch_ref,
            included_intents=[(intent_id, action) for intent_id, action in self.included_intents],
            fills=[fill.to_fill() for fill in self.fills],
            balance_deltas=[delta.to_balance_delta() for delta in self.balance_deltas],
            reserve_deltas=[delta.to_reserve_delta() for delta in self.reserve_deltas],
            lp_deltas=[delta.to_lp_delta() for delta in self.lp_deltas],
            events=None if self.events is None else [event.to_dict() for event in self.events],
        )


def _snapshot_fill(fill: object) -> FillSnapshot:
    if type(fill) is not Fill:
        raise TypeError("settlement.fills entries must be Fill")
    return FillSnapshot(**{field.name: getattr(fill, field.name) for field in fields(Fill)})


def _snapshot_balance_delta(delta: object) -> BalanceDeltaSnapshot:
    if type(delta) is not BalanceDelta:
        raise TypeError("settlement.balance_deltas entries must be BalanceDelta")
    return BalanceDeltaSnapshot(
        pubkey=delta.pubkey,
        asset=delta.asset,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _snapshot_reserve_delta(delta: object) -> ReserveDeltaSnapshot:
    if type(delta) is not ReserveDelta:
        raise TypeError("settlement.reserve_deltas entries must be ReserveDelta")
    return ReserveDeltaSnapshot(
        pool_id=delta.pool_id,
        asset=delta.asset,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def _snapshot_lp_delta(delta: object) -> LPDeltaSnapshot:
    if type(delta) is not LPDelta:
        raise TypeError("settlement.lp_deltas entries must be LPDelta")
    return LPDeltaSnapshot(
        pubkey=delta.pubkey,
        pool_id=delta.pool_id,
        delta_add=delta.delta_add,
        delta_sub=delta.delta_sub,
    )


def snapshot_settlement(value: Settlement | SettlementSnapshot) -> SettlementSnapshot:
    """Admit an owned settlement snapshot from a builder or an existing snapshot.

    Exact types only: the builder and every row must be the exact ZenoDEX
    settlement classes, so the owned value never carries caller behavior.
    """
    if type(value) is SettlementSnapshot:
        return value
    if type(value) is not Settlement:
        raise TypeError("settlement must be a Settlement builder or a SettlementSnapshot")
    events = value.events
    return SettlementSnapshot(
        module=value.module,
        version=value.version,
        batch_ref=value.batch_ref,
        included_intents=_owned_included_intents(value.included_intents),
        fills=tuple(_snapshot_fill(fill) for fill in _require_rows(value.fills, name="fills")),
        balance_deltas=tuple(
            _snapshot_balance_delta(delta)
            for delta in _require_rows(value.balance_deltas, name="balance_deltas")
        ),
        reserve_deltas=tuple(
            _snapshot_reserve_delta(delta)
            for delta in _require_rows(value.reserve_deltas, name="reserve_deltas")
        ),
        lp_deltas=tuple(
            _snapshot_lp_delta(delta) for delta in _require_rows(value.lp_deltas, name="lp_deltas")
        ),
        events=None
        if events is None
        else tuple(SettlementEventSnapshot(event) for event in _require_rows(events, name="events")),
    )
