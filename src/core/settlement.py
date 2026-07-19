"""
Settlement data structures for batch clearing.

A settlement represents a proposed execution of a set of intents in a batch.
"""

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
from typing import Any, Optional

from ..state.balances import Amount, AssetId, PubKey
from ..state.immutable import FrozenSequence, SealedValue, deep_freeze, seal_dataclass_init
from .domain_limits import is_strict_int

# Type alias
PoolId = str  # 32-byte hex string


def _require_non_negative_delta_limb(value: Any, *, name: str) -> int:
    if not is_strict_int(value):
        raise TypeError(f"{name} must be a non-negative int")
    if value < 0:
        raise TypeError(f"{name} must be a non-negative int")
    return int(value)


def _require_exact_str(value: Any, *, name: str, non_empty: bool = False) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if non_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_optional_non_negative_amount(value: Any, *, name: str) -> Optional[int]:
    if value is None:
        return None
    return _require_non_negative_delta_limb(value, name=name)


class FillAction(Enum):
    """Action taken on an intent."""
    FILL = "FILL"
    REJECT = "REJECT"


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class Fill(SealedValue):
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

    def __post_init__(self) -> None:
        _require_exact_str(self.intent_id, name="fill.intent_id", non_empty=True)
        if type(self.action) is not FillAction:
            raise TypeError("fill.action must be an exact FillAction")
        if self.reason is not None:
            _require_exact_str(self.reason, name="fill.reason")
        for name in (
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
        ):
            _require_optional_non_negative_amount(getattr(self, name), name=f"fill.{name}")


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class BalanceDelta(SealedValue):
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

    def __post_init__(self) -> None:
        _require_exact_str(self.pubkey, name="balance_delta.pubkey", non_empty=True)
        _require_exact_str(self.asset, name="balance_delta.asset", non_empty=True)
        _require_non_negative_delta_limb(self.delta_add, name="balance_delta.delta_add")
        _require_non_negative_delta_limb(self.delta_sub, name="balance_delta.delta_sub")
    
    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        delta_add = _require_non_negative_delta_limb(self.delta_add, name="balance_delta.delta_add")
        delta_sub = _require_non_negative_delta_limb(self.delta_sub, name="balance_delta.delta_sub")
        return delta_add - delta_sub


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class ReserveDelta(SealedValue):
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

    def __post_init__(self) -> None:
        _require_exact_str(self.pool_id, name="reserve_delta.pool_id", non_empty=True)
        _require_exact_str(self.asset, name="reserve_delta.asset", non_empty=True)
        _require_non_negative_delta_limb(self.delta_add, name="reserve_delta.delta_add")
        _require_non_negative_delta_limb(self.delta_sub, name="reserve_delta.delta_sub")
    
    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        delta_add = _require_non_negative_delta_limb(self.delta_add, name="reserve_delta.delta_add")
        delta_sub = _require_non_negative_delta_limb(self.delta_sub, name="reserve_delta.delta_sub")
        return delta_add - delta_sub


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class LPDelta(SealedValue):
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

    def __post_init__(self) -> None:
        _require_exact_str(self.pubkey, name="lp_delta.pubkey", non_empty=True)
        _require_exact_str(self.pool_id, name="lp_delta.pool_id", non_empty=True)
        _require_non_negative_delta_limb(self.delta_add, name="lp_delta.delta_add")
        _require_non_negative_delta_limb(self.delta_sub, name="lp_delta.delta_sub")
    
    def net_delta(self) -> Amount:
        """Compute net delta (add - sub)."""
        delta_add = _require_non_negative_delta_limb(self.delta_add, name="lp_delta.delta_add")
        delta_sub = _require_non_negative_delta_limb(self.delta_sub, name="lp_delta.delta_sub")
        return delta_add - delta_sub


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class Settlement(SealedValue):
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
    included_intents: Sequence[tuple[str, FillAction]]
    fills: Sequence[Fill]
    balance_deltas: Sequence[BalanceDelta]
    reserve_deltas: Sequence[ReserveDelta]
    lp_deltas: Sequence[LPDelta]
    events: Optional[Sequence[Mapping[str, Any]]] = None
    
    def __post_init__(self):
        """Validate settlement structure."""
        _require_exact_str(self.module, name="settlement.module", non_empty=True)
        if self.module != "TauSwap":
            raise ValueError(f"Invalid module: {self.module}")
        _require_exact_str(self.version, name="settlement.version", non_empty=True)
        _require_exact_str(self.batch_ref, name="settlement.batch_ref")

        included: list[tuple[str, FillAction]] = []
        for entry in self.included_intents:
            if not isinstance(entry, (list, tuple)) or len(entry) != 2:
                raise TypeError("included_intents entries must be (intent_id, action) pairs")
            intent_id, action = entry
            _require_exact_str(intent_id, name="included_intents.intent_id", non_empty=True)
            if type(action) is not FillAction:
                raise TypeError("included_intents.action must be an exact FillAction")
            included.append((intent_id, action))

        fills: list[Fill] = []
        for fill in self.fills:
            if type(fill) is not Fill:
                raise TypeError("settlement.fills entries must be exact Fill values")
            fills.append(fill)

        balance_deltas: list[BalanceDelta] = []
        for balance_delta in self.balance_deltas:
            if type(balance_delta) is not BalanceDelta:
                raise TypeError("settlement.balance_deltas entries must be exact BalanceDelta values")
            balance_deltas.append(balance_delta)

        reserve_deltas: list[ReserveDelta] = []
        for reserve_delta in self.reserve_deltas:
            if type(reserve_delta) is not ReserveDelta:
                raise TypeError("settlement.reserve_deltas entries must be exact ReserveDelta values")
            reserve_deltas.append(reserve_delta)

        lp_deltas: list[LPDelta] = []
        for lp_delta in self.lp_deltas:
            if type(lp_delta) is not LPDelta:
                raise TypeError("settlement.lp_deltas entries must be exact LPDelta values")
            lp_deltas.append(lp_delta)

        object.__setattr__(
            self,
            "included_intents",
            FrozenSequence(included),
        )
        object.__setattr__(self, "fills", FrozenSequence(fills))
        object.__setattr__(self, "balance_deltas", FrozenSequence(balance_deltas))
        object.__setattr__(self, "reserve_deltas", FrozenSequence(reserve_deltas))
        object.__setattr__(self, "lp_deltas", FrozenSequence(lp_deltas))
        if self.events is not None:
            frozen_events = deep_freeze(self.events, name="settlement.events")
            if not isinstance(frozen_events, FrozenSequence):
                raise TypeError("settlement.events must be a sequence")
            object.__setattr__(self, "events", frozen_events)

        # Reject duplicate intent ids (ambiguous semantics).
        included_ids = [intent_id for intent_id, _action in self.included_intents]
        if len(included_ids) != len(set(included_ids)):
            raise ValueError("included_intents contains duplicate intent_id entries")

        # Reject duplicate fill ids (ambiguous semantics).
        fill_ids = [fill.intent_id for fill in self.fills]
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
            intent_id for intent_id, action in self.included_intents
            if action == FillAction.FILL
        }
        fill_intent_ids = {fill.intent_id for fill in self.fills if fill.action == FillAction.FILL}
        
        if filled_intent_ids != fill_intent_ids:
            missing = filled_intent_ids - fill_intent_ids
            extra = fill_intent_ids - filled_intent_ids
            raise ValueError(
                f"Fill mismatch: missing {missing}, extra {extra}"
            )
