"""
Settlement data structures for batch clearing.

A settlement represents a proposed execution of a set of intents in a batch.
"""

from dataclasses import dataclass
from typing import List, Dict, Optional, Any
from enum import Enum

from ..state.balances import PubKey, AssetId, Amount

# Type alias
PoolId = str  # 32-byte hex string


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
        # Liquidity-specific fields
        amount0_used: Optional amount0 used (for add liquidity)
        amount1_used: Optional amount1 used (for add liquidity)
        lp_minted: Optional LP minted (for add liquidity)
        amount0_out: Optional amount0 out (for remove liquidity)
        amount1_out: Optional amount1 out (for remove liquidity)
        lp_burned: Optional LP burned (for remove liquidity)
    """
    intent_id: str
    action: FillAction
    reason: Optional[str] = None
    
    # Swap fields
    amount_in_filled: Optional[Amount] = None
    amount_out_filled: Optional[Amount] = None
    fee_paid: Optional[Amount] = None
    
    # Liquidity fields
    amount0_used: Optional[Amount] = None
    amount1_used: Optional[Amount] = None
    lp_minted: Optional[Amount] = None
    amount0_out: Optional[Amount] = None
    amount1_out: Optional[Amount] = None
    lp_burned: Optional[Amount] = None


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
        return self.delta_add - self.delta_sub


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
        return self.delta_add - self.delta_sub


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
        return self.delta_add - self.delta_sub


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
        if self.module != "TauSwap":
            raise ValueError(f"Invalid module: {self.module}")
        
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

