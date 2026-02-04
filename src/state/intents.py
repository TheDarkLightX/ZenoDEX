"""
Intent data models for TauSwap DEX.

Intents are user-authored requests (swap, add/remove liquidity, create pool)
that are collected and settled in batches.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Optional, Dict, Any

from .balances import PubKey


class IntentKind(Enum):
    """Intent type enumeration."""
    CREATE_POOL = "CREATE_POOL"
    ADD_LIQUIDITY = "ADD_LIQUIDITY"
    REMOVE_LIQUIDITY = "REMOVE_LIQUIDITY"
    SWAP_EXACT_IN = "SWAP_EXACT_IN"
    SWAP_EXACT_OUT = "SWAP_EXACT_OUT"


@dataclass
class Intent:
    """
    Base intent structure.
    
    Common fields for all intent types:
        module: Must be "TauSwap"
        version: Protocol version (e.g., "0.1")
        kind: Intent type
        intent_id: 32-byte hex identifier
        sender_pubkey: Public key of intent creator
        deadline: Unix timestamp expiration
        salt: Optional random bytes for uniqueness
    """
    module: str
    version: str
    kind: IntentKind
    intent_id: str
    sender_pubkey: PubKey
    deadline: int
    salt: Optional[str] = None
    
    # Intent-specific fields (stored as dict for flexibility)
    # These will be validated per intent kind
    fields: Optional[Dict[str, Any]] = None
    
    def __post_init__(self):
        """Validate intent structure."""
        if self.module != "TauSwap":
            raise ValueError(f"Invalid module: {self.module}")
        
        if not self.intent_id.startswith("0x") or len(self.intent_id) != 66:
            raise ValueError(f"Invalid intent_id format: {self.intent_id}")
        
        if self.fields is None:
            self.fields = {}
    
    def get_field(self, key: str, default: Any = None) -> Any:
        """Get intent-specific field value."""
        return self.fields.get(key, default) if self.fields else default
    
    def set_field(self, key: str, value: Any) -> None:
        """Set intent-specific field value."""
        if self.fields is None:
            self.fields = {}
        self.fields[key] = value


@dataclass
class SwapIntent(Intent):
    """Swap intent (exact-in or exact-out)."""
    
    def __post_init__(self):
        """Validate swap intent fields."""
        super().__post_init__()
        
        if self.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            raise ValueError(f"Invalid kind for SwapIntent: {self.kind}")
        
        # Required fields
        pool_id = self.get_field("pool_id")
        asset_in = self.get_field("asset_in")
        asset_out = self.get_field("asset_out")
        recipient = self.get_field("recipient", self.sender_pubkey)
        
        if not pool_id:
            raise ValueError("Missing required field: pool_id")
        if not asset_in:
            raise ValueError("Missing required field: asset_in")
        if not asset_out:
            raise ValueError("Missing required field: asset_out")
        if not isinstance(recipient, str) or not recipient:
            raise ValueError("recipient must be a non-empty string")
        
        if self.kind == IntentKind.SWAP_EXACT_IN:
            amount_in = self.get_field("amount_in")
            min_amount_out = self.get_field("min_amount_out")
            if amount_in is None or amount_in <= 0:
                raise ValueError("amount_in must be positive")
            if min_amount_out is None or min_amount_out < 0:
                raise ValueError("min_amount_out must be non-negative")
        else:  # SWAP_EXACT_OUT
            amount_out = self.get_field("amount_out")
            max_amount_in = self.get_field("max_amount_in")
            if amount_out is None or amount_out <= 0:
                raise ValueError("amount_out must be positive")
            if max_amount_in is None or max_amount_in < 0:
                raise ValueError("max_amount_in must be non-negative")


@dataclass
class CreatePoolIntent(Intent):
    """Create pool intent."""
    
    def __post_init__(self):
        """Validate create pool intent fields."""
        super().__post_init__()
        
        if self.kind != IntentKind.CREATE_POOL:
            raise ValueError(f"Invalid kind for CreatePoolIntent: {self.kind}")
        
        asset0 = self.get_field("asset0")
        asset1 = self.get_field("asset1")
        fee_bps = self.get_field("fee_bps")
        amount0 = self.get_field("amount0")
        amount1 = self.get_field("amount1")
        
        if not asset0 or not asset1:
            raise ValueError("Missing required fields: asset0, asset1")
        
        # Canonical ordering
        if asset0 >= asset1:
            raise ValueError(f"Assets must be in canonical order: {asset0} < {asset1}")
        
        if fee_bps is None or not (0 <= fee_bps <= 10000):
            raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
        
        if amount0 is None or amount0 <= 0:
            raise ValueError("amount0 must be positive")
        if amount1 is None or amount1 <= 0:
            raise ValueError("amount1 must be positive")


@dataclass
class SignedIntent:
    """
    Intent with cryptographic signature.
    
    Attributes:
        intent: The intent object
        signature: BLS12-381 signature (hex string)
    """
    intent: Intent
    signature: str
    
    def __post_init__(self):
        """Validate signature format."""
        if not self.signature.startswith("0x") or len(self.signature) < 130:
            raise ValueError(f"Invalid signature format: {self.signature}")
