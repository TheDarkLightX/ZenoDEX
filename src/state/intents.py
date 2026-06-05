"""
Intent data models for TauSwap DEX.

Intents are user-authored requests (swap, add/remove liquidity, create pool)
that are collected and settled in batches.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Optional, cast

from .balances import PubKey
from .canonical import canonical_hex_fixed_allow_0x
from .pools import normalize_pool_asset_pair


def _require_int_field(
    name: str,
    value: Any,
    *,
    minimum: int,
    positive: bool,
) -> int:
    # REVIEW [B- -> A-]: intent validators previously used Python comparison
    # checks, so bool values crossed this user-authored boundary as 0/1. This
    # guard keeps the intent surface aligned with the stricter core kernels.
    if not isinstance(value, int) or isinstance(value, bool):
        qualifier = "positive" if positive else "non-negative"
        raise ValueError(f"{name} must be {qualifier}")
    if value < minimum:
        qualifier = "positive" if positive else "non-negative"
        raise ValueError(f"{name} must be {qualifier}")
    return value


def _require_fee_bps_field(value: Any) -> int:
    # REVIEW [B- -> A-]: fee_bps is consensus-significant pool metadata. Reject
    # bool before range checks so signed intent payloads cannot rely on Python's
    # bool-is-int behavior.
    if not isinstance(value, int) or isinstance(value, bool) or not (0 <= value <= 10000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {value}")
    return value


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

        try:
            self.intent_id = canonical_hex_fixed_allow_0x(self.intent_id, nbytes=32, name="intent_id")
        except (TypeError, ValueError) as exc:
            raise ValueError(f"Invalid intent_id format: {self.intent_id}") from exc
        
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
            _require_int_field("amount_in", amount_in, minimum=1, positive=True)
            _require_int_field("min_amount_out", min_amount_out, minimum=0, positive=False)
        else:  # SWAP_EXACT_OUT
            amount_out = self.get_field("amount_out")
            max_amount_in = self.get_field("max_amount_in")
            _require_int_field("amount_out", amount_out, minimum=1, positive=True)
            _require_int_field("max_amount_in", max_amount_in, minimum=0, positive=False)


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
        
        try:
            asset0_norm, asset1_norm = normalize_pool_asset_pair(asset0, asset1)
        except Exception:
            raise ValueError(f"Assets must be in canonical order: {asset0} < {asset1}") from None
        fields = cast(Dict[str, Any], self.fields)
        fields["asset0"] = asset0_norm
        fields["asset1"] = asset1_norm
        
        _require_fee_bps_field(fee_bps)
        
        _require_int_field("amount0", amount0, minimum=1, positive=True)
        _require_int_field("amount1", amount1, minimum=1, positive=True)


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
