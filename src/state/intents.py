"""
Intent data models for TauSwap DEX.

Intents are user-authored requests (swap, add/remove liquidity, create pool)
that are collected and settled in batches.
"""

from dataclasses import dataclass, replace
from enum import Enum
from typing import Any, Mapping, Optional, cast

from .balances import PubKey
from .canonical import canonical_hex_fixed_allow_0x
from .immutable import SealedValue, freeze_mapping, seal_dataclass_init


class IntentKind(Enum):
    """Intent type enumeration."""
    CREATE_POOL = "CREATE_POOL"
    ADD_LIQUIDITY = "ADD_LIQUIDITY"
    REMOVE_LIQUIDITY = "REMOVE_LIQUIDITY"
    SWAP_EXACT_IN = "SWAP_EXACT_IN"
    SWAP_EXACT_OUT = "SWAP_EXACT_OUT"


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class Intent(SealedValue):
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
    fields: Optional[Mapping[str, Any]] = None
    
    def __post_init__(self):
        """Validate intent structure."""
        if type(self.module) is not str:
            raise TypeError("module must be a string")
        for name, value in (("version", self.version), ("sender_pubkey", self.sender_pubkey)):
            if type(value) is not str or not value:
                raise TypeError(f"{name} must be a non-empty string")
        if type(self.kind) is not IntentKind:
            raise TypeError("kind must be an exact IntentKind")
        if type(self.deadline) is not int or self.deadline < 0:
            raise TypeError("deadline must be a non-negative int")
        if self.salt is not None and (type(self.salt) is not str or not self.salt):
            raise TypeError("salt must be a non-empty string or None")
        if self.module != "TauSwap":
            raise ValueError(f"Invalid module: {self.module}")

        try:
            canonical_intent_id = canonical_hex_fixed_allow_0x(
                self.intent_id,
                nbytes=32,
                name="intent_id",
            )
        except (TypeError, ValueError) as exc:
            raise ValueError(f"Invalid intent_id format: {self.intent_id}") from exc

        fields = {} if self.fields is None else self.fields
        if not isinstance(fields, Mapping):
            raise TypeError("fields must be a mapping when present")
        object.__setattr__(self, "intent_id", canonical_intent_id)
        object.__setattr__(self, "fields", freeze_mapping(fields, name="intent.fields"))
    
    def get_field(self, key: str, default: Any = None) -> Any:
        """Get intent-specific field value."""
        return self.fields.get(key, default) if self.fields else default
    
    def with_field(self, key: str, value: Any) -> "Intent":
        """Return a new intent with one field changed; never mutate signed meaning."""

        if not isinstance(key, str) or not key:
            raise TypeError("field key must be a non-empty string")
        fields = dict(self.fields or {})
        fields[key] = value
        return replace(self, fields=fields)


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class SwapIntent(Intent):
    """Swap intent (exact-in or exact-out)."""
    
    def __post_init__(self):
        """Validate swap intent fields."""
        Intent.__post_init__(self)
        
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


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class CreatePoolIntent(Intent):
    """Create pool intent."""
    
    def __post_init__(self):
        """Validate create pool intent fields."""
        Intent.__post_init__(self)
        
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


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class SignedIntent(SealedValue):
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
        require_exact_intent(self.intent)
        if type(self.signature) is not str:
            raise TypeError("signature must be a string")
        if not self.signature.startswith("0x") or len(self.signature) < 130:
            raise ValueError(f"Invalid signature format: {self.signature}")


def require_exact_intent(value: object) -> Intent:
    """Reject behavior-changing subclasses at direct core API boundaries."""

    if type(value) not in (Intent, SwapIntent, CreatePoolIntent):
        raise TypeError("intent must be an exact ZenoDEX intent value")
    return cast(Intent, value)
