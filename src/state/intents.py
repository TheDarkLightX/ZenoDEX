"""
Intent data models for TauSwap DEX.

Intents are user-authored requests (swap, add/remove liquidity, create pool)
that are collected and settled in batches.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Optional

from .balances import PubKey
from .canonical import canonical_hex_fixed_allow_0x
from .pools import normalize_pool_asset_pair


class IntentKind(Enum):
    """Intent type enumeration."""
    CREATE_POOL = "CREATE_POOL"
    ADD_LIQUIDITY = "ADD_LIQUIDITY"
    REMOVE_LIQUIDITY = "REMOVE_LIQUIDITY"
    SWAP_EXACT_IN = "SWAP_EXACT_IN"
    SWAP_EXACT_OUT = "SWAP_EXACT_OUT"
    ROUTE_EXACT_IN = "ROUTE_EXACT_IN"
    ROUTE_EXACT_OUT = "ROUTE_EXACT_OUT"


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
class RouteIntent(Intent):
    """
    Atomic route settlement intent (exact-in or exact-out).

    A RouteIntent binds a single quoted multi-leg route to one signature: every
    leg validates and applies, or the whole route is rejected with no state
    change. This model validates only the *shape* of the route request; the
    full-coverage-vs-receipt check, pool-fingerprint binding, replay/deadline,
    and totals enforcement are engine-side (see
    docs/ATOMIC_ROUTE_SETTLEMENT_DESIGN.md).

    Fields (stored in the `.fields` dict):
        quote_receipt_hash: 32-byte hex hash binding the exact quoted route.
        asset_in, asset_out: route endpoints (non-empty, distinct).
        leg_indices: the receipt leg indices covered by this route — a
            non-empty list of non-negative ints, strictly ascending (sorted,
            no duplicates).
        ROUTE_EXACT_IN:  total_amount_in (>0) + total_min_amount_out (>=0).
        ROUTE_EXACT_OUT: total_amount_out (>0) + total_max_amount_in (>=0,
            REQUIRED — fail-closed against unbounded total input).
    """

    def __post_init__(self):
        """Validate route intent fields (shape only; engine validates the rest)."""
        super().__post_init__()
        fields = self.fields
        if fields is None:  # pragma: no cover - established by Intent.__post_init__
            raise AssertionError("route intent fields were not initialized")

        if self.kind not in (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT):
            raise ValueError(f"Invalid kind for RouteIntent: {self.kind}")

        # quote_receipt_hash: required, valid 32-byte hash hex (same convention
        # as intent_id). A present-but-None value must also fail closed.
        quote_receipt_hash = self.get_field("quote_receipt_hash")
        try:
            quote_receipt_hash = canonical_hex_fixed_allow_0x(
                quote_receipt_hash, nbytes=32, name="quote_receipt_hash"
            )
        except (TypeError, ValueError) as exc:
            raise ValueError(
                f"Invalid quote_receipt_hash format: {quote_receipt_hash}"
            ) from exc
        self.set_field("quote_receipt_hash", quote_receipt_hash)

        # Route endpoints: non-empty distinct strings (recipient idiom — a bare
        # `if not x` would let a truthy non-string through).
        asset_in = self.get_field("asset_in")
        asset_out = self.get_field("asset_out")
        if not isinstance(asset_in, str) or not asset_in:
            raise ValueError("asset_in must be a non-empty string")
        if not isinstance(asset_out, str) or not asset_out:
            raise ValueError("asset_out must be a non-empty string")
        if asset_in == asset_out:
            raise ValueError("asset_in must differ from asset_out")

        # leg_indices: non-empty list of non-negative ints, strictly ascending
        # (rejects both unsorted and duplicates). Check list-ness FIRST so a
        # str is not iterated char-by-char.
        leg_indices = self.get_field("leg_indices")
        if not isinstance(leg_indices, list) or not leg_indices:
            raise ValueError("leg_indices must be a non-empty list")
        for idx in leg_indices:
            if not isinstance(idx, int) or isinstance(idx, bool) or idx < 0:
                raise ValueError("leg_indices must be non-negative ints")
        if not all(a < b for a, b in zip(leg_indices, leg_indices[1:], strict=False)):
            raise ValueError("leg_indices must be strictly ascending with no duplicates")

        # Totals: kind-specific required fields, with the opposite kind's amount
        # fields forbidden (fail-closed against mixed exact-in/exact-out).
        if self.kind == IntentKind.ROUTE_EXACT_IN:
            total_amount_in = self.get_field("total_amount_in")
            total_min_amount_out = self.get_field("total_min_amount_out")
            if (
                total_amount_in is None
                or not isinstance(total_amount_in, int)
                or isinstance(total_amount_in, bool)
                or total_amount_in <= 0
            ):
                raise ValueError("total_amount_in must be positive")
            if (
                total_min_amount_out is None
                or not isinstance(total_min_amount_out, int)
                or isinstance(total_min_amount_out, bool)
                or total_min_amount_out < 0
            ):
                raise ValueError("total_min_amount_out must be non-negative")
            if "total_amount_out" in fields or "total_max_amount_in" in fields:
                raise ValueError(
                    "ROUTE_EXACT_IN must not carry exact-out fields "
                    "(total_amount_out, total_max_amount_in)"
                )
        else:  # ROUTE_EXACT_OUT
            total_amount_out = self.get_field("total_amount_out")
            total_max_amount_in = self.get_field("total_max_amount_in")
            if (
                total_amount_out is None
                or not isinstance(total_amount_out, int)
                or isinstance(total_amount_out, bool)
                or total_amount_out <= 0
            ):
                raise ValueError("total_amount_out must be positive")
            if (
                total_max_amount_in is None
                or not isinstance(total_max_amount_in, int)
                or isinstance(total_max_amount_in, bool)
                or total_max_amount_in < 0
            ):
                raise ValueError("total_max_amount_in must be non-negative")
            if "total_amount_in" in fields or "total_min_amount_out" in fields:
                raise ValueError(
                    "ROUTE_EXACT_OUT must not carry exact-in fields "
                    "(total_amount_in, total_min_amount_out)"
                )


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
        if self.fields is not None:
            self.fields["asset0"] = asset0_norm
            self.fields["asset1"] = asset1_norm
        
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
