"""
Multi-asset balance tracking with deterministic ordering.

Implements BalanceTable[PubKey, AssetId] -> Amount
"""

from typing import Dict, NoReturn, Tuple

from .canonical import canonical_hex_fixed_allow_0x
from .immutable import FrozenDict

# Type aliases
PubKey = str  # BLS12-381 public key as hex string
AssetId = str  # 32-byte hex string (0x...)
Amount = int  # Non-negative integer (arbitrary precision)
BalanceDelta = int

# Native asset identifier
NATIVE_ASSET = "0x" + "00" * 32


def _require_balance_int(name: str, value: object) -> int:
    # Balance entries feed canonical roots and settlement replay. Reject
    # bool-as-int and non-int numerics before they can enter sparse state.
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    return value


def _require_balance_key(pubkey: object, asset: object) -> tuple[PubKey, AssetId]:
    """Validate an owned balance key without retaining behavior-changing subclasses."""

    if type(pubkey) is not str or not pubkey:
        raise TypeError("pubkey must be a non-empty exact string")
    if type(asset) is not str or not asset:
        raise TypeError("asset must be a non-empty exact string")
    return pubkey, asset


def decoded_fixed_identity_or_text(value: str, *, nbytes: int, name: str) -> tuple[str, str]:
    """Return a decoded-hex identity when available, preserving legacy symbols."""

    try:
        return "hex", canonical_hex_fixed_allow_0x(value, nbytes=nbytes, name=name)
    except ValueError:
        # Symbolic identities remain supported by non-production/test profiles.
        # A versioned migration is required before canonical spelling can be
        # mandatory for every persisted state.
        return "text", value


def _validated_balance_entries(source: "BalanceTable") -> dict[tuple[PubKey, AssetId], Amount]:
    raw = object.__getattribute__(source, "_balances")
    if type(raw) not in (dict, FrozenDict):
        raise TypeError("balance storage must be an exact dict snapshot")

    owned: dict[tuple[PubKey, AssetId], Amount] = {}
    decoded_seen: dict[tuple[tuple[str, str], tuple[str, str]], tuple[str, str]] = {}
    for raw_key, raw_amount in raw.items():
        if type(raw_key) is not tuple or len(raw_key) != 2:
            raise TypeError("balance keys must be exact (pubkey, asset) tuples")
        pubkey, asset = _require_balance_key(raw_key[0], raw_key[1])
        amount = _require_balance_int("balance amount", raw_amount)
        if amount <= 0:
            raise ValueError("stored balance amounts must be positive")

        key = (pubkey, asset)
        decoded_key = (
            decoded_fixed_identity_or_text(pubkey, nbytes=48, name="balance pubkey"),
            decoded_fixed_identity_or_text(asset, nbytes=32, name="balance asset"),
        )
        prior = decoded_seen.get(decoded_key)
        if prior is not None and prior != key:
            raise ValueError("duplicate decoded (pubkey, asset) in balances")
        decoded_seen[decoded_key] = key
        owned[key] = amount
    return owned


class BalanceTable:
    """
    Deterministic balance table mapping (pubkey, asset) -> amount.
    
    Note: this class stores balances in a plain dict. Do not rely on dict
    iteration order for consensus-critical logic; callers should sort keys
    explicitly at serialization / hashing boundaries (see `src/integration/dex_snapshot.py`).
    """
    
    __slots__ = ("_balances",)

    def __init__(self):
        """Initialize empty balance table."""
        # Use tuple keys (pubkey, asset). Deterministic ordering is enforced at call sites via sorting.
        self._balances: Dict[Tuple[PubKey, AssetId], Amount] = {}
    
    def get(self, pubkey: PubKey, asset: AssetId) -> Amount:
        """Get balance for (pubkey, asset). Returns 0 if not found."""
        return self._balances.get(_require_balance_key(pubkey, asset), 0)
    
    def set(self, pubkey: PubKey, asset: AssetId, amount: Amount) -> None:
        """
        Set balance for (pubkey, asset).
        
        Args:
            pubkey: Public key
            asset: Asset identifier
            amount: Non-negative amount
            
        Raises:
            ValueError: If amount is negative
        """
        key = _require_balance_key(pubkey, asset)
        amount_i = _require_balance_int("amount", amount)
        if amount_i < 0:
            raise ValueError(f"Balance cannot be negative: {amount_i}")
        if amount_i == 0:
            # Remove zero balances to keep table sparse
            self._balances.pop(key, None)
        else:
            self._balances[key] = amount_i
    
    def add(self, pubkey: PubKey, asset: AssetId, delta: BalanceDelta) -> None:
        """
        Add delta to balance. Equivalent to set(pubkey, asset, get(...) + delta).
        
        Args:
            pubkey: Public key
            asset: Asset identifier
            delta: Amount to add (can be negative for subtraction)
            
        Raises:
            ValueError: If resulting balance would be negative
        """
        delta_i = _require_balance_int("delta", delta)
        current = self.get(pubkey, asset)
        new_balance = current + delta_i
        if new_balance < 0:
            raise ValueError(
                f"Insufficient balance: {current} + {delta_i} = {new_balance} < 0"
            )
        self.set(pubkey, asset, new_balance)
    
    def subtract(self, pubkey: PubKey, asset: AssetId, delta: Amount) -> None:
        """
        Subtract delta from balance. Equivalent to add(pubkey, asset, -delta).
        
        Args:
            pubkey: Public key
            asset: Asset identifier
            delta: Non-negative amount to subtract
            
        Raises:
            ValueError: If delta is negative or insufficient balance
        """
        delta_i = _require_balance_int("delta", delta)
        if delta_i < 0:
            raise ValueError(f"Delta must be non-negative: {delta_i}")
        self.add(pubkey, asset, -delta_i)
    
    def get_all_balances(self) -> Dict[Tuple[PubKey, AssetId], Amount]:
        """
        Get all balances as a dictionary.
        
        Returns:
            Dictionary mapping (pubkey, asset) -> amount
        """
        return dict(self._balances)
    
    def get_balances_for_asset(self, asset: AssetId) -> Dict[PubKey, Amount]:
        """
        Get all balances for a specific asset.
        
        Args:
            asset: Asset identifier
            
        Returns:
            Dictionary mapping pubkey -> amount
        """
        result = {}
        for (pk, a), amount in self._balances.items():
            if a == asset:
                result[pk] = amount
        return result
    
    def verify_non_negative(self) -> bool:
        """
        Verify all balances are non-negative.
        
        Returns:
            True if all balances >= 0
        """
        return all(amount >= 0 for amount in self._balances.values())
    
    def __repr__(self) -> str:
        return f"BalanceTable({len(self._balances)} entries)"


class FrozenBalanceTable(BalanceTable):
    """Transitively immutable, O(1)-lookup snapshot of a balance table."""

    __slots__ = ()

    def __init__(self, source: BalanceTable) -> None:
        try:
            object.__getattribute__(self, "_balances")
        except AttributeError:
            pass
        else:
            raise TypeError("FrozenBalanceTable is already initialized")
        if type(source) not in (BalanceTable, FrozenBalanceTable):
            raise TypeError("source must be an exact BalanceTable snapshot")
        object.__setattr__(self, "_balances", FrozenDict(_validated_balance_entries(source)))

    def __setattr__(self, name: str, value: object) -> NoReturn:
        raise TypeError("FrozenBalanceTable cannot be mutated")

    def set(self, pubkey: PubKey, asset: AssetId, amount: Amount) -> NoReturn:
        raise TypeError("FrozenBalanceTable cannot be mutated")

    def add(self, pubkey: PubKey, asset: AssetId, delta: BalanceDelta) -> NoReturn:
        raise TypeError("FrozenBalanceTable cannot be mutated")

    def subtract(self, pubkey: PubKey, asset: AssetId, delta: Amount) -> NoReturn:
        raise TypeError("FrozenBalanceTable cannot be mutated")


def copy_balance_table(source: BalanceTable) -> BalanceTable:
    """Return a detached mutable builder with the same logical balances."""

    if type(source) not in (BalanceTable, FrozenBalanceTable):
        raise TypeError("source must be an exact BalanceTable snapshot")
    copied = BalanceTable()
    for (pubkey, asset), amount in _validated_balance_entries(source).items():
        copied.set(pubkey, asset, amount)
    return copied


def freeze_balance_table(source: BalanceTable) -> FrozenBalanceTable:
    """Seal a balance table at an authoritative state boundary."""

    if type(source) is FrozenBalanceTable:
        try:
            storage = object.__getattribute__(source, "_balances")
        except AttributeError as exc:
            raise TypeError("FrozenBalanceTable is not initialized") from exc
        if type(storage) is not FrozenDict:
            raise TypeError("FrozenBalanceTable storage is not sealed")
        return source
    if type(source) is not BalanceTable:
        raise TypeError("source must be an exact BalanceTable snapshot")
    return FrozenBalanceTable(source)
