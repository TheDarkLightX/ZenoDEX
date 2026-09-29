"""
Multi-asset balance tracking with deterministic ordering.

Implements BalanceTable[PubKey, AssetId] -> Amount

Two phases share one read API:

- ``BalanceTable`` is the mutable builder used by kernels and parsers while a
  batch is being computed or decoded.
- ``BalanceSnapshot`` is the immutable committed value held by ``DexState``.
  It owns its entries, cannot be mutated, and ``to_table()`` returns a fresh
  builder copy for the next transition.
"""

from __future__ import annotations

from bisect import bisect_left
from collections.abc import Mapping
from typing import Any, Dict, Tuple

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
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


class BalanceTable:
    """
    Deterministic balance table mapping (pubkey, asset) -> amount.
    
    Note: this class stores balances in a plain dict. Do not rely on dict
    iteration order for consensus-critical logic; callers should sort keys
    explicitly at serialization / hashing boundaries (see `src/integration/dex_snapshot.py`).
    """
    
    def __init__(self):
        """Initialize empty balance table."""
        # Use tuple keys (pubkey, asset). Deterministic ordering is enforced at call sites via sorting.
        self._balances: Dict[Tuple[PubKey, AssetId], Amount] = {}
    
    def get(self, pubkey: PubKey, asset: AssetId) -> Amount:
        """Get balance for (pubkey, asset). Returns 0 if not found."""
        return self._balances.get((pubkey, asset), 0)
    
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
        amount_i = _require_balance_int("amount", amount)
        if amount_i < 0:
            raise ValueError(f"Balance cannot be negative: {amount_i}")
        if amount_i == 0:
            # Remove zero balances to keep table sparse
            self._balances.pop((pubkey, asset), None)
        else:
            self._balances[(pubkey, asset)] = amount_i
    
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


BalanceKey = tuple[PubKey, AssetId]


def _owned_balance_entries(
    entries: Mapping[BalanceKey, Amount],
) -> tuple[tuple[BalanceKey, ...], tuple[Amount, ...]]:
    # Same admission rules as ``BalanceTable.set``: strict ints, no negatives,
    # zero balances omitted so equal logical states share one representation.
    if not isinstance(entries, Mapping):
        raise TypeError("balance entries must be a mapping")
    rows: list[tuple[BalanceKey, Amount]] = []
    for key, amount in entries.items():
        if type(key) is not tuple or len(key) != 2:
            raise TypeError("balance keys must be (pubkey, asset) tuples")
        pubkey, asset = key
        if type(pubkey) is not str or type(asset) is not str:
            raise TypeError("balance keys must be (str, str) tuples")
        amount_i = _require_balance_int("amount", amount)
        if amount_i < 0:
            raise ValueError(f"Balance cannot be negative: {amount_i}")
        if amount_i == 0:
            continue
        rows.append(((pubkey, asset), amount_i))
    rows.sort(key=lambda row: row[0])
    return tuple(row[0] for row in rows), tuple(row[1] for row in rows)


class BalanceSnapshot:
    """
    Immutable, owned committed balance table (pubkey, asset) -> amount.

    Entries are stored as sorted owned tuples; lookups use binary search so the
    value carries no mutable container. The read API mirrors ``BalanceTable``.
    """

    __slots__ = ("_amounts", "_keys")
    _keys: tuple[BalanceKey, ...]
    _amounts: tuple[Amount, ...]

    def __init__(self, entries: Mapping[BalanceKey, Amount] | None = None) -> None:
        keys, amounts = _owned_balance_entries({} if entries is None else entries)
        object.__setattr__(self, "_keys", keys)
        object.__setattr__(self, "_amounts", amounts)

    def __setattr__(self, name: str, value: object) -> None:
        del name, value
        raise TypeError("committed balance snapshot is immutable")

    def __delattr__(self, name: str) -> None:
        del name
        raise TypeError("committed balance snapshot is immutable")

    def __copy__(self) -> BalanceSnapshot:
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> BalanceSnapshot:
        memo[id(self)] = self
        return self

    def __eq__(self, other: object) -> bool:
        if type(other) is not BalanceSnapshot:
            return NotImplemented
        return self._keys == other._keys and self._amounts == other._amounts

    def __len__(self) -> int:
        return len(self._keys)

    def __repr__(self) -> str:
        return f"BalanceSnapshot({len(self._keys)} entries)"

    def get(self, pubkey: PubKey, asset: AssetId) -> Amount:
        """Get balance for (pubkey, asset). Returns 0 if not found."""
        if type(pubkey) is not str or type(asset) is not str:
            return 0
        key = (pubkey, asset)
        index = bisect_left(self._keys, key)
        if index < len(self._keys) and self._keys[index] == key:
            return self._amounts[index]
        return 0

    def get_all_balances(self) -> dict[BalanceKey, Amount]:
        """Return a fresh dictionary mapping (pubkey, asset) -> amount."""
        return dict(zip(self._keys, self._amounts, strict=True))

    def get_balances_for_asset(self, asset: AssetId) -> dict[PubKey, Amount]:
        """Return a fresh dictionary mapping pubkey -> amount for one asset."""
        result: dict[PubKey, Amount] = {}
        for (pubkey, entry_asset), amount in zip(self._keys, self._amounts, strict=True):
            if entry_asset == asset:
                result[pubkey] = amount
        return result

    def verify_non_negative(self) -> bool:
        """Verify all balances are non-negative."""
        return all(amount >= 0 for amount in self._amounts)

    def to_table(self) -> BalanceTable:
        """Return a fresh mutable builder holding the same balances."""
        table = BalanceTable()
        for (pubkey, asset), amount in zip(self._keys, self._amounts, strict=True):
            table.set(pubkey, asset, amount)
        return table


def snapshot_balances(value: BalanceTable | BalanceSnapshot) -> BalanceSnapshot:
    """Admit a committed balance snapshot from a builder or an existing snapshot.

    Exact types only: subclasses of either phase are rejected so the committed
    value never carries caller-defined behavior.
    """
    if type(value) is BalanceSnapshot:
        return value
    if type(value) is BalanceTable:
        return BalanceSnapshot(value.get_all_balances())
    raise TypeError("balances must be a BalanceTable builder or a BalanceSnapshot")
