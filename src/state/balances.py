"""
Multi-asset balance tracking with deterministic ordering.

Implements BalanceTable[PubKey, AssetId] -> Amount
"""

from typing import Dict, Tuple

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

    def __setattr__(self, name: str, value: object) -> None:
        # Immutable committed subclasses set this private seal after construction.
        # Keeping the guard on the base blocks explicit
        # ``BalanceTable.__setattr__(snapshot, ...)`` bypass attempts while
        # ordinary scratch tables remain mutable.
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("committed balance snapshot is immutable")
        object.__setattr__(self, name, value)

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
            raise ValueError(f"Insufficient balance: {current} + {delta_i} = {new_balance} < 0")
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
