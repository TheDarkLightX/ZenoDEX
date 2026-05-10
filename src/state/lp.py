"""
LP token balance tracking for TauSwap pools.

LP tokens are scoped per pool_id and are tracked separately from asset balances.
"""

from __future__ import annotations

from typing import Dict, Optional, Tuple

from .balances import Amount, PubKey

# Type alias
PoolId = str


class LPTable:
    """
    Deterministic LP balance table mapping (pubkey, pool_id) -> lp_amount.

    Notes:
    - LP balances are always non-negative.
    - Zero balances are omitted to keep the table sparse.
    """

    def __init__(self) -> None:
        self._balances: Dict[Tuple[PubKey, PoolId], Amount] = {}
        self._last_mint_timestamps: Dict[Tuple[PubKey, PoolId], int] = {}

    def get(self, pubkey: PubKey, pool_id: PoolId) -> Amount:
        """Get LP balance for (pubkey, pool_id). Returns 0 if not found."""
        return self._balances.get((pubkey, pool_id), 0)

    def set(self, pubkey: PubKey, pool_id: PoolId, amount: Amount) -> None:
        """Set LP balance for (pubkey, pool_id)."""
        if amount < 0:
            raise ValueError(f"LP balance cannot be negative: {amount}")
        if amount == 0:
            self._balances.pop((pubkey, pool_id), None)
            self._last_mint_timestamps.pop((pubkey, pool_id), None)
        else:
            self._balances[(pubkey, pool_id)] = amount

    def add(self, pubkey: PubKey, pool_id: PoolId, delta: int) -> None:
        """Add delta to an LP balance (delta may be negative)."""
        current = self.get(pubkey, pool_id)
        new_balance = current + delta
        if new_balance < 0:
            raise ValueError(
                f"Insufficient LP balance: {current} + {delta} = {new_balance} < 0"
            )
        self.set(pubkey, pool_id, new_balance)

    def subtract(self, pubkey: PubKey, pool_id: PoolId, delta: Amount) -> None:
        """Subtract a non-negative amount from an LP balance."""
        if delta < 0:
            raise ValueError(f"Delta must be non-negative: {delta}")
        self.add(pubkey, pool_id, -delta)

    def get_all_balances(self) -> Dict[Tuple[PubKey, PoolId], Amount]:
        """Return all LP balances."""
        return dict(self._balances)

    def get_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> Optional[int]:
        """Return the last mint timestamp for an LP position, if tracked."""
        return self._last_mint_timestamps.get((pubkey, pool_id))

    def set_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> None:
        """Bind a runtime mint timestamp to an existing LP balance."""
        if not isinstance(timestamp, int) or isinstance(timestamp, bool) or timestamp < 0:
            raise ValueError(f"last mint timestamp must be a non-negative int: {timestamp!r}")
        if self.get(pubkey, pool_id) <= 0:
            raise ValueError("cannot set LP mint timestamp for an empty balance")
        self._last_mint_timestamps[(pubkey, pool_id)] = timestamp

    def clear_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        """Remove tracked LP mint timestamp metadata."""
        self._last_mint_timestamps.pop((pubkey, pool_id), None)

    def get_all_last_mint_timestamps(self) -> Dict[Tuple[PubKey, PoolId], int]:
        """Return tracked LP mint timestamps for non-empty LP balances."""
        return {
            key: timestamp
            for key, timestamp in self._last_mint_timestamps.items()
            if self._balances.get(key, 0) > 0
        }

    def verify_non_negative(self) -> bool:
        """Verify all stored balances are non-negative."""
        return all(amount >= 0 for amount in self._balances.values())

    def __repr__(self) -> str:
        return f"LPTable({len(self._balances)} entries)"
