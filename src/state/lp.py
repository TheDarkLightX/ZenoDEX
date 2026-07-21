"""
LP token balance tracking for TauSwap pools.

LP tokens are scoped per pool_id and are tracked separately from asset balances.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional, Tuple

from .balances import Amount, PubKey

# Type alias
PoolId = str


def _require_lp_int(name: str, value: object) -> int:
    # LP balances feed canonical state roots; reject bool-as-int and non-int
    # numerics before they can enter sparse state.
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_lp_non_negative_int(name: str, value: object) -> int:
    value_i = _require_lp_int(name, value)
    if value_i < 0:
        raise ValueError(f"{name} must be a non-negative int: {value!r}")
    return value_i


@dataclass(frozen=True)
class LPDurationRiskMetadata:
    """Committed duration-risk metadata for one aggregate LP position key."""

    last_mint_timestamp: Optional[int] = None
    last_remove_timestamp: Optional[int] = None
    churn_tier: int = 0
    last_churn_update_timestamp: Optional[int] = None


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
        self._last_remove_timestamps: Dict[Tuple[PubKey, PoolId], int] = {}
        self._churn_tiers: Dict[Tuple[PubKey, PoolId], int] = {}
        self._last_churn_update_timestamps: Dict[Tuple[PubKey, PoolId], int] = {}

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("committed LP snapshot is immutable")
        object.__setattr__(self, name, value)

    def get(self, pubkey: PubKey, pool_id: PoolId) -> Amount:
        """Get LP balance for (pubkey, pool_id). Returns 0 if not found."""
        return self._balances.get((pubkey, pool_id), 0)

    def set(self, pubkey: PubKey, pool_id: PoolId, amount: Amount) -> None:
        """Set LP balance for (pubkey, pool_id)."""
        amount_i = _require_lp_int("amount", amount)
        if amount_i < 0:
            raise ValueError(f"LP balance cannot be negative: {amount_i}")
        if amount_i == 0:
            self._balances.pop((pubkey, pool_id), None)
            self._last_mint_timestamps.pop((pubkey, pool_id), None)
        else:
            self._balances[(pubkey, pool_id)] = amount_i

    def add(self, pubkey: PubKey, pool_id: PoolId, delta: int) -> None:
        """Add delta to an LP balance (delta may be negative)."""
        delta_i = _require_lp_int("delta", delta)
        current = self.get(pubkey, pool_id)
        new_balance = current + delta_i
        if new_balance < 0:
            raise ValueError(f"Insufficient LP balance: {current} + {delta_i} = {new_balance} < 0")
        self.set(pubkey, pool_id, new_balance)

    def subtract(self, pubkey: PubKey, pool_id: PoolId, delta: Amount) -> None:
        """Subtract a non-negative amount from an LP balance."""
        delta_i = _require_lp_int("delta", delta)
        if delta_i < 0:
            raise ValueError(f"Delta must be non-negative: {delta_i}")
        self.add(pubkey, pool_id, -delta_i)

    def get_all_balances(self) -> Dict[Tuple[PubKey, PoolId], Amount]:
        """Return all LP balances."""
        return dict(self._balances)

    def get_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> Optional[int]:
        """Return the last mint timestamp for an LP position, if tracked."""
        return self._last_mint_timestamps.get((pubkey, pool_id))

    def set_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> None:
        """Bind a runtime mint timestamp to an existing LP balance."""
        timestamp_i = _require_lp_non_negative_int("last mint timestamp", timestamp)
        if self.get(pubkey, pool_id) <= 0:
            raise ValueError("cannot set LP mint timestamp for an empty balance")
        self._last_mint_timestamps[(pubkey, pool_id)] = timestamp_i

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

    def get_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> Optional[int]:
        """Return the last accepted LP burn timestamp for a position key, if tracked."""
        return self._last_remove_timestamps.get((pubkey, pool_id))

    def set_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> None:
        """Bind a runtime remove timestamp to an LP position key."""
        timestamp_i = _require_lp_non_negative_int("last remove timestamp", timestamp)
        self._last_remove_timestamps[(pubkey, pool_id)] = timestamp_i

    def clear_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        """Remove tracked LP remove timestamp metadata."""
        self._last_remove_timestamps.pop((pubkey, pool_id), None)

    def get_all_last_remove_timestamps(self) -> Dict[Tuple[PubKey, PoolId], int]:
        """Return tracked LP remove timestamps."""
        return dict(self._last_remove_timestamps)

    def get_churn_tier(self, pubkey: PubKey, pool_id: PoolId) -> int:
        """Return the committed LP churn tier for a position key."""
        return _require_lp_non_negative_int(
            "LP churn tier", self._churn_tiers.get((pubkey, pool_id), 0)
        )

    def set_churn_tier(self, pubkey: PubKey, pool_id: PoolId, tier: int) -> None:
        """Set the committed LP churn tier for a position key."""
        tier_i = _require_lp_non_negative_int("LP churn tier", tier)
        key = (pubkey, pool_id)
        if tier_i == 0:
            self._churn_tiers.pop(key, None)
        else:
            self._churn_tiers[key] = tier_i

    def get_all_churn_tiers(self) -> Dict[Tuple[PubKey, PoolId], int]:
        """Return tracked LP churn tiers."""
        return dict(self._churn_tiers)

    def get_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> Optional[int]:
        """Return the last timestamp at which churn metadata was updated."""
        return self._last_churn_update_timestamps.get((pubkey, pool_id))

    def set_last_churn_update_timestamp(
        self, pubkey: PubKey, pool_id: PoolId, timestamp: int
    ) -> None:
        """Bind a timestamp to the committed LP churn-tier state."""
        timestamp_i = _require_lp_non_negative_int("last churn update timestamp", timestamp)
        self._last_churn_update_timestamps[(pubkey, pool_id)] = timestamp_i

    def clear_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        """Remove tracked LP churn update timestamp metadata."""
        self._last_churn_update_timestamps.pop((pubkey, pool_id), None)

    def get_all_last_churn_update_timestamps(self) -> Dict[Tuple[PubKey, PoolId], int]:
        """Return tracked LP churn update timestamps."""
        return dict(self._last_churn_update_timestamps)

    def get_duration_risk_metadata(self, pubkey: PubKey, pool_id: PoolId) -> LPDurationRiskMetadata:
        """Return all duration-risk metadata for one LP position key."""
        return LPDurationRiskMetadata(
            last_mint_timestamp=self.get_last_mint_timestamp(pubkey, pool_id),
            last_remove_timestamp=self.get_last_remove_timestamp(pubkey, pool_id),
            churn_tier=self.get_churn_tier(pubkey, pool_id),
            last_churn_update_timestamp=self.get_last_churn_update_timestamp(pubkey, pool_id),
        )

    def get_all_duration_risk_metadata(self) -> Dict[Tuple[PubKey, PoolId], LPDurationRiskMetadata]:
        """Return all non-empty LP duration-risk metadata keyed by (pubkey, pool_id)."""
        keys = (
            set(self._last_mint_timestamps)
            | set(self._last_remove_timestamps)
            | set(self._churn_tiers)
            | set(self._last_churn_update_timestamps)
        )
        out: Dict[Tuple[PubKey, PoolId], LPDurationRiskMetadata] = {}
        for key in keys:
            metadata = self.get_duration_risk_metadata(key[0], key[1])
            if (
                metadata.last_mint_timestamp is not None
                or metadata.last_remove_timestamp is not None
                or metadata.churn_tier > 0
                or metadata.last_churn_update_timestamp is not None
            ):
                out[key] = metadata
        return out

    def verify_non_negative(self) -> bool:
        """Verify all stored balances are non-negative."""
        return all(amount >= 0 for amount in self._balances.values())

    def __repr__(self) -> str:
        return f"LPTable({len(self._balances)} entries)"
