"""
LP token balance tracking for TauSwap pools.

LP tokens are scoped per pool_id and are tracked separately from asset balances.

Two phases share one read API:

- ``LPTable`` is the mutable builder used while a batch is computed, replayed
  or decoded.
- ``LPSnapshot`` is the immutable committed value held by ``DexState``. It owns
  balances and all duration-risk metadata rails; ``to_table()`` returns a fresh
  builder copy for the next transition.
"""

from __future__ import annotations

from bisect import bisect_left
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple

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
            raise ValueError(
                f"Insufficient LP balance: {current} + {delta_i} = {new_balance} < 0"
            )
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

    def set_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> None:
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


LPKey = tuple[PubKey, PoolId]
_EMPTY_DURATION_RISK = LPDurationRiskMetadata()


def _owned_lp_timestamp(name: str, value: int | None) -> int | None:
    return None if value is None else _require_lp_non_negative_int(name, value)


@dataclass(frozen=True, slots=True)
class LPPositionRow:
    """Owned committed row for one (pubkey, pool_id) LP position key."""

    amount: Amount
    duration_risk: LPDurationRiskMetadata

    def __post_init__(self) -> None:
        amount = _require_lp_non_negative_int("amount", self.amount)
        metadata = self.duration_risk
        if type(metadata) is not LPDurationRiskMetadata:
            raise TypeError("duration_risk must be an LPDurationRiskMetadata value")
        metadata = LPDurationRiskMetadata(
            last_mint_timestamp=_owned_lp_timestamp(
                "last mint timestamp", metadata.last_mint_timestamp,
            ),
            last_remove_timestamp=_owned_lp_timestamp(
                "last remove timestamp", metadata.last_remove_timestamp,
            ),
            churn_tier=_require_lp_non_negative_int("LP churn tier", metadata.churn_tier),
            last_churn_update_timestamp=_owned_lp_timestamp(
                "last churn update timestamp", metadata.last_churn_update_timestamp,
            ),
        )
        # ``LPTable`` only tracks mint timestamps for positive balances.
        if amount == 0 and metadata.last_mint_timestamp is not None:
            raise ValueError("cannot commit an LP mint timestamp for an empty balance")
        object.__setattr__(self, "amount", amount)
        object.__setattr__(self, "duration_risk", metadata)

    @property
    def is_empty(self) -> bool:
        return self.amount == 0 and self.duration_risk == _EMPTY_DURATION_RISK


def _require_lp_key(key: object) -> LPKey:
    if type(key) is not tuple or len(key) != 2:
        raise TypeError("LP keys must be (pubkey, pool_id) tuples")
    pubkey, pool_id = key
    if type(pubkey) is not str or type(pool_id) is not str:
        raise TypeError("LP keys must be (str, str) tuples")
    return (pubkey, pool_id)


def _owned_lp_rows(
    balances: Mapping[LPKey, Amount],
    duration_risk: Mapping[LPKey, LPDurationRiskMetadata],
) -> tuple[tuple[LPKey, ...], tuple[LPPositionRow, ...]]:
    if not isinstance(balances, Mapping):
        raise TypeError("LP balances must be a mapping")
    if not isinstance(duration_risk, Mapping):
        raise TypeError("LP duration-risk metadata must be a mapping")
    amounts: dict[LPKey, Amount] = {}
    for key, amount in balances.items():
        amounts[_require_lp_key(key)] = _require_lp_int("amount", amount)
    metadata_by_key: dict[LPKey, LPDurationRiskMetadata] = {}
    for key, metadata in duration_risk.items():
        metadata_by_key[_require_lp_key(key)] = metadata
    rows: list[tuple[LPKey, LPPositionRow]] = []
    for key in sorted(set(amounts) | set(metadata_by_key)):
        row = LPPositionRow(
            amount=amounts.get(key, 0),
            duration_risk=metadata_by_key.get(key, _EMPTY_DURATION_RISK),
        )
        if row.is_empty:
            continue
        rows.append((key, row))
    return tuple(key for key, _row in rows), tuple(row for _key, row in rows)


class LPSnapshot:
    """
    Immutable, owned committed LP table keyed by (pubkey, pool_id).

    Each key owns one ``LPPositionRow`` (balance plus duration-risk metadata).
    The read API mirrors ``LPTable`` so encoders, gates and copy helpers accept
    either phase.
    """

    __slots__ = ("_keys", "_rows")  # sorted
    _keys: tuple[LPKey, ...]
    _rows: tuple[LPPositionRow, ...]

    def __init__(
        self,
        balances: Mapping[LPKey, Amount] | None = None,
        duration_risk: Mapping[LPKey, LPDurationRiskMetadata] | None = None,
    ) -> None:
        keys, rows = _owned_lp_rows(
            {} if balances is None else balances,
            {} if duration_risk is None else duration_risk,
        )
        object.__setattr__(self, "_keys", keys)
        object.__setattr__(self, "_rows", rows)

    def __setattr__(self, name: str, value: object) -> None:
        del name, value
        raise TypeError("committed LP snapshot is immutable")

    def __delattr__(self, name: str) -> None:
        del name
        raise TypeError("committed LP snapshot is immutable")

    def __copy__(self) -> LPSnapshot:
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> LPSnapshot:
        memo[id(self)] = self
        return self

    def __eq__(self, other: object) -> bool:
        if type(other) is not LPSnapshot:
            return NotImplemented
        return self._keys == other._keys and self._rows == other._rows

    def __len__(self) -> int:
        return len(self._keys)

    def __repr__(self) -> str:
        return f"LPSnapshot({sum(1 for row in self._rows if row.amount > 0)} entries)"

    def _row(self, pubkey: PubKey, pool_id: PoolId) -> LPPositionRow | None:
        if type(pubkey) is not str or type(pool_id) is not str:
            return None
        key = (pubkey, pool_id)
        index = bisect_left(self._keys, key)
        if index < len(self._keys) and self._keys[index] == key:
            return self._rows[index]
        return None

    def get(self, pubkey: PubKey, pool_id: PoolId) -> Amount:
        """Get LP balance for (pubkey, pool_id). Returns 0 if not found."""
        row = self._row(pubkey, pool_id)
        return 0 if row is None else row.amount

    def get_all_balances(self) -> dict[LPKey, Amount]:
        """Return all positive LP balances."""
        return {key: row.amount for key, row in zip(self._keys, self._rows, strict=True) if row.amount > 0}

    def get_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> int | None:
        row = self._row(pubkey, pool_id)
        return None if row is None else row.duration_risk.last_mint_timestamp

    def get_all_last_mint_timestamps(self) -> dict[LPKey, int]:
        return {
            key: row.duration_risk.last_mint_timestamp
            for key, row in zip(self._keys, self._rows, strict=True)
            if row.duration_risk.last_mint_timestamp is not None and row.amount > 0
        }

    def get_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> int | None:
        row = self._row(pubkey, pool_id)
        return None if row is None else row.duration_risk.last_remove_timestamp

    def get_all_last_remove_timestamps(self) -> dict[LPKey, int]:
        return {
            key: row.duration_risk.last_remove_timestamp
            for key, row in zip(self._keys, self._rows, strict=True)
            if row.duration_risk.last_remove_timestamp is not None
        }

    def get_churn_tier(self, pubkey: PubKey, pool_id: PoolId) -> int:
        row = self._row(pubkey, pool_id)
        return 0 if row is None else row.duration_risk.churn_tier

    def get_all_churn_tiers(self) -> dict[LPKey, int]:
        return {
            key: row.duration_risk.churn_tier
            for key, row in zip(self._keys, self._rows, strict=True)
            if row.duration_risk.churn_tier > 0
        }

    def get_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> int | None:
        row = self._row(pubkey, pool_id)
        return None if row is None else row.duration_risk.last_churn_update_timestamp

    def get_all_last_churn_update_timestamps(self) -> dict[LPKey, int]:
        return {
            key: row.duration_risk.last_churn_update_timestamp
            for key, row in zip(self._keys, self._rows, strict=True)
            if row.duration_risk.last_churn_update_timestamp is not None
        }

    def get_duration_risk_metadata(self, pubkey: PubKey, pool_id: PoolId) -> LPDurationRiskMetadata:
        row = self._row(pubkey, pool_id)
        return _EMPTY_DURATION_RISK if row is None else row.duration_risk

    def get_all_duration_risk_metadata(self) -> dict[LPKey, LPDurationRiskMetadata]:
        return {
            key: row.duration_risk
            for key, row in zip(self._keys, self._rows, strict=True)
            if row.duration_risk != _EMPTY_DURATION_RISK
        }

    def verify_non_negative(self) -> bool:
        """Verify all committed balances are non-negative."""
        return all(row.amount >= 0 for row in self._rows)

    def to_table(self) -> LPTable:
        """Return a fresh mutable builder holding the same balances and metadata."""
        table = LPTable()
        for (pubkey, pool_id), row in zip(self._keys, self._rows, strict=True):
            if row.amount > 0:
                table.set(pubkey, pool_id, row.amount)
            metadata = row.duration_risk
            if metadata.last_mint_timestamp is not None:
                table.set_last_mint_timestamp(pubkey, pool_id, metadata.last_mint_timestamp)
            if metadata.last_remove_timestamp is not None:
                table.set_last_remove_timestamp(pubkey, pool_id, metadata.last_remove_timestamp)
            if metadata.churn_tier > 0:
                table.set_churn_tier(pubkey, pool_id, metadata.churn_tier)
            if metadata.last_churn_update_timestamp is not None:
                table.set_last_churn_update_timestamp(
                    pubkey, pool_id, metadata.last_churn_update_timestamp
                )
        return table


def snapshot_lp_table(value: LPTable | LPSnapshot) -> LPSnapshot:
    """Admit a committed LP snapshot from a builder or an existing snapshot."""
    if type(value) is LPSnapshot:
        return value
    if type(value) is LPTable:
        return LPSnapshot(
            balances=value.get_all_balances(),
            duration_risk=value.get_all_duration_risk_metadata(),
        )
    raise TypeError("lp_balances must be an LPTable builder or an LPSnapshot")
