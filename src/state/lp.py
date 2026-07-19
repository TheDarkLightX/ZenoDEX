"""
LP token balance tracking for TauSwap pools.

LP tokens are scoped per pool_id and are tracked separately from asset balances.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Dict, NoReturn, Optional, Tuple, cast

from .balances import Amount, PubKey, decoded_fixed_identity_or_text
from .immutable import FrozenDict, SealedValue, seal_dataclass_init

# Type alias
PoolId = str


def _require_lp_int(name: str, value: object) -> int:
    # LP balances feed canonical state roots; reject bool-as-int and non-int
    # numerics before they can enter sparse state.
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    return value


def _require_lp_non_negative_int(name: str, value: object) -> int:
    value_i = _require_lp_int(name, value)
    if value_i < 0:
        raise ValueError(f"{name} must be a non-negative int: {value!r}")
    return value_i


def _require_lp_key(pubkey: object, pool_id: object) -> tuple[PubKey, PoolId]:
    if type(pubkey) is not str or not pubkey:
        raise TypeError("pubkey must be a non-empty exact string")
    if type(pool_id) is not str or not pool_id:
        raise TypeError("pool_id must be a non-empty exact string")
    return pubkey, pool_id


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class LPDurationRiskMetadata(SealedValue):
    """Committed duration-risk metadata for one aggregate LP position key."""

    last_mint_timestamp: Optional[int] = None
    last_remove_timestamp: Optional[int] = None
    churn_tier: int = 0
    last_churn_update_timestamp: Optional[int] = None

    def __post_init__(self) -> None:
        for name, value in (
            ("last_mint_timestamp", self.last_mint_timestamp),
            ("last_remove_timestamp", self.last_remove_timestamp),
            ("last_churn_update_timestamp", self.last_churn_update_timestamp),
        ):
            if value is not None:
                _require_lp_non_negative_int(name, value)
        _require_lp_non_negative_int("churn_tier", self.churn_tier)


def _validated_lp_key(
    raw_key: object,
    *,
    decoded_seen: dict[tuple[tuple[str, str], tuple[str, str]], tuple[str, str]],
) -> tuple[PubKey, PoolId]:
    if type(raw_key) is not tuple or len(raw_key) != 2:
        raise TypeError("LP keys must be exact (pubkey, pool_id) tuples")
    key = _require_lp_key(raw_key[0], raw_key[1])
    decoded_key = (
        decoded_fixed_identity_or_text(key[0], nbytes=48, name="LP pubkey"),
        decoded_fixed_identity_or_text(key[1], nbytes=32, name="LP pool_id"),
    )
    prior = decoded_seen.get(decoded_key)
    if prior is not None and prior != key:
        raise ValueError("duplicate decoded (pubkey, pool_id) in LP state")
    decoded_seen[decoded_key] = key
    return key


def _validated_lp_map(
    raw: object,
    *,
    name: str,
    decoded_seen: dict[tuple[tuple[str, str], tuple[str, str]], tuple[str, str]],
    positive: bool,
) -> dict[tuple[PubKey, PoolId], int]:
    if type(raw) not in (dict, FrozenDict):
        raise TypeError(f"{name} storage must be an exact dict snapshot")
    owned: dict[tuple[PubKey, PoolId], int] = {}
    raw_mapping = cast(Mapping[object, object], raw)
    for raw_key, raw_value in raw_mapping.items():
        key = _validated_lp_key(raw_key, decoded_seen=decoded_seen)
        value = _require_lp_non_negative_int(name, raw_value)
        if positive and value == 0:
            raise ValueError(f"stored {name} values must be positive")
        owned[key] = value
    return owned


def _validated_lp_snapshot(
    source: "LPTable",
) -> tuple[
    dict[tuple[PubKey, PoolId], Amount],
    dict[tuple[PubKey, PoolId], int],
    dict[tuple[PubKey, PoolId], int],
    dict[tuple[PubKey, PoolId], int],
    dict[tuple[PubKey, PoolId], int],
]:
    decoded_seen: dict[tuple[tuple[str, str], tuple[str, str]], tuple[str, str]] = {}
    balances = _validated_lp_map(
        object.__getattribute__(source, "_balances"),
        name="LP balance",
        decoded_seen=decoded_seen,
        positive=True,
    )
    last_mint = _validated_lp_map(
        object.__getattribute__(source, "_last_mint_timestamps"),
        name="last mint timestamp",
        decoded_seen=decoded_seen,
        positive=False,
    )
    last_remove = _validated_lp_map(
        object.__getattribute__(source, "_last_remove_timestamps"),
        name="last remove timestamp",
        decoded_seen=decoded_seen,
        positive=False,
    )
    churn_tiers = _validated_lp_map(
        object.__getattribute__(source, "_churn_tiers"),
        name="LP churn tier",
        decoded_seen=decoded_seen,
        positive=True,
    )
    last_churn_update = _validated_lp_map(
        object.__getattribute__(source, "_last_churn_update_timestamps"),
        name="last churn update timestamp",
        decoded_seen=decoded_seen,
        positive=False,
    )
    missing_balance = set(last_mint) - set(balances)
    if missing_balance:
        raise ValueError("last mint timestamp requires a positive LP balance")
    return balances, last_mint, last_remove, churn_tiers, last_churn_update


class LPTable:
    """
    Deterministic LP balance table mapping (pubkey, pool_id) -> lp_amount.

    Notes:
    - LP balances are always non-negative.
    - Zero balances are omitted to keep the table sparse.
    """

    __slots__ = (
        "_balances",
        "_last_mint_timestamps",
        "_last_remove_timestamps",
        "_churn_tiers",
        "_last_churn_update_timestamps",
    )

    def __init__(self) -> None:
        self._balances: Dict[Tuple[PubKey, PoolId], Amount] = {}
        self._last_mint_timestamps: Dict[Tuple[PubKey, PoolId], int] = {}
        self._last_remove_timestamps: Dict[Tuple[PubKey, PoolId], int] = {}
        self._churn_tiers: Dict[Tuple[PubKey, PoolId], int] = {}
        self._last_churn_update_timestamps: Dict[Tuple[PubKey, PoolId], int] = {}

    def get(self, pubkey: PubKey, pool_id: PoolId) -> Amount:
        """Get LP balance for (pubkey, pool_id). Returns 0 if not found."""
        return self._balances.get(_require_lp_key(pubkey, pool_id), 0)

    def set(self, pubkey: PubKey, pool_id: PoolId, amount: Amount) -> None:
        """Set LP balance for (pubkey, pool_id)."""
        key = _require_lp_key(pubkey, pool_id)
        amount_i = _require_lp_int("amount", amount)
        if amount_i < 0:
            raise ValueError(f"LP balance cannot be negative: {amount_i}")
        if amount_i == 0:
            self._balances.pop(key, None)
            self._last_mint_timestamps.pop(key, None)
        else:
            self._balances[key] = amount_i

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
        return self._last_mint_timestamps.get(_require_lp_key(pubkey, pool_id))

    def set_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> None:
        """Bind a runtime mint timestamp to an existing LP balance."""
        key = _require_lp_key(pubkey, pool_id)
        timestamp_i = _require_lp_non_negative_int("last mint timestamp", timestamp)
        if self.get(pubkey, pool_id) <= 0:
            raise ValueError("cannot set LP mint timestamp for an empty balance")
        self._last_mint_timestamps[key] = timestamp_i

    def clear_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        """Remove tracked LP mint timestamp metadata."""
        self._last_mint_timestamps.pop(_require_lp_key(pubkey, pool_id), None)

    def get_all_last_mint_timestamps(self) -> Dict[Tuple[PubKey, PoolId], int]:
        """Return tracked LP mint timestamps for non-empty LP balances."""
        return {
            key: timestamp
            for key, timestamp in self._last_mint_timestamps.items()
            if self._balances.get(key, 0) > 0
        }

    def get_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> Optional[int]:
        """Return the last accepted LP burn timestamp for a position key, if tracked."""
        return self._last_remove_timestamps.get(_require_lp_key(pubkey, pool_id))

    def set_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> None:
        """Bind a runtime remove timestamp to an LP position key."""
        key = _require_lp_key(pubkey, pool_id)
        timestamp_i = _require_lp_non_negative_int("last remove timestamp", timestamp)
        self._last_remove_timestamps[key] = timestamp_i

    def clear_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        """Remove tracked LP remove timestamp metadata."""
        self._last_remove_timestamps.pop(_require_lp_key(pubkey, pool_id), None)

    def get_all_last_remove_timestamps(self) -> Dict[Tuple[PubKey, PoolId], int]:
        """Return tracked LP remove timestamps."""
        return dict(self._last_remove_timestamps)

    def get_churn_tier(self, pubkey: PubKey, pool_id: PoolId) -> int:
        """Return the committed LP churn tier for a position key."""
        return _require_lp_non_negative_int(
            "LP churn tier", self._churn_tiers.get(_require_lp_key(pubkey, pool_id), 0)
        )

    def set_churn_tier(self, pubkey: PubKey, pool_id: PoolId, tier: int) -> None:
        """Set the committed LP churn tier for a position key."""
        tier_i = _require_lp_non_negative_int("LP churn tier", tier)
        key = _require_lp_key(pubkey, pool_id)
        if tier_i == 0:
            self._churn_tiers.pop(key, None)
        else:
            self._churn_tiers[key] = tier_i

    def get_all_churn_tiers(self) -> Dict[Tuple[PubKey, PoolId], int]:
        """Return tracked LP churn tiers."""
        return dict(self._churn_tiers)

    def get_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> Optional[int]:
        """Return the last timestamp at which churn metadata was updated."""
        return self._last_churn_update_timestamps.get(_require_lp_key(pubkey, pool_id))

    def set_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> None:
        """Bind a timestamp to the committed LP churn-tier state."""
        key = _require_lp_key(pubkey, pool_id)
        timestamp_i = _require_lp_non_negative_int("last churn update timestamp", timestamp)
        self._last_churn_update_timestamps[key] = timestamp_i

    def clear_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        """Remove tracked LP churn update timestamp metadata."""
        self._last_churn_update_timestamps.pop(_require_lp_key(pubkey, pool_id), None)

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


class FrozenLPTable(LPTable):
    """Transitively immutable LP ownership and duration-risk snapshot."""

    __slots__ = ()

    def __init__(self, source: LPTable) -> None:
        try:
            object.__getattribute__(self, "_balances")
        except AttributeError:
            pass
        else:
            raise TypeError("FrozenLPTable is already initialized")
        if type(source) not in (LPTable, FrozenLPTable):
            raise TypeError("source must be an exact LPTable snapshot")
        balances, last_mint, last_remove, churn_tiers, last_churn_update = (
            _validated_lp_snapshot(source)
        )
        object.__setattr__(self, "_balances", FrozenDict(balances))
        object.__setattr__(
            self,
            "_last_mint_timestamps",
            FrozenDict(last_mint),
        )
        object.__setattr__(
            self,
            "_last_remove_timestamps",
            FrozenDict(last_remove),
        )
        object.__setattr__(self, "_churn_tiers", FrozenDict(churn_tiers))
        object.__setattr__(
            self,
            "_last_churn_update_timestamps",
            FrozenDict(last_churn_update),
        )

    def __setattr__(self, name: str, value: object) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def set(self, pubkey: PubKey, pool_id: PoolId, amount: Amount) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def add(self, pubkey: PubKey, pool_id: PoolId, delta: int) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def subtract(self, pubkey: PubKey, pool_id: PoolId, delta: Amount) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def set_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def clear_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def set_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId, timestamp: int) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def clear_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def set_churn_tier(self, pubkey: PubKey, pool_id: PoolId, tier: int) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def set_last_churn_update_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
        timestamp: int,
    ) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")

    def clear_last_churn_update_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> NoReturn:
        raise TypeError("FrozenLPTable cannot be mutated")


def copy_lp_table(source: LPTable) -> LPTable:
    """Return a complete mutable copy, including duration-risk metadata."""

    if type(source) not in (LPTable, FrozenLPTable):
        raise TypeError("source must be an exact LPTable snapshot")
    balances, last_mint, last_remove, churn_tiers, last_churn_update = (
        _validated_lp_snapshot(source)
    )
    copied = LPTable()
    for (pubkey, pool_id), amount in balances.items():
        copied.set(pubkey, pool_id, amount)
    for (pubkey, pool_id), timestamp in last_mint.items():
        copied.set_last_mint_timestamp(pubkey, pool_id, timestamp)
    for (pubkey, pool_id), timestamp in last_remove.items():
        copied.set_last_remove_timestamp(pubkey, pool_id, timestamp)
    for (pubkey, pool_id), tier in churn_tiers.items():
        copied.set_churn_tier(pubkey, pool_id, tier)
    for (pubkey, pool_id), timestamp in last_churn_update.items():
        copied.set_last_churn_update_timestamp(pubkey, pool_id, timestamp)
    return copied


def freeze_lp_table(source: LPTable) -> FrozenLPTable:
    if type(source) is FrozenLPTable:
        for name in LPTable.__slots__:
            try:
                storage = object.__getattribute__(source, name)
            except AttributeError as exc:
                raise TypeError("FrozenLPTable is not initialized") from exc
            if type(storage) is not FrozenDict:
                raise TypeError("FrozenLPTable storage is not sealed")
        return source
    if type(source) is not LPTable:
        raise TypeError("source must be an exact LPTable snapshot")
    return FrozenLPTable(source)
