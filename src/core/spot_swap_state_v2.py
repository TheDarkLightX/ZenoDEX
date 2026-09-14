"""Owned single-pool Spot frame: physical reserves plus exact LP share rights.

Shares retain the existing proportional burn semantics. They are not fixed
atom liabilities, and swaps never reprice or redistribute them. This candidate
schema does not migrate an old ledger or establish publication authority.
"""

from dataclasses import dataclass, fields

from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.pools import compute_pool_id
from ..state.support_root import LP_LOCK_PUBKEY
from .cpmm import MIN_LP_LOCK
from .domain_limits import DEX_LP_SUPPLY_MAX
from .global_settlement_resource_limits_v2 import (
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    require_raw_tuple_ceiling_v2,
    require_rootable_asset_state_bytes_v2,
)
from .global_settlement_types_v2 import (
    MAX_U64_V2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_token_v2,
    _snapshot_dataclass_tuple_v2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from .spot_swap_plan_v2 import SpotPoolSnapshotV2, _integer, _snapshot_pool


def _require_spot_owner_v2(owner: object) -> None:
    value = _require_token_v2(owner, name="Spot owner")
    if value != canonical_hex_fixed_allow_0x(value, nbytes=48, name="Spot owner"):
        raise ValueError("Spot owner must be canonical lowercase 0x-prefixed 48-byte hex")


@dataclass(frozen=True, slots=True)
class SpotLPPositionV2:
    owner: str
    shares: int
    last_mint_timestamp: int | None = None
    last_remove_timestamp: int | None = None
    churn_tier: int = 0
    last_churn_update_timestamp: int | None = None

    def __post_init__(self) -> None:
        _require_spot_owner_v2(self.owner)
        _integer(self.shares, "LP shares", DEX_LP_SUPPLY_MAX)
        _integer(self.churn_tier, "LP churn tier", MAX_U64_V2)
        for name in ("last_mint_timestamp", "last_remove_timestamp", "last_churn_update_timestamp"):
            value = getattr(self, name)
            if value is not None:
                _integer(value, name, MAX_U64_V2)

    def to_canonical(self) -> dict[str, object]:
        return {field.name: getattr(self, field.name) for field in fields(self)}


@dataclass(frozen=True, slots=True)
class SpotIntentNonceV2:
    owner: str
    last_nonce: int

    def __post_init__(self) -> None:
        _require_spot_owner_v2(self.owner)
        _integer(self.last_nonce, "last intent nonce", (1 << 32) - 1)
        if self.last_nonce == 0:
            raise ValueError("zero intent nonce must be represented by absence")

    def to_canonical(self) -> dict[str, object]:
        return {"owner": self.owner, "last_nonce": self.last_nonce}


@dataclass(frozen=True, slots=True, init=False)
class SpotSwapStateV2:
    module_release_id: str
    _pool: SpotPoolSnapshotV2
    _lp_positions: tuple[SpotLPPositionV2, ...]
    _intent_nonces: tuple[SpotIntentNonceV2, ...]

    def __init__(self, module_release_id: str, pool: SpotPoolSnapshotV2,
                 lp_positions: tuple[SpotLPPositionV2, ...],
                 intent_nonces: tuple[SpotIntentNonceV2, ...] = ()) -> None:
        _require_root_v2(module_release_id, name="Spot module release")
        object.__setattr__(self, "module_release_id", module_release_id)
        object.__setattr__(self, "_pool", _snapshot_pool(pool))
        for name, rows, row_type in (("lp_positions", lp_positions, SpotLPPositionV2),
                                     ("intent_nonces", intent_nonces, SpotIntentNonceV2)):
            require_raw_tuple_ceiling_v2(rows, name=name, ceiling=MAX_BALANCE_ROWS_PER_ASSET_STATE_V2)
            owned = _snapshot_dataclass_tuple_v2(rows, row_type, name)
            _require_ordered_objects_v2(owned, name=name, expected_type=row_type, key="owner")
            object.__setattr__(self, "_" + name, owned)
        self._require_pool_ownership()
        require_rootable_asset_state_bytes_v2(canonical_global_bytes_v2(self.to_canonical()),
                                              name="Spot swap state")

    def _require_pool_ownership(self) -> None:
        pool = self._pool
        if pool.pool_id != compute_pool_id(pool.asset0, pool.asset1, pool.fee_bps,
                                          curve_tag=pool.curve_tag, curve_params=pool.curve_params):
            raise ValueError("Spot pool identity differs from its complete parameters")
        if min(pool.reserve0, pool.reserve1) <= 0 or not MIN_LP_LOCK <= pool.lp_supply <= DEX_LP_SUPPLY_MAX:
            raise ValueError("Spot pool reserves or LP supply outside the existing domain")
        if sum(row.shares for row in self._lp_positions) != pool.lp_supply:
            raise ValueError("Spot LP ownership must cover the complete supply")
        locked = next((row.shares for row in self._lp_positions if row.owner == LP_LOCK_PUBKEY), 0)
        if locked < MIN_LP_LOCK:
            raise ValueError("Spot LP ownership must retain the minimum locked shares")

    @property
    def pool(self) -> SpotPoolSnapshotV2:
        return _snapshot_pool(self._pool)

    @property
    def lp_positions(self) -> tuple[SpotLPPositionV2, ...]:
        return _snapshot_dataclass_tuple_v2(self._lp_positions, SpotLPPositionV2, "LP positions")

    @property
    def intent_nonces(self) -> tuple[SpotIntentNonceV2, ...]:
        return _snapshot_dataclass_tuple_v2(self._intent_nonces, SpotIntentNonceV2, "intent nonces")

    def intent_nonce(self, owner: str) -> int:
        _require_spot_owner_v2(owner)
        return next((row.last_nonce for row in self._intent_nonces if row.owner == owner), 0)

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": "zenodex/spot-swap-state/v2",
            "module_release_id": self.module_release_id,
            "pool": {field.name: getattr(self._pool, field.name) for field in fields(SpotPoolSnapshotV2)},
            "lp_positions": self.lp_positions,
            "intent_nonces": self.intent_nonces,
        }

    @property
    def state_root(self) -> str:
        return hash_global_v2("spot-swap-state-v2", self.to_canonical())


def snapshot_spot_swap_state_v2(state: SpotSwapStateV2) -> SpotSwapStateV2:
    if type(state) is not SpotSwapStateV2:
        raise TypeError("Spot swap state must be exact")
    # Validate raw capacities before any getter traverses a forged backing
    # tuple. The constructor performs the one required defensive copy.
    try:
        return SpotSwapStateV2(
            object.__getattribute__(state, "module_release_id"),
            object.__getattribute__(state, "_pool"),
            object.__getattribute__(state, "_lp_positions"),
            object.__getattribute__(state, "_intent_nonces"),
        )
    except AttributeError as exc:
        raise TypeError("Spot swap state is missing required data") from exc
