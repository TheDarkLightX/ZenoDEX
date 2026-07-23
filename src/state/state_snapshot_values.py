"""Exact immutable values admitted by the FCIS state snapshot profile.

These records contain only exact scalars, tuples, ``OwnedEnumV1``, and
``OwnedMapV1`` values. They do not inherit legacy mutable domain classes.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeVar, cast, final

from ..core.domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    PERP_POSITION_MAX,
)
from ..core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from ..core.perp_v2.math import MAX_COLLATERAL, MAX_EPOCH
from ..core.perps import (
    PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS,
    PERP_ISOLATED_GLOBAL_KEYS,
    PERPS_STATE_VERSION_V4,
    PERPS_STATE_VERSION_V5,
)
from .owned_collections import OwnedEnumV1, OwnedMapV1
from .pools import (
    compute_pool_id,
    normalize_curve_config,
    normalize_pool_asset_pair,
    validate_pool_id_format,
)

FCIS_STATE_SCHEMA_REVISION_V1 = "zenodex/fcis-authority-state/v1"

BALANCE_MAP_SCHEMA_ID_V1 = "zenodex/balances/v1"
LP_BALANCE_MAP_SCHEMA_ID_V1 = "zenodex/lp/balances/v1"
LP_LAST_MINT_MAP_SCHEMA_ID_V1 = "zenodex/lp/last-mint/v1"
LP_LAST_REMOVE_MAP_SCHEMA_ID_V1 = "zenodex/lp/last-remove/v1"
LP_CHURN_TIER_MAP_SCHEMA_ID_V1 = "zenodex/lp/churn-tier/v1"
LP_LAST_CHURN_UPDATE_MAP_SCHEMA_ID_V1 = "zenodex/lp/last-churn-update/v1"
NONCE_MAP_SCHEMA_ID_V1 = "zenodex/nonces/v1"
POOL_MAP_SCHEMA_ID_V1 = "zenodex/pools/v1"
PERPS_MARKET_MAP_SCHEMA_ID_V1 = "zenodex/perps/markets/v1"
PERPS_ISOLATED_GLOBAL_MAP_SCHEMA_ID_V1 = "zenodex/perps/isolated-global/v1"
PERPS_ISOLATED_ACCOUNT_MAP_SCHEMA_ID_V1 = "zenodex/perps/isolated-accounts/v1"
PERPS_CLEARINGHOUSE_2P_STATE_MAP_SCHEMA_ID_V1 = "zenodex/perps/ch2p-state/v1"
PERPS_CLEARINGHOUSE_3P_STATE_MAP_SCHEMA_ID_V1 = "zenodex/perps/ch3p-state/v1"
PERPS_CLEARINGHOUSE_NP_GLOBAL_MAP_SCHEMA_ID_V1 = "zenodex/perps/chnp-global/v1"

BalanceKeyV1 = tuple[str, str]
LPKeyV1 = tuple[str, str]
PerpsValueV1 = int | bool
K = TypeVar("K")
V = TypeVar("V")

MAX_STATE_STRING_CHARACTERS_V1 = 4_096
MAX_STATE_STRING_UTF8_BYTES_V1 = 16_384
MAX_BALANCES_V1 = 200_000
MAX_POOLS_V1 = 50_000
MAX_LP_ENTRIES_V1 = 200_000
MAX_NONCES_V1 = 200_000
MAX_PERPS_MARKETS_V1 = 10_000
MAX_PERPS_ACCOUNTS_V1 = 200_000
MAX_PERPS_PENDING_INTENTS_V1 = 200_000
MAX_PRICE_E8_V1 = 1_000_000_000_000
MAX_BPS_V1 = 10_000
MAX_DEPEG_BUFFER_BPS_V1 = 5_000
MAX_NP_NOTIONAL_FOR_BOUNTY_E8_V1 = 100_000_000_000_000_000_000
MAX_FIXED_CLEARINGHOUSE_COLLATERAL_E8_V1 = 1_000_000_000_000_000_000
MAX_CLEARINGHOUSE_2P_AGGREGATE_E8_V1 = 3_000_000_000_000_000_000
MAX_CLEARINGHOUSE_3P_AGGREGATE_E8_V1 = 4_000_000_000_000_000_000
MAX_U32_V1 = 0xFFFF_FFFF

# PoolStatus is the first and currently only enum registration in this profile.
POOL_STATUS_ENUM_TAG_ORDINAL_V1 = 0
POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1 = 0
POOL_STATUS_MEMBER_VALUES_V1 = ("ACTIVE", "FROZEN", "DISABLED")
POOL_STATUS_MEMBER_COUNT_V1 = len(POOL_STATUS_MEMBER_VALUES_V1)


def _require_exact_int(
    value: object,
    *,
    minimum: int | None = 0,
    maximum: int | None = None,
) -> int:
    if (
        type(value) is not int
        or (minimum is not None and value < minimum)
        or (maximum is not None and value > maximum)
    ):
        raise TypeError("committed integer field violates its exact domain")
    return value


def _require_exact_string(
    value: object,
    *,
    allow_empty: bool = False,
    max_characters: int = MAX_STATE_STRING_CHARACTERS_V1,
    max_utf8_bytes: int = MAX_STATE_STRING_UTF8_BYTES_V1,
) -> str:
    if type(value) is not str or (not allow_empty and not value):
        raise TypeError("committed string field violates its exact domain")
    if len(value) > max_characters:
        raise ValueError("committed string exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError("committed string is not a Unicode scalar string") from exc
    if len(encoded) > max_utf8_bytes:
        raise ValueError("committed string exceeds its UTF-8 bound")
    return value


def _require_exact_literal(value: object, expected: str) -> str:
    literal = _require_exact_string(value)
    if literal != expected:
        raise ValueError("committed literal field mismatch")
    return literal


def _require_canonical_pubkey(value: object) -> str:
    from .canonical import canonical_hex_fixed_allow_0x

    pubkey = _require_exact_string(value, max_characters=98, max_utf8_bytes=98)
    if canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey") != pubkey:
        raise ValueError("committed pubkey is not canonical")
    return pubkey


def _require_owned_map(
    value: object,
    schema_id: str,
) -> OwnedMapV1[K, V]:
    if type(value) is not OwnedMapV1:
        raise TypeError("committed map must be an exact OwnedMapV1")
    revision = object.__getattribute__(value, "_schema_revision")
    observed_schema_id = object.__getattribute__(value, "_schema_id")
    if revision != FCIS_STATE_SCHEMA_REVISION_V1 or observed_schema_id != schema_id:
        raise TypeError("committed map schema metadata mismatch")
    return cast(OwnedMapV1[K, V], value)


def _require_owned_pool_status(value: object) -> OwnedEnumV1:
    if type(value) is not OwnedEnumV1:
        raise TypeError("committed pool status must be an exact owned enum")
    owned = cast(OwnedEnumV1, value)
    if (
        owned.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or owned.enum_tag_ordinal != POOL_STATUS_ENUM_TAG_ORDINAL_V1
        or not 0 <= owned.member_ordinal < POOL_STATUS_MEMBER_COUNT_V1
    ):
        raise ValueError("committed pool status metadata mismatch")
    return owned


def _exact_map_dict(value: OwnedMapV1[str, V]) -> dict[str, V]:
    """Build one private nonescaping validation index from admitted entries."""

    return {key: item for key, item in value.entries}


def _require_exact_key_set(values: dict[str, V], expected: set[str]) -> None:
    if set(values) != expected:
        raise ValueError("committed keyed map field registry mismatch")


def _exact_int_at(values: dict[str, PerpsValueV1], key: str) -> int:
    value = values[key]
    if type(value) is not int:
        raise TypeError("committed keyed-map integer field is not exact")
    return value


def _exact_bool_at(values: dict[str, PerpsValueV1], key: str) -> bool:
    value = values[key]
    if type(value) is not bool:
        raise TypeError("committed keyed-map bool field is not exact")
    return value


@final
@dataclass(frozen=True, slots=True)
class _BalanceSourceV1:
    """Non-authoritative exact projection of one legacy balance table."""

    _balances: object


@final
@dataclass(frozen=True, slots=True)
class _LPSourceV1:
    """Non-authoritative exact projection of one legacy LP table."""

    _balances: object
    _last_mint_timestamps: object
    _last_remove_timestamps: object
    _churn_tiers: object
    _last_churn_update_timestamps: object


@final
@dataclass(frozen=True, slots=True)
class CommittedBalanceTableV1:
    _balances: OwnedMapV1[BalanceKeyV1, int]

    def __post_init__(self) -> None:
        _require_owned_map(self._balances, BALANCE_MAP_SCHEMA_ID_V1)
        if len(self._balances.entries) > MAX_BALANCES_V1:
            raise ValueError("committed balance table exceeds its item limit")
        if any(amount <= 0 for _key, amount in self._balances.entries):
            raise ValueError("committed balance table is not sparse")

    @property
    def entries(self) -> tuple[tuple[BalanceKeyV1, int], ...]:
        return self._balances.entries

    def get(self, pubkey: str, asset: str) -> int:
        return self._balances.get((pubkey, asset), 0)


@final
@dataclass(frozen=True, slots=True)
class CommittedLPTableV1:
    _balances: OwnedMapV1[LPKeyV1, int]
    _last_mint_timestamps: OwnedMapV1[LPKeyV1, int]
    _last_remove_timestamps: OwnedMapV1[LPKeyV1, int]
    _churn_tiers: OwnedMapV1[LPKeyV1, int]
    _last_churn_update_timestamps: OwnedMapV1[LPKeyV1, int]

    def __post_init__(self) -> None:
        _require_owned_map(self._balances, LP_BALANCE_MAP_SCHEMA_ID_V1)
        _require_owned_map(self._last_mint_timestamps, LP_LAST_MINT_MAP_SCHEMA_ID_V1)
        _require_owned_map(self._last_remove_timestamps, LP_LAST_REMOVE_MAP_SCHEMA_ID_V1)
        _require_owned_map(self._churn_tiers, LP_CHURN_TIER_MAP_SCHEMA_ID_V1)
        _require_owned_map(
            self._last_churn_update_timestamps,
            LP_LAST_CHURN_UPDATE_MAP_SCHEMA_ID_V1,
        )
        maps = (
            self._balances,
            self._last_mint_timestamps,
            self._last_remove_timestamps,
            self._churn_tiers,
            self._last_churn_update_timestamps,
        )
        if sum(len(value.entries) for value in maps) > MAX_LP_ENTRIES_V1:
            raise ValueError("committed LP table exceeds its item limit")
        if any(
            amount <= 0 or amount > DEX_LP_AMOUNT_MAX for _key, amount in self._balances.entries
        ):
            raise ValueError("committed LP balances are not canonical")
        balance_keys = {key for key, _amount in self._balances.entries}
        if any(key not in balance_keys for key, _timestamp in self._last_mint_timestamps.entries):
            raise ValueError("LP mint metadata requires a positive LP balance")
        if any(tier <= 0 for _key, tier in self._churn_tiers.entries):
            raise ValueError("committed LP churn-tier map is not sparse")

    def get(self, pubkey: str, pool_id: str) -> int:
        return self._balances.get((pubkey, pool_id), 0)

    def get_last_mint_timestamp(self, pubkey: str, pool_id: str) -> int | None:
        return self._last_mint_timestamps.get((pubkey, pool_id))

    def get_last_remove_timestamp(self, pubkey: str, pool_id: str) -> int | None:
        return self._last_remove_timestamps.get((pubkey, pool_id))

    def get_churn_tier(self, pubkey: str, pool_id: str) -> int:
        return self._churn_tiers.get((pubkey, pool_id), 0)

    def get_last_churn_update_timestamp(self, pubkey: str, pool_id: str) -> int | None:
        return self._last_churn_update_timestamps.get((pubkey, pool_id))

    @property
    def balance_entries(self) -> tuple[tuple[LPKeyV1, int], ...]:
        return self._balances.entries

    @property
    def last_mint_entries(self) -> tuple[tuple[LPKeyV1, int], ...]:
        return self._last_mint_timestamps.entries

    @property
    def last_remove_entries(self) -> tuple[tuple[LPKeyV1, int], ...]:
        return self._last_remove_timestamps.entries

    @property
    def churn_tier_entries(self) -> tuple[tuple[LPKeyV1, int], ...]:
        return self._churn_tiers.entries

    @property
    def last_churn_update_entries(self) -> tuple[tuple[LPKeyV1, int], ...]:
        return self._last_churn_update_timestamps.entries


@final
@dataclass(frozen=True, slots=True)
class CommittedNonceTableV1:
    _last: OwnedMapV1[str, int]

    def __post_init__(self) -> None:
        _require_owned_map(self._last, NONCE_MAP_SCHEMA_ID_V1)
        if len(self._last.entries) > MAX_NONCES_V1:
            raise ValueError("committed nonce table exceeds its item limit")
        for pubkey, _nonce in self._last.entries:
            _require_canonical_pubkey(pubkey)
        if any(nonce > MAX_U32_V1 for _pubkey, nonce in self._last.entries):
            raise ValueError("committed nonce exceeds u32")

    def get_last(self, pubkey: str) -> int:
        return self._last.get(pubkey, 0)

    @property
    def entries(self) -> tuple[tuple[str, int], ...]:
        return self._last.entries


@final
@dataclass(frozen=True, slots=True)
class CommittedPoolStateV1:
    pool_id: str
    asset0: str
    asset1: str
    reserve0: int
    reserve1: int
    fee_bps: int
    lp_supply: int
    status: OwnedEnumV1
    created_at: int
    curve_tag: str
    curve_params: str

    def __post_init__(self) -> None:
        _require_exact_string(self.pool_id, max_characters=256, max_utf8_bytes=256)
        _require_exact_string(self.asset0, max_characters=256, max_utf8_bytes=1_024)
        _require_exact_string(self.asset1, max_characters=256, max_utf8_bytes=1_024)
        _require_exact_int(self.reserve0, maximum=DEX_POOL_RESERVE_MAX)
        _require_exact_int(self.reserve1, maximum=DEX_POOL_RESERVE_MAX)
        _require_exact_int(self.lp_supply, maximum=DEX_LP_SUPPLY_MAX)
        _require_exact_int(self.created_at)
        if type(self.fee_bps) is not int or not 0 <= self.fee_bps <= 10_000:
            raise TypeError("committed pool fee_bps violates its exact domain")
        _require_owned_pool_status(self.status)
        _require_exact_string(self.curve_tag, max_characters=256, max_utf8_bytes=256)
        _require_exact_string(self.curve_params, allow_empty=True)

        normalized_asset0, normalized_asset1 = normalize_pool_asset_pair(
            self.asset0,
            self.asset1,
        )
        if (normalized_asset0, normalized_asset1) != (self.asset0, self.asset1):
            raise ValueError("committed pool asset pair is not canonical")
        normalized_tag, normalized_params = normalize_curve_config(
            curve_tag=self.curve_tag,
            curve_params=self.curve_params,
        )
        if (normalized_tag, normalized_params) != (self.curve_tag, self.curve_params):
            raise ValueError("committed pool curve configuration is not canonical")
        validate_pool_id_format(self.pool_id, allow_symbolic=False)
        expected_pool_id = compute_pool_id(
            self.asset0,
            self.asset1,
            self.fee_bps,
            curve_tag=self.curve_tag,
            curve_params=self.curve_params,
        )
        if self.pool_id != expected_pool_id:
            raise ValueError("committed pool ID does not bind its parameters")


@final
@dataclass(frozen=True, slots=True)
class CommittedVaultStateV1:
    acc_reward_per_share: int
    last_update_acc: int
    pending_rewards: int
    reward_balance: int
    staked_lp_shares: int

    def __post_init__(self) -> None:
        for value in (
            self.acc_reward_per_share,
            self.last_update_acc,
            self.pending_rewards,
            self.reward_balance,
            self.staked_lp_shares,
        ):
            _require_exact_int(value)
        if self.acc_reward_per_share < self.last_update_acc:
            raise ValueError("vault accumulator must be monotone")
        if self.pending_rewards > self.reward_balance:
            raise ValueError("vault pending rewards exceed custody")


@final
@dataclass(frozen=True, slots=True)
class CommittedOracleStateV1:
    price_timestamp: int
    max_staleness_seconds: int

    def __post_init__(self) -> None:
        _require_exact_int(self.price_timestamp)
        _require_exact_int(self.max_staleness_seconds, minimum=1)


@final
@dataclass(frozen=True, slots=True)
class CommittedFeeAccumulatorStateV1:
    dust: int

    def __post_init__(self) -> None:
        _require_exact_int(self.dust)


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpAccountStateV1:
    position_base: int
    entry_price_e8: int
    collateral_quote: int
    funding_paid_cumulative: int
    funding_last_applied_epoch: int
    liquidated_this_step: bool

    def __post_init__(self) -> None:
        _require_exact_int(
            self.position_base,
            minimum=-PERP_POSITION_MAX,
            maximum=PERP_POSITION_MAX,
        )
        _require_exact_int(self.entry_price_e8, maximum=MAX_PRICE_E8_V1)
        _require_exact_int(self.collateral_quote, maximum=MAX_COLLATERAL)
        _require_exact_int(
            self.funding_paid_cumulative,
            minimum=-MAX_COLLATERAL,
            maximum=MAX_COLLATERAL,
        )
        _require_exact_int(self.funding_last_applied_epoch, maximum=MAX_EPOCH)
        if type(self.liquidated_this_step) is not bool:
            raise TypeError("liquidated_this_step must be an exact bool")


def _require_isolated_global_bounds(global_state: dict[str, PerpsValueV1]) -> None:
    exact_bounds: dict[str, tuple[int, int]] = {
        "now_epoch": (0, MAX_EPOCH),
        "epoch_phase": (0, 2),
        "breaker_last_trigger_epoch": (0, MAX_EPOCH),
        "clearing_price_epoch": (0, MAX_EPOCH),
        "clearing_price_e8": (0, MAX_PRICE_E8_V1),
        "mark_price_source_kind": (0, MARK_PRICE_SOURCE_EXTERNAL_MEDIAN),
        "oracle_last_update_epoch": (0, MAX_EPOCH),
        "index_price_e8": (0, MAX_PRICE_E8_V1),
        "max_oracle_staleness_epochs": (1, MAX_EPOCH),
        "max_oracle_move_bps": (0, MAX_BPS_V1),
        "initial_margin_bps": (0, MAX_BPS_V1),
        "maintenance_margin_bps": (0, MAX_BPS_V1),
        "depeg_buffer_bps": (0, MAX_DEPEG_BUFFER_BPS_V1),
        "liquidation_penalty_bps": (0, MAX_BPS_V1),
        "max_position_abs": (1, PERP_POSITION_MAX),
        "fee_pool_quote": (0, MAX_COLLATERAL),
        "funding_rate_bps": (-MAX_BPS_V1, MAX_BPS_V1),
        "funding_cap_bps": (1, MAX_BPS_V1),
        "insurance_balance": (0, MAX_COLLATERAL),
        "initial_insurance": (0, MAX_COLLATERAL),
        "fee_income": (0, MAX_COLLATERAL),
        "claims_paid": (0, MAX_COLLATERAL),
        "min_notional_for_bounty": (0, MAX_PRICE_E8_V1),
    }
    for key, (minimum, maximum) in exact_bounds.items():
        _require_exact_int(global_state[key], minimum=minimum, maximum=maximum)
    for key in ("breaker_active", "clearing_price_seen", "oracle_seen"):
        if type(global_state[key]) is not bool:
            raise TypeError("committed isolated perps flag must be an exact bool")


def _funded_liquidation_parameters_ok(
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
    max_oracle_move_bps: int,
    liquidation_penalty_bps: int,
) -> bool:
    effective_maintenance = maintenance_margin_bps + depeg_buffer_bps
    return liquidation_penalty_bps * (MAX_BPS_V1 + max_oracle_move_bps) <= (
        MAX_BPS_V1 * (effective_maintenance - max_oracle_move_bps)
    )


def _require_isolated_global_consistency(global_state: dict[str, PerpsValueV1]) -> None:
    now_epoch = _exact_int_at(global_state, "now_epoch")
    phase = _exact_int_at(global_state, "epoch_phase")
    breaker_active = _exact_bool_at(global_state, "breaker_active")
    breaker_epoch = _exact_int_at(global_state, "breaker_last_trigger_epoch")
    clearing_seen = _exact_bool_at(global_state, "clearing_price_seen")
    clearing_epoch = _exact_int_at(global_state, "clearing_price_epoch")
    clearing_price = _exact_int_at(global_state, "clearing_price_e8")
    oracle_seen = _exact_bool_at(global_state, "oracle_seen")
    oracle_epoch = _exact_int_at(global_state, "oracle_last_update_epoch")
    index_price = _exact_int_at(global_state, "index_price_e8")

    if max(breaker_epoch, clearing_epoch, oracle_epoch) > now_epoch:
        raise ValueError("committed isolated perps state contains a future epoch")
    if not breaker_active and breaker_epoch != 0:
        raise ValueError("inactive breaker must have a zero trigger epoch")
    if not clearing_seen and (clearing_epoch != 0 or clearing_price != 0):
        raise ValueError("unseen clearing price fields must be zero")
    if (
        clearing_seen
        and global_state["mark_price_source_kind"] != MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
    ):
        raise ValueError("published clearing price requires the derivatives-safe source")
    if not oracle_seen and (oracle_epoch != 0 or index_price != 0):
        raise ValueError("unseen Oracle fields must be zero")
    if oracle_seen and index_price <= 0:
        raise ValueError("seen Oracle requires a positive index price")

    if phase == 0:
        if clearing_seen and clearing_epoch == now_epoch:
            raise ValueError("Open phase conflicts with a current clearing price")
        if now_epoch > 0 and oracle_seen and oracle_epoch == now_epoch:
            raise ValueError("Open phase conflicts with a current Oracle update")
    elif phase == 1:
        if not clearing_seen or clearing_epoch != now_epoch or oracle_epoch >= now_epoch:
            raise ValueError("PricePublished phase is inconsistent")
    elif not (
        clearing_seen and clearing_epoch == now_epoch and oracle_seen and oracle_epoch == now_epoch
    ):
        raise ValueError("Settled phase is inconsistent")


def _require_isolated_economics(global_state: dict[str, PerpsValueV1]) -> None:
    max_move = _exact_int_at(global_state, "max_oracle_move_bps")
    maintenance = _exact_int_at(global_state, "maintenance_margin_bps")
    depeg = _exact_int_at(global_state, "depeg_buffer_bps")
    initial = _exact_int_at(global_state, "initial_margin_bps")
    penalty = _exact_int_at(global_state, "liquidation_penalty_bps")
    effective_maintenance = maintenance + depeg
    if not max_move <= effective_maintenance <= initial:
        raise ValueError("committed isolated perps margin tiers are unordered")
    if penalty >= effective_maintenance or not _funded_liquidation_parameters_ok(
        maintenance,
        depeg,
        max_move,
        penalty,
    ):
        raise ValueError("committed isolated liquidation parameters are unsafe")
    funding_rate = _exact_int_at(global_state, "funding_rate_bps")
    funding_cap = _exact_int_at(global_state, "funding_cap_bps")
    if abs(funding_rate) > funding_cap:
        raise ValueError("committed isolated funding rate exceeds its cap")
    insurance = _exact_int_at(global_state, "insurance_balance")
    expected_insurance = (
        _exact_int_at(global_state, "initial_insurance")
        + _exact_int_at(global_state, "fee_income")
        - _exact_int_at(global_state, "claims_paid")
    )
    if insurance != expected_insurance:
        raise ValueError("committed isolated insurance accounting is inconsistent")
    if global_state["fee_pool_quote"] != global_state["fee_income"]:
        raise ValueError("committed isolated fee-pool accounting is inconsistent")


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpMarketStateV1:
    quote_asset: str
    global_state: OwnedMapV1[str, PerpsValueV1]
    accounts: OwnedMapV1[str, CommittedPerpAccountStateV1]
    kind: str

    def __post_init__(self) -> None:
        _require_exact_string(self.quote_asset)
        _require_owned_map(self.global_state, PERPS_ISOLATED_GLOBAL_MAP_SCHEMA_ID_V1)
        _require_owned_map(self.accounts, PERPS_ISOLATED_ACCOUNT_MAP_SCHEMA_ID_V1)
        _require_exact_literal(self.kind, "isolated_v2")
        if len(self.accounts.entries) > MAX_PERPS_ACCOUNTS_V1:
            raise ValueError("committed isolated account table exceeds its item limit")
        global_state: dict[str, PerpsValueV1] = _exact_map_dict(self.global_state)
        _require_exact_key_set(global_state, PERP_ISOLATED_GLOBAL_KEYS)
        _require_isolated_global_bounds(global_state)
        _require_isolated_global_consistency(global_state)
        _require_isolated_economics(global_state)

        now_epoch = _exact_int_at(global_state, "now_epoch")
        index_price = _exact_int_at(global_state, "index_price_e8")
        max_position = _exact_int_at(global_state, "max_position_abs")
        for pubkey, account in self.accounts.entries:
            _require_canonical_pubkey(pubkey)
            if type(account) is not CommittedPerpAccountStateV1:
                raise TypeError("isolated accounts must be exact committed values")
            if abs(account.position_base) > max_position:
                raise ValueError("isolated account position exceeds the market limit")
            if account.funding_last_applied_epoch > now_epoch:
                raise ValueError("isolated account funding epoch is from the future")
            if account.position_base == 0 and account.entry_price_e8 != 0:
                raise ValueError("flat isolated account must have zero entry price")
            if account.position_base != 0 and account.entry_price_e8 != index_price:
                raise ValueError("open isolated account entry price must equal index price")


def _require_fixed_clearinghouse_bounds(
    state: dict[str, PerpsValueV1],
    bool_keys: set[str],
    participant_suffixes: tuple[str, ...],
    aggregate_maximum: int,
) -> None:
    for key in bool_keys:
        if type(state[key]) is not bool:
            raise TypeError("clearinghouse flags must be exact bools")
    for key in (
        "now_epoch",
        "breaker_last_trigger_epoch",
        "clearing_price_epoch",
        "oracle_last_update_epoch",
    ):
        _require_exact_int(state[key], maximum=MAX_EPOCH)
    for key in ("clearing_price_e8", "index_price_e8"):
        _require_exact_int(state[key], maximum=MAX_PRICE_E8_V1)
    for key in (
        "max_oracle_move_bps",
        "initial_margin_bps",
        "maintenance_margin_bps",
        "liquidation_penalty_bps",
    ):
        _require_exact_int(state[key], maximum=MAX_BPS_V1)
    _require_exact_int(state["max_oracle_staleness_epochs"], minimum=1, maximum=MAX_EPOCH)
    _require_exact_int(state["max_position_abs"], minimum=1, maximum=PERP_POSITION_MAX)
    for key in ("fee_pool_e8", "net_deposited_e8"):
        _require_exact_int(state[key], maximum=aggregate_maximum)
    for suffix in participant_suffixes:
        _require_exact_int(
            state[f"position_base_{suffix}"],
            minimum=-PERP_POSITION_MAX,
            maximum=PERP_POSITION_MAX,
        )
        _require_exact_int(state[f"entry_price_e8_{suffix}"], maximum=MAX_PRICE_E8_V1)
        _require_exact_int(
            state[f"collateral_e8_{suffix}"],
            maximum=MAX_FIXED_CLEARINGHOUSE_COLLATERAL_E8_V1,
        )


def _require_fixed_clearinghouse_consistency(
    state: dict[str, PerpsValueV1],
    participant_suffixes: tuple[str, ...],
) -> None:
    now_epoch = _exact_int_at(state, "now_epoch")
    if (
        max(
            _exact_int_at(state, "breaker_last_trigger_epoch"),
            _exact_int_at(state, "clearing_price_epoch"),
            _exact_int_at(state, "oracle_last_update_epoch"),
        )
        > now_epoch
    ):
        raise ValueError("committed clearinghouse state contains a future epoch")
    if not state["breaker_active"] and state["breaker_last_trigger_epoch"] != 0:
        raise ValueError("inactive clearinghouse breaker must have zero trigger epoch")
    if not state["clearing_price_seen"] and (
        state["clearing_price_epoch"] != 0 or state["clearing_price_e8"] != 0
    ):
        raise ValueError("unseen clearinghouse price fields must be zero")
    if not state["oracle_seen"] and (
        state["oracle_last_update_epoch"] != 0 or state["index_price_e8"] != 0
    ):
        raise ValueError("unseen clearinghouse Oracle fields must be zero")
    max_move = _exact_int_at(state, "max_oracle_move_bps")
    maintenance = _exact_int_at(state, "maintenance_margin_bps")
    initial = _exact_int_at(state, "initial_margin_bps")
    if not max_move <= maintenance <= initial:
        raise ValueError("committed clearinghouse margin tiers are unordered")
    max_position = _exact_int_at(state, "max_position_abs")
    positions = tuple(
        _exact_int_at(state, f"position_base_{suffix}") for suffix in participant_suffixes
    )
    if any(abs(position) > max_position for position in positions) or sum(positions) != 0:
        raise ValueError("committed clearinghouse positions violate market bounds")
    if len(participant_suffixes) == 3 and all(position != 0 for position in positions):
        raise ValueError("three-party clearinghouse requires one flat participant")
    collateral_total = sum(
        (_exact_int_at(state, f"collateral_e8_{suffix}") for suffix in participant_suffixes),
        0,
    )
    if _exact_int_at(state, "net_deposited_e8") != collateral_total + _exact_int_at(
        state,
        "fee_pool_e8",
    ):
        raise ValueError("committed clearinghouse collateral conservation failed")


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpClearinghouse2pMarketStateV1:
    quote_asset: str
    account_a_pubkey: str
    account_b_pubkey: str
    state: OwnedMapV1[str, PerpsValueV1]
    kind: str

    def __post_init__(self) -> None:
        _require_exact_string(self.quote_asset)
        account_a = _require_canonical_pubkey(self.account_a_pubkey)
        account_b = _require_canonical_pubkey(self.account_b_pubkey)
        if account_a == account_b:
            raise ValueError("two-party clearinghouse participants must be distinct")
        _require_owned_map(self.state, PERPS_CLEARINGHOUSE_2P_STATE_MAP_SCHEMA_ID_V1)
        _require_exact_literal(self.kind, "clearinghouse_2p_v1")
        state: dict[str, PerpsValueV1] = _exact_map_dict(self.state)
        _require_exact_key_set(state, PERP_CLEARINGHOUSE_2P_STATE_KEYS)
        _require_fixed_clearinghouse_bounds(
            state,
            PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
            ("a", "b"),
            MAX_CLEARINGHOUSE_2P_AGGREGATE_E8_V1,
        )
        _require_fixed_clearinghouse_consistency(state, ("a", "b"))


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpClearinghouse3pTransferMarketStateV1:
    quote_asset: str
    account_a_pubkey: str
    account_b_pubkey: str
    account_c_pubkey: str
    state: OwnedMapV1[str, PerpsValueV1]
    kind: str

    def __post_init__(self) -> None:
        _require_exact_string(self.quote_asset)
        participants = (
            _require_canonical_pubkey(self.account_a_pubkey),
            _require_canonical_pubkey(self.account_b_pubkey),
            _require_canonical_pubkey(self.account_c_pubkey),
        )
        if len(set(participants)) != 3:
            raise ValueError("three-party clearinghouse participants must be distinct")
        _require_owned_map(self.state, PERPS_CLEARINGHOUSE_3P_STATE_MAP_SCHEMA_ID_V1)
        _require_exact_literal(self.kind, "clearinghouse_3p_transfer_v1")
        state: dict[str, PerpsValueV1] = _exact_map_dict(self.state)
        _require_exact_key_set(state, PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS)
        _require_fixed_clearinghouse_bounds(
            state,
            PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
            ("a", "b", "c"),
            MAX_CLEARINGHOUSE_3P_AGGREGATE_E8_V1,
        )
        _require_fixed_clearinghouse_consistency(state, ("a", "b", "c"))


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpClearinghouseNpAccountV1:
    pubkey: str
    position_base: int
    entry_price_e8: int
    collateral_e8: int
    funding_paid_cum_e8: int
    nonce: int

    def __post_init__(self) -> None:
        _require_canonical_pubkey(self.pubkey)
        _require_exact_int(
            self.position_base,
            minimum=-PERP_POSITION_MAX,
            maximum=PERP_POSITION_MAX,
        )
        _require_exact_int(self.entry_price_e8)
        _require_exact_int(self.collateral_e8)
        _require_exact_int(self.funding_paid_cum_e8, minimum=None)
        _require_exact_int(self.nonce)


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpClearinghouseNpPendingIntentV1:
    pubkey: str
    target_base: int
    nonce: int
    limit_price_e8: int
    min_fill_base: int
    expiry_epoch: int

    def __post_init__(self) -> None:
        _require_canonical_pubkey(self.pubkey)
        _require_exact_int(self.target_base, minimum=None)
        _require_exact_int(self.nonce, minimum=1)
        _require_exact_int(self.limit_price_e8)
        _require_exact_int(self.min_fill_base)
        _require_exact_int(self.expiry_epoch)


def _require_np_global_bounds(global_state: dict[str, int]) -> None:
    bounds: dict[str, tuple[int, int | None]] = {
        "now_epoch": (0, None),
        "index_price_e8": (1, None),
        "clearing_price_seen": (0, 1),
        "clearing_price_epoch": (0, None),
        "clearing_price_e8": (0, None),
        "fee_pool_e8": (0, None),
        "insurance_e8": (0, None),
        "insurance_ext_e8": (0, None),
        "claims_paid_e8": (0, None),
        "initial_margin_bps": (0, MAX_BPS_V1),
        "maintenance_margin_bps": (0, MAX_BPS_V1),
        "depeg_buffer_bps": (0, MAX_DEPEG_BUFFER_BPS_V1),
        "liquidation_penalty_bps": (0, MAX_BPS_V1),
        "max_oracle_move_bps": (0, MAX_BPS_V1),
        "funding_cap_bps": (1, MAX_BPS_V1),
        "max_position_abs": (1, PERP_POSITION_MAX),
        "min_notional_for_bounty_e8": (0, MAX_NP_NOTIONAL_FOR_BOUNTY_E8_V1),
    }
    for key, (minimum, maximum) in bounds.items():
        _require_exact_int(global_state[key], minimum=minimum, maximum=maximum)
    _require_exact_int(global_state["net_deposited_e8"], minimum=None)


def _require_np_global_consistency(global_state: dict[str, int]) -> None:
    effective_maintenance = (
        global_state["maintenance_margin_bps"] + global_state["depeg_buffer_bps"]
    )
    if not (
        global_state["max_oracle_move_bps"]
        <= effective_maintenance
        <= global_state["initial_margin_bps"]
    ):
        raise ValueError("N-party clearinghouse margin tiers are unordered")
    if global_state[
        "liquidation_penalty_bps"
    ] >= effective_maintenance or not _funded_liquidation_parameters_ok(
        global_state["maintenance_margin_bps"],
        global_state["depeg_buffer_bps"],
        global_state["max_oracle_move_bps"],
        global_state["liquidation_penalty_bps"],
    ):
        raise ValueError("N-party clearinghouse liquidation parameters are unsafe")
    if global_state["clearing_price_seen"] == 0:
        if global_state["clearing_price_epoch"] != 0 or global_state["clearing_price_e8"] != 0:
            raise ValueError("unseen N-party clearing price fields must be zero")
    elif (
        global_state["clearing_price_e8"] <= 0
        or global_state["clearing_price_epoch"] != global_state["now_epoch"]
    ):
        raise ValueError("seen N-party clearing price is inconsistent")
    if global_state["insurance_e8"] != (
        global_state["insurance_ext_e8"] - global_state["claims_paid_e8"]
    ):
        raise ValueError("N-party clearinghouse insurance accounting is inconsistent")


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpClearinghouseNpMarketStateV1:
    quote_asset: str
    global_state: OwnedMapV1[str, int]
    accounts: tuple[CommittedPerpClearinghouseNpAccountV1, ...]
    pending_intents: tuple[CommittedPerpClearinghouseNpPendingIntentV1, ...]
    kind: str

    def __post_init__(self) -> None:
        _require_exact_string(self.quote_asset)
        _require_owned_map(self.global_state, PERPS_CLEARINGHOUSE_NP_GLOBAL_MAP_SCHEMA_ID_V1)
        if type(self.accounts) is not tuple or any(
            type(account) is not CommittedPerpClearinghouseNpAccountV1 for account in self.accounts
        ):
            raise TypeError("N-party accounts must be exact committed tuple values")
        if type(self.pending_intents) is not tuple or any(
            type(intent) is not CommittedPerpClearinghouseNpPendingIntentV1
            for intent in self.pending_intents
        ):
            raise TypeError("N-party intents must be exact committed tuple values")
        _require_exact_literal(self.kind, "clearinghouse_np_v1")
        if len(self.accounts) > MAX_PERPS_ACCOUNTS_V1:
            raise ValueError("N-party account tuple exceeds its item limit")
        if len(self.pending_intents) > MAX_PERPS_PENDING_INTENTS_V1:
            raise ValueError("N-party pending-intent tuple exceeds its item limit")

        global_state: dict[str, int] = _exact_map_dict(self.global_state)
        _require_exact_key_set(global_state, PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS)
        _require_np_global_bounds(global_state)
        _require_np_global_consistency(global_state)

        account_pubkeys = tuple(account.pubkey for account in self.accounts)
        if account_pubkeys != tuple(sorted(account_pubkeys)):
            raise ValueError("N-party accounts are not in canonical pubkey order")
        if len(set(account_pubkeys)) != len(account_pubkeys):
            raise ValueError("N-party accounts must have unique pubkeys")
        max_position = global_state["max_position_abs"]
        if any(abs(account.position_base) > max_position for account in self.accounts):
            raise ValueError("N-party account position exceeds the market limit")
        if sum(account.position_base for account in self.accounts) != 0:
            raise ValueError("N-party positions must sum to zero")

        intent_pubkeys = tuple(intent.pubkey for intent in self.pending_intents)
        if intent_pubkeys != tuple(sorted(intent_pubkeys)):
            raise ValueError("N-party pending intents are not in canonical pubkey order")
        if len(set(intent_pubkeys)) != len(intent_pubkeys):
            raise ValueError("N-party pending intents must be one per account")
        account_pubkey_set = set(account_pubkeys)
        if any(pubkey not in account_pubkey_set for pubkey in intent_pubkeys):
            raise ValueError("N-party pending intent is not bound to a market member")

        collateral_total = sum(account.collateral_e8 for account in self.accounts)
        if global_state["net_deposited_e8"] + global_state["insurance_ext_e8"] != (
            collateral_total + global_state["fee_pool_e8"] + global_state["insurance_e8"]
        ):
            raise ValueError("N-party clearinghouse collateral conservation failed")


CommittedPerpAnyMarketStateV1 = (
    CommittedPerpMarketStateV1
    | CommittedPerpClearinghouse2pMarketStateV1
    | CommittedPerpClearinghouse3pTransferMarketStateV1
    | CommittedPerpClearinghouseNpMarketStateV1
)


@final
@dataclass(frozen=True, slots=True)
class CommittedPerpsStateV1:
    version: int
    markets: OwnedMapV1[str, CommittedPerpAnyMarketStateV1]

    def __post_init__(self) -> None:
        _require_exact_int(
            self.version, minimum=PERPS_STATE_VERSION_V4, maximum=PERPS_STATE_VERSION_V5
        )
        if self.version not in (PERPS_STATE_VERSION_V4, PERPS_STATE_VERSION_V5):
            raise ValueError("unsupported committed perps version")
        _require_owned_map(self.markets, PERPS_MARKET_MAP_SCHEMA_ID_V1)
        if len(self.markets.entries) > MAX_PERPS_MARKETS_V1:
            raise ValueError("committed perps market map exceeds its item limit")
        supported_types = (
            CommittedPerpMarketStateV1,
            CommittedPerpClearinghouse2pMarketStateV1,
            CommittedPerpClearinghouse3pTransferMarketStateV1,
            CommittedPerpClearinghouseNpMarketStateV1,
        )
        for _market_id, market in self.markets.entries:
            if type(market) not in supported_types:
                raise TypeError("committed perps map contains an unsupported market type")
            if (
                self.version == PERPS_STATE_VERSION_V4
                and type(market) is not CommittedPerpMarketStateV1
            ):
                raise ValueError("perps v4 supports isolated markets only")
