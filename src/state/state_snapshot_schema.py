"""Closed declarative schema for the FCIS committed-state admission profile.

This module contains data only: closed tags, exact field schemas, and exhaustive
type registrations. Construction and canonical encoding are source-bound in
``state_admission_profile`` and cannot be selected by authority input.
"""

from __future__ import annotations

from enum import Enum

from ..core.domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    PERP_POSITION_MAX,
)
from ..core.fees import FeeAccumulatorState
from ..core.oracle import OracleState
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
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpAccount,
    PerpClearinghouseNpMarketState,
    PerpClearinghouseNpPendingIntent,
    PerpMarketState,
    PerpsState,
)
from ..core.vault import VaultState
from .nonces import NonceTable
from .pools import PoolState, PoolStatus
from .snapshot_combinators import (
    DeclaredFieldV1,
    EnumRegistrationV1,
    ExactBool,
    ExactEnum,
    ExactInt,
    ExactKeyedMap,
    ExactPair,
    ExactString,
    MapOf,
    OptionalValue,
    RecordOf,
    RecordRegistrationV1,
    RecordUnionOf,
    SchemaRegistrationV1,
    SchemaV1,
    SequenceOf,
    SequenceSourceKind,
    StringRuleV1,
)
from .state_snapshot_values import (
    BALANCE_MAP_SCHEMA_ID_V1,
    LP_BALANCE_MAP_SCHEMA_ID_V1,
    LP_CHURN_TIER_MAP_SCHEMA_ID_V1,
    LP_LAST_CHURN_UPDATE_MAP_SCHEMA_ID_V1,
    LP_LAST_MINT_MAP_SCHEMA_ID_V1,
    LP_LAST_REMOVE_MAP_SCHEMA_ID_V1,
    MAX_BALANCES_V1,
    MAX_BPS_V1,
    MAX_CLEARINGHOUSE_2P_AGGREGATE_E8_V1,
    MAX_CLEARINGHOUSE_3P_AGGREGATE_E8_V1,
    MAX_DEPEG_BUFFER_BPS_V1,
    MAX_FIXED_CLEARINGHOUSE_COLLATERAL_E8_V1,
    MAX_LP_ENTRIES_V1,
    MAX_NONCES_V1,
    MAX_NP_NOTIONAL_FOR_BOUNTY_E8_V1,
    MAX_PERPS_ACCOUNTS_V1,
    MAX_PERPS_MARKETS_V1,
    MAX_PERPS_PENDING_INTENTS_V1,
    MAX_POOLS_V1,
    MAX_PRICE_E8_V1,
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    MAX_U32_V1,
    NONCE_MAP_SCHEMA_ID_V1,
    PERPS_CLEARINGHOUSE_2P_STATE_MAP_SCHEMA_ID_V1,
    PERPS_CLEARINGHOUSE_3P_STATE_MAP_SCHEMA_ID_V1,
    PERPS_CLEARINGHOUSE_NP_GLOBAL_MAP_SCHEMA_ID_V1,
    PERPS_ISOLATED_ACCOUNT_MAP_SCHEMA_ID_V1,
    PERPS_ISOLATED_GLOBAL_MAP_SCHEMA_ID_V1,
    PERPS_MARKET_MAP_SCHEMA_ID_V1,
    POOL_MAP_SCHEMA_ID_V1,
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpAccountStateV1,
    CommittedPerpClearinghouse2pMarketStateV1,
    CommittedPerpClearinghouse3pTransferMarketStateV1,
    CommittedPerpClearinghouseNpAccountV1,
    CommittedPerpClearinghouseNpMarketStateV1,
    CommittedPerpClearinghouseNpPendingIntentV1,
    CommittedPerpMarketStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
    _BalanceSourceV1,
    _LPSourceV1,
)


class StateEnumTagV1(Enum):
    POOL_STATUS = "pool_status"


class StateRecordTagV1(Enum):
    BALANCE_TABLE = "balance_table"
    LP_TABLE = "lp_table"
    NONCE_TABLE = "nonce_table"
    POOL = "pool"
    VAULT = "vault"
    ORACLE = "oracle"
    FEE_ACCUMULATOR = "fee_accumulator"
    PERP_ACCOUNT = "perp_account"
    PERP_ISOLATED_MARKET = "perp_isolated_market"
    PERP_CLEARINGHOUSE_2P_MARKET = "perp_clearinghouse_2p_market"
    PERP_CLEARINGHOUSE_3P_MARKET = "perp_clearinghouse_3p_market"
    PERP_CLEARINGHOUSE_NP_ACCOUNT = "perp_clearinghouse_np_account"
    PERP_CLEARINGHOUSE_NP_PENDING_INTENT = "perp_clearinghouse_np_pending_intent"
    PERP_CLEARINGHOUSE_NP_MARKET = "perp_clearinghouse_np_market"
    PERPS = "perps"


BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/balance-table/v1"
LP_TABLE_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/lp-table/v1"
NONCE_TABLE_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/nonce-table/v1"
POOL_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/pool/v1"
POOL_MAP_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/pool-map/v1"
VAULT_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/vault/v1"
ORACLE_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/oracle/v1"
FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/fee-accumulator/v1"
PERPS_ADMISSION_SCHEMA_ID_V1 = "zenodex/fcis/state/perps/v1"


def _field(name: str, schema: SchemaV1) -> DeclaredFieldV1:
    return DeclaredFieldV1(name, schema)


STATE_TEXT = ExactString(
    StringRuleV1.NON_EMPTY,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    max_characters=MAX_STATE_STRING_CHARACTERS_V1,
)
POOL_ID_TEXT = ExactString(StringRuleV1.NON_EMPTY, 256, max_characters=256)
POOL_ASSET_TEXT = ExactString(StringRuleV1.NON_EMPTY, 1_024, max_characters=256)
POOL_CURVE_TAG_TEXT = ExactString(StringRuleV1.NON_EMPTY, 256, max_characters=256)
POOL_CURVE_PARAMS_TEXT = ExactString(
    StringRuleV1.EXACT_TEXT,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    max_characters=MAX_STATE_STRING_CHARACTERS_V1,
)
PUBKEY_TEXT = ExactString(StringRuleV1.NON_EMPTY, 98, max_characters=98)
NONNEGATIVE_INT = ExactInt(0, None)
SIGNED_INT = ExactInt(None, None)

BALANCE_KEY_SCHEMA_V1 = ExactPair(STATE_TEXT, STATE_TEXT)
LP_KEY_SCHEMA_V1 = ExactPair(STATE_TEXT, STATE_TEXT)

BALANCE_TABLE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.BALANCE_TABLE,
    (
        _field(
            "_balances",
            MapOf(
                BALANCE_KEY_SCHEMA_V1,
                NONNEGATIVE_INT,
                MAX_BALANCES_V1,
                BALANCE_MAP_SCHEMA_ID_V1,
            ),
        ),
    ),
)

LP_TABLE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.LP_TABLE,
    (
        _field(
            "_balances",
            MapOf(
                LP_KEY_SCHEMA_V1,
                ExactInt(0, DEX_LP_AMOUNT_MAX),
                MAX_LP_ENTRIES_V1,
                LP_BALANCE_MAP_SCHEMA_ID_V1,
            ),
        ),
        _field(
            "_last_mint_timestamps",
            MapOf(
                LP_KEY_SCHEMA_V1,
                NONNEGATIVE_INT,
                MAX_LP_ENTRIES_V1,
                LP_LAST_MINT_MAP_SCHEMA_ID_V1,
            ),
        ),
        _field(
            "_last_remove_timestamps",
            MapOf(
                LP_KEY_SCHEMA_V1,
                NONNEGATIVE_INT,
                MAX_LP_ENTRIES_V1,
                LP_LAST_REMOVE_MAP_SCHEMA_ID_V1,
            ),
        ),
        _field(
            "_churn_tiers",
            MapOf(
                LP_KEY_SCHEMA_V1,
                NONNEGATIVE_INT,
                MAX_LP_ENTRIES_V1,
                LP_CHURN_TIER_MAP_SCHEMA_ID_V1,
            ),
        ),
        _field(
            "_last_churn_update_timestamps",
            MapOf(
                LP_KEY_SCHEMA_V1,
                NONNEGATIVE_INT,
                MAX_LP_ENTRIES_V1,
                LP_LAST_CHURN_UPDATE_MAP_SCHEMA_ID_V1,
            ),
        ),
    ),
)

NONCE_TABLE_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.NONCE_TABLE,
    (
        _field(
            "_last",
            MapOf(
                PUBKEY_TEXT,
                ExactInt(0, MAX_U32_V1),
                MAX_NONCES_V1,
                NONCE_MAP_SCHEMA_ID_V1,
            ),
        ),
    ),
)

POOL_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.POOL,
    (
        _field("pool_id", POOL_ID_TEXT),
        _field("asset0", POOL_ASSET_TEXT),
        _field("asset1", POOL_ASSET_TEXT),
        _field("reserve0", ExactInt(0, DEX_POOL_RESERVE_MAX)),
        _field("reserve1", ExactInt(0, DEX_POOL_RESERVE_MAX)),
        _field("fee_bps", ExactInt(0, MAX_BPS_V1)),
        _field("lp_supply", ExactInt(0, DEX_LP_SUPPLY_MAX)),
        _field("status", ExactEnum(StateEnumTagV1.POOL_STATUS)),
        _field("created_at", NONNEGATIVE_INT),
        _field("curve_tag", POOL_CURVE_TAG_TEXT),
        _field("curve_params", POOL_CURVE_PARAMS_TEXT),
    ),
)

POOL_MAP_SCHEMA_V1 = MapOf(
    STATE_TEXT,
    POOL_SCHEMA_V1,
    MAX_POOLS_V1,
    POOL_MAP_SCHEMA_ID_V1,
)

VAULT_RECORD_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.VAULT,
    (
        _field("acc_reward_per_share", NONNEGATIVE_INT),
        _field("last_update_acc", NONNEGATIVE_INT),
        _field("pending_rewards", NONNEGATIVE_INT),
        _field("reward_balance", NONNEGATIVE_INT),
        _field("staked_lp_shares", NONNEGATIVE_INT),
    ),
)
VAULT_SCHEMA_V1 = OptionalValue(VAULT_RECORD_SCHEMA_V1)

ORACLE_RECORD_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.ORACLE,
    (
        _field("price_timestamp", NONNEGATIVE_INT),
        _field("max_staleness_seconds", ExactInt(1, None)),
    ),
)
ORACLE_SCHEMA_V1 = OptionalValue(ORACLE_RECORD_SCHEMA_V1)

FEE_ACCUMULATOR_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.FEE_ACCUMULATOR,
    (_field("dust", NONNEGATIVE_INT),),
)

PERP_ACCOUNT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERP_ACCOUNT,
    (
        _field("position_base", ExactInt(-PERP_POSITION_MAX, PERP_POSITION_MAX)),
        _field("entry_price_e8", ExactInt(0, MAX_PRICE_E8_V1)),
        _field("collateral_quote", ExactInt(0, MAX_COLLATERAL)),
        _field("funding_paid_cumulative", ExactInt(-MAX_COLLATERAL, MAX_COLLATERAL)),
        _field("funding_last_applied_epoch", ExactInt(0, MAX_EPOCH)),
        _field("liquidated_this_step", ExactBool()),
    ),
)


def _isolated_global_field_schema(name: str) -> SchemaV1:
    if name in {"breaker_active", "clearing_price_seen", "oracle_seen"}:
        return ExactBool()
    bounds: tuple[int | None, int | None]
    if name in {
        "now_epoch",
        "breaker_last_trigger_epoch",
        "clearing_price_epoch",
        "oracle_last_update_epoch",
    }:
        bounds = (0, MAX_EPOCH)
    elif name == "epoch_phase":
        bounds = (0, 2)
    elif name in {"clearing_price_e8", "index_price_e8", "min_notional_for_bounty"}:
        bounds = (0, MAX_PRICE_E8_V1)
    elif name == "mark_price_source_kind":
        bounds = (0, MARK_PRICE_SOURCE_EXTERNAL_MEDIAN)
    elif name == "max_oracle_staleness_epochs":
        bounds = (1, MAX_EPOCH)
    elif name in {
        "max_oracle_move_bps",
        "initial_margin_bps",
        "maintenance_margin_bps",
        "liquidation_penalty_bps",
    }:
        bounds = (0, MAX_BPS_V1)
    elif name == "depeg_buffer_bps":
        bounds = (0, MAX_DEPEG_BUFFER_BPS_V1)
    elif name == "max_position_abs":
        bounds = (1, PERP_POSITION_MAX)
    elif name in {
        "fee_pool_quote",
        "insurance_balance",
        "initial_insurance",
        "fee_income",
        "claims_paid",
    }:
        bounds = (0, MAX_COLLATERAL)
    elif name == "funding_rate_bps":
        bounds = (-MAX_BPS_V1, MAX_BPS_V1)
    elif name == "funding_cap_bps":
        bounds = (1, MAX_BPS_V1)
    else:  # pragma: no cover - registry drift tests keep this branch unreachable
        raise ValueError("unknown isolated perps global field")
    return ExactInt(*bounds)


ISOLATED_GLOBAL_FIELDS_V1 = tuple(
    _field(name, _isolated_global_field_schema(name)) for name in sorted(PERP_ISOLATED_GLOBAL_KEYS)
)
ISOLATED_GLOBAL_SCHEMA_V1 = ExactKeyedMap(
    ISOLATED_GLOBAL_FIELDS_V1,
    PERPS_ISOLATED_GLOBAL_MAP_SCHEMA_ID_V1,
)
ISOLATED_ACCOUNT_MAP_SCHEMA_V1 = MapOf(
    PUBKEY_TEXT,
    PERP_ACCOUNT_SCHEMA_V1,
    MAX_PERPS_ACCOUNTS_V1,
    PERPS_ISOLATED_ACCOUNT_MAP_SCHEMA_ID_V1,
)
PERP_ISOLATED_MARKET_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERP_ISOLATED_MARKET,
    (
        _field("quote_asset", STATE_TEXT),
        _field("global_state", ISOLATED_GLOBAL_SCHEMA_V1),
        _field("accounts", ISOLATED_ACCOUNT_MAP_SCHEMA_V1),
        _field(
            "kind",
            ExactString(
                StringRuleV1.EXACT_LITERAL,
                len("isolated_v2"),
                exact_literal="isolated_v2",
                exact_utf8_bytes=len("isolated_v2"),
                max_characters=len("isolated_v2"),
            ),
        ),
    ),
)


def _fixed_clearinghouse_field_schema(
    name: str,
    *,
    bool_keys: set[str],
    aggregate_maximum: int,
) -> SchemaV1:
    if name in bool_keys:
        return ExactBool()
    if name in {
        "now_epoch",
        "breaker_last_trigger_epoch",
        "clearing_price_epoch",
        "oracle_last_update_epoch",
    }:
        return ExactInt(0, MAX_EPOCH)
    if name in {"clearing_price_e8", "index_price_e8"} or name.startswith("entry_price_e8_"):
        return ExactInt(0, MAX_PRICE_E8_V1)
    if name == "max_oracle_staleness_epochs":
        return ExactInt(1, MAX_EPOCH)
    if name in {
        "max_oracle_move_bps",
        "initial_margin_bps",
        "maintenance_margin_bps",
        "liquidation_penalty_bps",
    }:
        return ExactInt(0, MAX_BPS_V1)
    if name == "max_position_abs":
        return ExactInt(1, PERP_POSITION_MAX)
    if name.startswith("position_base_"):
        return ExactInt(-PERP_POSITION_MAX, PERP_POSITION_MAX)
    if name.startswith("collateral_e8_"):
        return ExactInt(0, MAX_FIXED_CLEARINGHOUSE_COLLATERAL_E8_V1)
    if name in {"fee_pool_e8", "net_deposited_e8"}:
        return ExactInt(0, aggregate_maximum)
    raise ValueError("unknown fixed clearinghouse state field")


CH2P_STATE_FIELDS_V1 = tuple(
    _field(
        name,
        _fixed_clearinghouse_field_schema(
            name,
            bool_keys=PERP_CLEARINGHOUSE_2P_BOOL_KEYS,
            aggregate_maximum=MAX_CLEARINGHOUSE_2P_AGGREGATE_E8_V1,
        ),
    )
    for name in sorted(PERP_CLEARINGHOUSE_2P_STATE_KEYS)
)
CH2P_STATE_SCHEMA_V1 = ExactKeyedMap(
    CH2P_STATE_FIELDS_V1,
    PERPS_CLEARINGHOUSE_2P_STATE_MAP_SCHEMA_ID_V1,
)

PERP_CLEARINGHOUSE_2P_MARKET_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERP_CLEARINGHOUSE_2P_MARKET,
    (
        _field("quote_asset", STATE_TEXT),
        _field("account_a_pubkey", PUBKEY_TEXT),
        _field("account_b_pubkey", PUBKEY_TEXT),
        _field("state", CH2P_STATE_SCHEMA_V1),
        _field(
            "kind",
            ExactString(
                StringRuleV1.EXACT_LITERAL,
                len("clearinghouse_2p_v1"),
                exact_literal="clearinghouse_2p_v1",
                exact_utf8_bytes=len("clearinghouse_2p_v1"),
                max_characters=len("clearinghouse_2p_v1"),
            ),
        ),
    ),
)

CH3P_STATE_FIELDS_V1 = tuple(
    _field(
        name,
        _fixed_clearinghouse_field_schema(
            name,
            bool_keys=PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS,
            aggregate_maximum=MAX_CLEARINGHOUSE_3P_AGGREGATE_E8_V1,
        ),
    )
    for name in sorted(PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS)
)
CH3P_STATE_SCHEMA_V1 = ExactKeyedMap(
    CH3P_STATE_FIELDS_V1,
    PERPS_CLEARINGHOUSE_3P_STATE_MAP_SCHEMA_ID_V1,
)

PERP_CLEARINGHOUSE_3P_MARKET_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERP_CLEARINGHOUSE_3P_MARKET,
    (
        _field("quote_asset", STATE_TEXT),
        _field("account_a_pubkey", PUBKEY_TEXT),
        _field("account_b_pubkey", PUBKEY_TEXT),
        _field("account_c_pubkey", PUBKEY_TEXT),
        _field("state", CH3P_STATE_SCHEMA_V1),
        _field(
            "kind",
            ExactString(
                StringRuleV1.EXACT_LITERAL,
                len("clearinghouse_3p_transfer_v1"),
                exact_literal="clearinghouse_3p_transfer_v1",
                exact_utf8_bytes=len("clearinghouse_3p_transfer_v1"),
                max_characters=len("clearinghouse_3p_transfer_v1"),
            ),
        ),
    ),
)

PERP_CLEARINGHOUSE_NP_ACCOUNT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERP_CLEARINGHOUSE_NP_ACCOUNT,
    (
        _field("pubkey", PUBKEY_TEXT),
        _field("position_base", ExactInt(-PERP_POSITION_MAX, PERP_POSITION_MAX)),
        _field("entry_price_e8", NONNEGATIVE_INT),
        _field("collateral_e8", NONNEGATIVE_INT),
        _field("funding_paid_cum_e8", SIGNED_INT),
        _field("nonce", NONNEGATIVE_INT),
    ),
)

PERP_CLEARINGHOUSE_NP_PENDING_INTENT_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERP_CLEARINGHOUSE_NP_PENDING_INTENT,
    (
        _field("pubkey", PUBKEY_TEXT),
        _field("target_base", SIGNED_INT),
        _field("nonce", ExactInt(1, None)),
        _field("limit_price_e8", NONNEGATIVE_INT),
        _field("min_fill_base", NONNEGATIVE_INT),
        _field("expiry_epoch", NONNEGATIVE_INT),
    ),
)


def _np_global_field_schema(name: str) -> SchemaV1:
    if name == "net_deposited_e8":
        return SIGNED_INT
    if name == "index_price_e8":
        return ExactInt(1, None)
    if name == "clearing_price_seen":
        return ExactInt(0, 1)
    if name in {
        "now_epoch",
        "clearing_price_epoch",
        "clearing_price_e8",
        "fee_pool_e8",
        "insurance_e8",
        "insurance_ext_e8",
        "claims_paid_e8",
    }:
        return NONNEGATIVE_INT
    if name in {
        "initial_margin_bps",
        "maintenance_margin_bps",
        "liquidation_penalty_bps",
        "max_oracle_move_bps",
    }:
        return ExactInt(0, MAX_BPS_V1)
    if name == "depeg_buffer_bps":
        return ExactInt(0, MAX_DEPEG_BUFFER_BPS_V1)
    if name == "funding_cap_bps":
        return ExactInt(1, MAX_BPS_V1)
    if name == "max_position_abs":
        return ExactInt(1, PERP_POSITION_MAX)
    if name == "min_notional_for_bounty_e8":
        return ExactInt(0, MAX_NP_NOTIONAL_FOR_BOUNTY_E8_V1)
    raise ValueError("unknown N-party clearinghouse global field")


CHNP_GLOBAL_FIELDS_V1 = tuple(
    _field(name, _np_global_field_schema(name))
    for name in sorted(PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS)
)
CHNP_GLOBAL_SCHEMA_V1 = ExactKeyedMap(
    CHNP_GLOBAL_FIELDS_V1,
    PERPS_CLEARINGHOUSE_NP_GLOBAL_MAP_SCHEMA_ID_V1,
)

PERP_CLEARINGHOUSE_NP_MARKET_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERP_CLEARINGHOUSE_NP_MARKET,
    (
        _field("quote_asset", STATE_TEXT),
        _field("global_state", CHNP_GLOBAL_SCHEMA_V1),
        _field(
            "accounts",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,),
                PERP_CLEARINGHOUSE_NP_ACCOUNT_SCHEMA_V1,
                0,
                MAX_PERPS_ACCOUNTS_V1,
            ),
        ),
        _field(
            "pending_intents",
            SequenceOf(
                (SequenceSourceKind.EXACT_TUPLE,),
                PERP_CLEARINGHOUSE_NP_PENDING_INTENT_SCHEMA_V1,
                0,
                MAX_PERPS_PENDING_INTENTS_V1,
            ),
        ),
        _field(
            "kind",
            ExactString(
                StringRuleV1.EXACT_LITERAL,
                len("clearinghouse_np_v1"),
                exact_literal="clearinghouse_np_v1",
                exact_utf8_bytes=len("clearinghouse_np_v1"),
                max_characters=len("clearinghouse_np_v1"),
            ),
        ),
    ),
)

PERPS_MARKET_UNION_SCHEMA_V1 = RecordUnionOf(
    (
        PERP_ISOLATED_MARKET_SCHEMA_V1,
        PERP_CLEARINGHOUSE_2P_MARKET_SCHEMA_V1,
        PERP_CLEARINGHOUSE_3P_MARKET_SCHEMA_V1,
        PERP_CLEARINGHOUSE_NP_MARKET_SCHEMA_V1,
    )
)

PERPS_RECORD_SCHEMA_V1 = RecordOf(
    StateRecordTagV1.PERPS,
    (
        _field("version", ExactInt(PERPS_STATE_VERSION_V4, PERPS_STATE_VERSION_V5)),
        _field(
            "markets",
            MapOf(
                STATE_TEXT,
                PERPS_MARKET_UNION_SCHEMA_V1,
                MAX_PERPS_MARKETS_V1,
                PERPS_MARKET_MAP_SCHEMA_ID_V1,
            ),
        ),
    ),
)
PERPS_SCHEMA_V1 = OptionalValue(PERPS_RECORD_SCHEMA_V1)


ENUM_REGISTRATIONS_V1 = (EnumRegistrationV1(StateEnumTagV1.POOL_STATUS, PoolStatus),)

RECORD_REGISTRATIONS_V1 = (
    RecordRegistrationV1(
        StateRecordTagV1.BALANCE_TABLE,
        _BalanceSourceV1,
        CommittedBalanceTableV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.LP_TABLE,
        _LPSourceV1,
        CommittedLPTableV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.NONCE_TABLE,
        NonceTable,
        CommittedNonceTableV1,
    ),
    RecordRegistrationV1(StateRecordTagV1.POOL, PoolState, CommittedPoolStateV1),
    RecordRegistrationV1(StateRecordTagV1.VAULT, VaultState, CommittedVaultStateV1),
    RecordRegistrationV1(StateRecordTagV1.ORACLE, OracleState, CommittedOracleStateV1),
    RecordRegistrationV1(
        StateRecordTagV1.FEE_ACCUMULATOR,
        FeeAccumulatorState,
        CommittedFeeAccumulatorStateV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.PERP_ACCOUNT,
        PerpAccountState,
        CommittedPerpAccountStateV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.PERP_ISOLATED_MARKET,
        PerpMarketState,
        CommittedPerpMarketStateV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.PERP_CLEARINGHOUSE_2P_MARKET,
        PerpClearinghouse2pMarketState,
        CommittedPerpClearinghouse2pMarketStateV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.PERP_CLEARINGHOUSE_3P_MARKET,
        PerpClearinghouse3pTransferMarketState,
        CommittedPerpClearinghouse3pTransferMarketStateV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.PERP_CLEARINGHOUSE_NP_ACCOUNT,
        PerpClearinghouseNpAccount,
        CommittedPerpClearinghouseNpAccountV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.PERP_CLEARINGHOUSE_NP_PENDING_INTENT,
        PerpClearinghouseNpPendingIntent,
        CommittedPerpClearinghouseNpPendingIntentV1,
    ),
    RecordRegistrationV1(
        StateRecordTagV1.PERP_CLEARINGHOUSE_NP_MARKET,
        PerpClearinghouseNpMarketState,
        CommittedPerpClearinghouseNpMarketStateV1,
    ),
    RecordRegistrationV1(StateRecordTagV1.PERPS, PerpsState, CommittedPerpsStateV1),
)

SCHEMA_REGISTRATIONS_V1 = (
    SchemaRegistrationV1(BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1, BALANCE_TABLE_SCHEMA_V1),
    SchemaRegistrationV1(LP_TABLE_ADMISSION_SCHEMA_ID_V1, LP_TABLE_SCHEMA_V1),
    SchemaRegistrationV1(NONCE_TABLE_ADMISSION_SCHEMA_ID_V1, NONCE_TABLE_SCHEMA_V1),
    SchemaRegistrationV1(POOL_ADMISSION_SCHEMA_ID_V1, POOL_SCHEMA_V1),
    SchemaRegistrationV1(POOL_MAP_ADMISSION_SCHEMA_ID_V1, POOL_MAP_SCHEMA_V1),
    SchemaRegistrationV1(VAULT_ADMISSION_SCHEMA_ID_V1, VAULT_SCHEMA_V1),
    SchemaRegistrationV1(ORACLE_ADMISSION_SCHEMA_ID_V1, ORACLE_SCHEMA_V1),
    SchemaRegistrationV1(
        FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1,
        FEE_ACCUMULATOR_SCHEMA_V1,
    ),
    SchemaRegistrationV1(PERPS_ADMISSION_SCHEMA_ID_V1, PERPS_SCHEMA_V1),
)

KNOWN_STATE_ADMISSION_SCHEMA_IDS_V1 = tuple(
    registration.schema_id for registration in SCHEMA_REGISTRATIONS_V1
)
