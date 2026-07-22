"""Single mounted FCIS admission profile for committed DEX state values."""

from __future__ import annotations

from enum import Enum
from typing import cast

from src.state import snapshot_combinators

from ..state.canonical import bounded_json_utf8_size, canonical_json_bytes
from .owned_collections import OwnedEnumV1, OwnedMapV1
from .snapshot_combinators import (
    AdmitOk,
    AdmitReject,
    ValidatedAdmissionLimitsV1,
    build_admission_registry_v1,
)
from .state_snapshot_schema import (
    BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
    ENUM_REGISTRATIONS_V1,
    FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1,
    KNOWN_STATE_ADMISSION_SCHEMA_IDS_V1,
    LP_TABLE_ADMISSION_SCHEMA_ID_V1,
    NONCE_TABLE_ADMISSION_SCHEMA_ID_V1,
    ORACLE_ADMISSION_SCHEMA_ID_V1,
    PERPS_ADMISSION_SCHEMA_ID_V1,
    POOL_ADMISSION_SCHEMA_ID_V1,
    POOL_MAP_ADMISSION_SCHEMA_ID_V1,
    RECORD_REGISTRATIONS_V1,
    SCHEMA_REGISTRATIONS_V1,
    VAULT_ADMISSION_SCHEMA_ID_V1,
    StateEnumTagV1,
    StateRecordTagV1,
)
from .state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
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
)

FCIS_REQUIRED_REGISTRY_IDS = (
    "zenodex/fcis/state/balance-table/v1",
    "zenodex/fcis/state/lp-table/v1",
    "zenodex/fcis/state/nonce-table/v1",
    "zenodex/fcis/state/pool/v1",
    "zenodex/fcis/state/pool-map/v1",
    "zenodex/fcis/state/vault/v1",
    "zenodex/fcis/state/oracle/v1",
    "zenodex/fcis/state/fee-accumulator/v1",
    "zenodex/fcis/state/perps/v1",
)
FCIS_REGISTERED_REGISTRY_IDS = (
    "zenodex/fcis/state/balance-table/v1",
    "zenodex/fcis/state/lp-table/v1",
    "zenodex/fcis/state/nonce-table/v1",
    "zenodex/fcis/state/pool/v1",
    "zenodex/fcis/state/pool-map/v1",
    "zenodex/fcis/state/vault/v1",
    "zenodex/fcis/state/oracle/v1",
    "zenodex/fcis/state/fee-accumulator/v1",
    "zenodex/fcis/state/perps/v1",
)

_STATE_ADMISSION_REGISTRY_V1 = build_admission_registry_v1(
    schema_revision=FCIS_STATE_SCHEMA_REVISION_V1,
    enum_tag_type=StateEnumTagV1,
    record_tag_type=StateRecordTagV1,
    enum_registrations=ENUM_REGISTRATIONS_V1,
    record_registrations=RECORD_REGISTRATIONS_V1,
    schema_registrations=SCHEMA_REGISTRATIONS_V1,
)


def _record_field(
    values: tuple[tuple[str, object], ...],
    index: int,
    expected_name: str,
) -> object:
    if type(values) is not tuple or index >= len(values):
        raise ValueError("record field registry drift")
    field = values[index]
    if type(field) is not tuple or len(field) != 2 or field[0] != expected_name:
        raise ValueError("record field registry drift")
    return field[1]


def _construct_state_record(
    record_tag: Enum,
    values: tuple[tuple[str, object], ...],
) -> object:
    """Construct one exact committed record from already-admitted children."""

    if record_tag is StateRecordTagV1.BALANCE_TABLE and len(values) == 1:
        return CommittedBalanceTableV1(
            cast(OwnedMapV1[tuple[str, str], int], _record_field(values, 0, "_balances"))
        )
    if record_tag is StateRecordTagV1.LP_TABLE and len(values) == 5:
        return CommittedLPTableV1(
            cast(OwnedMapV1[tuple[str, str], int], _record_field(values, 0, "_balances")),
            cast(
                OwnedMapV1[tuple[str, str], int],
                _record_field(values, 1, "_last_mint_timestamps"),
            ),
            cast(
                OwnedMapV1[tuple[str, str], int],
                _record_field(values, 2, "_last_remove_timestamps"),
            ),
            cast(
                OwnedMapV1[tuple[str, str], int],
                _record_field(values, 3, "_churn_tiers"),
            ),
            cast(
                OwnedMapV1[tuple[str, str], int],
                _record_field(values, 4, "_last_churn_update_timestamps"),
            ),
        )
    if record_tag is StateRecordTagV1.NONCE_TABLE and len(values) == 1:
        return CommittedNonceTableV1(cast(OwnedMapV1[str, int], _record_field(values, 0, "_last")))
    if record_tag is StateRecordTagV1.POOL and len(values) == 11:
        return CommittedPoolStateV1(
            cast(str, _record_field(values, 0, "pool_id")),
            cast(str, _record_field(values, 1, "asset0")),
            cast(str, _record_field(values, 2, "asset1")),
            cast(int, _record_field(values, 3, "reserve0")),
            cast(int, _record_field(values, 4, "reserve1")),
            cast(int, _record_field(values, 5, "fee_bps")),
            cast(int, _record_field(values, 6, "lp_supply")),
            cast(OwnedEnumV1, _record_field(values, 7, "status")),
            cast(int, _record_field(values, 8, "created_at")),
            cast(str, _record_field(values, 9, "curve_tag")),
            cast(str, _record_field(values, 10, "curve_params")),
        )
    if record_tag is StateRecordTagV1.VAULT and len(values) == 5:
        return CommittedVaultStateV1(
            cast(int, _record_field(values, 0, "acc_reward_per_share")),
            cast(int, _record_field(values, 1, "last_update_acc")),
            cast(int, _record_field(values, 2, "pending_rewards")),
            cast(int, _record_field(values, 3, "reward_balance")),
            cast(int, _record_field(values, 4, "staked_lp_shares")),
        )
    if record_tag is StateRecordTagV1.ORACLE and len(values) == 2:
        return CommittedOracleStateV1(
            cast(int, _record_field(values, 0, "price_timestamp")),
            cast(int, _record_field(values, 1, "max_staleness_seconds")),
        )
    if record_tag is StateRecordTagV1.FEE_ACCUMULATOR and len(values) == 1:
        return CommittedFeeAccumulatorStateV1(cast(int, _record_field(values, 0, "dust")))
    if record_tag is StateRecordTagV1.PERP_ACCOUNT and len(values) == 6:
        return CommittedPerpAccountStateV1(
            cast(int, _record_field(values, 0, "position_base")),
            cast(int, _record_field(values, 1, "entry_price_e8")),
            cast(int, _record_field(values, 2, "collateral_quote")),
            cast(int, _record_field(values, 3, "funding_paid_cumulative")),
            cast(int, _record_field(values, 4, "funding_last_applied_epoch")),
            cast(bool, _record_field(values, 5, "liquidated_this_step")),
        )
    if record_tag is StateRecordTagV1.PERP_ISOLATED_MARKET and len(values) == 4:
        return CommittedPerpMarketStateV1(
            cast(str, _record_field(values, 0, "quote_asset")),
            cast(OwnedMapV1[str, int | bool], _record_field(values, 1, "global_state")),
            cast(
                OwnedMapV1[str, CommittedPerpAccountStateV1],
                _record_field(values, 2, "accounts"),
            ),
            cast(str, _record_field(values, 3, "kind")),
        )
    if record_tag is StateRecordTagV1.PERP_CLEARINGHOUSE_2P_MARKET and len(values) == 5:
        return CommittedPerpClearinghouse2pMarketStateV1(
            cast(str, _record_field(values, 0, "quote_asset")),
            cast(str, _record_field(values, 1, "account_a_pubkey")),
            cast(str, _record_field(values, 2, "account_b_pubkey")),
            cast(OwnedMapV1[str, int | bool], _record_field(values, 3, "state")),
            cast(str, _record_field(values, 4, "kind")),
        )
    if record_tag is StateRecordTagV1.PERP_CLEARINGHOUSE_3P_MARKET and len(values) == 6:
        return CommittedPerpClearinghouse3pTransferMarketStateV1(
            cast(str, _record_field(values, 0, "quote_asset")),
            cast(str, _record_field(values, 1, "account_a_pubkey")),
            cast(str, _record_field(values, 2, "account_b_pubkey")),
            cast(str, _record_field(values, 3, "account_c_pubkey")),
            cast(OwnedMapV1[str, int | bool], _record_field(values, 4, "state")),
            cast(str, _record_field(values, 5, "kind")),
        )
    if record_tag is StateRecordTagV1.PERP_CLEARINGHOUSE_NP_ACCOUNT and len(values) == 6:
        return CommittedPerpClearinghouseNpAccountV1(
            cast(str, _record_field(values, 0, "pubkey")),
            cast(int, _record_field(values, 1, "position_base")),
            cast(int, _record_field(values, 2, "entry_price_e8")),
            cast(int, _record_field(values, 3, "collateral_e8")),
            cast(int, _record_field(values, 4, "funding_paid_cum_e8")),
            cast(int, _record_field(values, 5, "nonce")),
        )
    if record_tag is StateRecordTagV1.PERP_CLEARINGHOUSE_NP_PENDING_INTENT and len(values) == 6:
        return CommittedPerpClearinghouseNpPendingIntentV1(
            cast(str, _record_field(values, 0, "pubkey")),
            cast(int, _record_field(values, 1, "target_base")),
            cast(int, _record_field(values, 2, "nonce")),
            cast(int, _record_field(values, 3, "limit_price_e8")),
            cast(int, _record_field(values, 4, "min_fill_base")),
            cast(int, _record_field(values, 5, "expiry_epoch")),
        )
    if record_tag is StateRecordTagV1.PERP_CLEARINGHOUSE_NP_MARKET and len(values) == 5:
        return CommittedPerpClearinghouseNpMarketStateV1(
            cast(str, _record_field(values, 0, "quote_asset")),
            cast(OwnedMapV1[str, int], _record_field(values, 1, "global_state")),
            cast(
                tuple[CommittedPerpClearinghouseNpAccountV1, ...],
                _record_field(values, 2, "accounts"),
            ),
            cast(
                tuple[CommittedPerpClearinghouseNpPendingIntentV1, ...],
                _record_field(values, 3, "pending_intents"),
            ),
            cast(str, _record_field(values, 4, "kind")),
        )
    if record_tag is StateRecordTagV1.PERPS and len(values) == 2:
        return CommittedPerpsStateV1(
            cast(int, _record_field(values, 0, "version")),
            cast(OwnedMapV1[str, object], _record_field(values, 1, "markets")),
        )
    raise ValueError("unsupported state record tag or field registry drift")


def _project_map(value: OwnedMapV1[object, object]) -> list[object]:
    return [[_project_owned(key), _project_owned(item)] for key, item in value.entries]


def _project_owned(value: object) -> object:
    """Project exact admitted values into a bounded canonical JSON tree."""

    if value is None or type(value) in {bool, int, str}:
        return value
    if type(value) is tuple:
        return [_project_owned(item) for item in cast(tuple[object, ...], value)]
    if type(value) is OwnedEnumV1:
        enum_value = cast(OwnedEnumV1, value)
        return [
            enum_value.schema_revision,
            enum_value.enum_tag_ordinal,
            enum_value.member_ordinal,
        ]
    if type(value) is OwnedMapV1:
        return _project_map(cast(OwnedMapV1[object, object], value))
    if type(value) is CommittedBalanceTableV1:
        balance = value
        return {"_balances": _project_owned(balance._balances)}
    if type(value) is CommittedLPTableV1:
        lp = value
        return {
            "_balances": _project_owned(lp._balances),
            "_last_mint_timestamps": _project_owned(lp._last_mint_timestamps),
            "_last_remove_timestamps": _project_owned(lp._last_remove_timestamps),
            "_churn_tiers": _project_owned(lp._churn_tiers),
            "_last_churn_update_timestamps": _project_owned(lp._last_churn_update_timestamps),
        }
    if type(value) is CommittedNonceTableV1:
        nonce = value
        return {"_last": _project_owned(nonce._last)}
    if type(value) is CommittedPoolStateV1:
        pool = value
        return {
            "pool_id": pool.pool_id,
            "asset0": pool.asset0,
            "asset1": pool.asset1,
            "reserve0": pool.reserve0,
            "reserve1": pool.reserve1,
            "fee_bps": pool.fee_bps,
            "lp_supply": pool.lp_supply,
            "status": _project_owned(pool.status),
            "created_at": pool.created_at,
            "curve_tag": pool.curve_tag,
            "curve_params": pool.curve_params,
        }
    if type(value) is CommittedVaultStateV1:
        vault = value
        return {
            "acc_reward_per_share": vault.acc_reward_per_share,
            "last_update_acc": vault.last_update_acc,
            "pending_rewards": vault.pending_rewards,
            "reward_balance": vault.reward_balance,
            "staked_lp_shares": vault.staked_lp_shares,
        }
    if type(value) is CommittedOracleStateV1:
        oracle = value
        return {
            "price_timestamp": oracle.price_timestamp,
            "max_staleness_seconds": oracle.max_staleness_seconds,
        }
    if type(value) is CommittedFeeAccumulatorStateV1:
        fees = value
        return {"dust": fees.dust}
    if type(value) is CommittedPerpAccountStateV1:
        account = value
        return {
            "position_base": account.position_base,
            "entry_price_e8": account.entry_price_e8,
            "collateral_quote": account.collateral_quote,
            "funding_paid_cumulative": account.funding_paid_cumulative,
            "funding_last_applied_epoch": account.funding_last_applied_epoch,
            "liquidated_this_step": account.liquidated_this_step,
        }
    if type(value) is CommittedPerpMarketStateV1:
        isolated = value
        return {
            "quote_asset": isolated.quote_asset,
            "global_state": _project_owned(isolated.global_state),
            "accounts": _project_owned(isolated.accounts),
            "kind": isolated.kind,
        }
    if type(value) is CommittedPerpClearinghouse2pMarketStateV1:
        ch2p = value
        return {
            "quote_asset": ch2p.quote_asset,
            "account_a_pubkey": ch2p.account_a_pubkey,
            "account_b_pubkey": ch2p.account_b_pubkey,
            "state": _project_owned(ch2p.state),
            "kind": ch2p.kind,
        }
    if type(value) is CommittedPerpClearinghouse3pTransferMarketStateV1:
        ch3p = value
        return {
            "quote_asset": ch3p.quote_asset,
            "account_a_pubkey": ch3p.account_a_pubkey,
            "account_b_pubkey": ch3p.account_b_pubkey,
            "account_c_pubkey": ch3p.account_c_pubkey,
            "state": _project_owned(ch3p.state),
            "kind": ch3p.kind,
        }
    if type(value) is CommittedPerpClearinghouseNpAccountV1:
        np_account = value
        return {
            "pubkey": np_account.pubkey,
            "position_base": np_account.position_base,
            "entry_price_e8": np_account.entry_price_e8,
            "collateral_e8": np_account.collateral_e8,
            "funding_paid_cum_e8": np_account.funding_paid_cum_e8,
            "nonce": np_account.nonce,
        }
    if type(value) is CommittedPerpClearinghouseNpPendingIntentV1:
        pending = value
        return {
            "pubkey": pending.pubkey,
            "target_base": pending.target_base,
            "nonce": pending.nonce,
            "limit_price_e8": pending.limit_price_e8,
            "min_fill_base": pending.min_fill_base,
            "expiry_epoch": pending.expiry_epoch,
        }
    if type(value) is CommittedPerpClearinghouseNpMarketStateV1:
        np_market = value
        return {
            "quote_asset": np_market.quote_asset,
            "global_state": _project_owned(np_market.global_state),
            "accounts": _project_owned(np_market.accounts),
            "pending_intents": _project_owned(np_market.pending_intents),
            "kind": np_market.kind,
        }
    if type(value) is CommittedPerpsStateV1:
        perps = value
        return {"version": perps.version, "markets": _project_owned(perps.markets)}
    raise TypeError("canonical state projection received an unsupported exact type")


def _canonical_state_encoder(schema_id: str, value: object) -> bytes:
    if type(schema_id) is not str or schema_id not in KNOWN_STATE_ADMISSION_SCHEMA_IDS_V1:
        raise ValueError("unknown state admission schema ID")
    expected_types: dict[str, tuple[type[object], ...]] = {
        BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1: (CommittedBalanceTableV1,),
        LP_TABLE_ADMISSION_SCHEMA_ID_V1: (CommittedLPTableV1,),
        NONCE_TABLE_ADMISSION_SCHEMA_ID_V1: (CommittedNonceTableV1,),
        POOL_ADMISSION_SCHEMA_ID_V1: (CommittedPoolStateV1,),
        POOL_MAP_ADMISSION_SCHEMA_ID_V1: (OwnedMapV1,),
        VAULT_ADMISSION_SCHEMA_ID_V1: (type(None), CommittedVaultStateV1),
        ORACLE_ADMISSION_SCHEMA_ID_V1: (type(None), CommittedOracleStateV1),
        FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1: (CommittedFeeAccumulatorStateV1,),
        PERPS_ADMISSION_SCHEMA_ID_V1: (type(None), CommittedPerpsStateV1),
    }
    if type(value) not in expected_types[schema_id]:
        raise TypeError("state admission schema and result type disagree")
    if schema_id == POOL_MAP_ADMISSION_SCHEMA_ID_V1:
        pool_map = cast(OwnedMapV1[str, CommittedPoolStateV1], value)
        if any(pool_id != pool.pool_id for pool_id, pool in pool_map.entries):
            raise ValueError("pool map key does not bind its committed pool")
    projection = _project_owned(value)
    bounded_json_utf8_size(
        projection,
        max_bytes=4_000_000,
        max_depth=64,
        max_items=200_000,
    )
    return canonical_json_bytes(projection)


def admit(
    schema_revision: str,
    schema_id: str,
    validated_limits: ValidatedAdmissionLimitsV1,
    source: object,
) -> AdmitOk[object] | AdmitReject:
    """Admit through the sole source-owned four-argument state profile."""

    return snapshot_combinators._admit_with_registry_v1(
        _STATE_ADMISSION_REGISTRY_V1,
        schema_revision,
        schema_id,
        validated_limits,
        source,
        _construct_state_record,
        _canonical_state_encoder,
    )
