"""Canonical DEX snapshot bytes from the exact committed FCIS graph.

The encoder is shadow-only during PR #477. Temporary dictionaries and lists
exist only inside these pure functions and are lowered immediately to canonical
JSON bytes; no mutable projection escapes to an authority caller.
"""

from __future__ import annotations

from ..core.perps import PERPS_STATE_VERSION_V5
from .canonical import bounded_json_utf8_size, canonical_json_bytes, domain_sep_bytes, sha256_hex
from .dex_snapshot_profile import DEX_SNAPSHOT_SUPPORTED_VERSIONS_V1
from .fcis_committed_state_values import FCISCommittedStateV1
from .owned_collections import OwnedMapV1
from .snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
)
from .state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpClearinghouse2pMarketStateV1,
    CommittedPerpClearinghouse3pTransferMarketStateV1,
    CommittedPerpClearinghouseNpMarketStateV1,
    CommittedPerpMarketStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
)
from .state_snapshots import (
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_oracle,
    snapshot_perps,
    snapshot_pool_map,
    snapshot_vault,
)

_POOL_STATUS_LABELS_V1 = ("ACTIVE", "FROZEN", "DISABLED")


def _exact_balances_v1(value: CommittedBalanceTableV1) -> CommittedBalanceTableV1:
    if type(value) is not CommittedBalanceTableV1:
        raise TypeError("balances must be an exact CommittedBalanceTableV1")
    return snapshot_balance_table(value)


def _exact_pools_v1(
    value: OwnedMapV1[str, CommittedPoolStateV1],
) -> OwnedMapV1[str, CommittedPoolStateV1]:
    if type(value) is not OwnedMapV1:
        raise TypeError("pools must be an exact OwnedMapV1")
    return snapshot_pool_map(value)


def _exact_lp_v1(value: CommittedLPTableV1) -> CommittedLPTableV1:
    if type(value) is not CommittedLPTableV1:
        raise TypeError("lp_balances must be an exact CommittedLPTableV1")
    return snapshot_lp_table(value)


def _exact_nonces_v1(value: CommittedNonceTableV1) -> CommittedNonceTableV1:
    if type(value) is not CommittedNonceTableV1:
        raise TypeError("nonces must be an exact CommittedNonceTableV1")
    return snapshot_nonce_table(value)


def _exact_fees_v1(
    value: CommittedFeeAccumulatorStateV1,
) -> CommittedFeeAccumulatorStateV1:
    if type(value) is not CommittedFeeAccumulatorStateV1:
        raise TypeError("fee_accumulator must be an exact CommittedFeeAccumulatorStateV1")
    return snapshot_fee_accumulator(value)


def _exact_vault_v1(
    value: CommittedVaultStateV1 | None,
) -> CommittedVaultStateV1 | None:
    if value is not None and type(value) is not CommittedVaultStateV1:
        raise TypeError("vault must be None or an exact CommittedVaultStateV1")
    return snapshot_vault(value)


def _exact_oracle_v1(
    value: CommittedOracleStateV1 | None,
) -> CommittedOracleStateV1 | None:
    if value is not None and type(value) is not CommittedOracleStateV1:
        raise TypeError("oracle must be None or an exact CommittedOracleStateV1")
    return snapshot_oracle(value)


def _exact_perps_v1(
    value: CommittedPerpsStateV1 | None,
) -> CommittedPerpsStateV1 | None:
    if value is not None and type(value) is not CommittedPerpsStateV1:
        raise TypeError("perps must be None or an exact CommittedPerpsStateV1")
    return snapshot_perps(value)


def _balance_entries_v1(state: CommittedBalanceTableV1) -> list[dict[str, object]]:
    return [
        {"pubkey": pubkey, "asset": asset, "amount": amount}
        for (pubkey, asset), amount in state.entries
    ]


def _pool_entries_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> list[dict[str, object]]:
    return [
        {
            "pool_id": pool_id,
            "asset0": pool.asset0,
            "asset1": pool.asset1,
            "reserve0": pool.reserve0,
            "reserve1": pool.reserve1,
            "fee_bps": pool.fee_bps,
            "lp_supply": pool.lp_supply,
            "status": _POOL_STATUS_LABELS_V1[pool.status.member_ordinal],
            "created_at": pool.created_at,
            "curve_tag": pool.curve_tag,
            "curve_params": pool.curve_params,
        }
        for pool_id, pool in pools.entries
    ]


def _lp_balance_entries_v1(state: CommittedLPTableV1) -> list[dict[str, object]]:
    return [
        {"pubkey": pubkey, "pool_id": pool_id, "amount": amount}
        for (pubkey, pool_id), amount in state.balance_entries
    ]


def _lp_mint_entries_v1(state: CommittedLPTableV1) -> list[dict[str, object]]:
    return [
        {"pubkey": pubkey, "pool_id": pool_id, "last_mint_timestamp": timestamp}
        for (pubkey, pool_id), timestamp in state.last_mint_entries
    ]


def _lp_risk_entries_v1(state: CommittedLPTableV1) -> list[dict[str, object]]:
    keys = [
        key
        for entries in (
            state.last_mint_entries,
            state.last_remove_entries,
            state.churn_tier_entries,
            state.last_churn_update_entries,
        )
        for key, _value in entries
    ]
    keys.sort()
    unique_keys = [key for index, key in enumerate(keys) if index == 0 or key != keys[index - 1]]
    return [
        {
            "pubkey": pubkey,
            "pool_id": pool_id,
            "last_remove_timestamp": state.get_last_remove_timestamp(pubkey, pool_id),
            "churn_tier": state.get_churn_tier(pubkey, pool_id),
            "last_churn_update_timestamp": state.get_last_churn_update_timestamp(
                pubkey,
                pool_id,
            ),
        }
        for pubkey, pool_id in unique_keys
    ]


def _nonce_entries_v1(state: CommittedNonceTableV1) -> list[dict[str, object]]:
    return [{"pubkey": pubkey, "last_nonce": nonce} for pubkey, nonce in state.entries]


def _isolated_market_v1(
    market_id: str,
    market: CommittedPerpMarketStateV1,
    *,
    perps_version: int,
) -> dict[str, object]:
    accounts = [
        {
            "pubkey": pubkey,
            "position_base": account.position_base,
            "entry_price_e8": account.entry_price_e8,
            "collateral_quote": account.collateral_quote,
            "funding_paid_cumulative": account.funding_paid_cumulative,
            "funding_last_applied_epoch": account.funding_last_applied_epoch,
            "liquidated_this_step": account.liquidated_this_step,
        }
        for pubkey, account in market.accounts.entries
    ]
    entry: dict[str, object] = {
        "market_id": market_id,
        "quote_asset": market.quote_asset,
        "global_state": {key: value for key, value in market.global_state.entries},
        "accounts": accounts,
    }
    if perps_version >= PERPS_STATE_VERSION_V5:
        entry["kind"] = market.kind
    return entry


def _fixed_market_v1(
    market_id: str,
    market: CommittedPerpClearinghouse2pMarketStateV1
    | CommittedPerpClearinghouse3pTransferMarketStateV1,
) -> dict[str, object]:
    entry: dict[str, object] = {
        "market_id": market_id,
        "kind": market.kind,
        "quote_asset": market.quote_asset,
        "account_a_pubkey": market.account_a_pubkey,
        "account_b_pubkey": market.account_b_pubkey,
        "state": {key: value for key, value in market.state.entries},
    }
    if type(market) is CommittedPerpClearinghouse3pTransferMarketStateV1:
        entry["account_c_pubkey"] = market.account_c_pubkey
    return entry


def _np_market_v1(
    market_id: str,
    market: CommittedPerpClearinghouseNpMarketStateV1,
) -> dict[str, object]:
    accounts = [
        {
            "pubkey": account.pubkey,
            "position_base": account.position_base,
            "entry_price_e8": account.entry_price_e8,
            "collateral_e8": account.collateral_e8,
            "funding_paid_cum_e8": account.funding_paid_cum_e8,
            "nonce": account.nonce,
        }
        for account in market.accounts
    ]
    pending = [
        {
            "pubkey": intent.pubkey,
            "target_base": intent.target_base,
            "limit_price_e8": intent.limit_price_e8,
            "min_fill_base": intent.min_fill_base,
            "expiry_epoch": intent.expiry_epoch,
            "nonce": intent.nonce,
        }
        for intent in market.pending_intents
    ]
    return {
        "market_id": market_id,
        "kind": market.kind,
        "quote_asset": market.quote_asset,
        "global_state": {key: value for key, value in market.global_state.entries},
        "accounts": accounts,
        "pending_intents": pending,
    }


def _perps_market_v1(
    market_id: str,
    market: object,
    *,
    perps_version: int,
) -> dict[str, object]:
    if type(market) is CommittedPerpMarketStateV1:
        return _isolated_market_v1(market_id, market, perps_version=perps_version)
    if type(market) is CommittedPerpClearinghouse2pMarketStateV1:
        return _fixed_market_v1(market_id, market)
    if type(market) is CommittedPerpClearinghouse3pTransferMarketStateV1:
        return _fixed_market_v1(market_id, market)
    if type(market) is CommittedPerpClearinghouseNpMarketStateV1:
        return _np_market_v1(market_id, market)
    raise TypeError("committed perps map contains an unsupported exact market")


def _perps_v1(state: CommittedPerpsStateV1 | None) -> dict[str, object] | None:
    if state is None:
        return None
    markets = [
        _perps_market_v1(market_id, market, perps_version=state.version)
        for market_id, market in state.markets.entries
    ]
    return {"version": state.version, "markets": markets}


def canonical_snapshot_bytes_from_committed_state_v1(
    *,
    version: int,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    nonces: CommittedNonceTableV1,
    fee_accumulator: CommittedFeeAccumulatorStateV1,
    vault: CommittedVaultStateV1 | None,
    oracle: CommittedOracleStateV1 | None,
    perps: CommittedPerpsStateV1 | None,
) -> bytes:
    """Encode exact committed state in the existing DEX snapshot language."""

    if type(version) is not int or version <= 0:
        raise ValueError("version must be a positive exact int")
    if version not in DEX_SNAPSHOT_SUPPORTED_VERSIONS_V1:
        raise ValueError(f"unsupported snapshot version: {version}")
    admitted_balances = _exact_balances_v1(balances)
    admitted_pools = _exact_pools_v1(pools)
    admitted_lp = _exact_lp_v1(lp_balances)
    admitted_nonces = _exact_nonces_v1(nonces)
    admitted_fees = _exact_fees_v1(fee_accumulator)
    admitted_vault = _exact_vault_v1(vault)
    admitted_oracle = _exact_oracle_v1(oracle)
    admitted_perps = _exact_perps_v1(perps)

    data: dict[str, object] = {
        "version": version,
        "balances": _balance_entries_v1(admitted_balances),
        "pools": _pool_entries_v1(admitted_pools),
        "lp_balances": _lp_balance_entries_v1(admitted_lp),
        "lp_mint_timestamps": _lp_mint_entries_v1(admitted_lp),
        "lp_duration_risk": _lp_risk_entries_v1(admitted_lp),
        "nonces": _nonce_entries_v1(admitted_nonces),
        "fee_accumulator": {"dust": admitted_fees.dust},
        "vault": None
        if admitted_vault is None
        else {
            "acc_reward_per_share": admitted_vault.acc_reward_per_share,
            "last_update_acc": admitted_vault.last_update_acc,
            "pending_rewards": admitted_vault.pending_rewards,
            "reward_balance": admitted_vault.reward_balance,
            "staked_lp_shares": admitted_vault.staked_lp_shares,
        },
        "oracle": None
        if admitted_oracle is None
        else {
            "price_timestamp": admitted_oracle.price_timestamp,
            "max_staleness_seconds": admitted_oracle.max_staleness_seconds,
        },
    }
    if version >= 2:
        data["perps"] = _perps_v1(admitted_perps)
    bounded_json_utf8_size(
        data,
        max_bytes=MAX_CANONICAL_BYTES_V1,
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_items=MAX_ADMISSION_NODES_V1,
    )
    return canonical_json_bytes(data)


def canonical_committed_state_root_binding_v1(
    state: FCISCommittedStateV1,
    snapshot_version: int,
) -> tuple[bytes, bytes, str]:
    """Revalidate all eight fields and bind their canonical snapshot root.

    The evaluator and commit port share this function so the publication
    boundary cannot drift from the transition's state-root language.
    """

    if type(state) is not FCISCommittedStateV1:
        raise TypeError("state-root binding requires an exact committed state")
    if type(snapshot_version) is not int or snapshot_version <= 0:
        raise TypeError("snapshot_version must be an exact positive int")
    snapshot_bytes = canonical_snapshot_bytes_from_committed_state_v1(
        version=snapshot_version,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
        fee_accumulator=state.fee_accumulator,
        vault=state.vault,
        oracle=state.oracle,
        perps=state.perps,
    )
    root_preimage = domain_sep_bytes("dex_snapshot", version=snapshot_version) + snapshot_bytes
    return snapshot_bytes, root_preimage, sha256_hex(root_preimage)


__all__ = (
    "canonical_committed_state_root_binding_v1",
    "canonical_snapshot_bytes_from_committed_state_v1",
)
