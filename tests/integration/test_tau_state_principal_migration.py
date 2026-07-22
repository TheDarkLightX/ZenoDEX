from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.dex import DexState
from src.core.perps import PerpAccountState, PerpMarketState
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
from src.integration.tau_state_principal_migration import (
    canonicalize_legacy_tau_state_principals,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.nonces import NonceTable

RAW = "11" * 48
CANONICAL = "0x" + RAW
OPERATOR = "22" * 48
QUOTE_ASSET = "0x" + "33" * 32
MARKET_ID = "perp:tau-principal-migration"


def _isolated_init_op() -> dict[str, object]:
    return {
        "module": "TauPerp",
        "version": "0.1",
        "market_id": MARKET_ID,
        "action": "init_market",
        "quote_asset": QUOTE_ASSET,
    }


def _tau_perp_config() -> PerpEngineConfig:
    return PerpEngineConfig(
        operator_pubkey=OPERATOR,
        allow_isolated_markets=True,
        canonicalize_authenticated_bls_principals=True,
    )


def _initialized_state() -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    result = apply_perp_ops(
        config=_tau_perp_config(),
        state=state,
        operations={"5": [_isolated_init_op()]},
        tx_sender_pubkey=OPERATOR,
        block_timestamp=0,
    )
    assert result.ok is True, result.error
    assert result.state is not None
    return result.state


def _state_with_raw_principal() -> DexState:
    state = _initialized_state()
    assert state.perps is not None
    market = state.perps.markets[MARKET_ID]
    assert isinstance(market, PerpMarketState)

    account = PerpAccountState(
        position_base=0,
        entry_price_e8=0,
        collateral_quote=0,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )
    raw_market = replace(market, accounts={RAW: account})

    balances = BalanceTable()
    balances.set(RAW, QUOTE_ASSET, 100)
    lp_balances = LPTable()
    lp_balances.set(RAW, "pool-1", 7)
    lp_balances.set_last_mint_timestamp(RAW, "pool-1", 10)
    lp_balances.set_last_remove_timestamp(RAW, "pool-1", 11)
    lp_balances.set_churn_tier(RAW, "pool-1", 2)
    lp_balances.set_last_churn_update_timestamp(RAW, "pool-1", 12)
    nonces = NonceTable()
    nonces.set_last(RAW, 3)
    return replace(
        state,
        balances=balances,
        lp_balances=lp_balances,
        nonces=nonces,
        perps=replace(state.perps, markets={MARKET_ID: raw_market}),
    )


def test_tau_state_migration_is_atomic_complete_and_idempotent() -> None:
    legacy = _state_with_raw_principal()

    migrated = canonicalize_legacy_tau_state_principals(legacy)

    assert migrated is not legacy
    assert migrated.balances.get(CANONICAL, QUOTE_ASSET) == 100
    assert migrated.balances.get(RAW, QUOTE_ASSET) == 0
    assert migrated.lp_balances.get(CANONICAL, "pool-1") == 7
    assert migrated.lp_balances.get_last_mint_timestamp(CANONICAL, "pool-1") == 10
    metadata = migrated.lp_balances.get_duration_risk_metadata(CANONICAL, "pool-1")
    assert metadata.last_remove_timestamp == 11
    assert metadata.churn_tier == 2
    assert metadata.last_churn_update_timestamp == 12
    assert migrated.nonces.get_last(CANONICAL) == 3
    assert migrated.perps is not None
    market = migrated.perps.markets[MARKET_ID]
    assert isinstance(market, PerpMarketState)
    assert tuple(market.accounts) == (CANONICAL,)
    assert market.global_state is not legacy.perps.markets[MARKET_ID].global_state  # type: ignore[union-attr]

    assert legacy.balances.get(RAW, QUOTE_ASSET) == 100
    assert legacy.balances.get(CANONICAL, QUOTE_ASSET) == 0
    assert canonicalize_legacy_tau_state_principals(migrated) is migrated


def test_tau_state_migration_rejects_alias_collision_without_mutation() -> None:
    legacy = _state_with_raw_principal()
    balances = BalanceTable()
    for (pubkey, asset), amount in legacy.balances.get_all_balances().items():
        balances.set(pubkey, asset, amount)
    balances.set(CANONICAL, QUOTE_ASSET, 5)
    legacy = replace(legacy, balances=balances)

    with pytest.raises(ValueError, match="ambiguous principal spellings"):
        canonicalize_legacy_tau_state_principals(legacy)

    assert legacy.balances.get(RAW, QUOTE_ASSET) == 100
    assert legacy.balances.get(CANONICAL, QUOTE_ASSET) == 5
    assert legacy.nonces.get_last(RAW) == 3


def test_tau_state_migration_rejects_isolated_perps_account_aliases() -> None:
    legacy = _state_with_raw_principal()
    assert legacy.perps is not None
    market = legacy.perps.markets[MARKET_ID]
    assert isinstance(market, PerpMarketState)
    account = market.accounts[RAW]
    aliased_market = replace(
        market,
        accounts={RAW: account, CANONICAL: account},
    )
    aliased = replace(
        legacy,
        perps=replace(legacy.perps, markets={MARKET_ID: aliased_market}),
    )

    with pytest.raises(ValueError, match="isolated perps account has ambiguous"):
        canonicalize_legacy_tau_state_principals(aliased)

    assert tuple(aliased_market.accounts) == (RAW, CANONICAL)
    assert legacy.balances.get(RAW, QUOTE_ASSET) == 100


def test_tau_state_migration_rejects_outstanding_account_bound_evidence() -> None:
    legacy = _state_with_raw_principal()
    assert legacy.perps is not None
    market = legacy.perps.markets[MARKET_ID]
    assert isinstance(market, PerpMarketState)
    guarded_market = replace(
        market,
        pending_funding_closeout_root_hashes=("sha256:" + "44" * 32,),
    )
    guarded = replace(
        legacy,
        perps=replace(legacy.perps, markets={MARKET_ID: guarded_market}),
    )

    with pytest.raises(ValueError, match="account-bound funding closeout evidence"):
        canonicalize_legacy_tau_state_principals(guarded)

    assert tuple(guarded_market.accounts) == (RAW,)


def test_tau_perps_direct_entry_migrates_before_canonical_execution() -> None:
    state = _initialized_state()
    balances = BalanceTable()
    balances.set(RAW, QUOTE_ASSET, 100)
    legacy = replace(state, balances=balances)
    operation = {
        "module": "TauPerp",
        "version": "0.1",
        "market_id": MARKET_ID,
        "action": "deposit_collateral",
        "account_pubkey": RAW,
        "amount": 10,
    }

    result = apply_perp_ops(
        config=_tau_perp_config(),
        state=legacy,
        operations={"5": [operation]},
        tx_sender_pubkey=RAW,
        block_timestamp=0,
    )

    assert result.ok is True, result.error
    assert result.state is not None
    assert result.state.balances.get(CANONICAL, QUOTE_ASSET) == 90
    assert result.state.balances.get(RAW, QUOTE_ASSET) == 0
    assert legacy.balances.get(RAW, QUOTE_ASSET) == 100
    assert result.state.perps is not None
    market = result.state.perps.markets[MARKET_ID]
    assert isinstance(market, PerpMarketState)
    assert market.accounts[CANONICAL].collateral_quote == 10
    assert RAW not in market.accounts


def test_recompute_proof_rejects_noncanonical_signed_identity_profile() -> None:
    from src.core.batch_clearing import compute_settlement
    from src.integration.dex_engine import DexEngineConfig, apply_ops
    from src.integration.operations import (
        canonicalize_authenticated_intent_for_execution,
        create_settlement_operation,
        parse_intents,
    )

    asset0 = "0x" + "55" * 32
    asset1 = "0x" + "66" * 32
    balances = BalanceTable()
    balances.set(CANONICAL, asset0, 1000)
    balances.set(CANONICAL, asset1, 1000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    raw_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "77" * 32,
        "sender_pubkey": RAW,
        "deadline": 100,
        "nonce": 1,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 100,
        "amount1": 100,
    }
    parsed = parse_intents({"2": [raw_intent]})
    execution = [canonicalize_authenticated_intent_for_execution(parsed[0])]
    settlement = compute_settlement(
        intents=execution,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )
    settlement_op = create_settlement_operation(settlement)["3"]
    settlement_op["proof"] = {"scheme": "recompute_batch_v1"}

    result = apply_ops(
        config=DexEngineConfig(
            require_intent_signatures=False,
            canonicalize_authenticated_bls_principals=True,
        ),
        state=state,
        operations={"2": [raw_intent], "3": settlement_op},
        block_timestamp=1,
        tx_sender_pubkey=RAW,
    )

    assert result.ok is False
    assert result.error == (
        "proof-bearing intents must use canonical BLS principal spellings; "
        "recompute proof v1-v4 do not bind an identity execution profile"
    )
