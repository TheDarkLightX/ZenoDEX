from __future__ import annotations

from dataclasses import replace

import pytest

from src.core import perp_liquidation_tau_source_binding as tau_source_binding
from src.core.dex import DexState
from src.core.perp_epoch import PerpStepResult
from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
from src.integration.perp_engine import (
    _ORACLE_PERPS_INDEX_QUERY_ID,
    _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
    PerpEngineConfig,
    _kernel_initial_global_state,
    _LiquidateAccountOracleRuntimeRequest,
    _perps_liquidate_account_runtime_oracle_action_id,
    apply_perp_ops,
)
from src.state.balances import BalanceTable
from src.state.jmt import compute_jmt_root, encode_jmt_membership_proof, prove_jmt_membership
from src.state.lp import LPTable


def _market_with_open_account(account_pubkey: str) -> PerpMarketState:
    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": 100_000_000,
            "fee_pool_quote": 100,
            "fee_income": 100,
            "initial_insurance": 500,
            "insurance_balance": 600,
            "min_notional_for_bounty": 0,
        }
    )
    account = PerpAccountState(
        position_base=100_000,
        entry_price_e8=100_000_000,
        collateral_quote=20_000,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )
    return PerpMarketState(
        quote_asset="0x" + "55" * 32,
        global_state=global_state,
        accounts={account_pubkey: account},
    )


def _caller_anchored_tau_source_operation() -> tuple[
    DexState,
    PerpEngineConfig,
    dict[str, object],
    str,
]:
    account_pubkey = "11" * 48
    market_id = "perp:partial-liq-caller-root"
    base_market = _market_with_open_account(account_pubkey)
    global_state = dict(base_market.global_state)
    global_state.update(
        {
            "clearing_price_e8": 100_000_000,
            "clearing_price_epoch": 2,
            "clearing_price_seen": True,
            "depeg_buffer_bps": 0,
            "maintenance_margin_bps": 500,
            "max_oracle_move_bps": 100,
            "max_oracle_staleness_epochs": 2,
        }
    )
    account = PerpAccountState(
        position_base=100_000,
        entry_price_e8=100_000_000,
        collateral_quote=0,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )
    market = PerpMarketState(
        quote_asset=base_market.quote_asset,
        global_state=global_state,
        accounts={account_pubkey: account},
    )
    config = PerpEngineConfig(
        operator_pubkey="aa" * 48,
        allow_isolated_markets=True,
    )
    fraction_bps = 2_500
    request_id = _perps_liquidate_account_runtime_oracle_action_id(
        _LiquidateAccountOracleRuntimeRequest(
            config=config,
            market_id=market_id,
            market=market,
            account_pubkey=account_pubkey,
            fraction_bps=fraction_bps,
        )
    )
    facts = tau_source_binding.PerpLiquidationTauSourceFacts(
        request_id=request_id,
        market_id=market_id,
        account_id=account_pubkey,
        action=tau_source_binding.PARTIAL_LIQUIDATE_ACTION,
        fraction_bps=fraction_bps,
        now_epoch=int(global_state["now_epoch"]),
        position_base=account.position_base,
        collateral_quote=account.collateral_quote,
        index_price_e8=int(global_state["index_price_e8"]),
        maintenance_margin_bps=int(global_state["maintenance_margin_bps"]),
        depeg_buffer_bps=int(global_state["depeg_buffer_bps"]),
        oracle_seen=bool(global_state["oracle_seen"]),
        oracle_last_update_epoch=int(global_state["oracle_last_update_epoch"]),
        max_oracle_staleness_epochs=int(global_state["max_oracle_staleness_epochs"]),
        clearing_price_e8=int(global_state["clearing_price_e8"]),
        max_oracle_move_bps=int(global_state["max_oracle_move_bps"]),
        breaker_active=False,
        proof_result_ok=True,
        proof_receipt_hash="sha256:" + "33" * 32,
    )
    membership_key = tau_source_binding.perp_liquidation_tau_source_membership_key(facts)
    membership_value = tau_source_binding.perp_liquidation_tau_source_membership_value(facts)
    entries = [(membership_key, membership_value)]
    source_root = compute_jmt_root(entries)
    source_root_hash = "sha256:" + source_root.removeprefix("0x")
    membership = tau_source_binding.build_perp_liquidation_tau_source_membership_proof(
        facts,
        jmt_membership_proof_payload=encode_jmt_membership_proof(
            prove_jmt_membership(entries, membership_key)
        ),
    )
    root_binding = tau_source_binding.build_perp_liquidation_tau_source_state_root_binding(
        facts,
        source_state_root_hash=source_root_hash,
        state_root_kind=tau_source_binding.JMT_SOURCE_STATE_ROOT_KIND,
        source_membership_proof=membership,
    )
    facts_hash = tau_source_binding.perp_liquidation_tau_source_facts_hash(facts)
    binding = tau_source_binding.PerpLiquidationTauSourceBinding(
        facts=facts,
        expected_source_facts_hash=facts_hash,
        proof_source_facts_hash=facts_hash,
        source_state_root_binding=root_binding,
    )
    operation = {
        "module": "TauPerp",
        "version": "0.1",
        "market_id": market_id,
        "action": "partial_liquidate",
        "account_pubkey": account_pubkey,
        "fraction_bps": fraction_bps,
        "tau_source_binding": tau_source_binding.perp_liquidation_tau_source_binding_payload(
            binding
        ),
    }
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={market_id: market}),
    )
    return state, config, operation, source_root_hash


def _install_partial_liquidation_step(monkeypatch) -> None:
    from src.integration import perp_engine as module

    def _fake_default_apply(*, state, action, params):
        assert action == "partial_liquidate"
        assert params == {"fraction_bps": 2_500, "auth_ok": True}
        post = dict(state)
        post["position_base"] = 75_000
        post["liquidated_this_step"] = True
        return PerpStepResult(
            ok=True,
            state=post,
            effects={"event": "PartialLiquidationApplied", "liquidated": True},
        )

    monkeypatch.setattr(module, "perp_epoch_isolated_default_apply", _fake_default_apply)


def test_partial_liquidate_rejects_caller_anchored_membership_root(monkeypatch) -> None:
    # Arrange
    state, config, operation, _source_root_hash = _caller_anchored_tau_source_operation()
    _install_partial_liquidation_step(monkeypatch)

    # Act
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={"5": [operation]},
        tx_sender_pubkey=str(operation["account_pubkey"]),
        block_timestamp=0,
    )

    # Assert
    assert result.ok is False
    assert result.error == "tau_source_binding source state root anchor expected but not configured"
    assert result.state is None
    assert result.effects is None
    assert state.perps is not None
    market = state.perps.markets[str(operation["market_id"])]
    assert isinstance(market, PerpMarketState)
    assert market.accounts[str(operation["account_pubkey"])].position_base == 100_000


def test_partial_liquidate_accepts_membership_root_bound_by_configuration(monkeypatch) -> None:
    # Arrange
    state, base_config, operation, source_root_hash = _caller_anchored_tau_source_operation()
    config = replace(
        base_config,
        isolated_partial_liquidate_tau_source_state_root_hash=source_root_hash,
        isolated_partial_liquidate_tau_source_state_root_kind=(
            tau_source_binding.JMT_SOURCE_STATE_ROOT_KIND
        ),
    )
    _install_partial_liquidation_step(monkeypatch)

    # Act
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={"5": [operation]},
        tx_sender_pubkey=str(operation["account_pubkey"]),
        block_timestamp=0,
    )

    # Assert
    assert result.ok is True, result.error
    assert result.state is not None
    assert result.state.perps is not None
    market = result.state.perps.markets[str(operation["market_id"])]
    assert isinstance(market, PerpMarketState)
    assert market.accounts[str(operation["account_pubkey"])].position_base == 75_000


def test_partial_liquidate_rejects_configured_root_mismatch_without_effects(monkeypatch) -> None:
    # Arrange
    state, base_config, operation, _source_root_hash = _caller_anchored_tau_source_operation()
    config = replace(
        base_config,
        isolated_partial_liquidate_tau_source_state_root_hash="sha256:" + "00" * 32,
        isolated_partial_liquidate_tau_source_state_root_kind=(
            tau_source_binding.JMT_SOURCE_STATE_ROOT_KIND
        ),
    )
    _install_partial_liquidation_step(monkeypatch)

    # Act
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={"5": [operation]},
        tx_sender_pubkey=str(operation["account_pubkey"]),
        block_timestamp=0,
    )

    # Assert
    assert result.ok is False
    assert result.error == "tau_source_binding rejects: source_state_root_binding_root_mismatch"
    assert result.state is None
    assert result.effects is None


def test_perp_liquidation_facts_tree_has_a_distinct_root_kind() -> None:
    assert (
        tau_source_binding.JMT_SOURCE_STATE_ROOT_KIND
        == "perp_liquidation_source_facts_jmt_v1"
    )


def test_apply_perp_ops_supports_partial_liquidate_on_default_adapter(monkeypatch) -> None:
    from src.integration import perp_engine as module

    account_pubkey = "11" * 48
    market_id = "perp:partial-liq"
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={market_id: _market_with_open_account(account_pubkey)},
        ),
    )

    def _fake_default_apply(*, state, action, params):
        assert action == "partial_liquidate"
        assert params == {"fraction_bps": 2_500, "auth_ok": True}
        post = dict(state)
        post["position_base"] = 75_000
        post["entry_price_e8"] = int(state["index_price_e8"])
        post["liquidated_this_step"] = True
        post["fee_pool_quote"] = int(state["fee_pool_quote"]) + 25
        post["fee_income"] = int(state["fee_income"]) + 25
        post["insurance_balance"] = int(state["insurance_balance"]) + 25
        return PerpStepResult(
            ok=True,
            state=post,
            effects={"event": "PartialLiquidationApplied", "liquidated": True},
        )

    monkeypatch.setattr(module, "perp_epoch_isolated_default_apply", _fake_default_apply)

    res = apply_perp_ops(
        config=PerpEngineConfig(operator_pubkey="aa" * 48, allow_isolated_markets=True),
        state=state,
        operations={
            "5": [
                {
                    "module": "TauPerp",
                    "version": "0.1",
                    "market_id": market_id,
                    "action": "partial_liquidate",
                    "account_pubkey": account_pubkey,
                    "fraction_bps": 2_500,
                }
            ]
        },
        tx_sender_pubkey=account_pubkey,
        block_timestamp=0,
    )

    assert res.ok is True, res.error
    assert res.state is not None
    assert res.effects is not None
    assert res.state.perps is not None
    market = res.state.perps.markets[market_id]
    assert isinstance(market, PerpMarketState)
    assert market.accounts[account_pubkey].position_base == 75_000
    assert market.accounts[account_pubkey].liquidated_this_step is True
    assert int(market.global_state["fee_pool_quote"]) == 125
    assert int(market.global_state["insurance_balance"]) == 625
    assert res.effects[0]["effects"]["event"] == "PartialLiquidationApplied"


def test_apply_perp_ops_partial_liquidate_requires_oracle_adapter_when_configured(monkeypatch) -> None:
    from src.integration import perp_engine as module

    account_pubkey = "11" * 48
    market_id = "perp:partial-liq-oracle-required"
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={market_id: _market_with_open_account(account_pubkey)},
        ),
    )

    def _unexpected_default_apply(*, state, action, params):
        raise AssertionError("default adapter should not run without oracle adapter bridge")

    monkeypatch.setattr(module, "perp_epoch_isolated_default_apply", _unexpected_default_apply)

    res = apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey="aa" * 48,
            allow_isolated_markets=True,
            require_oracle_adapter_for_isolated_partial_liquidate=True,
        ),
        state=state,
        operations={
            "5": [
                {
                    "module": "TauPerp",
                    "version": "0.1",
                    "market_id": market_id,
                    "action": "partial_liquidate",
                    "account_pubkey": account_pubkey,
                    "fraction_bps": 2_500,
                }
            ]
        },
        tx_sender_pubkey=account_pubkey,
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == "liquidate_account requires oracle_adapter_bridge"


def test_apply_perp_ops_partial_liquidate_accepts_matching_oracle_adapter(monkeypatch) -> None:
    from src.integration import perp_engine as module

    account_pubkey = "11" * 48
    market_id = "perp:partial-liq-oracle-ok"
    market = _market_with_open_account(account_pubkey)
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={market_id: market}),
    )
    base_config = PerpEngineConfig(
        operator_pubkey="aa" * 48,
        allow_isolated_markets=True,
        require_oracle_adapter_for_isolated_partial_liquidate=True,
    )
    expected_action_id = _perps_liquidate_account_runtime_oracle_action_id(
        _LiquidateAccountOracleRuntimeRequest(
            config=base_config,
            market_id=market_id,
            market=market,
            account_pubkey=account_pubkey,
            fraction_bps=2_500,
        )
    )

    def _fake_verifier(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "liquidate_account",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
            "action_id": expected_action_id,
            "value_e8": int(market.global_state["index_price_e8"]),
            "action_epoch": int(market.global_state["now_epoch"]),
            "errors": [],
        }

    def _fake_default_apply(*, state, action, params):
        assert action == "partial_liquidate"
        assert params == {"fraction_bps": 2_500, "auth_ok": True}
        post = dict(state)
        post["position_base"] = 75_000
        post["entry_price_e8"] = int(state["index_price_e8"])
        post["liquidated_this_step"] = True
        return PerpStepResult(
            ok=True,
            state=post,
            effects={"event": "PartialLiquidationApplied", "liquidated": True},
        )

    monkeypatch.setattr(module, "perp_epoch_isolated_default_apply", _fake_default_apply)

    res = apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey="aa" * 48,
            allow_isolated_markets=True,
            require_oracle_adapter_for_isolated_partial_liquidate=True,
            oracle_adapter_bridge_verifier=_fake_verifier,
        ),
        state=state,
        operations={
            "5": [
                {
                    "module": "TauPerp",
                    "version": "0.1",
                    "market_id": market_id,
                    "action": "partial_liquidate",
                    "account_pubkey": account_pubkey,
                    "fraction_bps": 2_500,
                    "oracle_adapter_bridge": {"schema": "test.bridge"},
                }
            ]
        },
        tx_sender_pubkey=account_pubkey,
        block_timestamp=0,
    )

    assert res.ok is True, res.error
    assert res.state is not None


@pytest.mark.parametrize(
    "value_delta,epoch_delta,expected_error",
    [
        (1, 0, "oracle_adapter_bridge value_e8 mismatch"),
        (0, 1, "oracle_adapter_bridge action_epoch mismatch"),
    ],
)
def test_apply_perp_ops_partial_liquidate_rejects_oracle_bridge_semantic_drift(
    monkeypatch,
    value_delta: int,
    epoch_delta: int,
    expected_error: str,
) -> None:
    from src.integration import perp_engine as module

    # Arrange: the adapter accepts the exact liquidation action identity while
    # reporting a neighboring Oracle price or epoch.
    account_pubkey = "11" * 48
    market_id = "perp:partial-liq-oracle-semantic-drift"
    market = _market_with_open_account(account_pubkey)
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={market_id: market}),
    )
    base_config = PerpEngineConfig(
        operator_pubkey="aa" * 48,
        allow_isolated_markets=True,
    )
    expected_action_id = _perps_liquidate_account_runtime_oracle_action_id(
        _LiquidateAccountOracleRuntimeRequest(
            config=base_config,
            market_id=market_id,
            market=market,
            account_pubkey=account_pubkey,
            fraction_bps=2_500,
        )
    )

    def accepted_neighboring_bridge(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "liquidate_account",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
            "action_id": expected_action_id,
            "value_e8": int(market.global_state["index_price_e8"]) + value_delta,
            "action_epoch": int(market.global_state["now_epoch"]) + epoch_delta,
        }

    def unexpected_transition(*, state, action, params):
        raise AssertionError("partial liquidation transition ran after Oracle drift")

    monkeypatch.setattr(module, "perp_epoch_isolated_default_apply", unexpected_transition)

    # Act.
    result = apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey="aa" * 48,
            allow_isolated_markets=True,
            require_oracle_adapter_for_isolated_partial_liquidate=True,
            oracle_adapter_bridge_verifier=accepted_neighboring_bridge,
        ),
        state=state,
        operations={
            "5": [
                {
                    "module": "TauPerp",
                    "version": "0.1",
                    "market_id": market_id,
                    "action": "partial_liquidate",
                    "account_pubkey": account_pubkey,
                    "fraction_bps": 2_500,
                    "oracle_adapter_bridge": {"schema": "test.bridge"},
                }
            ]
        },
        tx_sender_pubkey=account_pubkey,
        block_timestamp=0,
    )

    # Assert.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == expected_error


def test_apply_perp_ops_partial_liquidate_rejects_wrong_oracle_adapter_action_id() -> None:
    account_pubkey = "11" * 48
    market_id = "perp:partial-liq-oracle-wrong-action"
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={market_id: _market_with_open_account(account_pubkey)},
        ),
    )

    def _fake_verifier(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "liquidate_account",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
            "action_id": "sha256:" + "00" * 32,
            "errors": [],
        }

    res = apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey="aa" * 48,
            allow_isolated_markets=True,
            require_oracle_adapter_for_isolated_partial_liquidate=True,
            oracle_adapter_bridge_verifier=_fake_verifier,
        ),
        state=state,
        operations={
            "5": [
                {
                    "module": "TauPerp",
                    "version": "0.1",
                    "market_id": market_id,
                    "action": "partial_liquidate",
                    "account_pubkey": account_pubkey,
                    "fraction_bps": 2_500,
                    "oracle_adapter_bridge": {"schema": "test.bridge"},
                }
            ]
        },
        tx_sender_pubkey=account_pubkey,
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == "oracle_adapter_bridge action_id mismatch"


def test_apply_perp_ops_partial_liquidate_requires_sender_binding(monkeypatch) -> None:
    from src.integration import perp_engine as module

    account_pubkey = "11" * 48
    market_id = "perp:partial-liq-binding"
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={market_id: _market_with_open_account(account_pubkey)},
        ),
    )

    def _unexpected_default_apply(*, state, action, params):
        raise AssertionError("default adapter should not run when sender binding fails")

    monkeypatch.setattr(module, "perp_epoch_isolated_default_apply", _unexpected_default_apply)

    res = apply_perp_ops(
        config=PerpEngineConfig(operator_pubkey="aa" * 48, allow_isolated_markets=True),
        state=state,
        operations={
            "5": [
                {
                    "module": "TauPerp",
                    "version": "0.1",
                    "market_id": market_id,
                    "action": "partial_liquidate",
                    "account_pubkey": account_pubkey,
                    "fraction_bps": 2_500,
                }
            ]
        },
        tx_sender_pubkey="22" * 48,
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == "account_pubkey must match tx sender"
