"""Tests for the perps oracle bridge dataclass call signature fix.

Verifies that _perps_clearinghouse_runtime_oracle_action_id and
_perps_liquidate_account_runtime_oracle_action_id accept their respective
frozen dataclass request types (not kwargs), and that the
_local_perps_oracle_bridge_fixture function in perps_wallet_api.py
constructs those dataclasses correctly.
"""
from __future__ import annotations

import inspect

from src.core.perps import (
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpMarketState,
)
from src.integration.perp_engine import (
    PerpEngineConfig,
    _ClearinghouseOracleRuntimeRequest,
    _LiquidateAccountOracleRuntimeRequest,
    _perps_clearinghouse_runtime_oracle_action_id,
    _perps_liquidate_account_runtime_oracle_action_id,
)

_QUOTE_ASSET = "0x" + "aa" * 32
_OPERATOR = "00" * 48
_ALICE = "11" * 48
_BOB = "22" * 48


def _config() -> PerpEngineConfig:
    return PerpEngineConfig(operator_pubkey=_OPERATOR)


def _clearinghouse_market() -> PerpClearinghouse2pMarketState:
    return PerpClearinghouse2pMarketState(
        quote_asset=_QUOTE_ASSET,
        account_a_pubkey=_ALICE,
        account_b_pubkey=_BOB,
        state={
            "now_epoch": 5,
            "breaker_active": False,
            "breaker_last_trigger_epoch": 0,
            "clearing_price_seen": True,
            "clearing_price_epoch": 4,
            "clearing_price_e8": 100_000_000,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 100_000_000,
            "max_oracle_staleness_epochs": 2,
            "max_oracle_move_bps": 5000,
            "initial_margin_bps": 5000,
            "maintenance_margin_bps": 2500,
            "liquidation_penalty_bps": 100,
            "max_position_abs": 1_000_000,
            "fee_pool_e8": 0,
            "liquidated_this_step": False,
            "net_deposited_e8": 2_000_000_000,
            "position_base_a": 1,
            "entry_price_e8_a": 100_000_000,
            "collateral_e8_a": 1_000_000_000,
            "position_base_b": -1,
            "entry_price_e8_b": 100_000_000,
            "collateral_e8_b": 1_000_000_000,
        },
    )


def _isolated_market() -> PerpMarketState:
    return PerpMarketState(
        quote_asset=_QUOTE_ASSET,
        global_state={
            "now_epoch": 5,
            "epoch_phase": 0,
            "breaker_active": False,
            "breaker_last_trigger_epoch": 0,
            "clearing_price_seen": True,
            "clearing_price_epoch": 4,
            "clearing_price_e8": 100_000_000,
            "mark_price_source_kind": 1,
            "oracle_seen": True,
            "oracle_last_update_epoch": 4,
            "index_price_e8": 100_000_000,
            "max_oracle_staleness_epochs": 2,
            "max_oracle_move_bps": 2000,
            "initial_margin_bps": 5000,
            "maintenance_margin_bps": 2500,
            "depeg_buffer_bps": 0,
            "liquidation_penalty_bps": 100,
            "max_position_abs": 1_000_000,
            "fee_pool_quote": 0,
            "funding_rate_bps": 0,
            "funding_cap_bps": 1000,
            "insurance_balance": 0,
            "initial_insurance": 0,
            "fee_income": 0,
            "claims_paid": 0,
            "min_notional_for_bounty": 0,
        },
        accounts={
            _ALICE: PerpAccountState(
                position_base=1,
                entry_price_e8=100_000_000,
                collateral_quote=1_000_000_000,
                funding_paid_cumulative=0,
                funding_last_applied_epoch=0,
                liquidated_this_step=False,
            ),
        },
    )


class TestClearinghouseOracleActionIdDataclass:
    """_perps_clearinghouse_runtime_oracle_action_id must accept a
    _ClearinghouseOracleRuntimeRequest dataclass, not kwargs.
    """

    def test_accepts_dataclass_and_returns_sha256_hex(self) -> None:
        market = _clearinghouse_market()
        request = _ClearinghouseOracleRuntimeRequest(
            config=_config(),
            market_id="perp:ch2p:test",
            action_kind="settle_epoch",
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
        action_id = _perps_clearinghouse_runtime_oracle_action_id(request)
        assert isinstance(action_id, str)
        assert action_id.startswith("sha256:")
        assert len(action_id) == len("sha256:") + 64

    def test_rejects_kwargs_call_signature(self) -> None:
        """The function must not accept positional config + keyword args."""
        sig = inspect.signature(_perps_clearinghouse_runtime_oracle_action_id)
        params = list(sig.parameters.values())
        assert len(params) == 1
        assert params[0].name == "request"

    def test_is_deterministic(self) -> None:
        market = _clearinghouse_market()
        request = _ClearinghouseOracleRuntimeRequest(
            config=_config(),
            market_id="perp:ch2p:test",
            action_kind="settle_epoch",
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
        id1 = _perps_clearinghouse_runtime_oracle_action_id(request)
        id2 = _perps_clearinghouse_runtime_oracle_action_id(request)
        assert id1 == id2

    def test_different_market_id_produces_different_action_id(self) -> None:
        market = _clearinghouse_market()
        base_kwargs = dict(
            config=_config(),
            action_kind="settle_epoch",
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
        id1 = _perps_clearinghouse_runtime_oracle_action_id(
            _ClearinghouseOracleRuntimeRequest(market_id="perp:ch2p:a", **base_kwargs),
        )
        id2 = _perps_clearinghouse_runtime_oracle_action_id(
            _ClearinghouseOracleRuntimeRequest(market_id="perp:ch2p:b", **base_kwargs),
        )
        assert id1 != id2

    def test_constructor_state_alias_cannot_change_action_id(self) -> None:
        market = _clearinghouse_market()
        caller_state = dict(market.state)
        request = _ClearinghouseOracleRuntimeRequest(
            config=_config(),
            market_id="perp:ch2p:test",
            action_kind="settle_epoch",
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=caller_state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
        action_id = _perps_clearinghouse_runtime_oracle_action_id(request)

        caller_state["index_price_e8"] = 1

        assert _perps_clearinghouse_runtime_oracle_action_id(request) == action_id
        assert request.state["index_price_e8"] == 100_000_000


class TestLiquidateAccountOracleActionIdDataclass:
    """_perps_liquidate_account_runtime_oracle_action_id must accept a
    _LiquidateAccountOracleRuntimeRequest dataclass, not kwargs.
    """

    def test_accepts_dataclass_and_returns_sha256_hex(self) -> None:
        market = _isolated_market()
        request = _LiquidateAccountOracleRuntimeRequest(
            config=_config(),
            market_id="perp:iso:test",
            market=market,
            account_pubkey=_ALICE,
            fraction_bps=2500,
        )
        action_id = _perps_liquidate_account_runtime_oracle_action_id(request)
        assert isinstance(action_id, str)
        assert action_id.startswith("sha256:")
        assert len(action_id) == len("sha256:") + 64

    def test_rejects_kwargs_call_signature(self) -> None:
        sig = inspect.signature(_perps_liquidate_account_runtime_oracle_action_id)
        params = list(sig.parameters.values())
        assert len(params) == 1
        assert params[0].name == "request"

    def test_different_fraction_produces_different_action_id(self) -> None:
        market = _isolated_market()
        base_kwargs = dict(
            config=_config(),
            market_id="perp:iso:test",
            market=market,
            account_pubkey=_ALICE,
        )
        id1 = _perps_liquidate_account_runtime_oracle_action_id(
            _LiquidateAccountOracleRuntimeRequest(fraction_bps=1000, **base_kwargs),
        )
        id2 = _perps_liquidate_account_runtime_oracle_action_id(
            _LiquidateAccountOracleRuntimeRequest(fraction_bps=2500, **base_kwargs),
        )
        assert id1 != id2


class TestLocalPerpsOracleBridgeFixtureCallSignature:
    """Verify that _local_perps_oracle_bridge_fixture in perps_wallet_api
    imports and constructs the dataclass types correctly (no kwargs leak).
    """

    def test_module_imports_dataclass_types(self) -> None:
        from src.integration import perps_wallet_api
        source = inspect.getsource(perps_wallet_api._local_perps_oracle_bridge_fixture)
        assert "_ClearinghouseOracleRuntimeRequest" in source
        assert "_LiquidateAccountOracleRuntimeRequest" in source
        assert "_perps_clearinghouse_runtime_oracle_action_id(" in source
        assert "_perps_liquidate_account_runtime_oracle_action_id(" in source

    def test_no_kwargs_call_pattern_for_clearinghouse(self) -> None:
        from src.integration import perps_wallet_api
        source = inspect.getsource(perps_wallet_api._local_perps_oracle_bridge_fixture)
        # The old broken pattern was: _perps_clearinghouse_runtime_oracle_action_id(
        #     config, market_id=..., ...
        # The fixed pattern wraps args in _ClearinghouseOracleRuntimeRequest(...).
        # Verify the dataclass constructor call is present.
        assert "_ClearinghouseOracleRuntimeRequest(" in source
        assert "config=config" in source

    def test_no_kwargs_call_pattern_for_liquidate(self) -> None:
        from src.integration import perps_wallet_api
        source = inspect.getsource(perps_wallet_api._local_perps_oracle_bridge_fixture)
        assert "_LiquidateAccountOracleRuntimeRequest(" in source
        assert "fraction_bps=fraction_bps" in source
