"""Perps Oracle action-id and production-boundary regression tests."""
from __future__ import annotations

import inspect
from pathlib import Path

from src.core.perps import (
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpMarketState,
)
from src.integration.perp_engine import (
    PerpEngineConfig,
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


class TestClearinghouseOracleActionId:

    def test_returns_sha256_hex(self) -> None:
        market = _clearinghouse_market()
        action_id = _perps_clearinghouse_runtime_oracle_action_id(
            _config(),
            market_id="perp:ch2p:test",
            action_kind="settle_epoch",
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
        assert isinstance(action_id, str)
        assert action_id.startswith("sha256:")
        assert len(action_id) == len("sha256:") + 64

    def test_config_is_positional_and_action_facts_are_keyword_only(self) -> None:
        sig = inspect.signature(_perps_clearinghouse_runtime_oracle_action_id)
        params = list(sig.parameters.values())
        assert [param.name for param in params] == [
            "config",
            "market_id",
            "action_kind",
            "market_kind",
            "quote_asset",
            "state",
            "participant_pubkeys",
        ]
        assert params[0].kind is inspect.Parameter.POSITIONAL_OR_KEYWORD
        assert all(param.kind is inspect.Parameter.KEYWORD_ONLY for param in params[1:])

    def test_is_deterministic(self) -> None:
        market = _clearinghouse_market()
        kwargs = dict(
            market_id="perp:ch2p:test",
            action_kind="settle_epoch",
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
        id1 = _perps_clearinghouse_runtime_oracle_action_id(_config(), **kwargs)
        id2 = _perps_clearinghouse_runtime_oracle_action_id(_config(), **kwargs)
        assert id1 == id2

    def test_different_market_id_produces_different_action_id(self) -> None:
        market = _clearinghouse_market()
        base_kwargs = dict(
            action_kind="settle_epoch",
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
        id1 = _perps_clearinghouse_runtime_oracle_action_id(
            _config(), market_id="perp:ch2p:a", **base_kwargs
        )
        id2 = _perps_clearinghouse_runtime_oracle_action_id(
            _config(), market_id="perp:ch2p:b", **base_kwargs
        )
        assert id1 != id2


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

    def test_accepts_dataclass_or_explicit_keyword_fields(self) -> None:
        sig = inspect.signature(_perps_liquidate_account_runtime_oracle_action_id)
        params = list(sig.parameters.values())
        assert [param.name for param in params] == [
            "config",
            "market_id",
            "market",
            "account_pubkey",
            "fraction_bps",
        ]
        market = _isolated_market()
        request = _LiquidateAccountOracleRuntimeRequest(
            config=_config(),
            market_id="perp:iso:test",
            market=market,
            account_pubkey=_ALICE,
            fraction_bps=2500,
        )
        assert _perps_liquidate_account_runtime_oracle_action_id(
            request
        ) == _perps_liquidate_account_runtime_oracle_action_id(
            _config(),
            market_id="perp:iso:test",
            market=market,
            account_pubkey=_ALICE,
            fraction_bps=2500,
        )

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


class TestProductionWalletOracleBridgeBoundary:
    def test_runtime_module_has_no_synthetic_bridge_builder(self) -> None:
        source = (
            Path(__file__).resolve().parents[2] / "src" / "integration" / "perps_wallet_api.py"
        ).read_text(encoding="utf-8")
        assert "def _local_perps_oracle_bridge_fixture(" not in source

    def test_runtime_source_has_no_sample_or_fixture_construction_imports(self) -> None:
        source = (
            Path(__file__).resolve().parents[2] / "src" / "integration" / "perps_wallet_api.py"
        ).read_text(encoding="utf-8")
        for forbidden in (
            "sample_admitted_median3_aggregate",
            "zenodex_oracle_admitted_median3",
            "zenodex_oracle_aggregate_read",
            "_local_perps_oracle_bridge_fixture",
            'rest == ["oracle-bridge-template"]',
        ):
            assert forbidden not in source

    def test_runtime_source_has_no_fixture_faucet_or_recipient_key_loader(self) -> None:
        source = (
            Path(__file__).resolve().parents[2] / "src" / "integration" / "perps_wallet_api.py"
        ).read_text(encoding="utf-8")
        for forbidden in (
            'rest == ["testnet-faucet"]',
            "def _build_testnet_faucet_response(",
            "PERPS_WALLET_TESTNET_FAUCET_",
            "recipient_root_keys_from_fixture_v1",
            "PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_",
            "PERPS_WALLET_ALLOW_LOCAL_SIGNING",
            "build_signed_tau_transaction",
            "sign_perp_op_for_engine",
            "bls_pubkey_hex_from_privkey",
            "local_test_signing",
        ):
            assert forbidden not in source

    def test_live_wallet_ui_exposes_external_signing_data_only(self) -> None:
        root = Path(__file__).resolve().parents[2]
        component = (
            root / "tools" / "dex-ui" / "src" / "components" / "perps" / "PerpLiveWalletSurface.jsx"
        ).read_text(encoding="utf-8")
        api_source = (root / "tools" / "dex-ui" / "src" / "lib" / "api.js").read_text(
            encoding="utf-8"
        )
        for forbidden in (
            "privkey",
            "apiMintPerpsWalletTestnetFaucet",
            "/api/perps/wallet/testnet-faucet",
        ):
            assert forbidden not in component
            assert forbidden not in api_source
        for required in (
            "account_a_pubkey",
            "account_b_pubkey",
            "account_pubkey",
            "operator_pubkey",
            "oracle_pubkey",
            "sig_a",
            "sig_b",
            "oracle_sig",
            "signed_tau_tx_payload",
            "tx_expiration_time",
            "External signing bundle",
        ):
            assert required in component
