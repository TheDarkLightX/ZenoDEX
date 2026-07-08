from __future__ import annotations

from src.core.dex import DexState
from src.core.perp_epoch import PerpStepResult
from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
from src.integration.perp_engine import (
    PerpEngineConfig,
    _ORACLE_PERPS_INDEX_QUERY_ID,
    _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
    _kernel_initial_global_state,
    _perps_liquidate_account_runtime_oracle_action_id,
    apply_perp_ops,
)
from src.runtime.authority import (
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _perp_stateful_policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"perp_stateful": mode},
        promoted_surfaces=frozenset(),
    )


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
            "19": [
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
            "19": [
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
        base_config,
        market_id=market_id,
        market=market,
        account_pubkey=account_pubkey,
        fraction_bps=2_500,
    )

    def _fake_verifier(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "liquidate_account",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
            "action_id": expected_action_id,
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
            "19": [
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
            "19": [
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
            "19": [
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


def test_rust_shadow_unauthorized_partial_liquidate_does_not_run_oracle_bridge_verifier() -> None:
    account_pubkey = "11" * 48
    unauthorized_sender = "22" * 48
    market_id = "perp:shadow-partial-liq-preauth"
    market = _market_with_open_account(account_pubkey)
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(version=PERPS_STATE_VERSION, markets={market_id: market}),
    )
    expected_action_id = _perps_liquidate_account_runtime_oracle_action_id(
        PerpEngineConfig(operator_pubkey="aa" * 48, allow_isolated_markets=True),
        market_id=market_id,
        market=market,
        account_pubkey=account_pubkey,
        fraction_bps=2_500,
    )
    verifier_calls = 0

    def verifier(_bridge: object) -> dict[str, object]:
        nonlocal verifier_calls
        verifier_calls += 1
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "liquidate_account",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
            "action_id": expected_action_id,
            "errors": [],
        }

    set_active_authority_policy(_perp_stateful_policy(AuthorityMode.RUST_SHADOW))
    try:
        res = apply_perp_ops(
            config=PerpEngineConfig(
                operator_pubkey="aa" * 48,
                allow_isolated_markets=True,
                oracle_adapter_bridge_verifier=verifier,
            ),
            state=state,
            operations={
                "19": [
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
            tx_sender_pubkey=unauthorized_sender,
            block_timestamp=0,
        )
    finally:
        reset_active_authority_policy()

    assert res.ok is False
    assert res.error == "account_pubkey must match tx sender"
    assert verifier_calls == 0
