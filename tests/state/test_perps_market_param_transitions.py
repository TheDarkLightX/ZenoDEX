from __future__ import annotations

from typing import cast

import pytest

from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perp_v2.math import MAX_COLLATERAL
from src.core.perps import (
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from src.integration.perp_engine import _apply_isolated_market_params
from src.state.perps_market_param_transitions import (
    IsolatedMarketParamsTransitionOkV1,
    IsolatedMarketParamsUpdateV1,
    evaluate_isolated_market_params_v1,
)
from src.state.perps_state_transitions import (
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
)
from src.state.state_snapshot_values import CommittedPerpMarketStateV1
from src.state.state_snapshots import snapshot_perps

_ALICE = "0x" + "11" * 48


def _global(*, settled: bool = True) -> dict[str, int | bool]:
    return {
        "now_epoch": 1,
        "epoch_phase": 2 if settled else 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": settled,
        "clearing_price_epoch": 1 if settled else 0,
        "clearing_price_e8": 100_000_000 if settled else 0,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": True,
        "oracle_last_update_epoch": 1 if settled else 0,
        "index_price_e8": 100_000_000,
        "max_oracle_staleness_epochs": 2,
        "max_oracle_move_bps": 500,
        "initial_margin_bps": 1_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_position_abs": 1_000_000,
        "fee_pool_quote": 0,
        "funding_rate_bps": 90,
        "funding_cap_bps": 100,
        "insurance_balance": 0,
        "initial_insurance": 0,
        "fee_income": 0,
        "claims_paid": 0,
        "min_notional_for_bounty": 100_000_000,
    }


def _account(*, position_base: int = 0) -> PerpAccountState:
    return PerpAccountState(
        position_base=position_base,
        entry_price_e8=100_000_000 if position_base else 0,
        collateral_quote=100_000,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )


def _legacy_market(
    *,
    settled: bool = True,
    position_base: int = 0,
) -> PerpMarketState:
    return PerpMarketState(
        quote_asset="zUSD",
        global_state=_global(settled=settled),
        accounts={_ALICE: _account(position_base=position_base)},
    )


def _exact_market(legacy: PerpMarketState) -> CommittedPerpMarketStateV1:
    committed = snapshot_perps(
        PerpsState(
            version=PERPS_STATE_VERSION_V5,
            markets={"perp:test": legacy},
        )
    )
    assert committed is not None
    market = committed.get_market("perp:test")
    assert type(market) is CommittedPerpMarketStateV1
    return market


def test_parameter_update_matches_mounted_reference_and_clamps_rate() -> None:
    legacy = _legacy_market()
    pre = _exact_market(legacy)
    update = IsolatedMarketParamsUpdateV1(
        (
            ("funding_cap_bps", 50),
            ("initial_margin_bps", 1_200),
        )
    )
    reference = _apply_isolated_market_params(
        legacy,
        params=dict(update.entries),
        min_collectible_liquidation_penalty_quote=0,
    )

    result = evaluate_isolated_market_params_v1(
        pre,
        update,
        min_collectible_penalty_quote=0,
    )

    assert type(result) is IsolatedMarketParamsTransitionOkV1
    assert dict(result.market.global_entries) == reference.global_state
    assert result.market.accounts is pre.accounts
    assert result.market.global_value("funding_rate_bps") == 50
    assert result.global_patch is not None
    assert tuple(write.field for write in result.global_patch.writes) == (
        "funding_cap_bps",
        "funding_rate_bps",
        "initial_margin_bps",
    )


def test_parameter_patch_replays_and_preserves_the_prestate() -> None:
    pre = _exact_market(_legacy_market())
    result = evaluate_isolated_market_params_v1(
        pre,
        IsolatedMarketParamsUpdateV1((("initial_margin_bps", 1_200),)),
        min_collectible_penalty_quote=0,
    )

    assert type(result) is IsolatedMarketParamsTransitionOkV1
    assert result.global_patch is not None
    replayed = dict(pre.global_entries)
    for write in result.global_patch.writes:
        assert replayed[write.field] == write.expected
        replayed[write.field] = write.replacement
    assert replayed == dict(result.market.global_entries)
    assert pre.global_value("initial_margin_bps") == 1_000


@pytest.mark.parametrize(
    ("update", "policy_floor"),
    (
        (IsolatedMarketParamsUpdateV1(()), MAX_COLLATERAL),
        (IsolatedMarketParamsUpdateV1((("initial_margin_bps", 1_000),)), 0),
    ),
)
def test_empty_or_semantic_noop_update_reuses_the_exact_prestate(
    update: IsolatedMarketParamsUpdateV1,
    policy_floor: int,
) -> None:
    pre = _exact_market(_legacy_market())

    result = evaluate_isolated_market_params_v1(
        pre,
        update,
        min_collectible_penalty_quote=policy_floor,
    )

    assert result == IsolatedMarketParamsTransitionOkV1(pre, None)
    assert result.market is pre


def test_open_position_anti_farming_checks_match_mounted_errors() -> None:
    pre = _exact_market(_legacy_market(position_base=1_000))

    penalty_increase = evaluate_isolated_market_params_v1(
        pre,
        IsolatedMarketParamsUpdateV1((("liquidation_penalty_bps", 60),)),
        min_collectible_penalty_quote=0,
    )
    bounty_decrease = evaluate_isolated_market_params_v1(
        pre,
        IsolatedMarketParamsUpdateV1((("min_notional_for_bounty", 99_999_999),)),
        min_collectible_penalty_quote=0,
    )

    assert penalty_increase == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.MARKET_PARAMS,
        ("params",),
        "invalid params: cannot increase liquidation_penalty_bps while positions are open",
    )
    assert bounty_decrease == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.MARKET_PARAMS,
        ("params",),
        "invalid params: cannot decrease min_notional_for_bounty while positions are open",
    )


def test_cross_parameter_policy_and_account_risk_reject_without_candidate() -> None:
    flat = _exact_market(_legacy_market())
    open_market = _exact_market(_legacy_market(position_base=1_000))

    invalid_order = evaluate_isolated_market_params_v1(
        flat,
        IsolatedMarketParamsUpdateV1((("depeg_buffer_bps", 0),)),
        min_collectible_penalty_quote=0,
    )
    policy_floor = evaluate_isolated_market_params_v1(
        flat,
        IsolatedMarketParamsUpdateV1((("min_notional_for_bounty", 200),)),
        min_collectible_penalty_quote=2,
    )
    position_bound = evaluate_isolated_market_params_v1(
        open_market,
        IsolatedMarketParamsUpdateV1((("max_position_abs", 500),)),
        min_collectible_penalty_quote=0,
    )

    assert invalid_order == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.MARKET_PARAMS,
        ("params",),
        "invalid params: require depeg_buffer_bps > 0",
    )
    assert policy_floor == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.MARKET_PARAMS,
        ("params",),
        "invalid params: require min_notional_for_bounty >= ceil(2 * 10000 / liquidation_penalty_bps)",
    )
    assert position_bound == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.MARKET_PARAMS,
        ("params",),
        f"invalid params: account {_ALICE} position exceeds new max_position_abs",
    )
    for rejected in (invalid_order, policy_floor, position_bound):
        assert not hasattr(rejected, "market")


def test_phase_gate_precedes_parameter_and_context_representation_checks() -> None:
    pre = _exact_market(_legacy_market(settled=False))

    result = evaluate_isolated_market_params_v1(
        pre,
        cast(IsolatedMarketParamsUpdateV1, object()),
        min_collectible_penalty_quote=cast(int, True),
    )

    assert result == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.RUNTIME_GUARD,
        ("gate",),
        "MarketParamsMidEpoch",
    )


def test_exact_update_and_policy_context_fail_closed() -> None:
    pre = _exact_market(_legacy_market())

    wrong_update = evaluate_isolated_market_params_v1(
        pre,
        cast(IsolatedMarketParamsUpdateV1, object()),
        min_collectible_penalty_quote=0,
    )
    wrong_context = evaluate_isolated_market_params_v1(
        pre,
        IsolatedMarketParamsUpdateV1(()),
        min_collectible_penalty_quote=cast(int, True),
    )
    excessive_context = evaluate_isolated_market_params_v1(
        pre,
        IsolatedMarketParamsUpdateV1(()),
        min_collectible_penalty_quote=MAX_COLLATERAL + 1,
    )

    assert wrong_update == IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
        ("params",),
    )
    expected_context = IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.WRONG_EXACT_TYPE,
        ("context", "min_collectible_penalty_quote"),
    )
    assert wrong_context == expected_context
    assert excessive_context == expected_context


def test_parameter_value_constructor_is_closed_and_canonical() -> None:
    with pytest.raises(TypeError):
        IsolatedMarketParamsUpdateV1((("initial_margin_bps", cast(int, True)),))
    with pytest.raises(ValueError):
        IsolatedMarketParamsUpdateV1(
            (("maintenance_margin_bps", 500), ("initial_margin_bps", 1_000))
        )
    with pytest.raises(ValueError):
        IsolatedMarketParamsUpdateV1((("unknown", 1),))
    with pytest.raises(ValueError):
        IsolatedMarketParamsUpdateV1((("funding_cap_bps", 0),))
