"""Fail-closed regressions for the isolated-perps functional cores.

These tests encode the product behavior required by a trader and settlement
operator: malformed committed state is never repaired implicitly, a published
price must settle before epoch advancement, and settlement never consumes an
unusable oracle snapshot.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Callable

import pytest

from src.core.domain_limits import PERP_PRICE_E8_MAX
from src.core.perp_v2 import (
    Action,
    ActionParams,
    EpochPhase,
    PerpState,
    StepResult,
    initial_state,
)
from src.core.perp_v2.engine import step as step_v2
from src.core.perp_v2.math import MAX_COLLATERAL
from src.core.perp_v2.state import state_from_dict, state_to_dict
from src.core.perp_v4.engine import step as step_v4

Engine = Callable[[PerpState, ActionParams], StepResult]
_ENGINES: tuple[Engine, ...] = (step_v2, step_v4)


def _published_state(**changes: object) -> PerpState:
    state = replace(
        initial_state(),
        now_epoch=5,
        epoch_phase=EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=5,
        clearing_price_e8=100_000_000,
        oracle_seen=True,
        oracle_last_update_epoch=4,
        index_price_e8=100_000_000,
        max_oracle_staleness_epochs=2,
    )
    return replace(state, **changes)


@pytest.mark.parametrize("engine", _ENGINES)
def test_invalid_prestate_cannot_be_repaired_by_clear_breaker(engine: Engine) -> None:
    malformed = replace(
        initial_state(),
        breaker_active=True,
        breaker_last_trigger_epoch=1,
        now_epoch=0,
    )

    result = engine(
        malformed,
        ActionParams(action=Action.CLEAR_BREAKER, auth_ok=True),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection is not None
    assert result.rejection.startswith("pre_invariant:")
    assert "inv_breaker_not_from_future" in result.rejection
    assert malformed.breaker_active is True
    assert malformed.breaker_last_trigger_epoch == 1


@pytest.mark.parametrize("engine", _ENGINES)
def test_invalid_prestate_precedes_malformed_command_domain(engine: Engine) -> None:
    malformed = replace(
        initial_state(),
        breaker_active=True,
        breaker_last_trigger_epoch=1,
        now_epoch=0,
    )

    result = engine(
        malformed,
        ActionParams(action=Action.CLEAR_BREAKER, auth_ok=1),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection is not None
    assert result.rejection.startswith("pre_invariant:")
    assert "inv_breaker_not_from_future" in result.rejection


@pytest.mark.parametrize("engine", _ENGINES)
def test_partial_liquidation_only_exempts_maintenance_violation(
    engine: Engine,
) -> None:
    malformed = replace(
        initial_state(),
        now_epoch=1,
        breaker_active=True,
        breaker_last_trigger_epoch=2,
        oracle_seen=True,
        oracle_last_update_epoch=1,
        index_price_e8=100_000_000,
        position_base=100,
        entry_price_e8=100_000_000,
    )

    result = engine(
        malformed,
        ActionParams(
            action=Action.PARTIAL_LIQUIDATE,
            fraction_bps=10_000,
            auth_ok=True,
        ),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection == "pre_invariant:inv_breaker_not_from_future"


@pytest.mark.parametrize("engine", _ENGINES)
def test_publish_authority_rejects_bool_integer_alias(engine: Engine) -> None:
    state = replace(
        initial_state(),
        now_epoch=1,
        clearing_price_epoch=0,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        index_price_e8=100_000_000,
    )

    result = engine(
        state,
        ActionParams(
            action=Action.PUBLISH_CLEARING_PRICE,
            price_e8=100_000_000,
            auth_ok=1,
        ),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection == "param_domain:auth_ok"


@pytest.mark.parametrize("engine", _ENGINES)
@pytest.mark.parametrize(
    ("changes", "expected_violation"),
    (
        ({"now_epoch": -1}, "domain_now_epoch"),
        ({"now_epoch": 1_000_001}, "domain_now_epoch"),
        ({"now_epoch": True}, "domain_now_epoch"),
        ({"max_oracle_staleness_epochs": 0}, "domain_max_oracle_staleness_epochs"),
        ({"index_price_e8": PERP_PRICE_E8_MAX + 1}, "domain_index_price_e8"),
        ({"funding_cap_bps": 0}, "domain_funding_cap_bps"),
        ({"position_base": 1_000_001}, "domain_position_base"),
    ),
)
def test_state_domain_bva_rejects_before_dispatch(
    engine: Engine,
    changes: dict[str, object],
    expected_violation: str,
) -> None:
    malformed = replace(initial_state(), **changes)

    result = engine(
        malformed,
        ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection is not None
    assert result.rejection.startswith("pre_invariant:")
    assert expected_violation in result.rejection


@pytest.mark.parametrize("engine", _ENGINES)
def test_exact_committed_state_type_rejects_behavior_changing_subclass(
    engine: Engine,
) -> None:
    class DerivedPerpState(PerpState):
        pass

    result = engine(
        DerivedPerpState(),
        ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection == "pre_invariant:domain_state_type"


@pytest.mark.parametrize("engine", _ENGINES)
def test_exact_command_type_rejects_behavior_changing_subclass(engine: Engine) -> None:
    class DerivedActionParams(ActionParams):
        pass

    result = engine(
        initial_state(),
        DerivedActionParams(action=Action.ADVANCE_EPOCH, delta=1),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection == "param_shape:action_params"


@pytest.mark.parametrize("engine", _ENGINES)
def test_published_price_must_settle_before_epoch_advance(engine: Engine) -> None:
    prestate = _published_state()

    result = engine(
        prestate,
        ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
    )

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection == "guard"
    assert prestate.epoch_phase is EpochPhase.PRICE_PUBLISHED
    assert prestate.now_epoch == 5


def test_v2_publication_cannot_create_unsettleable_price_published_state() -> None:
    prestate = replace(
        initial_state(),
        now_epoch=1,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        index_price_e8=19_425_419,
        position_base=7,
        entry_price_e8=19_425_419,
        collateral_quote=0,
        initial_margin_bps=7_500,
        maintenance_margin_bps=7_500,
        depeg_buffer_bps=0,
        max_oracle_move_bps=7_500,
    )

    published = step_v2(
        prestate,
        ActionParams(
            action=Action.PUBLISH_CLEARING_PRICE,
            price_e8=1,
            auth_ok=True,
        ),
    )

    assert published.accepted is False
    assert published.state is None
    assert published.effect is None
    assert published.rejection == "guard"


def test_v2_funding_cannot_destroy_published_settlement_path() -> None:
    prestate = replace(
        initial_state(),
        now_epoch=1,
        epoch_phase=EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=1,
        clearing_price_e8=1,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        index_price_e8=102,
        max_oracle_staleness_epochs=1,
        max_oracle_move_bps=9_902,
        initial_margin_bps=9_903,
        maintenance_margin_bps=9_902,
        depeg_buffer_bps=0,
        funding_cap_bps=10_000,
        position_base=990_100,
        entry_price_e8=102,
        collateral_quote=1,
    )

    settle = step_v2(prestate, ActionParams(action=Action.SETTLE_EPOCH))
    funding = step_v2(
        prestate,
        ActionParams(
            action=Action.APPLY_FUNDING,
            new_rate_bps=10_000,
            auth_ok=True,
        ),
    )

    assert settle.accepted is True
    assert funding.accepted is False
    assert funding.state is None
    assert funding.effect is None
    assert funding.rejection == "guard"


def test_v4_funding_cannot_create_liquidation_accounting_overflow() -> None:
    prestate = replace(
        initial_state(),
        now_epoch=1,
        epoch_phase=EpochPhase.PRICE_PUBLISHED,
        clearing_price_seen=True,
        clearing_price_epoch=1,
        clearing_price_e8=101_000_000,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        index_price_e8=100_000_000,
        max_oracle_move_bps=500,
        initial_margin_bps=1_000,
        maintenance_margin_bps=600,
        liquidation_penalty_bps=500,
        funding_cap_bps=100,
        position_base=-100,
        entry_price_e8=100_000_000,
        collateral_quote=9,
        fee_pool_quote=MAX_COLLATERAL,
        fee_income=MAX_COLLATERAL,
        insurance_balance=MAX_COLLATERAL,
        min_notional_for_bounty=1,
    )

    settle = step_v4(prestate, ActionParams(action=Action.SETTLE_EPOCH))
    funding = step_v4(
        prestate,
        ActionParams(
            action=Action.APPLY_FUNDING,
            new_rate_bps=-100,
            auth_ok=True,
        ),
    )

    assert settle.accepted is True
    assert funding.accepted is False
    assert funding.state is None
    assert funding.effect is None
    assert funding.rejection == "guard"


@pytest.mark.parametrize("engine", _ENGINES)
def test_insurance_deposit_waits_until_published_price_settles(
    engine: Engine,
) -> None:
    prestate = _published_state()

    settle = engine(prestate, ActionParams(action=Action.SETTLE_EPOCH))
    deposit = engine(
        prestate,
        ActionParams(action=Action.DEPOSIT_INSURANCE, amount=1),
    )

    assert settle.accepted is True
    assert deposit.accepted is False
    assert deposit.state is None
    assert deposit.effect is None
    assert deposit.rejection == "guard"


@pytest.mark.parametrize("engine", _ENGINES)
@pytest.mark.parametrize(
    "prestate",
    (
        _published_state(
            oracle_seen=False,
            oracle_last_update_epoch=0,
            index_price_e8=0,
        ),
        _published_state(oracle_last_update_epoch=2),
    ),
)
def test_invalid_published_oracle_prestate_rejects_exact_noop(
    engine: Engine,
    prestate: PerpState,
) -> None:
    result = engine(prestate, ActionParams(action=Action.SETTLE_EPOCH))

    assert result.accepted is False
    assert result.state is None
    assert result.effect is None
    assert result.rejection == "pre_invariant:inv_phase_published_has_settlement_path"


@pytest.mark.parametrize("engine", _ENGINES)
def test_settlement_accepts_exact_freshness_boundary(engine: Engine) -> None:
    prestate = _published_state(oracle_last_update_epoch=3)

    result = engine(prestate, ActionParams(action=Action.SETTLE_EPOCH))

    assert result.accepted is True
    assert result.state is not None
    assert result.effect is not None
    assert result.state.epoch_phase is EpochPhase.SETTLED
    assert result.state.oracle_last_update_epoch == result.state.now_epoch


@pytest.mark.parametrize("engine", _ENGINES)
def test_open_epoch_still_advances_normally(engine: Engine) -> None:
    result = engine(
        initial_state(),
        ActionParams(action=Action.ADVANCE_EPOCH, delta=1),
    )

    assert result.accepted is True
    assert result.state is not None
    assert result.effect is not None
    assert result.state.now_epoch == 1
    assert result.state.epoch_phase is EpochPhase.OPEN


def test_state_decoder_rejects_missing_unknown_and_boolean_as_integer() -> None:
    canonical = state_to_dict(initial_state())

    missing = dict(canonical)
    missing.pop("now_epoch")
    with pytest.raises(ValueError, match="fields must match exactly"):
        state_from_dict(missing)

    unknown = dict(canonical)
    unknown["future_consensus_field"] = 0
    with pytest.raises(ValueError, match="fields must match exactly"):
        state_from_dict(unknown)

    bool_alias = dict(canonical)
    bool_alias["oracle_seen"] = 1
    with pytest.raises(TypeError, match="exact bool"):
        state_from_dict(bool_alias)

    int_alias = dict(canonical)
    int_alias["now_epoch"] = False
    with pytest.raises(TypeError, match="exact int"):
        state_from_dict(int_alias)


def test_named_legacy_phase_is_rejected_at_canonical_decoder() -> None:
    legacy = state_to_dict(initial_state())
    legacy["epoch_phase"] = "Open"

    with pytest.raises(TypeError, match="exact canonical int"):
        state_from_dict(legacy)
