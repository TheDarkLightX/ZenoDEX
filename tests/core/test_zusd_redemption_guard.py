from __future__ import annotations

import inspect
from dataclasses import fields

import pytest

import src.core.zusd as zusd_core
from src.core.zusd import (
    BPS_SCALE,
    E8,
    ZUSDCommand,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDRedemptionAdmissionProfile,
    ZUSDState,
    ZUSDVault,
    step,
    step_multi,
)
from src.core.zusd_redemption_guard import (
    ZUSDLiquityV1RedemptionDecision,
    ZUSDUnmountedRedemptionDrainGuardContext,
    evaluate_liquity_v1_minimum_redemption_guard,
    evaluate_redemption_guard,
)

_BASELINE_FORBIDDEN_FIELDS = {
    "epoch_redemption_used_e8",
    "max_epoch_redemption_fraction_bps",
    "redemption_min_post_tcr_bps",
    "redemption_shutdown_tcr_bps",
    "shutdown_extension",
    "shutdown_phase",
    "shutdown_epoch",
    "shutdown_oracle_observed_epoch",
    "shutdown_price_e8",
    "shutdown_collateral_e8",
    "shutdown_debt_e8",
    "shutdown_source_state_root",
}


def test_liquity_v1_baseline_guard_matches_bounded_integer_reference() -> None:
    for collateral_e8 in range(5):
        for debt_e8 in range(5):
            for price_e8 in range(1, 4):
                for mcr_bps in (1, BPS_SCALE, 11_000):
                    decision = evaluate_liquity_v1_minimum_redemption_guard(
                        system_collateral_e8=collateral_e8,
                        system_debt_e8=debt_e8,
                        price_e8=price_e8,
                        mcr_bps=mcr_bps,
                    )
                    expected = (
                        debt_e8 == 0
                        or collateral_e8 * price_e8 * BPS_SCALE
                        >= debt_e8 * mcr_bps * E8
                    )
                    assert decision.accepted is expected
                    assert decision.error == (
                        None
                        if expected
                        else "redemption blocked: system TCR below MCR"
                    )


def test_liquity_v1_baseline_decision_cannot_carry_extension_authority() -> None:
    assert [field.name for field in fields(ZUSDLiquityV1RedemptionDecision)] == [
        "pre_system_tcr_at_least_mcr"
    ]


def test_baseline_state_types_structurally_omit_ce067_extensions() -> None:
    for state_type in (ZUSDState, ZUSDMultiState):
        names = {field.name for field in fields(state_type)}
        assert names.isdisjoint(_BASELINE_FORBIDDEN_FIELDS)


def test_mounted_redemption_profile_is_closed_and_exactly_typed() -> None:
    for state in (ZUSDState(), ZUSDMultiState()):
        assert (
            type(state.redemption_admission_profile)
            is ZUSDRedemptionAdmissionProfile
        )
        assert (
            state.redemption_admission_profile
            is ZUSDRedemptionAdmissionProfile.LIQUITY_V1_MINIMUM
        )
    with pytest.raises(ValueError):
        ZUSDRedemptionAdmissionProfile("zenodex/zusd-drain-guard-experimental")


def test_mounted_transition_union_has_no_experimental_guard_binding() -> None:
    mounted_source = "\n".join(
        (inspect.getsource(zusd_core.step), inspect.getsource(zusd_core.step_multi))
    )
    for forbidden in (
        "evaluate_redemption_guard",
        "redemption_min_post_tcr_bps",
        "max_epoch_redemption_fraction_bps",
        "epoch_redemption_used_e8",
    ):
        assert forbidden not in mounted_source


@pytest.mark.parametrize(
    "field_name",
    ("system_collateral_e8", "system_debt_e8", "price_e8", "mcr_bps"),
)
def test_liquity_v1_baseline_guard_rejects_boolean_integer_aliases(
    field_name: str,
) -> None:
    args: dict[str, object] = {
        "system_collateral_e8": 2 * E8,
        "system_debt_e8": E8,
        "price_e8": E8,
        "mcr_bps": 11_000,
    }
    args[field_name] = True
    with pytest.raises(TypeError, match=f"{field_name} must be an int"):
        evaluate_liquity_v1_minimum_redemption_guard(**args)  # type: ignore[arg-type]


def test_unmounted_drain_guard_matches_bounded_integer_reference() -> None:
    for collateral in range(3):
        for debt in range(1, 4):
            for redeem in range(1, debt + 1):
                for post_collateral in range(collateral + 1):
                    for used in range(2):
                        for threshold in (0, 11_000):
                            for cap_bps in (0, BPS_SCALE):
                                context = ZUSDUnmountedRedemptionDrainGuardContext(
                                    epoch_redemption_used_e8=used,
                                    branch_tcr_floor_bps=threshold,
                                    min_post_tcr_bps=threshold,
                                    max_epoch_redemption_fraction_bps=cap_bps,
                                )
                                post_debt = debt - redeem
                                decision = evaluate_redemption_guard(
                                    collateral_e8=collateral,
                                    debt_e8=debt,
                                    price_e8=1,
                                    post_collateral_e8=post_collateral,
                                    post_debt_e8=post_debt,
                                    redeem_e8=redeem,
                                    extension_context=context,
                                    no_liquidation_priority=True,
                                )
                                branch_ok = (
                                    collateral * BPS_SCALE
                                    >= debt * threshold * E8
                                )
                                post_ok = (
                                    post_debt == 0
                                    or post_collateral * BPS_SCALE
                                    >= post_debt * threshold * E8
                                )
                                cap_ok = (
                                    used + redeem
                                    <= debt * cap_bps // BPS_SCALE
                                )
                                assert decision.branch_tcr_ok is branch_ok
                                assert decision.post_tcr_ok is post_ok
                                assert decision.epoch_cap_ok is cap_ok
                                assert decision.accepted is (
                                    branch_ok and post_ok and cap_ok
                                )


def test_unmounted_guard_requires_exact_context_type() -> None:
    with pytest.raises(TypeError, match="extension_context must be"):
        evaluate_redemption_guard(
            collateral_e8=2 * E8,
            debt_e8=E8,
            price_e8=E8,
            post_collateral_e8=E8,
            post_debt_e8=0,
            redeem_e8=E8,
            extension_context=object(),  # type: ignore[arg-type]
            no_liquidation_priority=True,
        )


def test_liquity_v1_baseline_repeated_redemptions_have_no_epoch_throttle() -> None:
    state = ZUSDState(
        oracle_seen=True,
        price_e8=E8,
        price_pending_e8=E8,
        collateral_e8=6_000 * E8,
        debt_e8=4_000 * E8,
        free_debt_e8=4_000 * E8,
    )
    for amount_e8 in (1_000 * E8, 1_000 * E8, 500 * E8):
        result = step(
            state,
            ZUSDCommand(tag="redeem_zusd", args={"amount_e8": amount_e8}),
        )
        assert result.ok is True, result.error
        assert result.state is not None
        state = result.state
    assert state.debt_e8 == 1_500 * E8
    assert state.collateral_e8 == 3_500 * E8


def test_liquity_v1_baseline_rejects_when_pre_system_tcr_is_below_mcr() -> None:
    state = ZUSDState(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        collateral_e8=105_000_000,
        debt_e8=100 * E8,
        free_debt_e8=100 * E8,
        min_debt_open_e8=E8,
    )
    result = step(
        state,
        ZUSDCommand(tag="redeem_zusd", args={"amount_e8": 10 * E8}),
    )
    assert result.ok is False
    assert result.error == "redemption blocked: system TCR below MCR"
    assert result.state is None


def test_multi_redemption_reaches_source_eligible_head() -> None:
    state = ZUSDMultiState(
        oracle_seen=True,
        price_e8=100 * E8,
        price_pending_e8=100 * E8,
        vault_a=ZUSDVault(collateral_e8=105_000_000, debt_e8=100 * E8),
        vault_b=ZUSDVault(collateral_e8=10 * E8, debt_e8=200 * E8),
        free_debt_e8=300 * E8,
    )
    result = step_multi(
        state,
        ZUSDMultiCommand(
            tag="redeem_zusd",
            args={"vault": "b", "amount_e8": 10 * E8},
        ),
    )
    assert result.ok is True, result.error
    assert result.state is not None
    assert result.effects is not None
    assert result.effects["vault"] == "b"
    assert result.state.vault_a == state.vault_a
    assert result.state.vault_b.debt_e8 == state.vault_b.debt_e8 - 10 * E8


@pytest.mark.parametrize("invalid", (0, True))
def test_single_state_rejects_nonpositive_or_boolean_min_debt(invalid: object) -> None:
    with pytest.raises(ValueError, match="min_debt_open_e8 must be"):
        ZUSDState(min_debt_open_e8=invalid)  # type: ignore[arg-type]


@pytest.mark.parametrize("invalid", (0, True))
def test_multi_state_rejects_nonpositive_or_boolean_min_debt(invalid: object) -> None:
    with pytest.raises(ValueError, match="min_debt_open_e8 must be"):
        ZUSDMultiState(min_debt_open_e8=invalid)  # type: ignore[arg-type]
