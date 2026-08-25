"""Conservation and reject-no-op obligations for the perps lane coordinator."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    LaneIdV1,
)
from src.core.perps_margin_lane_coordinator_v1 import (
    PerpsMarginLaneCompositionAcceptedV1,
    PerpsMarginLaneCompositionCandidateV1,
    PerpsMarginLaneCompositionRejectedV1,
    PerpsMarginLaneCoordinatorContextV1,
    PerpsMarginLaneCoordinatorRejectCodeV1,
    PerpsMarginLaneProjectionV1,
    PerpsMarginModuleCompatibilityV1,
    compose_perps_margin_lane_single_v1,
)
from src.core.perps_margin_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_MODULE_SCHEMA_V1,
)
from tests.core.test_perps_margin_release_receipt_binding_v1 import (
    QUOTE_ASSET,
    _fixture,
    _root,
)

TOTAL_SUPPLY = 4_000_000_000_000
ACCOUNT_BALANCE = 2_000_000_000_000
WITHDRAW_AMOUNT = 10_000


def _ordered_amounts(*rows: EconomicAmountV1) -> tuple[EconomicAmountV1, ...]:
    return tuple(sorted(rows, key=lambda row: row.key))


def _projection_pair() -> tuple[
    object,
    PerpsMarginLaneProjectionV1,
    PerpsMarginLaneProjectionV1,
    PerpsMarginLaneCoordinatorContextV1,
]:
    fixture = _fixture(with_position=True)
    pre_lane = fixture.module_input.pre_state
    post_lane = fixture.accepted.post_state
    pre = PerpsMarginLaneProjectionV1(
        lane_state=pre_lane,
        balances=(
            EconomicAmountV1(
                "alice",
                QUOTE_ASSET,
                ACCOUNT_CUSTODY_DOMAIN_V1,
                ACCOUNT_BALANCE,
            ),
        ),
        accounting_locations=_ordered_amounts(
            EconomicAmountV1(
                "alice-margin",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000,
            ),
            EconomicAmountV1(
                "bob-margin",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000,
            ),
        ),
        liabilities=_ordered_amounts(
            EconomicAmountV1(
                "alice",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000,
            ),
            EconomicAmountV1(
                "bob",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000,
            ),
        ),
        supplies=(AssetSupplyV1(QUOTE_ASSET, TOTAL_SUPPLY),),
        terminal_obligations=pre_lane.terminal_obligations,
    )
    post = PerpsMarginLaneProjectionV1(
        lane_state=post_lane,
        balances=(
            EconomicAmountV1(
                "alice",
                QUOTE_ASSET,
                ACCOUNT_CUSTODY_DOMAIN_V1,
                ACCOUNT_BALANCE + WITHDRAW_AMOUNT,
            ),
        ),
        accounting_locations=_ordered_amounts(
            EconomicAmountV1(
                "alice-margin",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000 - WITHDRAW_AMOUNT,
            ),
            EconomicAmountV1(
                "bob-margin",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000,
            ),
        ),
        liabilities=_ordered_amounts(
            EconomicAmountV1(
                "alice",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000 - WITHDRAW_AMOUNT,
            ),
            EconomicAmountV1(
                "bob",
                QUOTE_ASSET,
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1_000_000_000_000,
            ),
        ),
        supplies=(AssetSupplyV1(QUOTE_ASSET, TOTAL_SUPPLY),),
        terminal_obligations=post_lane.terminal_obligations,
    )
    coordinator = fixture.profile.lane_coordinator_registry.release_for(
        LaneIdV1.PERPS_MARKET
    )
    context = PerpsMarginLaneCoordinatorContextV1(
        chain_id=fixture.occurrence.chain_id,
        deployment_root=fixture.occurrence.deployment_root,
        profile_root=fixture.profile.profile_id,
        writer_epoch=fixture.profile.authority_epoch,
        coordinator_release_id=coordinator.coordinator_release_id,
        command_occurrence_id=fixture.occurrence.occurrence_id,
        compatible_modules=(
            PerpsMarginModuleCompatibilityV1(
                fixture.module_input.context.module_release_id,
                PERPS_MARGIN_MODULE_SCHEMA_V1,
            ),
        ),
    )
    return fixture, pre, post, context


def test_withdraw_refines_candidate_rows_into_complete_conservation() -> None:
    # Arrange.
    fixture, pre, post, context = _projection_pair()

    # Act.
    result = compose_perps_margin_lane_single_v1(
        PerpsMarginLaneCompositionCandidateV1(
            context,
            fixture.accepted.module_journal,
            fixture.accepted.private_port,
            pre,
            post,
            fixture.accepted.effects,
        )
    )

    # Assert.
    assert isinstance(result, PerpsMarginLaneCompositionAcceptedV1)
    assert result.post_state == post
    assert pre.state_root == (
        "0x8570aa2d5eaaaa28aad048749250ab1b16588ac209a07a49cd043786d11867a9"
    )
    assert post.state_root == (
        "0x48efacb34784dfecbc0560e1233e6be8f4d589c58d26fdc4447f5c41928a5eb7"
    )
    assert result.lane_journal.pre_lane_root == pre.state_root
    assert result.lane_journal.post_lane_root == post.state_root
    assert result.lane_journal.effect_plan_root == result.effects.effect_plan_root
    assert result.effects.effect_plan_root == (
        "0x53cb336b2b2c28c7cc5d130f1ff75d3e6d1b1dcee25e34adec16e03bceedac61"
    )
    assert result.lane_journal.journal_root == (
        "0xc1b65ad2a9a2a493f4c6e218a71d638a98c29476fcb91912ccb2f7e46de8810c"
    )
    assert result.effects.rows == fixture.accepted.effects.rows
    assert len(result.effects.asset_conservation) == 1
    conservation = result.effects.asset_conservation[0]
    assert conservation.asset == QUOTE_ASSET
    assert conservation.owned_and_custodied_pre_atoms == TOTAL_SUPPLY
    assert conservation.owned_and_custodied_post_atoms == TOTAL_SUPPLY
    assert conservation.supply_pre_atoms == TOTAL_SUPPLY
    assert conservation.supply_post_atoms == TOTAL_SUPPLY
    assert conservation.authorized_issue_atoms == 0
    assert conservation.authorized_burn_atoms == 0
    assert {row.kind for row in result.effects.rows} == {
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        EconomicEffectKindV1.CUSTODY,
        EconomicEffectKindV1.LIABILITY,
    }


def test_unrecorded_accounting_location_movement_rejects_as_exact_no_op() -> None:
    fixture, pre, post, context = _projection_pair()
    drifted = replace(
        post,
        balances=(
            replace(post.balances[0], amount_atoms=post.balances[0].amount_atoms - 1),
        ),
        accounting_locations=_ordered_amounts(
            *post.accounting_locations,
            EconomicAmountV1("treasury", QUOTE_ASSET, "treasury", 1),
        ),
    )

    result = compose_perps_margin_lane_single_v1(
        PerpsMarginLaneCompositionCandidateV1(
            context,
            fixture.accepted.module_journal,
            fixture.accepted.private_port,
            pre,
            drifted,
            fixture.accepted.effects,
        )
    )

    assert isinstance(result, PerpsMarginLaneCompositionRejectedV1)
    assert result.code is PerpsMarginLaneCoordinatorRejectCodeV1.STATE_EFFECT_MISMATCH
    assert result.pre_state_root == pre.state_root
    assert result.post_state_root == pre.state_root
    assert result.effects.is_empty


def test_wrong_profile_and_extra_effect_kind_reject_without_effects() -> None:
    fixture, pre, post, context = _projection_pair()
    wrong_context = replace(context, profile_root=_root(999))
    context_reject = compose_perps_margin_lane_single_v1(
        PerpsMarginLaneCompositionCandidateV1(
            wrong_context,
            fixture.accepted.module_journal,
            fixture.accepted.private_port,
            pre,
            post,
            fixture.accepted.effects,
        )
    )
    assert isinstance(context_reject, PerpsMarginLaneCompositionRejectedV1)
    assert context_reject.code is PerpsMarginLaneCoordinatorRejectCodeV1.CONTEXT_MISMATCH
    assert context_reject.effects.is_empty

    extra = replace(
        fixture.accepted.effects,
        rows=tuple(
            sorted(
                (
                    *fixture.accepted.effects.rows,
                    replace(
                        fixture.accepted.effects.rows[0],
                        kind=EconomicEffectKindV1.RESERVE,
                        principal="reserve",
                    ),
                ),
                key=lambda row: row.key,
            )
        ),
    )
    extra_port = replace(
        fixture.accepted.private_port,
        module_effect_plan_root=extra.effect_plan_root,
    )
    effect_reject = compose_perps_margin_lane_single_v1(
        PerpsMarginLaneCompositionCandidateV1(
            context,
            replace(
                fixture.accepted.module_journal,
                effect_plan_root=extra.effect_plan_root,
                private_port_root=extra_port.port_root,
            ),
            extra_port,
            pre,
            post,
            extra,
        )
    )
    assert isinstance(effect_reject, PerpsMarginLaneCompositionRejectedV1)
    assert effect_reject.code is PerpsMarginLaneCoordinatorRejectCodeV1.EFFECT_SHAPE_MISMATCH
    assert effect_reject.effects.is_empty


def test_projection_requires_exact_liability_and_terminal_coverage() -> None:
    _, pre, _, _ = _projection_pair()
    with pytest.raises(ValueError, match="liabilities differ"):
        replace(pre, liabilities=pre.liabilities[1:])
    with pytest.raises(ValueError, match="terminal obligations are incomplete"):
        replace(pre, terminal_obligations=pre.terminal_obligations[1:])


def test_composition_candidate_rejects_untyped_parallel_inputs() -> None:
    fixture, pre, post, context = _projection_pair()
    with pytest.raises(TypeError, match="candidate must have the exact type"):
        compose_perps_margin_lane_single_v1(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="requires exact typed inputs"):
        PerpsMarginLaneCompositionCandidateV1(
            context,
            object(),  # type: ignore[arg-type]
            fixture.accepted.private_port,
            pre,
            post,
            fixture.accepted.effects,
        )
