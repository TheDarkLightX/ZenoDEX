from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import LaneModuleTransitionJournalV1
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    LaneIdV1,
)
from src.core.zdex_fee_allocation_types_v1 import (
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeStateV1,
)
from src.core.zdex_hyperdeflation_route_refinement_v1 import (
    ZDEXBurnLeafProjectionV1,
    refine_zdex_burn_leaf_v1,
)
from src.core.zdex_hyperdeflation_v1 import (
    ZDEXAmountBucketV1,
    ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1,
    ZDEXPurchaseAndBurnAcceptedV1,
    ZDEXPurchaseAndBurnCommandV1,
    ZDEXSupplyStateV1,
    transition_zdex_purchase_and_burn_v1,
)
from src.core.zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import ZDEXAMMPurchaseJournalV1
from src.core.zdex_tokenomics_lane_coordinator_v1 import (
    ZDEXTokenomicsBurnLaneCandidateV1,
    compose_zdex_tokenomics_burn_lane_v1,
)
from src.core.zdex_tokenomics_lane_v1 import (
    MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1,
    ZDEXTokenomicsBurnCoordinatorContextV1,
    ZDEXTokenomicsLaneCompositionAcceptedV1,
    ZDEXTokenomicsLaneCompositionRejectedV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1,
    build_zdex_tokenomics_burn_private_port_v1,
    zdex_tokenomics_complete_lane_obligation_root_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _burn_projection() -> ZDEXBurnLeafProjectionV1:
    policy = ZDEXHyperdeflationPolicyV1(
        asset_id=_root(1),
        retained_numerator=9,
        retained_denominator=10,
        maximum_decimals=64,
        maximum_decimal_step=8,
    )
    draft_purchase = ZDEXAMMPurchaseJournalV1(
        chain_id="tau-testnet",
        deployment_root=_root(10),
        profile_root=_root(11),
        writer_epoch=7,
        route_release_id=_root(2),
        command_occurrence_id=_root(12),
        spot_module_release_id=_root(13),
        issue_burn_policy_root=policy.policy_root,
        buyback_budget_occurrence_root=_root(14),
        quote_asset_id=_root(15),
        zdex_asset_id=policy.asset_id,
        quote_source_bucket_id="protocol:buyback:quote",
        quote_pool_bucket_id="pool:quote",
        zdex_pool_bucket_id="pool:zdex",
        burn_bucket_id="route:buyburn:source",
        quote_amount_in_atoms=50,
        purchased_zdex_atoms=100,
        quote_source_pre_atoms=1000,
        quote_source_post_atoms=950,
        quote_pool_pre_atoms=200,
        quote_pool_post_atoms=250,
        zdex_pool_pre_atoms=600,
        zdex_pool_post_atoms=500,
        burn_bucket_pre_atoms=0,
        burn_bucket_post_atoms=100,
        quote_owned_atoms=1200,
        quote_supply_atoms=2000,
        zdex_owned_atoms=1000,
        zdex_supply_atoms=1000,
        pre_spot_lane_root=_root(16),
        post_spot_lane_root=_root(17),
        effect_plan_root=_root(18),
    )
    purchase = replace(
        draft_purchase,
        effect_plan_root=purchase_effects_v1(draft_purchase).effect_plan_root,
    )
    pre_state = ZDEXSupplyStateV1(
        asset_id=policy.asset_id,
        policy_root=policy.policy_root,
        decimals=8,
        precision_epoch=0,
        live_supply_atoms=1000,
        buckets=(
            ZDEXAmountBucketV1(purchase.burn_bucket_id, 100),
            ZDEXAmountBucketV1("wallet:alice", 900),
        ),
        burn_budget_epoch=5,
        remaining_epoch_burn_cap_atoms=100,
    )
    route_context = ZDEXBurnRouteContextV1(
        route_release_id=purchase.route_release_id,
        policy_root=policy.policy_root,
        purchase_occurrence_root=purchase.journal_root,
        burn_source_bucket_id=purchase.burn_bucket_id,
        purchased_zdex_atoms=100,
        source_reserve_floor_atoms=0,
        remaining_epoch_burn_cap_atoms=100,
        route_safe_output_cap_atoms=100,
        burn_budget_epoch=5,
    )
    command = ZDEXPurchaseAndBurnCommandV1(
        expected_pre_state_root=pre_state.state_root,
        expected_precision_epoch=0,
        expected_purchase_occurrence_root=purchase.journal_root,
        source_bucket_id=purchase.burn_bucket_id,
        purchased_zdex_atoms=100,
    )
    accepted = transition_zdex_purchase_and_burn_v1(
        policy,
        pre_state,
        route_context,
        command,
    )
    assert type(accepted) is ZDEXPurchaseAndBurnAcceptedV1
    return refine_zdex_burn_leaf_v1(accepted, purchase, _root(20))


def _fee_state() -> ZDEXFeeStateV1:
    return ZDEXFeeStateV1(
        fee_asset_id=_root(15),
        policy_root=_root(30),
        fee_ingress_atoms=1000,
        unallocated_reserve_atoms=100,
        destination_balances=tuple(
            ZDEXFeeDestinationAmountV1(destination, 0)
            for destination in ZDEX_FEE_DESTINATIONS_V1
        ),
        owned_and_custodied_atoms=2000,
        supply_atoms=2000,
    )


def _lane_state(supply_state: ZDEXSupplyStateV1) -> ZDEXTokenomicsLaneStateV1:
    return ZDEXTokenomicsLaneStateV1(
        supply_state=supply_state,
        fee_allocation_states=(_fee_state(),),
        staking_state_root=_root(31),
        host_claims_state_root=_root(32),
        treasury_claims_state_root=_root(33),
        proof_rewards_state_root=_root(34),
        cover_reserve_state_root=_root(35),
        lp_rebates_state_root=_root(36),
    )


def _candidate() -> tuple[
    ZDEXTokenomicsBurnLaneCandidateV1,
    ZDEXBurnLeafProjectionV1,
]:
    projection = _burn_projection()
    journal = projection.journal
    effects = projection.effects
    obligation = zdex_tokenomics_complete_lane_obligation_root_v1()
    private_port = build_zdex_tokenomics_burn_private_port_v1(journal, effects)
    module_journal = LaneModuleTransitionJournalV1(
        chain_id=journal.chain_id,
        deployment_root=journal.deployment_root,
        profile_root=journal.profile_root,
        writer_epoch=journal.writer_epoch,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        module_release_id=journal.tokenomics_module_release_id,
        command_occurrence_id=journal.command_occurrence_id,
        pre_lane_root=ZERO_ROOT_V1,
        post_lane_root=ZERO_ROOT_V1,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=private_port.port_root,
        receipt_root=_root(41),
        terminal_obligations_root=obligation,
    )
    context = ZDEXTokenomicsBurnCoordinatorContextV1(
        chain_id=journal.chain_id,
        deployment_root=journal.deployment_root,
        profile_root=journal.profile_root,
        writer_epoch=journal.writer_epoch,
        coordinator_release_id=_root(42),
        route_release_id=journal.route_release_id,
        tokenomics_module_release_id=journal.tokenomics_module_release_id,
        command_occurrence_id=journal.command_occurrence_id,
        issue_burn_policy_root=journal.issue_burn_policy_root,
    )
    pre_lane = _lane_state(projection.accepted.pre_state)
    post_lane = _lane_state(projection.accepted.post_state)
    return (
        ZDEXTokenomicsBurnLaneCandidateV1(
            context,
            module_journal,
            private_port,
            pre_lane,
            post_lane,
            projection.journal,
            projection.effects,
        ),
        projection,
    )


def test_burn_substate_is_embedded_in_one_complete_tokenomics_lane_write() -> None:
    # Arrange
    candidate, _ = _candidate()

    # Act
    result = compose_zdex_tokenomics_burn_lane_v1(candidate)

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionAcceptedV1
    assert result.post_state == candidate.post_state
    assert result.lane_journal.pre_lane_root == candidate.pre_state.state_root
    assert result.lane_journal.post_lane_root == candidate.post_state.state_root
    assert result.lane_journal.terminal_obligations_root == ZERO_ROOT_V1
    assert result.effects.lane_writes == (
        result.expected_lane_write,
    )
    assert candidate.pre_state.state_root == (
        "0x13e77d130b8b5c1dfe49d5885cd7ee968d4fd4514a7af19b261d3e1b76d0e7ca"
    )
    assert candidate.post_state.state_root == (
        "0xaf35a07a30050310c6343947ba773ebd4424a816418d5e03b17b68820cb5656b"
    )
    assert candidate.private_port.port_root == (
        "0x3599e1c7349810b87811902c2cfc367f9c791c9d16aead73c7280753dc24e619"
    )
    assert candidate.module_journal.journal_root == (
        "0xbcf63554276350f9f76d4150fd033fd897fd57938238f669c3e29fad52122ee6"
    )
    assert result.effects.effect_plan_root == (
        "0x211aa4aa89fb7f65b422adfb8d1d0549f85b2fdfd83d4222d8285baf7dd534bc"
    )
    assert result.lane_journal.journal_root == (
        "0x19a31e3c73851451198350d031df6737ac4008b2ca30b47a50f3c1378cff31b7"
    )


def test_fee_state_registry_rejects_zero_duplicate_unsorted_and_excess_width() -> None:
    # Arrange
    candidate, _ = _candidate()
    base = candidate.pre_state
    low = replace(_fee_state(), fee_asset_id=_root(90))
    high = replace(_fee_state(), fee_asset_id=_root(91))

    # Act / Assert
    with pytest.raises(ValueError, match="width"):
        replace(base, fee_allocation_states=())
    with pytest.raises(ValueError, match="asset-ordered"):
        replace(base, fee_allocation_states=(low, low))
    with pytest.raises(ValueError, match="asset-ordered"):
        replace(base, fee_allocation_states=(high, low))
    with pytest.raises(ValueError, match="width"):
        replace(
            base,
            fee_allocation_states=(low,) * (MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1 + 1),
        )


@pytest.mark.parametrize(
    "field_name",
    (
        "fee_allocation_states",
        "staking_state_root",
        "host_claims_state_root",
        "treasury_claims_state_root",
        "proof_rewards_state_root",
        "cover_reserve_state_root",
        "lp_rebates_state_root",
    ),
)
def test_unrelated_tokenomics_component_mutation_rejects_without_effects(
    field_name: str,
) -> None:
    # Arrange
    candidate, _ = _candidate()
    replacement = (
        (
            replace(
                candidate.post_state.fee_allocation_states[0],
                fee_ingress_atoms=999,
            ),
        )
        if field_name == "fee_allocation_states"
        else _root(99)
    )
    mutated_post = replace(candidate.post_state, **{field_name: replacement})

    # Act
    result = compose_zdex_tokenomics_burn_lane_v1(
        replace(candidate, post_state=mutated_post)
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.UNRELATED_STATE_MUTATION
    assert result.pre_lane_root == result.post_lane_root == candidate.pre_state.state_root
    assert result.effects.is_empty


def test_partial_substate_cannot_be_claimed_as_a_complete_lane_root() -> None:
    # Arrange
    candidate, _ = _candidate()
    forged_module = replace(
        candidate.module_journal,
        pre_lane_root=candidate.burn_journal.pre_tokenomics_burn_substate_root,
        post_lane_root=candidate.burn_journal.post_tokenomics_burn_substate_root,
    )

    # Act
    result = compose_zdex_tokenomics_burn_lane_v1(
        replace(candidate, module_journal=forged_module)
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PARTIAL_LANE_ROOT_CLAIM
    assert result.effects.is_empty


def test_private_port_and_post_substate_substitutions_reject() -> None:
    # Arrange
    candidate, _ = _candidate()
    forged_port = replace(candidate.private_port, post_burn_substate_root=_root(98))

    # Act
    port_result = compose_zdex_tokenomics_burn_lane_v1(
        replace(candidate, private_port=forged_port)
    )
    state_result = compose_zdex_tokenomics_burn_lane_v1(
        replace(
            candidate,
            post_state=replace(
                candidate.post_state,
                supply_state=candidate.pre_state.supply_state,
            ),
        )
    )

    # Assert
    assert type(port_result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert port_result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PRIVATE_PORT_MISMATCH
    assert type(state_result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert state_result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.POST_SUBSTATE_MISMATCH


def test_route_release_substitution_has_a_closed_no_effect_rejection() -> None:
    # Arrange
    candidate, _ = _candidate()

    # Act
    result = compose_zdex_tokenomics_burn_lane_v1(
        replace(
            candidate,
            context=replace(candidate.context, route_release_id=_root(99)),
        )
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.ROUTE_RELEASE_MISMATCH
    assert result.effects.is_empty


@pytest.mark.parametrize(
    ("case", "expected_code"),
    (
        ("chain", ZDEXTokenomicsLaneCoordinatorRejectCodeV1.CHAIN_MISMATCH),
        (
            "deployment",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.DEPLOYMENT_MISMATCH,
        ),
        ("profile", ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PROFILE_MISMATCH),
        (
            "writer_epoch",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.WRITER_EPOCH_MISMATCH,
        ),
        ("lane", ZDEXTokenomicsLaneCoordinatorRejectCodeV1.WRONG_LANE),
        (
            "module_release",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.MODULE_RELEASE_MISMATCH,
        ),
        (
            "occurrence",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.OCCURRENCE_MISMATCH,
        ),
        (
            "terminal_obligation",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.TERMINAL_OBLIGATION_MISMATCH,
        ),
        (
            "burn_policy",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.BURN_JOURNAL_MISMATCH,
        ),
        (
            "effect_plan",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.EFFECT_PLAN_MISMATCH,
        ),
        (
            "pre_substate",
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PRE_SUBSTATE_MISMATCH,
        ),
    ),
)
def test_each_coordinator_binding_substitution_is_a_typed_no_effect_rejection(
    case: str,
    expected_code: ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
) -> None:
    # Arrange
    candidate, _ = _candidate()
    if case == "chain":
        candidate = replace(
            candidate,
            context=replace(candidate.context, chain_id="other-testnet"),
        )
    elif case == "deployment":
        candidate = replace(
            candidate,
            context=replace(candidate.context, deployment_root=_root(90)),
        )
    elif case == "profile":
        candidate = replace(
            candidate,
            context=replace(candidate.context, profile_root=_root(90)),
        )
    elif case == "writer_epoch":
        candidate = replace(
            candidate,
            context=replace(
                candidate.context,
                writer_epoch=candidate.context.writer_epoch + 1,
            ),
        )
    elif case == "lane":
        candidate = replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                lane_id=LaneIdV1.ASSET_TRANSFER,
            ),
        )
    elif case == "module_release":
        candidate = replace(
            candidate,
            context=replace(candidate.context, tokenomics_module_release_id=_root(90)),
        )
    elif case == "occurrence":
        candidate = replace(
            candidate,
            context=replace(candidate.context, command_occurrence_id=_root(90)),
        )
    elif case == "terminal_obligation":
        candidate = replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                terminal_obligations_root=_root(90),
            ),
        )
    elif case == "burn_policy":
        candidate = replace(
            candidate,
            context=replace(candidate.context, issue_burn_policy_root=_root(90)),
        )
    elif case == "effect_plan":
        candidate = replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                effect_plan_root=_root(90),
            ),
        )
    elif case == "pre_substate":
        candidate = replace(candidate, pre_state=candidate.post_state)
    else:  # pragma: no cover - the closed parameter table makes this unreachable.
        raise AssertionError(f"unknown test case: {case}")

    # Act
    result = compose_zdex_tokenomics_burn_lane_v1(candidate)

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is expected_code
    assert result.pre_lane_root == result.post_lane_root == candidate.pre_state.state_root
    assert result.effects.is_empty


def test_self_consistent_leaf_totals_cannot_override_complete_lane_supply() -> None:
    # Arrange
    candidate, _ = _candidate()
    forged_draft = replace(
        candidate.burn_journal,
        zdex_owned_pre_atoms=2000,
        zdex_owned_post_atoms=1900,
        effect_plan_root=_root(90),
    )
    forged_effects = burn_effects_v1(forged_draft)
    forged_burn = replace(
        forged_draft,
        effect_plan_root=forged_effects.effect_plan_root,
    )
    forged_port = build_zdex_tokenomics_burn_private_port_v1(
        forged_burn,
        forged_effects,
    )
    forged_module = replace(
        candidate.module_journal,
        effect_plan_root=forged_effects.effect_plan_root,
        private_port_root=forged_port.port_root,
    )

    # Act
    result = compose_zdex_tokenomics_burn_lane_v1(
        replace(
            candidate,
            module_journal=forged_module,
            private_port=forged_port,
            burn_journal=forged_burn,
            module_effects=forged_effects,
        )
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.STATE_EFFECT_MISMATCH
    assert result.pre_lane_root == result.post_lane_root == candidate.pre_state.state_root
    assert result.effects.is_empty


def test_hostile_post_construction_mutation_is_revalidated() -> None:
    # Arrange
    candidate, projection = _candidate()
    object.__setattr__(candidate.private_port, "module_effect_plan_root", "malformed")
    object.__setattr__(
        candidate.pre_state.fee_allocation_states[0],
        "fee_ingress_atoms",
        -1,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="root"):
        compose_zdex_tokenomics_burn_lane_v1(
            replace(
                candidate,
                pre_state=_lane_state(projection.accepted.pre_state),
            )
        )
    with pytest.raises((TypeError, ValueError)):
        _ = candidate.pre_state.state_root
