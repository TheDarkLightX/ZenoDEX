from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    LaneIdV1,
    LaneWriteV1,
)
from src.core.zdex_fee_allocation_types_v1 import (
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
)
from src.core.zdex_fee_allocation_v1 import transition_zdex_fee_allocation_v1
from src.core.zdex_hyperdeflation_types_v1 import (
    ZDEXAmountBucketV1,
    ZDEXSupplyStateV1,
)
from src.core.zdex_tokenomics_fee_lane_coordinator_v1 import (
    ZDEXTokenomicsFeeAllocationLaneCandidateV1,
    compose_zdex_tokenomics_fee_allocation_lane_v1,
)
from src.core.zdex_tokenomics_fee_lane_v1 import (
    ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    build_zdex_tokenomics_fee_allocation_module_journal_v1,
    build_zdex_tokenomics_fee_allocation_private_port_v1,
)
from src.core.zdex_tokenomics_lane_v1 import (
    ZDEXTokenomicsLaneCompositionAcceptedV1,
    ZDEXTokenomicsLaneCompositionRejectedV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _fee_state(asset_ordinal: int, policy_root: str) -> ZDEXFeeStateV1:
    return ZDEXFeeStateV1(
        fee_asset_id=_root(asset_ordinal),
        policy_root=policy_root,
        fee_ingress_atoms=50_000,
        unallocated_reserve_atoms=700,
        destination_balances=tuple(
            ZDEXFeeDestinationAmountV1(destination, ordinal * 10)
            for ordinal, destination in enumerate(ZDEX_FEE_DESTINATIONS_V1, start=1)
        ),
        owned_and_custodied_atoms=1_000_000,
        supply_atoms=1_000_000,
    )


def _accepted() -> ZDEXFeeAllocationAcceptedV1:
    policy = candidate_zdex_fee_allocation_policy_v1()
    context = ZDEXFeeAllocationContextV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=11,
        allocation_route_release_id=_root(3),
        authorized_buyback_route_release_id=_root(4),
        tokenomics_module_release_id=_root(5),
        command_occurrence_id=_root(6),
        policy_root=policy.policy_root,
    )
    result = transition_zdex_fee_allocation_v1(
        context,
        _fee_state(40, policy.policy_root),
        policy,
        ZDEXFeeAllocationCommandV1(10_003),
    )
    assert type(result) is ZDEXFeeAllocationAcceptedV1
    return result


def _supply_state() -> ZDEXSupplyStateV1:
    return ZDEXSupplyStateV1(
        asset_id=_root(90),
        policy_root=_root(91),
        decimals=8,
        precision_epoch=0,
        live_supply_atoms=1_000,
        buckets=(ZDEXAmountBucketV1("wallet:alice", 1_000),),
        burn_budget_epoch=5,
        remaining_epoch_burn_cap_atoms=100,
    )


def _lane_state(
    target: ZDEXFeeStateV1,
    *,
    other: ZDEXFeeStateV1 | None = None,
) -> ZDEXTokenomicsLaneStateV1:
    other_state = other or _fee_state(41, _root(50))
    return ZDEXTokenomicsLaneStateV1(
        supply_state=_supply_state(),
        fee_allocation_states=(target, other_state),
        staking_state_root=_root(31),
        host_claims_state_root=_root(32),
        treasury_claims_state_root=_root(33),
        proof_rewards_state_root=_root(34),
        cover_reserve_state_root=_root(35),
        lp_rebates_state_root=_root(36),
    )


def _candidate() -> ZDEXTokenomicsFeeAllocationLaneCandidateV1:
    accepted = _accepted()
    policy = candidate_zdex_fee_allocation_policy_v1()
    port = build_zdex_tokenomics_fee_allocation_private_port_v1(accepted, policy)
    module = build_zdex_tokenomics_fee_allocation_module_journal_v1(
        accepted,
        policy,
        port,
    )
    occurrence = accepted.occurrence
    context = ZDEXTokenomicsFeeAllocationCoordinatorContextV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=occurrence.writer_epoch,
        coordinator_release_id=_root(7),
        allocation_route_release_id=occurrence.allocation_route_release_id,
        authorized_buyback_route_release_id=(
            occurrence.authorized_buyback_route_release_id
        ),
        tokenomics_module_release_id=occurrence.tokenomics_module_release_id,
        command_occurrence_id=occurrence.command_occurrence_id,
        policy_root=occurrence.policy_root,
    )
    return ZDEXTokenomicsFeeAllocationLaneCandidateV1(
        context,
        module,
        port,
        _lane_state(accepted.pre_state),
        _lane_state(accepted.post_state),
        accepted,
        policy,
    )


def test_fee_substate_is_embedded_in_one_complete_tokenomics_lane_write() -> None:
    # Arrange
    candidate = _candidate()

    # Act
    result = compose_zdex_tokenomics_fee_allocation_lane_v1(candidate)

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionAcceptedV1
    assert result.post_state == candidate.post_state
    assert result.lane_journal.pre_lane_root == candidate.pre_state.state_root
    assert result.lane_journal.post_lane_root == candidate.post_state.state_root
    assert result.lane_journal.terminal_obligations_root == ZERO_ROOT_V1
    assert result.effects.lane_writes == (result.expected_lane_write,)
    assert result.effects.rows == candidate.allocation.effects.rows
    assert result.effects.fee_conservation == candidate.allocation.effects.fee_conservation
    assert candidate.allocation.occurrence.occurrence_root == (
        "0xc00e0d5f4f83c82a18ba0b552aa0129d497be0806b2f833541b937fae16fac4e"
    )
    assert candidate.private_port.port_root == (
        "0x532e46cd7be6a84d3b610c7ae362d81bca67ce6baffe14d80087824adaf211aa"
    )
    assert candidate.module_journal.journal_root == (
        "0x3f9ff650e0d9e17de0535390db14c7cde561056f206fe62a5eb6da9890b99cf7"
    )
    assert result.effects.effect_plan_root == (
        "0x7e6b5578cc8279ab06cd812e4c2c882b7df4008a1e612e860a769149bb265ca0"
    )
    assert result.lane_journal.journal_root == (
        "0x0a2395ac0ad4a73d6fa2f8dc902541cfdf0b554c96657bc7dd64aa8178d59db6"
    )


def test_partial_fee_substate_cannot_claim_complete_lane_roots() -> None:
    # Arrange
    candidate = _candidate()
    forged = replace(
        candidate.module_journal,
        pre_lane_root=candidate.allocation.pre_state.state_root,
        post_lane_root=candidate.allocation.post_state.state_root,
    )

    # Act
    result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, module_journal=forged)
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PARTIAL_LANE_ROOT_CLAIM
    assert result.effects.is_empty


@pytest.mark.parametrize(
    "mutation",
    ("supply", "other_fee", "staking"),
)
def test_unrelated_component_mutation_rejects_as_exact_no_op(mutation: str) -> None:
    # Arrange
    candidate = _candidate()
    post = candidate.post_state
    if mutation == "supply":
        mutated = replace(post, supply_state=replace(post.supply_state, precision_epoch=1))
    elif mutation == "other_fee":
        other = replace(post.fee_allocation_states[1], fee_ingress_atoms=49_999)
        mutated = replace(
            post,
            fee_allocation_states=(post.fee_allocation_states[0], other),
        )
    else:
        mutated = replace(post, staking_state_root=_root(99))

    # Act
    result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, post_state=mutated)
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.UNRELATED_STATE_MUTATION
    assert result.pre_lane_root == result.post_lane_root == candidate.pre_state.state_root
    assert result.effects.is_empty


def test_wrong_target_post_substate_rejects_without_effects() -> None:
    # Arrange
    candidate = _candidate()
    wrong_target = replace(candidate.allocation.post_state, fee_ingress_atoms=40_000)
    mutated = replace(
        candidate.post_state,
        fee_allocation_states=(wrong_target, candidate.post_state.fee_allocation_states[1]),
    )

    # Act
    result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, post_state=mutated)
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.POST_SUBSTATE_MISMATCH
    assert result.effects.is_empty


def test_route_and_module_receipt_substitutions_reject_without_effects() -> None:
    # Arrange
    candidate = _candidate()
    wrong_route = replace(candidate.context, allocation_route_release_id=_root(98))
    wrong_receipt = replace(candidate.module_journal, receipt_root=_root(99))

    # Act
    route_result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, context=wrong_route)
    )
    receipt_result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, module_journal=wrong_receipt)
    )

    # Assert
    assert type(route_result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert route_result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.ROUTE_RELEASE_MISMATCH
    assert type(receipt_result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert (
        receipt_result.code
        is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.MODULE_RECEIPT_MISMATCH
    )
    assert route_result.effects.is_empty and receipt_result.effects.is_empty


def test_sum_preserving_destination_shift_cannot_build_a_module_statement() -> None:
    # Arrange
    accepted = _accepted()
    balances = list(accepted.post_state.destination_balances)
    balances[0] = replace(balances[0], allocation_atoms=balances[0].allocation_atoms + 1)
    balances[2] = replace(balances[2], allocation_atoms=balances[2].allocation_atoms - 1)
    shifted_post = replace(accepted.post_state, destination_balances=tuple(balances))
    shifted_occurrence = replace(
        accepted.occurrence,
        post_lane_root=shifted_post.state_root,
    )
    shifted = ZDEXFeeAllocationAcceptedV1(
        accepted.pre_state,
        shifted_post,
        accepted.effects,
        shifted_occurrence,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="destination delta"):
        build_zdex_tokenomics_fee_allocation_private_port_v1(
            shifted,
            candidate_zdex_fee_allocation_policy_v1(),
        )


def test_coherent_forged_fee_split_cannot_refine_the_governed_policy() -> None:
    # Arrange
    accepted = _accepted()
    allocations = list(accepted.occurrence.allocations)
    allocations[0] = replace(
        allocations[0],
        allocation_atoms=allocations[0].allocation_atoms + 1,
    )
    allocations[2] = replace(
        allocations[2],
        allocation_atoms=allocations[2].allocation_atoms - 1,
    )
    balances = list(accepted.post_state.destination_balances)
    balances[0] = replace(balances[0], allocation_atoms=balances[0].allocation_atoms + 1)
    balances[2] = replace(balances[2], allocation_atoms=balances[2].allocation_atoms - 1)
    shifted_post = replace(accepted.post_state, destination_balances=tuple(balances))
    rows = tuple(
        replace(row, delta_atoms=row.delta_atoms + 1)
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
        and row.principal == "protocol-fee-buyback-reserve"
        else replace(row, delta_atoms=row.delta_atoms - 1)
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
        and row.principal == "protocol:fee-treasury"
        else row
        for row in accepted.effects.rows
    )
    shifted_effects = replace(accepted.effects, rows=rows)
    shifted_occurrence = replace(
        accepted.occurrence,
        allocations=tuple(allocations),
        post_lane_root=shifted_post.state_root,
        effect_plan_root=shifted_effects.effect_plan_root,
    )
    shifted = ZDEXFeeAllocationAcceptedV1(
        accepted.pre_state,
        shifted_post,
        shifted_effects,
        shifted_occurrence,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="policy"):
        build_zdex_tokenomics_fee_allocation_private_port_v1(
            shifted,
            candidate_zdex_fee_allocation_policy_v1(),
        )


def test_partial_fee_substate_lane_write_cannot_build_a_module_statement() -> None:
    # Arrange
    accepted = _accepted()
    partial_effects = replace(
        accepted.effects,
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                accepted.pre_state.state_root,
                accepted.post_state.state_root,
            ),
        ),
    )
    partial_occurrence = replace(
        accepted.occurrence,
        effect_plan_root=partial_effects.effect_plan_root,
    )
    partial = ZDEXFeeAllocationAcceptedV1(
        accepted.pre_state,
        accepted.post_state,
        partial_effects,
        partial_occurrence,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="effect plan"):
        build_zdex_tokenomics_fee_allocation_private_port_v1(
            partial,
            candidate_zdex_fee_allocation_policy_v1(),
        )


def test_post_construction_context_mutation_is_revalidated_before_composition() -> None:
    # Arrange
    candidate = _candidate()
    object.__setattr__(candidate.context, "writer_epoch", True)

    # Act / Assert
    with pytest.raises(ValueError, match="integer"):
        compose_zdex_tokenomics_fee_allocation_lane_v1(candidate)


def test_post_construction_occurrence_mutation_is_revalidated_before_hashing() -> None:
    # Arrange
    candidate = _candidate()
    object.__setattr__(candidate.allocation.occurrence, "schema", "wrong-schema")

    # Act / Assert
    with pytest.raises(ValueError, match="schema"):
        compose_zdex_tokenomics_fee_allocation_lane_v1(candidate)


def test_target_is_found_inside_the_maximal_fee_asset_registry() -> None:
    # Arrange
    candidate = _candidate()
    pre_states = tuple(
        candidate.allocation.pre_state
        if ordinal == 40
        else _fee_state(ordinal, _root(100 + ordinal))
        for ordinal in range(1, 65)
    )
    post_states = tuple(
        candidate.allocation.post_state
        if ordinal == 40
        else _fee_state(ordinal, _root(100 + ordinal))
        for ordinal in range(1, 65)
    )
    maximal = replace(
        candidate,
        pre_state=replace(candidate.pre_state, fee_allocation_states=pre_states),
        post_state=replace(candidate.post_state, fee_allocation_states=post_states),
    )

    # Act
    result = compose_zdex_tokenomics_fee_allocation_lane_v1(maximal)

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionAcceptedV1
    assert len(result.post_state.fee_allocation_states) == 64


@pytest.mark.parametrize(
    ("field_name", "replacement", "expected_code"),
    (
        ("chain_id", "other-chain", ZDEXTokenomicsLaneCoordinatorRejectCodeV1.CHAIN_MISMATCH),
        ("deployment_root", _root(71), ZDEXTokenomicsLaneCoordinatorRejectCodeV1.DEPLOYMENT_MISMATCH),
        ("profile_root", _root(72), ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PROFILE_MISMATCH),
        ("writer_epoch", 12, ZDEXTokenomicsLaneCoordinatorRejectCodeV1.WRITER_EPOCH_MISMATCH),
        ("tokenomics_module_release_id", _root(73), ZDEXTokenomicsLaneCoordinatorRejectCodeV1.MODULE_RELEASE_MISMATCH),
        ("command_occurrence_id", _root(74), ZDEXTokenomicsLaneCoordinatorRejectCodeV1.OCCURRENCE_MISMATCH),
        ("allocation_route_release_id", _root(75), ZDEXTokenomicsLaneCoordinatorRejectCodeV1.ROUTE_RELEASE_MISMATCH),
        ("authorized_buyback_route_release_id", _root(76), ZDEXTokenomicsLaneCoordinatorRejectCodeV1.ROUTE_RELEASE_MISMATCH),
        ("policy_root", _root(77), ZDEXTokenomicsLaneCoordinatorRejectCodeV1.FEE_ALLOCATION_OCCURRENCE_MISMATCH),
    ),
)
def test_each_context_binding_substitution_is_a_typed_no_effect_rejection(
    field_name: str,
    replacement: object,
    expected_code: ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
) -> None:
    # Arrange
    candidate = _candidate()
    context = replace(candidate.context, **{field_name: replacement})

    # Act
    result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, context=context)
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert result.code is expected_code
    assert result.pre_lane_root == result.post_lane_root == candidate.pre_state.state_root
    assert result.effects.is_empty


def test_private_port_terminal_and_effect_commitment_substitutions_reject() -> None:
    # Arrange
    candidate = _candidate()
    wrong_port = replace(candidate.private_port, allocation_occurrence_root=_root(81))
    wrong_terminal = replace(candidate.module_journal, terminal_obligations_root=_root(82))
    wrong_effect = replace(candidate.module_journal, effect_plan_root=_root(83))

    # Act
    port_result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, private_port=wrong_port)
    )
    terminal_result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, module_journal=wrong_terminal)
    )
    effect_result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        replace(candidate, module_journal=wrong_effect)
    )

    # Assert
    assert type(port_result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert port_result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.PRIVATE_PORT_MISMATCH
    assert type(terminal_result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert terminal_result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.TERMINAL_OBLIGATION_MISMATCH
    assert type(effect_result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert effect_result.code is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.EFFECT_PLAN_MISMATCH
    assert port_result.effects.is_empty
    assert terminal_result.effects.is_empty
    assert effect_result.effects.is_empty
