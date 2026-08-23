from __future__ import annotations

import hashlib
from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    ReceiptKindV1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    ZERO_ROOT_V1,
    EconomicProfileSnapshotV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
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
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXBurnReceiptCandidateV1,
    ZDEXLaneReceiptEnvelopeV1,
    verify_zdex_burn_receipt_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEXAMMPurchaseJournalV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)
from src.core.zdex_tokenomics_lane_coordinator_v1 import (
    ZDEXTokenomicsBurnLaneCandidateV1,
    compose_zdex_tokenomics_burn_lane_v1,
)
from src.core.zdex_tokenomics_lane_receipt_verification_v1 import (
    GovernedZDEXTokenomicsProfileV1,
    VerifiedZDEXTokenomicsLaneV1,
    ZDEXTokenomicsLaneReceiptCandidateV1,
    bind_zdex_tokenomics_shadow_profile_v1,
    verify_zdex_tokenomics_lane_receipt_v1,
)
from src.core.zdex_tokenomics_lane_v1 import (
    MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1,
    ZDEXTokenomicsBurnCoordinatorContextV1,
    ZDEXTokenomicsLaneCompositionAcceptedV1,
    ZDEXTokenomicsLaneCompositionRejectedV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1,
    build_zdex_tokenomics_burn_module_journal_v1,
    build_zdex_tokenomics_burn_private_port_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


class _HostileRoot(str):
    __hash__ = str.__hash__

    def to_canonical(self) -> str:
        return str(self)


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
    private_port = build_zdex_tokenomics_burn_private_port_v1(journal, effects)
    module_journal = build_zdex_tokenomics_burn_module_journal_v1(
        journal,
        effects,
        private_port,
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


def _lane_release(
    lane_id: LaneIdV1,
    ordinal: int,
    *,
    guest_image_id: str | None = None,
) -> LaneModuleReleaseV1:
    offset = ordinal * 16
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-test",
        state_schema_root=_root(100 + offset),
        command_variants=(PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,),
        terminal_command_variants=(),
        guest_image_id=guest_image_id or _root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _coordinator_release(
    lane_id: LaneIdV1,
    ordinal: int,
    *,
    max_journal_bytes: int = 65_536,
) -> LaneCoordinatorReleaseV1:
    offset = ordinal * 16
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-test",
        coordinator_schema_root=_root(700 + offset),
        guest_image_id=_root(701 + offset),
        specification_root=_root(702 + offset),
        source_root=_root(703 + offset),
        toolchain_root=_root(704 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=max_journal_bytes,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


class _Verifier:
    def __init__(self, *, reject: bool = False) -> None:
        self.reject = reject
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if self.reject:
            raise ValueError("test verifier rejection")


class _ExactVerifier:
    def __init__(self, receipt: bytes, image: str, journal: bytes) -> None:
        self.expected = (receipt, image, journal)
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        actual = (receipt_bytes, expected_image_id, expected_journal_bytes)
        self.calls.append(actual)
        if actual != self.expected:
            raise ValueError("tokenomics lane exact receipt binding mismatch")


def _receipt_fixture(
    *,
    tokenomics_max_journal_bytes: int = 65_536,
    tokenomics_guest_image_id: str | None = None,
) -> tuple[
    ZDEXTokenomicsLaneReceiptCandidateV1,
    GovernedZDEXTokenomicsProfileV1,
    EconomicProfileSnapshotV1,
]:
    base, _ = _candidate()
    releases = tuple(
        _lane_release(
            lane_id,
            ordinal,
            guest_image_id=(
                tokenomics_guest_image_id
                if lane_id is LaneIdV1.ZDEX_TOKENOMICS
                else None
            ),
        )
        for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )
    lane_registry = LaneRegistryV1(releases)
    tokenomics_release = lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS)
    spot_release = lane_registry.release_for(LaneIdV1.SPOT_LIQUIDITY)
    route = RouteReleaseV1.build(
        semantic_version="1.0.0-shadow-test",
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS),
        module_release_ids=(spot_release.release_id, tokenomics_release.release_id),
        dependency_roles=(AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1),
        port_schema_roots=(
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        ),
        guest_image_id=_root(500),
        specification_root=_root(501),
        source_root=_root(502),
        toolchain_root=_root(503),
        oracle_policy_root=_root(504),
        issue_burn_policy_root=base.pre_state.supply_state.policy_root,
        max_cycles=2_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )
    coordinator_registry = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(
                lane_id,
                ordinal,
                max_journal_bytes=(
                    tokenomics_max_journal_bytes
                    if lane_id is LaneIdV1.ZDEX_TOKENOMICS
                    else 65_536
                ),
            )
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=base.context.writer_epoch,
        lane_registry=lane_registry,
        lane_coordinator_registry=coordinator_registry,
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(810),
        root_image_id=_root(811),
        verifier_registry_root=_root(812),
        migration_registry_root=_root(813),
        policy_registry_root=_root(814),
        terminal_registry_root=_root(815),
        status=ProfileStatusV1.SHADOW,
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=base.context.chain_id,
        deployment_root=base.context.deployment_root,
        height=7,
        tx_index=2,
        op_index=1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        command_body_hash=_root(821),
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(820),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=_root(816),
        consumed_object_ids=(),
    )
    burn = replace(
        base.burn_journal,
        profile_root=profile.profile_id,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        tokenomics_module_release_id=tokenomics_release.release_id,
        effect_plan_root=_root(821),
    )
    effects = burn_effects_v1(burn)
    burn = replace(burn, effect_plan_root=effects.effect_plan_root)
    effects = burn_effects_v1(burn)
    port = build_zdex_tokenomics_burn_private_port_v1(burn, effects)
    module = build_zdex_tokenomics_burn_module_journal_v1(
        burn,
        effects,
        port,
    )
    tokenomics_coordinator = coordinator_registry.release_for(
        LaneIdV1.ZDEX_TOKENOMICS
    )
    context = replace(
        base.context,
        profile_root=profile.profile_id,
        coordinator_release_id=tokenomics_coordinator.coordinator_release_id,
        route_release_id=route.route_release_id,
        tokenomics_module_release_id=tokenomics_release.release_id,
        command_occurrence_id=occurrence.occurrence_id,
    )
    lane_candidate = replace(
        base,
        context=context,
        module_journal=module,
        private_port=port,
        burn_journal=burn,
        module_effects=effects,
    )
    governed = bind_zdex_tokenomics_shadow_profile_v1(
        expected_profile_id=profile.profile_id,
        expected_authority_epoch=profile.authority_epoch,
        profile=profile,
    )
    verified_burn = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1(
            route,
            tokenomics_release,
            occurrence,
            burn,
            effects,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"tokenomics-burn-leaf-receipt",
            ),
        ),
        _Verifier(),
    )
    return (
        ZDEXTokenomicsLaneReceiptCandidateV1(
            occurrence,
            lane_candidate,
            verified_burn,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"tokenomics-coordinator-receipt",
            ),
        ),
        governed,
        profile,
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
        "0x0b5ab6278d91be413bb56072a4210bd1a4b621d0379a85fe6e309cdd727471ca"
    )
    assert result.effects.effect_plan_root == (
        "0x211aa4aa89fb7f65b422adfb8d1d0549f85b2fdfd83d4222d8285baf7dd534bc"
    )
    assert result.lane_journal.journal_root == (
        "0x0f608f755e7fa941a454a49e4e92c86e1e5ca88589be2591a769d238b60ad6f3"
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


def test_module_receipt_commitment_substitution_rejects_without_effects() -> None:
    # Arrange
    candidate, _ = _candidate()
    forged_module = replace(candidate.module_journal, receipt_root=_root(99))

    # Act
    result = compose_zdex_tokenomics_burn_lane_v1(
        replace(candidate, module_journal=forged_module)
    )

    # Assert
    assert type(result) is ZDEXTokenomicsLaneCompositionRejectedV1
    assert (
        result.code
        is ZDEXTokenomicsLaneCoordinatorRejectCodeV1.MODULE_RECEIPT_MISMATCH
    )
    assert result.effects.is_empty


def test_verified_tokenomics_lane_witness_cannot_be_caller_constructed() -> None:
    # Arrange / Act / Assert
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXTokenomicsLaneV1(object(), object())


def test_release_selected_coordinator_receipt_binds_exact_lane_journal() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    verifier = _Verifier()
    recomputed = compose_zdex_tokenomics_burn_lane_v1(candidate.lane_candidate)
    assert type(recomputed) is ZDEXTokenomicsLaneCompositionAcceptedV1
    assert (
        candidate.occurrence.pre_state_root
        != candidate.lane_candidate.pre_state.state_root
    )

    # Act
    verified = verify_zdex_tokenomics_lane_receipt_v1(
        candidate,
        governed,
        verifier,
    )

    # Assert
    fields = governed._fields
    assert verifier.calls == [
        (
            candidate.receipt.receipt_bytes,
            fields.coordinator_release.guest_image_id,
            canonical_global_bytes_v1(recomputed.lane_journal),
        )
    ]
    assert verified.profile_root == fields.profile.profile_id
    assert verified.route_release_id == fields.route_release.route_release_id
    assert verified.module_release_id == fields.module_release.release_id
    assert verified.coordinator_release_id == (
        fields.coordinator_release.coordinator_release_id
    )
    assert verified.pre_lane_root == candidate.lane_candidate.pre_state.state_root
    assert verified.post_lane_root == candidate.lane_candidate.post_state.state_root
    assert verified.effect_plan_root == recomputed.effects.effect_plan_root
    assert verified.module_image_id == fields.module_release.guest_image_id
    assert verified.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified.binding_root == (
        "0x3d9398fda81e68baa95f537e08197e6474bbe9d5ecef562853d25888e1dbdd5f"
    )
    with pytest.raises(AttributeError, match="immutable"):
        verified._fields = object()


def test_burn_coordinator_callback_cannot_mutate_owned_witness_bindings() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    fields = governed._fields
    expected = (
        fields.coordinator_release.coordinator_release_id,
        fields.coordinator_release.guest_image_id,
        "0x" + hashlib.sha256(candidate.receipt.receipt_bytes).hexdigest(),
        candidate.receipt.receipt_kind,
    )

    class _MutatingVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(
                fields.coordinator_release,
                "coordinator_release_id",
                _root(78_501),
            )
            object.__setattr__(
                fields.coordinator_release,
                "guest_image_id",
                _root(78_502),
            )
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-lane")
            object.__setattr__(candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)

    # Act
    verified = verify_zdex_tokenomics_lane_receipt_v1(
        candidate,
        governed,
        _MutatingVerifier(),
    )

    # Assert
    assert (
        verified.coordinator_release_id,
        verified.expected_image_id,
        verified.receipt_digest,
        verified.receipt_kind,
    ) == expected


def test_burn_coordinator_rejects_hostile_release_scalar_before_callback() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    fields = governed._fields
    object.__setattr__(
        fields.module_release,
        "guest_image_id",
        _HostileRoot(fields.module_release.guest_image_id),
    )
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        verify_zdex_tokenomics_lane_receipt_v1(candidate, governed, verifier)
    assert verifier.calls == []


def test_burn_lane_unrelated_root_substitution_requires_new_exact_receipt() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    original = compose_zdex_tokenomics_burn_lane_v1(candidate.lane_candidate)
    assert type(original) is ZDEXTokenomicsLaneCompositionAcceptedV1
    verifier = _ExactVerifier(
        candidate.receipt.receipt_bytes,
        governed._fields.coordinator_release.guest_image_id,
        canonical_global_bytes_v1(original.lane_journal),
    )
    shifted_lane = replace(
        candidate.lane_candidate,
        pre_state=replace(
            candidate.lane_candidate.pre_state,
            staking_state_root=_root(999),
        ),
        post_state=replace(
            candidate.lane_candidate.post_state,
            staking_state_root=_root(999),
        ),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="exact receipt binding mismatch"):
        verify_zdex_tokenomics_lane_receipt_v1(
            replace(candidate, lane_candidate=shifted_lane),
            governed,
            verifier,
        )
    assert len(verifier.calls) == 1
    assert verifier.calls[0][2] != verifier.expected[2]


def test_profile_and_coordinator_substitutions_reject_before_receipt_verifier() -> None:
    # Arrange
    candidate, governed, profile = _receipt_fixture()
    verifier = _Verifier()
    wrong_context = replace(
        candidate.lane_candidate.context,
        coordinator_release_id=_root(999),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="candidate binding mismatch"):
        verify_zdex_tokenomics_lane_receipt_v1(
            replace(
                candidate,
                lane_candidate=replace(
                    candidate.lane_candidate,
                    context=wrong_context,
                ),
            ),
            governed,
            verifier,
        )
    with pytest.raises(ValueError, match="expected profile mismatch"):
        bind_zdex_tokenomics_shadow_profile_v1(
            expected_profile_id=_root(998),
            expected_authority_epoch=profile.authority_epoch,
            profile=profile,
        )
    with pytest.raises(ValueError, match="must remain SHADOW"):
        bind_zdex_tokenomics_shadow_profile_v1(
            expected_profile_id=profile.profile_id,
            expected_authority_epoch=profile.authority_epoch,
            profile=replace(profile, status=ProfileStatusV1.CANDIDATE),
        )
    with pytest.raises(ValueError, match="expected authority epoch mismatch"):
        bind_zdex_tokenomics_shadow_profile_v1(
            expected_profile_id=profile.profile_id,
            expected_authority_epoch=profile.authority_epoch + 1,
            profile=profile,
        )
    assert verifier.calls == []


@pytest.mark.parametrize("release_kind", ("module", "coordinator"))
def test_post_bind_release_image_mutation_rejects_before_receipt_verifier(
    release_kind: str,
) -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    verifier = _Verifier()
    release = (
        governed._fields.module_release
        if release_kind == "module"
        else governed._fields.coordinator_release
    )
    object.__setattr__(release, "guest_image_id", _root(995))

    # Act / Assert
    with pytest.raises(ValueError, match="content-derived"):
        verify_zdex_tokenomics_lane_receipt_v1(candidate, governed, verifier)
    assert verifier.calls == []


def test_rejected_lane_semantics_never_reach_receipt_verifier() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    verifier = _Verifier()
    invalid_post = replace(
        candidate.lane_candidate.post_state,
        staking_state_root=_root(997),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="composition rejected"):
        verify_zdex_tokenomics_lane_receipt_v1(
            replace(
                candidate,
                lane_candidate=replace(
                    candidate.lane_candidate,
                    post_state=invalid_post,
                ),
            ),
            governed,
            verifier,
        )
    assert verifier.calls == []


@pytest.mark.parametrize(
    "receipt",
    (
        ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional"),
        ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b""),
    ),
)
def test_non_authoritative_receipt_shapes_reject(
    receipt: ZDEXLaneReceiptEnvelopeV1,
) -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(ValueError):
        verify_zdex_tokenomics_lane_receipt_v1(
            replace(candidate, receipt=receipt),
            governed,
            verifier,
        )
    assert verifier.calls == []


def test_receipt_verifier_rejection_produces_no_witness() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    verifier = _Verifier(reject=True)

    # Act / Assert
    with pytest.raises(ValueError, match="test verifier rejection"):
        verify_zdex_tokenomics_lane_receipt_v1(candidate, governed, verifier)
    assert len(verifier.calls) == 1


def test_foreign_verified_burn_witness_rejects_before_coordinator_verifier() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture()
    foreign, _, _ = _receipt_fixture(tokenomics_guest_image_id=_root(996))
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(ValueError, match="candidate binding mismatch"):
        verify_zdex_tokenomics_lane_receipt_v1(
            replace(candidate, verified_burn=foreign.verified_burn),
            governed,
            verifier,
        )
    assert verifier.calls == []


def test_one_byte_coordinator_journal_ceiling_rejects_before_verifier() -> None:
    # Arrange
    candidate, governed, _ = _receipt_fixture(tokenomics_max_journal_bytes=1)
    verifier = _Verifier()

    # Act / Assert
    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        verify_zdex_tokenomics_lane_receipt_v1(candidate, governed, verifier)
    assert verifier.calls == []


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
    forged_module = build_zdex_tokenomics_burn_module_journal_v1(
        forged_burn,
        forged_effects,
        forged_port,
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
