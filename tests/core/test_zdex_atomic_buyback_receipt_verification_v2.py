"""Authenticated receipt-binding evidence for the buyback successor leaves."""

from __future__ import annotations

from dataclasses import dataclass, replace

import pytest

from src.core.economic_receipt_verifier_deployment_v1 import (
    BoundEconomicReceiptVerifierV1,
    bind_economic_receipt_verifier_deployment_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierReleaseV1,
    EconomicReceiptVerifierSelectionPurposeV1,
)
from src.core.global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    LaneCoordinatorRegistryV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    LaneStateRootV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
)
from src.core.zdex_atomic_buyback_receipt_verification_v2 import (
    VerifiedZDEXSpotBuybackLeafV2,
    VerifiedZDEXTokenomicsBuybackLeafV2,
    ZDEXSpotBuybackReceiptCandidateV2,
    ZDEXTokenomicsBuybackReceiptCandidateV2,
    snapshot_verified_zdex_spot_buyback_leaf_v2,
    snapshot_verified_zdex_tokenomics_buyback_leaf_v2,
    verify_governed_zdex_spot_buyback_receipt_shadow_v2,
    verify_governed_zdex_tokenomics_buyback_receipt_shadow_v2,
)
from src.core.zdex_atomic_buyback_route_types_v2 import (
    ZDEX_SPOT_BUYBACK_LEAF_ROLE_V2,
    ZDEX_TOKENOMICS_BUYBACK_LEAF_ROLE_V2,
    zdex_spot_buyback_leaf_port_schema_root_v2,
    zdex_tokenomics_buyback_leaf_port_schema_root_v2,
)
from src.core.zdex_buyback_price_safety_v1 import (
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
)
from src.core.zdex_buyback_spend_v1 import ZDEX_BUYBACK_SPEND_POLICY_KIND_V1
from src.core.zdex_fee_allocation_types_v1 import (
    FEE_BUYBACK_PRINCIPAL_V1,
    FEE_INGRESS_CONTROL_DOMAIN_V1,
    FEE_INGRESS_PRINCIPAL_V1,
    ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneReceiptEnvelopeV1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    zdex_pool_reserve_principal_v1,
)
from src.core.zdex_spot_buyback_transition_v1 import (
    ZDEXSpotPoolCreationReleaseV1,
)
from src.core.zdex_spot_buyback_transition_v2 import (
    ZDEXSpotBuybackAcceptedV2,
    transition_zdex_spot_buyback_v2,
)
from src.core.zdex_tokenomics_buyback_transition_v1 import (
    ZDEXTokenomicsBuybackIntentInputV1,
    ZDEXTokenomicsBuybackIntentV1,
    ZDEXTokenomicsBuybackReleaseV1,
    ZDEXTokenomicsProfileAuthorizationV1,
    derive_zdex_tokenomics_buyback_intent_v1,
)
from src.core.zdex_tokenomics_buyback_transition_v2 import (
    ZDEXTokenomicsBuybackAcceptedV2,
    ZDEXTokenomicsBuybackInputV2,
    transition_zdex_tokenomics_buyback_v2,
)
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _VERIFIER_ARTIFACT,
    _VERIFIER_EVIDENCE,
    _coordinator_release,
    _lane_release,
    _RecordingVerifier,
    _root,
    _verifier_manifest,
)
from tests.core.test_zdex_spot_buyback_transition_v2 import (
    _candidate as _spot_candidate,
)
from tests.core.test_zdex_spot_buyback_transition_v2 import _rebind as _spot_rebind
from tests.core.test_zdex_spot_buyback_transition_v2 import (
    _stable_authority as _spot_authority,
)
from tests.core.test_zdex_tokenomics_buyback_transition_v1 import (
    _authority as _tokenomics_authority,
)
from tests.core.test_zdex_tokenomics_buyback_transition_v1 import _intent_input


@dataclass(frozen=True, slots=True)
class _Fixture:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    route: RouteReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    global_pre_state: GlobalEconomicStateV1
    spot_release: LaneModuleReleaseV1
    tokenomics_release: LaneModuleReleaseV1
    authority_head: GlobalEconomicAuthorityHeadV1
    receipt_verifier: BoundEconomicReceiptVerifierV1
    backend: _RecordingVerifier
    spot: ZDEXSpotBuybackAcceptedV2
    tokenomics: ZDEXTokenomicsBuybackAcceptedV2


def _fixture() -> _Fixture:
    base_intent = _intent_input()
    base_tokenomics_authority = _tokenomics_authority(base_intent)
    releases = tuple(
        _lane_release(lane_id, ordinal)
        for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )
    release_by_lane = {release.lane_id: release for release in releases}
    spot_release = release_by_lane[LaneIdV1.SPOT_LIQUIDITY]
    tokenomics_release = release_by_lane[LaneIdV1.ZDEX_TOKENOMICS]
    policy_registry = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (
                    EconomicPolicyBindingV1(
                        ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        base_tokenomics_authority.execution_policy.policy_root,
                    ),
                    EconomicPolicyBindingV1(
                        ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        base_tokenomics_authority.price_policy_root,
                    ),
                    EconomicPolicyBindingV1(
                        ZDEX_BUYBACK_SPEND_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        base_tokenomics_authority.spend_policy.policy_root,
                    ),
                    EconomicPolicyBindingV1(
                        ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        base_tokenomics_authority.fee_policy.policy_root,
                    ),
                ),
                key=lambda row: (row.policy_kind, row.command_kind),
            )
        )
    )
    route = RouteReleaseV1.build(
        semantic_version="2.0.0-shadow-buyback-successor-test",
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS),
        module_release_ids=(spot_release.release_id, tokenomics_release.release_id),
        dependency_roles=(
            ZDEX_SPOT_BUYBACK_LEAF_ROLE_V2,
            ZDEX_TOKENOMICS_BUYBACK_LEAF_ROLE_V2,
        ),
        port_schema_roots=(
            zdex_spot_buyback_leaf_port_schema_root_v2(),
            zdex_tokenomics_buyback_leaf_port_schema_root_v2(),
        ),
        guest_image_id=_root(20_001),
        specification_root=_root(20_002),
        source_root=_root(20_003),
        toolchain_root=_root(20_004),
        oracle_policy_root=base_tokenomics_authority.price_policy_root,
        issue_burn_policy_root=(
            base_tokenomics_authority.hyperdeflation_policy.policy_root
        ),
        max_cycles=2_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )
    verifier_manifest = _verifier_manifest()
    verifier_release = EconomicReceiptVerifierReleaseV1.build(
        semantic_version="3.0.6-shadow-buyback-successor-test",
        proof_system=verifier_manifest.proof_system,
        implementation_root=verifier_manifest.implementation_root,
        receipt_schema_root=verifier_manifest.receipt_schema_root,
        journal_schema_root=verifier_manifest.journal_schema_root,
        root_image_id=verifier_manifest.root_image_id,
        specification_root=verifier_manifest.specification_root,
        source_root=verifier_manifest.source_root,
        toolchain_root=verifier_manifest.toolchain_root,
        evidence_manifest_root=verifier_manifest.manifest_root,
        backend_protocol_root=verifier_manifest.backend_protocol_root,
        max_receipt_bytes=verifier_manifest.max_receipt_bytes,
        max_journal_bytes=verifier_manifest.max_journal_bytes,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_receipts=False,
        evidence_statuses=_VERIFIER_EVIDENCE,
    )
    verifier_registry = EconomicReceiptVerifierRegistryV1((verifier_release,))
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=11,
        lane_registry=LaneRegistryV1(releases),
        lane_coordinator_registry=LaneCoordinatorRegistryV1(
            tuple(
                _coordinator_release(lane_id, ordinal)
                for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
            )
        ),
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(20_010),
        root_image_id=verifier_manifest.root_image_id,
        verifier_registry_root=verifier_registry.registry_root,
        migration_registry_root=_root(20_011),
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=_root(20_012),
        status=ProfileStatusV1.SHADOW,
    )
    base_spot = _spot_candidate()
    base_spot_authority = _spot_authority(base_spot)
    assert (
        base_spot_authority.execution_policy.policy_root
        == base_tokenomics_authority.execution_policy.policy_root
    )
    spot_state = replace(
        base_spot.pre_state,
        pools=(
            replace(
                base_spot.pre_state.pools[0],
                creation_release_id=spot_release.release_id,
            ),
        ),
    )
    global_pre_state = GlobalEconomicStateV1(
        chain_id=base_tokenomics_authority.chain_id,
        deployment_root=base_tokenomics_authority.deployment_root,
        writer_epoch=profile.authority_epoch,
        height=76,
        profile_root=profile.profile_id,
        lane_roots=tuple(
            LaneStateRootV1(
                release.lane_id,
                release.release_id,
                False,
                (
                    spot_state.state_root
                    if release.lane_id is LaneIdV1.SPOT_LIQUIDITY
                    else base_intent.pre_state.state_root
                    if release.lane_id is LaneIdV1.ZDEX_TOKENOMICS
                    else _root(30_000 + ordinal)
                ),
            )
            for ordinal, release in enumerate(releases, start=1)
        ),
        custody=tuple(
            sorted(
                (
                    EconomicAmountV1(
                        FEE_INGRESS_PRINCIPAL_V1,
                        base_tokenomics_authority.execution_policy.quote_asset_id,
                        FEE_INGRESS_CONTROL_DOMAIN_V1,
                        125,
                    ),
                    EconomicAmountV1(
                        FEE_BUYBACK_PRINCIPAL_V1,
                        base_tokenomics_authority.execution_policy.quote_asset_id,
                        PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
                        100,
                    ),
                    EconomicAmountV1(
                        zdex_pool_reserve_principal_v1(
                            pool_id=base_tokenomics_authority.execution_policy.pool_id,
                            asset_id=(
                                base_tokenomics_authority.execution_policy.quote_asset_id
                            ),
                        ),
                        base_tokenomics_authority.execution_policy.quote_asset_id,
                        AMM_POOL_CUSTODY_DOMAIN_V1,
                        1_000,
                    ),
                    EconomicAmountV1(
                        "account:quote-holder",
                        base_tokenomics_authority.execution_policy.quote_asset_id,
                        "zenoledger:account",
                        8_775,
                    ),
                    EconomicAmountV1(
                        zdex_pool_reserve_principal_v1(
                            pool_id=base_tokenomics_authority.execution_policy.pool_id,
                            asset_id=(
                                base_tokenomics_authority.execution_policy.zdex_asset_id
                            ),
                        ),
                        base_tokenomics_authority.execution_policy.zdex_asset_id,
                        AMM_POOL_CUSTODY_DOMAIN_V1,
                        1_000,
                    ),
                ),
                key=lambda row: row.key,
            )
        ),
        supplies=(
            AssetSupplyV1(
                base_tokenomics_authority.execution_policy.quote_asset_id,
                10_000,
            ),
            AssetSupplyV1(
                base_tokenomics_authority.execution_policy.zdex_asset_id,
                1_000,
            ),
        ),
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=global_pre_state.chain_id,
        deployment_root=global_pre_state.deployment_root,
        height=77,
        tx_index=2,
        op_index=1,
        command_kind=route.command_kind,
        command_body_hash=_root(20_020),
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(20_021),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=global_pre_state.state_root,
        consumed_object_ids=(),
    )
    tokenomics_release_value = ZDEXTokenomicsBuybackReleaseV1(
        tokenomics_release.release_id,
        spot_release.release_id,
        route.route_release_id,
        64,
    )
    tokenomics_profile = ZDEXTokenomicsProfileAuthorizationV1(
        profile.profile_id,
        occurrence.chain_id,
        occurrence.deployment_root,
        route.route_release_id,
        spot_release.release_id,
        tokenomics_release.release_id,
        tokenomics_release_value.release_root,
        base_tokenomics_authority.execution_policy.policy_root,
        base_tokenomics_authority.fee_policy.policy_root,
        base_tokenomics_authority.spend_policy.policy_root,
        base_tokenomics_authority.hyperdeflation_policy.policy_root,
        base_tokenomics_authority.price_policy_root,
    )
    rebound_tokenomics_authority = replace(
        base_tokenomics_authority,
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        profile_authorization_root=tokenomics_profile.authorization_root,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        global_pre_state_root=occurrence.pre_state_root,
        tokenomics_pre_state_root=base_intent.pre_state.state_root,
        writer_epoch=profile.authority_epoch,
        current_height=occurrence.height,
        spot_module_release_id=spot_release.release_id,
        tokenomics_module_release_id=tokenomics_release.release_id,
        release=tokenomics_release_value,
        profile_authorization=tokenomics_profile,
    )
    rebound_safe_limit = replace(
        base_intent.safe_limit_port,
        profile_root=occurrence.profile_root,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        global_pre_state_root=occurrence.pre_state_root,
        tokenomics_pre_state_root=base_intent.pre_state.state_root,
        current_height=occurrence.height,
    )
    intent_input = ZDEXTokenomicsBuybackIntentInputV1(
        rebound_tokenomics_authority,
        base_intent.pre_state,
        rebound_safe_limit,
    )
    intent = derive_zdex_tokenomics_buyback_intent_v1(intent_input)
    assert type(intent) is ZDEXTokenomicsBuybackIntentV1
    spot_release_value = replace(
        base_spot_authority.release,
        spot_module_release_id=spot_release.release_id,
        tokenomics_module_release_id=tokenomics_release.release_id,
        route_release_id=route.route_release_id,
        pool_creation_releases=(
            ZDEXSpotPoolCreationReleaseV1(
                spot_release.release_id,
                ReleaseStatusV1.ACTIVE_NEW,
            ),
        ),
    )
    spot_profile = replace(
        base_spot_authority.profile_authorization,
        profile_root=profile.profile_id,
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        route_release_id=route.route_release_id,
        spot_module_release_id=spot_release.release_id,
        tokenomics_module_release_id=tokenomics_release.release_id,
        release_root=spot_release_value.release_root,
    )
    rebound_spot_authority = replace(
        base_spot_authority,
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        profile_authorization_root=spot_profile.authorization_root,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        global_pre_state_root=occurrence.pre_state_root,
        spot_pre_state_root=spot_state.state_root,
        writer_epoch=profile.authority_epoch,
        current_height=occurrence.height,
        spot_module_release_id=spot_release.release_id,
        tokenomics_module_release_id=tokenomics_release.release_id,
        release=spot_release_value,
        profile_authorization=spot_profile,
    )
    spot_result = transition_zdex_spot_buyback_v2(
        _spot_rebind(
            base_spot,
            authority=rebound_spot_authority,
            pre_state=spot_state,
            quote_port=intent.quote_output,
        )
    )
    assert type(spot_result) is ZDEXSpotBuybackAcceptedV2
    tokenomics_result = transition_zdex_tokenomics_buyback_v2(
        ZDEXTokenomicsBuybackInputV2(intent_input, spot_result.terminal_obligation)
    )
    assert type(tokenomics_result) is ZDEXTokenomicsBuybackAcceptedV2
    backend = _RecordingVerifier()
    receipt_verifier = bind_economic_receipt_verifier_deployment_v1(
        profile=profile,
        verifier_registry=verifier_registry,
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
        evidence_manifest=verifier_manifest,
        measured_artifact_bytes=_VERIFIER_ARTIFACT,
        deployment_root=occurrence.deployment_root,
        backend=backend,
    )
    authority_head = GlobalEconomicAuthorityHeadV1(
        generation=0,
        activation_id=_root(20_030),
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        epoch_store_root=_root(20_031),
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        verifier_registry_root=verifier_registry.registry_root,
        verifier_release_id=verifier_release.release_id,
        verifier_binding_root=receipt_verifier.binding_root,
        root_image_id=profile.root_image_id,
        status=GlobalEconomicAuthorityStatusV1.ACTIVE,
    )
    return _Fixture(
        profile,
        policy_registry,
        route,
        occurrence,
        global_pre_state,
        spot_release,
        tokenomics_release,
        authority_head,
        receipt_verifier,
        backend,
        spot_result,
        tokenomics_result,
    )


def _verify_pair(
    fixture: _Fixture,
) -> tuple[VerifiedZDEXSpotBuybackLeafV2, VerifiedZDEXTokenomicsBuybackLeafV2]:
    spot = verify_governed_zdex_spot_buyback_receipt_shadow_v2(
        ZDEXSpotBuybackReceiptCandidateV2(
            fixture.route,
            fixture.spot_release,
            fixture.occurrence,
            fixture.spot,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"spot-v2-receipt"),
        ),
        profile=fixture.profile,
        policy_registry=fixture.policy_registry,
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )
    tokenomics = verify_governed_zdex_tokenomics_buyback_receipt_shadow_v2(
        ZDEXTokenomicsBuybackReceiptCandidateV2(
            fixture.route,
            fixture.tokenomics_release,
            fixture.occurrence,
            fixture.tokenomics,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"tokenomics-v2-receipt",
            ),
        ),
        profile=fixture.profile,
        policy_registry=fixture.policy_registry,
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )
    return spot, tokenomics


def test_verified_successor_leaf_witnesses_are_verifier_constructed() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXSpotBuybackLeafV2(object(), object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXTokenomicsBuybackLeafV2(object(), object())  # type: ignore[arg-type]


def test_object_new_cannot_forge_registered_successor_leaf_authority() -> None:
    forged_spot = object.__new__(VerifiedZDEXSpotBuybackLeafV2)
    forged_tokenomics = object.__new__(VerifiedZDEXTokenomicsBuybackLeafV2)
    with pytest.raises(TypeError, match="not registered"):
        _ = forged_spot.binding_root
    with pytest.raises(TypeError, match="not registered"):
        _ = forged_tokenomics.binding_root


def test_authenticated_successor_leaves_bind_one_occurrence_and_exact_journals() -> None:
    # Arrange
    fixture = _fixture()

    # Act
    verified_spot, verified_tokenomics = _verify_pair(fixture)
    spot_snapshot = snapshot_verified_zdex_spot_buyback_leaf_v2(verified_spot)
    tokenomics_snapshot = snapshot_verified_zdex_tokenomics_buyback_leaf_v2(
        verified_tokenomics
    )

    # Assert
    assert fixture.backend.calls == [
        (
            b"spot-v2-receipt",
            fixture.spot_release.guest_image_id,
            spot_snapshot.journal_bytes,
        ),
        (
            b"tokenomics-v2-receipt",
            fixture.tokenomics_release.guest_image_id,
            tokenomics_snapshot.journal_bytes,
        ),
    ]
    assert verified_spot.command_occurrence_id == fixture.occurrence.occurrence_id
    assert verified_tokenomics.command_occurrence_id == fixture.occurrence.occurrence_id
    assert verified_spot.route_release_id == fixture.route.route_release_id
    assert verified_tokenomics.route_release_id == fixture.route.route_release_id
    assert verified_spot.profile_root == fixture.profile.profile_id
    assert verified_tokenomics.profile_root == fixture.profile.profile_id
    assert verified_spot.authority_head_root == fixture.authority_head.authority_root
    assert (
        verified_tokenomics.authority_head_root
        == fixture.authority_head.authority_root
    )
    assert verified_spot.verifier_binding_root == fixture.receipt_verifier.binding_root
    assert (
        verified_tokenomics.verifier_binding_root
        == fixture.receipt_verifier.binding_root
    )
    assert (
        spot_snapshot.journal.context.coordinates.quote_port_root
        == tokenomics_snapshot.journal.quote_port_root
    )
    assert (
        spot_snapshot.journal.terminal_obligation_id
        == tokenomics_snapshot.journal.discharged_obligation_id
    )
    assert (
        spot_snapshot.journal.purchased_zdex_atoms
        == tokenomics_snapshot.journal.burned_zdex_atoms
    )


@pytest.mark.parametrize(
    "receipt_kind",
    (
        ReceiptKindV1.COMPOSITE,
        ReceiptKindV1.CONDITIONAL,
        ReceiptKindV1.FAKE,
        ReceiptKindV1.DEVELOPMENT,
    ),
)
def test_non_succinct_successor_receipts_reject_before_verifier(
    receipt_kind: ReceiptKindV1,
) -> None:
    # Arrange
    fixture = _fixture()
    candidate = ZDEXSpotBuybackReceiptCandidateV2(
        fixture.route,
        fixture.spot_release,
        fixture.occurrence,
        fixture.spot,
        ZDEXLaneReceiptEnvelopeV1(receipt_kind, b"invalid-kind"),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="succinct receipt"):
        verify_governed_zdex_spot_buyback_receipt_shadow_v2(
            candidate,
            profile=fixture.profile,
            policy_registry=fixture.policy_registry,
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert fixture.backend.calls == []


def test_wrong_route_role_rejects_before_receipt_verifier() -> None:
    # Arrange
    fixture = _fixture()
    wrong_route = RouteReleaseV1.build(
        semantic_version=fixture.route.semantic_version,
        command_kind=fixture.route.command_kind,
        ordered_lanes=fixture.route.ordered_lanes,
        module_release_ids=fixture.route.module_release_ids,
        dependency_roles=("WRONG_ROLE", fixture.route.dependency_roles[1]),
        port_schema_roots=fixture.route.port_schema_roots,
        guest_image_id=fixture.route.guest_image_id,
        specification_root=fixture.route.specification_root,
        source_root=fixture.route.source_root,
        toolchain_root=fixture.route.toolchain_root,
        oracle_policy_root=fixture.route.oracle_policy_root,
        issue_burn_policy_root=fixture.route.issue_burn_policy_root,
        max_cycles=fixture.route.max_cycles,
        max_journal_bytes=fixture.route.max_journal_bytes,
        status=fixture.route.status,
        accepts_new_objects=fixture.route.accepts_new_objects,
    )
    candidate = ZDEXSpotBuybackReceiptCandidateV2(
        wrong_route,
        fixture.spot_release,
        replace(fixture.occurrence, route_release_id=wrong_route.route_release_id),
        fixture.spot,
        ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"spot-v2-receipt"),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="dependency roles"):
        verify_governed_zdex_spot_buyback_receipt_shadow_v2(
            candidate,
            profile=fixture.profile,
            policy_registry=fixture.policy_registry,
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert fixture.backend.calls == []
