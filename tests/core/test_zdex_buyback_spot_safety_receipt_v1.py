"""Adversarial evidence for the shadow ZDEX buyback Spot receipt boundary."""

from __future__ import annotations

import hashlib
from collections.abc import Callable
from dataclasses import dataclass, replace

import pytest

from src.core.economic_receipt_verifier_deployment_v1 import (
    BoundEconomicReceiptVerifierV1,
    EconomicReceiptVerifierEvidenceArtifactV1,
    EconomicReceiptVerifierEvidenceManifestV1,
    bind_economic_receipt_verifier_deployment_v1,
    economic_receipt_verifier_backend_protocol_root_v1,
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierEvidenceStatusV1,
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierReleaseV1,
    EconomicReceiptVerifierSelectionPurposeV1,
)
from src.core.global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    ReceiptKindV1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    LaneStateRootV1,
    OracleOccurrenceStateV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from src.core.zdex_atomic_buyback_state_v1 import (
    ZDEXAtomicBuybackTokenomicsStateV1,
    zdex_atomic_buyback_tokenomics_state_schema_root_v1,
)
from src.core.zdex_buyback_price_authority_v1 import (
    VerifiedZDEXBuybackPriceAuthorityV1,
    ZDEXBuybackPriceAuthorityCandidateV1,
    ZDEXBuybackPriceAuthorityRejectCodeV1,
    ZDEXBuybackPriceAuthorityRejectedV1,
    verify_zdex_buyback_price_authority_v1,
)
from src.core.zdex_buyback_price_safety_v1 import (
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1,
)
from src.core.zdex_buyback_spend_v1 import (
    ZDEX_BUYBACK_SPEND_POLICY_KIND_V1,
    ZDEXBuybackSpendPolicyV1,
    ZDEXBuybackSpendStateV1,
)
from src.core.zdex_buyback_spot_safety_receipt_v1 import (
    VerifiedZDEXBuybackSpotSafetyPurchaseV2,
    ZDEXBuybackSpotReceiptCandidateV2,
    ZDEXBuybackSpotReceiptEnvelopeV1,
    ZDEXBuybackSpotReceiptRejectCodeV1,
    ZDEXBuybackSpotReceiptRejectedV1,
    ZDEXBuybackSpotSafetyPurchaseJournalV2,
    verify_zdex_buyback_spot_safety_receipt_shadow_v2,
)
from src.core.zdex_fee_allocation_types_v1 import (
    ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
)
from src.core.zdex_hyperdeflation_types_v1 import (
    ZDEXAmountBucketV1,
    ZDEXHyperdeflationPolicyV1,
    ZDEXSupplyStateV1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
    zdex_pool_reserve_principal_v1,
)
from src.core.zdex_tokenomics_lane_v1 import ZDEXTokenomicsLaneStateV1


def _root(value: int) -> str:
    return f"0x{value:064x}"


class _HostileRoot(str):
    """Valid-looking scalar subclass rejected at the owned boundary."""


_VERIFIER_ARTIFACT = b"shadow-buyback-profile-bound-verifier"
_VERIFIER_EVIDENCE = tuple(
    sorted(
        (
            EconomicReceiptVerifierEvidenceStatusV1.SPECIFIED,
            EconomicReceiptVerifierEvidenceStatusV1.IMPLEMENTED,
            EconomicReceiptVerifierEvidenceStatusV1.TESTED,
            EconomicReceiptVerifierEvidenceStatusV1.SOURCE_PINNED,
            EconomicReceiptVerifierEvidenceStatusV1.TOOLCHAIN_PINNED,
        ),
        key=lambda status: status.value,
    )
)


def _verifier_manifest() -> EconomicReceiptVerifierEvidenceManifestV1:
    artifacts = tuple(
        EconomicReceiptVerifierEvidenceArtifactV1(status, _root(900 + index))
        for index, status in enumerate(_VERIFIER_EVIDENCE)
    )
    return EconomicReceiptVerifierEvidenceManifestV1(
        proof_system="RISC0_ZKVM_3_0_6",
        implementation_root=economic_receipt_verifier_implementation_root_v1(_VERIFIER_ARTIFACT),
        receipt_schema_root=_root(920),
        journal_schema_root=_root(921),
        root_image_id=_root(31),
        specification_root=_root(922),
        source_root=_root(923),
        toolchain_root=_root(924),
        backend_protocol_root=economic_receipt_verifier_backend_protocol_root_v1(),
        max_receipt_bytes=4096,
        max_journal_bytes=65_536,
        evidence_artifacts=artifacts,
    )


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    offset = ordinal * 32
    commands: tuple[str, ...] = ()
    if lane_id in {LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS}:
        commands = (PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,)
    state_schema_root = _root(1_000 + offset)
    if lane_id is LaneIdV1.ZDEX_TOKENOMICS:
        state_schema_root = zdex_atomic_buyback_tokenomics_state_schema_root_v1()
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-buyback-spot-test",
        state_schema_root=state_schema_root,
        command_variants=commands,
        terminal_command_variants=(),
        guest_image_id=_root(1_001 + offset),
        specification_root=_root(1_002 + offset),
        source_root=_root(1_003 + offset),
        toolchain_root=_root(1_004 + offset),
        terminal_coverage_root=_root(1_005 + offset),
        migration_compatibility_root=_root(1_006 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _coordinator_release(
    lane_id: LaneIdV1,
    ordinal: int,
) -> LaneCoordinatorReleaseV1:
    offset = ordinal * 32
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-shadow-buyback-spot-test",
        coordinator_schema_root=_root(2_000 + offset),
        guest_image_id=_root(2_001 + offset),
        specification_root=_root(2_002 + offset),
        source_root=_root(2_003 + offset),
        toolchain_root=_root(2_004 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


class _RecordingVerifier:
    def __init__(self) -> None:
        self.calls: list[tuple[bytes, str, bytes]] = []
        self.result: object = None
        self.error: Exception | None = None
        self.hook: object = None

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if callable(self.hook):
            self.hook(receipt_bytes, expected_image_id, expected_journal_bytes)
        if self.error is not None:
            raise self.error
        return self.result


@dataclass(frozen=True, slots=True)
class _Fixture:
    candidate: ZDEXBuybackSpotReceiptCandidateV2
    route: RouteReleaseV1
    spot_release: LaneModuleReleaseV1
    authority_head: GlobalEconomicAuthorityHeadV1
    receipt_verifier: BoundEconomicReceiptVerifierV1
    backend: _RecordingVerifier


def _fixture() -> _Fixture:
    policy = ZDEXBuybackExecutionPolicyV1(
        pool_id=_root(10),
        pool_definition_root=_root(11),
        quote_asset_id=_root(12),
        zdex_asset_id=_root(13),
    )
    fee_policy = candidate_zdex_fee_allocation_policy_v1()
    spend_policy = ZDEXBuybackSpendPolicyV1(policy.quote_asset_id, 1, 200, 1)
    price_policy = ZDEXBuybackPriceSafetyPolicyV1(
        oracle_id="zdex-buyback-oracle",
        maximum_oracle_age_blocks=3,
        minimum_quote_reserve_atoms=500,
        minimum_zdex_reserve_atoms=500,
        maximum_pool_oracle_deviation_bps=500,
        maximum_execution_impact_bps=1_300,
        maximum_oracle_execution_deviation_bps=1_500,
        maximum_quote_reserve_spend_bps=2_000,
    )
    quote_pool_principal = zdex_pool_reserve_principal_v1(
        pool_id=policy.pool_id,
        asset_id=policy.quote_asset_id,
    )
    zdex_pool_principal = zdex_pool_reserve_principal_v1(
        pool_id=policy.pool_id,
        asset_id=policy.zdex_asset_id,
    )
    fee_state = ZDEXFeeStateV1(
        policy.quote_asset_id,
        fee_policy.policy_root,
        125,
        0,
        tuple(
            ZDEXFeeDestinationAmountV1(
                destination,
                100 if destination is ZDEXFeeDestinationV1.BUYBACK else 0,
            )
            for destination in ZDEX_FEE_DESTINATIONS_V1
        ),
        10_000,
        10_000,
    )
    cadence = ZDEXBuybackSpendStateV1(
        policy.quote_asset_id,
        spend_policy.policy_root,
        None,
    )
    supply_policy = ZDEXHyperdeflationPolicyV1(policy.zdex_asset_id, 1, 10, 38, 8)
    tokenomics_pre_state = ZDEXAtomicBuybackTokenomicsStateV1(
        ZDEXTokenomicsLaneStateV1(
            ZDEXSupplyStateV1(
                policy.zdex_asset_id,
                supply_policy.policy_root,
                8,
                0,
                1_000,
                (ZDEXAmountBucketV1(zdex_pool_principal, 1_000),),
                0,
                500,
            ),
            (fee_state,),
            _root(800),
            _root(801),
            _root(802),
            _root(803),
            _root(804),
            _root(805),
        ),
        (cadence,),
    )
    releases = tuple(
        _lane_release(lane_id, ordinal) for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )
    release_by_lane = {release.lane_id: release for release in releases}
    spot_release = release_by_lane[LaneIdV1.SPOT_LIQUIDITY]
    tokenomics_release = release_by_lane[LaneIdV1.ZDEX_TOKENOMICS]
    route = RouteReleaseV1.build(
        semantic_version="1.0.0-shadow-buyback-spot-test",
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS),
        module_release_ids=(spot_release.release_id, tokenomics_release.release_id),
        dependency_roles=(AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1),
        port_schema_roots=(
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        ),
        guest_image_id=_root(20),
        specification_root=_root(21),
        source_root=_root(22),
        toolchain_root=_root(23),
        oracle_policy_root=price_policy.policy_root,
        issue_burn_policy_root=supply_policy.policy_root,
        max_cycles=2_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )
    policy_registry = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (
                    EconomicPolicyBindingV1(
                        ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        policy.policy_root,
                    ),
                    EconomicPolicyBindingV1(
                        ZDEX_BUYBACK_SPEND_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        spend_policy.policy_root,
                    ),
                    EconomicPolicyBindingV1(
                        ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        price_policy.policy_root,
                    ),
                    EconomicPolicyBindingV1(
                        ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
                        PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
                        fee_policy.policy_root,
                    ),
                ),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )
    verifier_manifest = _verifier_manifest()
    verifier_release = EconomicReceiptVerifierReleaseV1.build(
        semantic_version="3.0.6-shadow-buyback-test",
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
        proof_shape_root=_root(30),
        root_image_id=_root(31),
        verifier_registry_root=verifier_registry.registry_root,
        migration_registry_root=_root(33),
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=_root(34),
        status=ProfileStatusV1.SHADOW,
    )
    oracle_id = "zdex-buyback-oracle"
    oracle_occurrence_root = ZDEXBuybackOraclePriceOccurrenceV1(
        oracle_id=oracle_id,
        quote_asset_id=policy.quote_asset_id,
        zdex_asset_id=policy.zdex_asset_id,
        quote_numerator_atoms=1,
        zdex_denominator_atoms=1,
        observed_height=76,
    ).occurrence_root
    global_pre_state = GlobalEconomicStateV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(40),
        writer_epoch=profile.authority_epoch,
        height=76,
        profile_root=profile.profile_id,
        lane_roots=tuple(
            LaneStateRootV1(
                release.lane_id,
                release.release_id,
                False,
                (
                    _root(50)
                    if release.lane_id is LaneIdV1.SPOT_LIQUIDITY
                    else tokenomics_pre_state.state_root
                    if release.lane_id is LaneIdV1.ZDEX_TOKENOMICS
                    else _root(5_000 + ordinal)
                ),
            )
            for ordinal, release in enumerate(releases, start=1)
        ),
        oracle_occurrences=(OracleOccurrenceStateV1(oracle_id, oracle_occurrence_root, 76, True),),
        custody=tuple(
            sorted(
                (
                    EconomicAmountV1(
                        "protocol:fee-ingress",
                        policy.quote_asset_id,
                        "zenoledger:protocol-fee-ingress",
                        125,
                    ),
                    EconomicAmountV1(
                        "protocol-fee-buyback-reserve",
                        policy.quote_asset_id,
                        "zenoledger:protocol-buyback",
                        100,
                    ),
                    EconomicAmountV1(
                        quote_pool_principal,
                        policy.quote_asset_id,
                        AMM_POOL_CUSTODY_DOMAIN_V1,
                        1_000,
                    ),
                    EconomicAmountV1(
                        "account:quote-holder",
                        policy.quote_asset_id,
                        "zenoledger:account",
                        8_775,
                    ),
                    EconomicAmountV1(
                        zdex_pool_principal,
                        policy.zdex_asset_id,
                        AMM_POOL_CUSTODY_DOMAIN_V1,
                        1_000,
                    ),
                ),
                key=lambda row: row.key,
            )
        ),
        supplies=tuple(
            sorted(
                (
                    AssetSupplyV1(policy.quote_asset_id, 10_000),
                    AssetSupplyV1(policy.zdex_asset_id, 1_000),
                ),
                key=lambda row: row.asset,
            )
        ),
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(40),
        height=77,
        tx_index=2,
        op_index=1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        command_body_hash=_root(41),
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(42),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=global_pre_state.state_root,
        consumed_object_ids=(oracle_occurrence_root,),
    )
    fee_context = ZDEXFeeAllocationContextV1(
        occurrence.chain_id,
        occurrence.deployment_root,
        occurrence.profile_root,
        profile.authority_epoch,
        occurrence.route_release_id,
        occurrence.route_release_id,
        tokenomics_release.release_id,
        occurrence.occurrence_id,
        fee_policy.policy_root,
    )
    fee_command = ZDEXFeeAllocationCommandV1(125)
    expected_spot_pre_root = _root(50)
    journal = ZDEXBuybackSpotSafetyPurchaseJournalV2(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        global_pre_state_root=occurrence.pre_state_root,
        spot_module_release_id=spot_release.release_id,
        spot_guest_image_id=spot_release.guest_image_id,
        tokenomics_module_release_id=tokenomics_release.release_id,
        tokenomics_pre_state_root=tokenomics_pre_state.state_root,
        spend_policy_root=spend_policy.policy_root,
        fee_policy_root=fee_policy.policy_root,
        fee_pre_state_root=fee_state.state_root,
        cadence_pre_state_root=cadence.state_root,
        fee_context_root=hash_global_v1(
            "zdex-fee-allocation-context-v1",
            fee_context.to_canonical(),
        ),
        fee_command_root=hash_global_v1(
            "zdex-fee-allocation-command-v1",
            {"fee_charged_atoms": fee_command.fee_charged_atoms},
        ),
        pre_spot_lane_root=expected_spot_pre_root,
        post_spot_lane_root=_root(51),
        pool_id=policy.pool_id,
        pool_definition_root=policy.pool_definition_root,
        quote_asset_id=policy.quote_asset_id,
        zdex_asset_id=policy.zdex_asset_id,
        oracle_policy_root=route.oracle_policy_root,
        oracle_id=oracle_id,
        oracle_occurrence_root=oracle_occurrence_root,
        oracle_observed_height=76,
        oracle_quote_numerator_atoms=1,
        oracle_zdex_denominator_atoms=1,
        quote_reserve_atoms=1_000,
        zdex_reserve_atoms=1_000,
        consensus_height=occurrence.height,
        route_safe_quote_limit_atoms=200,
        quote_amount_in_atoms=125,
        minimum_output_atoms=109,
        purchased_zdex_atoms=111,
    )
    candidate = ZDEXBuybackSpotReceiptCandidateV2(
        profile=profile,
        policy_registry=policy_registry,
        buyback_policy=policy,
        spend_policy=spend_policy,
        price_policy=price_policy,
        fee_policy=fee_policy,
        fee_context=fee_context,
        fee_command=fee_command,
        occurrence=occurrence,
        global_pre_state=global_pre_state,
        tokenomics_pre_state=tokenomics_pre_state,
        journal=journal,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(
            ReceiptKindV1.SUCCINCT,
            b"succinct-buyback-spot-receipt",
        ),
    )
    backend = _RecordingVerifier()
    bound_verifier = bind_economic_receipt_verifier_deployment_v1(
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
        activation_id=_root(930),
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        epoch_store_root=_root(931),
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        verifier_registry_root=verifier_registry.registry_root,
        verifier_release_id=verifier_release.release_id,
        verifier_binding_root=bound_verifier.binding_root,
        root_image_id=profile.root_image_id,
        status=GlobalEconomicAuthorityStatusV1.ACTIVE,
    )
    return _Fixture(
        candidate,
        route,
        spot_release,
        authority_head,
        bound_verifier,
        backend,
    )


def test_fee_ingress_amount_is_derived_from_committed_tokenomics_state() -> None:
    # Arrange
    fixture = _fixture()

    # Act
    verified = _verify(fixture)

    # Assert
    assert verified.fee_ingress.fee_ingress_atoms == 125
    assert verified.fee_ingress.fee_asset_id == fixture.candidate.journal.quote_asset_id
    assert verified.fee_command.fee_charged_atoms == 125


def test_caller_selected_fee_budget_rejects_before_receipt_callback() -> None:
    # Arrange
    fixture = _fixture()
    substituted_command = ZDEXFeeAllocationCommandV1(124)
    substituted_journal = replace(
        fixture.candidate.journal,
        fee_command_root=hash_global_v1(
            "zdex-fee-allocation-command-v1",
            {"fee_charged_atoms": substituted_command.fee_charged_atoms},
        ),
    )
    candidate = replace(
        fixture.candidate,
        fee_command=substituted_command,
        journal=substituted_journal,
    )

    # Act / Assert
    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as rejected:
        verify_zdex_buyback_spot_safety_receipt_shadow_v2(
            candidate,
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert rejected.value.code is ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH
    assert fixture.backend.calls == []


def _verify(
    fixture: _Fixture,
    candidate: ZDEXBuybackSpotReceiptCandidateV2 | None = None,
) -> VerifiedZDEXBuybackSpotSafetyPurchaseV2:
    return verify_zdex_buyback_spot_safety_receipt_shadow_v2(
        candidate or fixture.candidate,
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )


def _price_occurrence(
    fixture: _Fixture,
) -> ZDEXBuybackOraclePriceOccurrenceV1:
    journal = fixture.candidate.journal
    return ZDEXBuybackOraclePriceOccurrenceV1(
        oracle_id=journal.oracle_id,
        quote_asset_id=journal.quote_asset_id,
        zdex_asset_id=journal.zdex_asset_id,
        quote_numerator_atoms=journal.oracle_quote_numerator_atoms,
        zdex_denominator_atoms=journal.oracle_zdex_denominator_atoms,
        observed_height=journal.oracle_observed_height,
    )


def _price_authority_candidate(
    fixture: _Fixture,
) -> ZDEXBuybackPriceAuthorityCandidateV1:
    journal = fixture.candidate.journal
    return ZDEXBuybackPriceAuthorityCandidateV1(
        pre_state=fixture.candidate.global_pre_state,
        route=fixture.route,
        occurrence=fixture.candidate.occurrence,
        execution_policy=fixture.candidate.buyback_policy,
        price_policy=fixture.candidate.price_policy,
        price_occurrence=_price_occurrence(fixture),
        route_safe_quote_limit_atoms=journal.route_safe_quote_limit_atoms,
        minimum_output_atoms=journal.minimum_output_atoms,
        expected_quote_reserve_atoms=journal.quote_reserve_atoms,
        expected_zdex_reserve_atoms=journal.zdex_reserve_atoms,
        quote_amount_in_atoms=journal.quote_amount_in_atoms,
        purchased_zdex_atoms=journal.purchased_zdex_atoms,
    )


def _with_price_authority_pre_state(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
    pre_state: GlobalEconomicStateV1,
) -> ZDEXBuybackPriceAuthorityCandidateV1:
    return replace(
        candidate,
        pre_state=pre_state,
        occurrence=replace(
            candidate.occurrence,
            pre_state_root=pre_state.state_root,
        ),
    )


def _unfinalized_oracle_mutant(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
) -> ZDEXBuybackPriceAuthorityCandidateV1:
    pre_state = replace(
        candidate.pre_state,
        oracle_occurrences=tuple(
            replace(occurrence, finalized=False)
            for occurrence in candidate.pre_state.oracle_occurrences
        ),
    )
    return _with_price_authority_pre_state(candidate, pre_state)


def _future_oracle_mutant(
    candidate: ZDEXBuybackPriceAuthorityCandidateV1,
) -> ZDEXBuybackPriceAuthorityCandidateV1:
    price_occurrence = replace(
        candidate.price_occurrence,
        observed_height=candidate.occurrence.height + 1,
    )
    pre_state = replace(
        candidate.pre_state,
        oracle_occurrences=(
            replace(
                candidate.pre_state.oracle_occurrences[0],
                occurrence_root=price_occurrence.occurrence_root,
                observed_height=price_occurrence.observed_height,
            ),
        ),
    )
    rebound = _with_price_authority_pre_state(candidate, pre_state)
    return replace(
        rebound,
        occurrence=replace(
            rebound.occurrence,
            consumed_object_ids=(price_occurrence.occurrence_root,),
        ),
        price_occurrence=price_occurrence,
    )


def test_price_authority_binds_exact_committed_state_oracle_and_policy() -> None:
    # Arrange
    fixture = _fixture()
    candidate = _price_authority_candidate(fixture)

    # Act
    verified = verify_zdex_buyback_price_authority_v1(candidate)

    # Assert
    assert verified.pre_state_root == fixture.candidate.global_pre_state.state_root
    assert verified.command_occurrence_id == fixture.candidate.occurrence.occurrence_id
    assert verified.execution_policy_root == fixture.candidate.buyback_policy.policy_root
    assert verified.price_policy_root == fixture.candidate.price_policy.policy_root
    assert verified.price_occurrence_root == candidate.price_occurrence.occurrence_root
    assert verified.price_safety_binding_root == verified.price_safety.binding_root
    assert verified.authority_root.startswith("0x")
    assert len(verified.authority_root) == 66


def test_price_authority_witness_is_verifier_constructed_and_immutable() -> None:
    # Arrange
    fixture = _fixture()
    candidate = _price_authority_candidate(fixture)
    verified = verify_zdex_buyback_price_authority_v1(candidate)
    stable_root = verified.authority_root

    # Act / Assert
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXBuybackPriceAuthorityV1(object(), object())  # type: ignore[arg-type]
    with pytest.raises(AttributeError, match="immutable"):
        verified._fields = object()  # type: ignore[assignment]
    object.__setattr__(candidate.execution_policy, "pool_id", _root(80_001))
    assert verified.authority_root == stable_root


def test_price_authority_rejects_hostile_scalar_after_candidate_construction() -> None:
    # Arrange
    fixture = _fixture()
    candidate = _price_authority_candidate(fixture)
    object.__setattr__(
        candidate.pre_state,
        "deployment_root",
        _HostileRoot(candidate.pre_state.deployment_root),
    )

    # Act / Assert
    with pytest.raises(TypeError, match="exact primitive"):
        verify_zdex_buyback_price_authority_v1(candidate)


@pytest.mark.parametrize(
    ("mutate", "expected_code"),
    (
        (
            lambda candidate: replace(
                candidate,
                occurrence=replace(candidate.occurrence, consumed_object_ids=()),
            ),
            ZDEXBuybackPriceAuthorityRejectCodeV1.CONTEXT_MISMATCH,
        ),
        (
            lambda candidate: replace(
                candidate,
                expected_quote_reserve_atoms=(
                    candidate.expected_quote_reserve_atoms - 1
                ),
            ),
            ZDEXBuybackPriceAuthorityRejectCodeV1.RESERVE_AMOUNT_MISMATCH,
        ),
        (
            _unfinalized_oracle_mutant,
            ZDEXBuybackPriceAuthorityRejectCodeV1.ORACLE_AUTHORITY_MISMATCH,
        ),
        (
            _future_oracle_mutant,
            ZDEXBuybackPriceAuthorityRejectCodeV1.ORACLE_AUTHORITY_MISMATCH,
        ),
    ),
)
def test_price_authority_mutants_reject_before_witness_creation(
    mutate: Callable[
        [ZDEXBuybackPriceAuthorityCandidateV1],
        ZDEXBuybackPriceAuthorityCandidateV1,
    ],
    expected_code: ZDEXBuybackPriceAuthorityRejectCodeV1,
) -> None:
    # Arrange
    fixture = _fixture()
    candidate = _price_authority_candidate(fixture)
    mutant = mutate(candidate)

    # Act / Assert
    with pytest.raises(ZDEXBuybackPriceAuthorityRejectedV1) as rejected:
        verify_zdex_buyback_price_authority_v1(mutant)
    assert rejected.value.code is expected_code


def _assert_reject(
    fixture: _Fixture,
    candidate: ZDEXBuybackSpotReceiptCandidateV2,
    expected_code: ZDEXBuybackSpotReceiptRejectCodeV1,
) -> None:
    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        _verify(fixture, candidate)
    assert exc_info.value.code is expected_code
    assert fixture.backend.calls == []


def test_authenticated_journal_uses_exact_release_image_and_canonical_bytes() -> None:
    # Arrange
    fixture = _fixture()

    # Act
    verified = _verify(fixture)

    # Assert
    assert len(fixture.backend.calls) == 1
    receipt_bytes, image_id, journal_bytes = fixture.backend.calls[0]
    assert receipt_bytes == fixture.candidate.receipt.receipt_bytes
    assert image_id == fixture.spot_release.guest_image_id
    assert journal_bytes == canonical_global_bytes_v1(fixture.candidate.journal)
    assert verified.expected_image_id == fixture.spot_release.guest_image_id
    assert verified.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified.journal == fixture.candidate.journal
    assert verified.journal is not fixture.candidate.journal
    assert verified.journal.terminal_obligations_root != ZERO_ROOT_V1
    assert verified.journal.quote_amount_in_atoms == 125
    assert verified.journal.purchased_zdex_atoms == 111


def test_verified_witness_is_opaque_immutable_and_binding_stable() -> None:
    fixture = _fixture()
    verified = _verify(fixture)
    binding_root = verified.binding_root
    journal_copy = verified.journal

    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedZDEXBuybackSpotSafetyPurchaseV2(object(), object())  # type: ignore[arg-type]
    with pytest.raises(AttributeError, match="immutable"):
        verified._fields = object()  # type: ignore[assignment]
    object.__setattr__(journal_copy, "safety_binding_root", _root(90_001))

    assert verified.binding_root == binding_root
    assert verified.journal.safety_binding_root == fixture.candidate.journal.safety_binding_root


def test_canonical_journal_digest_is_fixed() -> None:
    journal_bytes = canonical_global_bytes_v1(_fixture().candidate.journal)

    assert hashlib.sha256(journal_bytes).hexdigest() == (
        "15fc1d0093129ab31273b9d2d4dc5a1eb8ada41233af59c64e6e5e92b39bd28f"
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
def test_fake_conditional_and_non_succinct_receipts_reject_before_callback(
    receipt_kind: ReceiptKindV1,
) -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(receipt_kind, b"inadmissible"),
    )

    _assert_reject(
        fixture,
        candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.UNSUPPORTED_RECEIPT_KIND,
    )


def test_empty_succinct_receipt_rejects_before_callback() -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b""),
    )

    _assert_reject(
        fixture,
        candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.EMPTY_RECEIPT,
    )


def test_callback_failure_creates_no_witness() -> None:
    fixture = _fixture()
    fixture.backend.error = RuntimeError("backend details must not escape")

    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        _verify(fixture)

    assert exc_info.value.code is ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED
    assert "backend details" not in str(exc_info.value)


def test_callback_non_none_success_shape_rejects() -> None:
    fixture = _fixture()
    fixture.backend.result = True

    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        _verify(fixture)

    assert exc_info.value.code is ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED


def test_raw_accept_all_callback_cannot_create_authority_witness() -> None:
    fixture = _fixture()

    class _AcceptAll:
        def verify_succinct_receipt(self, *args: object, **kwargs: object) -> None:
            del args, kwargs

    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        verify_zdex_buyback_spot_safety_receipt_shadow_v2(
            fixture.candidate,
            authority_head=fixture.authority_head,
            receipt_verifier=_AcceptAll(),
        )

    assert exc_info.value.code is ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH
    assert fixture.backend.calls == []


def test_stale_current_authority_head_rejects_before_receipt_verification() -> None:
    fixture = _fixture()
    stale = replace(fixture.authority_head, profile_root=_root(70_000))

    with pytest.raises(ZDEXBuybackSpotReceiptRejectedV1) as exc_info:
        verify_zdex_buyback_spot_safety_receipt_shadow_v2(
            fixture.candidate,
            authority_head=stale,
            receipt_verifier=fixture.receipt_verifier,
        )

    assert exc_info.value.code is ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH
    assert fixture.backend.calls == []


def test_caller_substituted_spend_policy_rejects_before_receipt_verification() -> None:
    fixture = _fixture()
    substituted = replace(
        fixture.candidate.spend_policy,
        per_command_quote_cap_atoms=201,
    )
    _assert_reject(
        fixture,
        replace(fixture.candidate, spend_policy=substituted),
        ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
    )


def test_caller_substituted_price_policy_rejects_before_receipt_verification() -> None:
    fixture = _fixture()
    substituted = replace(
        fixture.candidate.price_policy,
        maximum_execution_impact_bps=1_301,
    )

    _assert_reject(
        fixture,
        replace(fixture.candidate, price_policy=substituted),
        ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
    )


def test_caller_substituted_fee_policy_rejects_before_receipt_verification() -> None:
    fixture = _fixture()
    shares = list(fixture.candidate.fee_policy.shares)
    shares[0] = replace(shares[0], share_bps=shares[0].share_bps + 1)
    substituted = ZDEXFeeAllocationPolicyV1(tuple(shares))

    _assert_reject(
        fixture,
        replace(fixture.candidate, fee_policy=substituted),
        ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
    )


def test_caller_substituted_cadence_state_rejects_before_receipt_verification() -> None:
    fixture = _fixture()
    state = fixture.candidate.tokenomics_pre_state
    cadence = replace(
        state.buyback_spend_states[0],
        last_execution_height=1,
    )
    substituted = ZDEXAtomicBuybackTokenomicsStateV1(
        state.tokenomics,
        (cadence,),
    )

    _assert_reject(
        fixture,
        replace(fixture.candidate, tokenomics_pre_state=substituted),
        ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
    )


def test_quote_spend_above_authenticated_route_limit_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(fixture.candidate.journal, "quote_amount_in_atoms", 201)

    _assert_reject(
        fixture,
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_purchased_output_below_positive_minimum_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(fixture.candidate.journal, "purchased_zdex_atoms", 108)

    _assert_reject(
        fixture,
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


@pytest.mark.parametrize(
    ("changes", "expected_code"),
    (
        (
            {"oracle_quote_numerator_atoms": 2},
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
        ),
        (
            {"purchased_zdex_atoms": 110},
            ZDEXBuybackSpotReceiptRejectCodeV1.PRICE_SAFETY_REJECTED,
        ),
        (
            {"route_safe_quote_limit_atoms": 199},
            ZDEXBuybackSpotReceiptRejectCodeV1.PRICE_SAFETY_REJECTED,
        ),
        (
            {"minimum_output_atoms": 110},
            ZDEXBuybackSpotReceiptRejectCodeV1.PRICE_SAFETY_REJECTED,
        ),
    ),
)
def test_price_envelope_mutations_reject_before_receipt_callback(
    changes: dict[str, int],
    expected_code: ZDEXBuybackSpotReceiptRejectCodeV1,
) -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        journal=replace(fixture.candidate.journal, **changes),  # type: ignore[arg-type]
    )

    _assert_reject(
        fixture,
        candidate,
        expected_code,
    )


def test_uncommitted_reserve_claim_rejects_before_receipt_callback() -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        journal=replace(fixture.candidate.journal, quote_reserve_atoms=999),
    )

    _assert_reject(
        fixture,
        candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
    )


@pytest.mark.parametrize(
    ("field_name", "hostile_value", "expected_code"),
    (
        (
            "profile_root",
            _root(70_001),
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
        ),
        ("writer_epoch", 12, ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        (
            "route_release_id",
            _root(70_002),
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            "command_occurrence_id",
            _root(70_003),
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            "spot_module_release_id",
            _root(70_004),
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
        ),
        (
            "spot_guest_image_id",
            _root(70_005),
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
        ),
        ("consensus_height", 78, ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH),
        (
            "global_pre_state_root",
            _root(70_006),
            ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
        ),
        (
            "pre_spot_lane_root",
            _root(70_007),
            ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
        ),
        ("pool_id", _root(70_008), ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH),
        (
            "pool_definition_root",
            _root(70_009),
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
        ),
        (
            "quote_asset_id",
            _root(70_010),
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
        ),
        (
            "zdex_asset_id",
            _root(70_011),
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
        ),
        (
            "oracle_policy_root",
            _root(70_012),
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
        ),
        (
            "oracle_id",
            "substituted-oracle",
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
        ),
        (
            "oracle_occurrence_root",
            _root(70_013),
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
        ),
    ),
)
def test_hostile_coordinate_substitution_rejects_before_callback(
    field_name: str,
    hostile_value: object,
    expected_code: ZDEXBuybackSpotReceiptRejectCodeV1,
) -> None:
    fixture = _fixture()
    journal = replace(
        fixture.candidate.journal,
        **{field_name: hostile_value},  # type: ignore[arg-type]
    )
    candidate = replace(fixture.candidate, journal=journal)

    _assert_reject(fixture, candidate, expected_code)


@pytest.mark.parametrize(
    ("field_name", "hostile_value"),
    (
        ("global_pre_state_root", _root(80_001)),
        ("pre_spot_lane_root", _root(80_002)),
    ),
)
def test_stale_global_or_spot_pre_root_rejects(
    field_name: str,
    hostile_value: str,
) -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        journal=replace(
            fixture.candidate.journal,
            **{field_name: hostile_value},  # type: ignore[arg-type]
        ),
    )

    _assert_reject(
        fixture,
        candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
    )


@pytest.mark.parametrize(
    ("oracle_occurrences", "expected_code"),
    (
        ((), ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH),
        (
            (
                OracleOccurrenceStateV1(
                    "zdex-buyback-oracle",
                    ZDEXBuybackOraclePriceOccurrenceV1(
                        "zdex-buyback-oracle",
                        _root(12),
                        _root(13),
                        1,
                        1,
                        76,
                    ).occurrence_root,
                    76,
                    False,
                ),
            ),
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
        ),
        (
            (
                OracleOccurrenceStateV1(
                    "zdex-buyback-oracle",
                    _root(52),
                    78,
                    True,
                ),
            ),
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
        ),
    ),
)
def test_missing_unfinalized_or_future_oracle_rejects_before_callback(
    oracle_occurrences: tuple[OracleOccurrenceStateV1, ...],
    expected_code: ZDEXBuybackSpotReceiptRejectCodeV1,
) -> None:
    fixture = _fixture()
    state = replace(
        fixture.candidate.global_pre_state,
        oracle_occurrences=oracle_occurrences,
    )
    occurrence = replace(fixture.candidate.occurrence, pre_state_root=state.state_root)
    fee_context = replace(
        fixture.candidate.fee_context,
        command_occurrence_id=occurrence.occurrence_id,
    )
    journal = replace(
        fixture.candidate.journal,
        global_pre_state_root=state.state_root,
        command_occurrence_id=occurrence.occurrence_id,
        fee_context_root=hash_global_v1(
            "zdex-fee-allocation-context-v1",
            fee_context.to_canonical(),
        ),
    )
    candidate = replace(
        fixture.candidate,
        occurrence=occurrence,
        fee_context=fee_context,
        global_pre_state=state,
        journal=journal,
    )

    _assert_reject(fixture, candidate, expected_code)


def test_enabled_spot_lane_rejects_from_shadow_receipt_boundary() -> None:
    fixture = _fixture()
    state = fixture.candidate.global_pre_state
    lanes = tuple(
        replace(row, enabled=True) if row.lane_id is LaneIdV1.SPOT_LIQUIDITY else row
        for row in state.lane_roots
    )
    substituted = replace(state, lane_roots=lanes)
    occurrence = replace(
        fixture.candidate.occurrence,
        pre_state_root=substituted.state_root,
    )
    fee_context = replace(
        fixture.candidate.fee_context,
        command_occurrence_id=occurrence.occurrence_id,
    )
    journal = replace(
        fixture.candidate.journal,
        global_pre_state_root=substituted.state_root,
        command_occurrence_id=occurrence.occurrence_id,
        fee_context_root=hash_global_v1(
            "zdex-fee-allocation-context-v1",
            fee_context.to_canonical(),
        ),
    )

    _assert_reject(
        fixture,
        replace(
            fixture.candidate,
            global_pre_state=substituted,
            occurrence=occurrence,
            fee_context=fee_context,
            journal=journal,
        ),
        ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
    )


def test_stale_post_root_equal_to_pre_root_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(
        fixture.candidate.journal,
        "post_spot_lane_root",
        fixture.candidate.journal.pre_spot_lane_root,
    )

    _assert_reject(
        fixture,
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_safety_binding_root_mutation_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(fixture.candidate.journal, "safety_binding_root", _root(81_001))

    _assert_reject(
        fixture,
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_nonzero_terminal_obligation_mutation_rejects_before_callback() -> None:
    fixture = _fixture()
    object.__setattr__(
        fixture.candidate.journal,
        "terminal_obligations_root",
        _root(81_002),
    )

    _assert_reject(
        fixture,
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_hostile_scalar_subclass_rejects_without_behavior_or_callback() -> None:
    fixture = _fixture()

    class _ExplodingRoot(str):
        def __eq__(self, other: object) -> bool:
            raise AssertionError("hostile equality executed")

        def __hash__(self) -> int:
            raise AssertionError("hostile hash executed")

    object.__setattr__(
        fixture.candidate.journal,
        "profile_root",
        _ExplodingRoot(fixture.candidate.journal.profile_root),
    )

    _assert_reject(
        fixture,
        fixture.candidate,
        ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
    )


def test_callback_alias_mutation_cannot_rebind_returned_witness() -> None:
    fixture = _fixture()
    candidate = fixture.candidate
    expected_journal = candidate.journal
    expected_image_id = fixture.spot_release.guest_image_id
    expected_receipt_digest = "0x" + hashlib.sha256(candidate.receipt.receipt_bytes).hexdigest()

    def mutate(receipt_bytes: bytes, image_id: str, journal_bytes: bytes) -> None:
        assert receipt_bytes == b"succinct-buyback-spot-receipt"
        assert image_id == fixture.spot_release.guest_image_id
        assert journal_bytes == canonical_global_bytes_v1(expected_journal)
        object.__setattr__(candidate.journal, "quote_amount_in_atoms", 1)
        object.__setattr__(candidate.profile, "profile_id", _root(99_001))
        object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated")

    fixture.backend.hook = mutate
    verified = _verify(fixture, candidate)

    assert verified.journal.quote_amount_in_atoms == 125
    assert verified.journal.profile_root == expected_journal.profile_root
    assert verified.expected_image_id == expected_image_id
    assert verified.receipt_digest == expected_receipt_digest
