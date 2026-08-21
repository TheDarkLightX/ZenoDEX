from __future__ import annotations

import hashlib
from concurrent.futures import ThreadPoolExecutor
from dataclasses import FrozenInstanceError, dataclass, replace

import pytest

from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_abi_v1 import (
    ALL_LANE_IDS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_EPOCH_COMMANDS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    AssetSupplyV1,
    CommandAggregationJournalV1,
    EconomicAmountV1,
    EconomicCommandOccurrenceV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    EconomicEpochReceiptCandidateV1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicEpochCertificateV1,
    GlobalEconomicStateRootV1,
    GlobalEconomicStateV1,
    LaneCompositionJournalV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    LaneStateRootV1,
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
    MigrationObjectClassV1,
    MigrationObjectRowV1,
    ProfileStatusV1,
    ReceiptKindV1,
    ReleaseStatusV1,
    RouteCompositionJournalV1,
    RouteRegistryV1,
    RouteReleaseV1,
    StateMigrationCertificateV1,
    VerifiedEconomicEpochV1,
    compose_asset_lane_epoch_effect_plans_v1,
    validate_global_state_profile_v1,
    verify_economic_epoch_v1,
)
from src.core.lane_composition_receipt_verification_v1 import (
    LaneCompositionReceiptCandidateV1,
    LaneCompositionReceiptEnvelopeV1,
    VerifiedLaneCompositionV1,
    verify_asset_lane_composition_receipt_v1,
)
from src.core.lane_module_receipt_verification_v1 import (
    AssetTransferLaneModuleReceiptCandidateV1,
    LaneModuleReceiptEnvelopeV1,
    VerifiedLaneModuleTransitionV1,
    verify_asset_transfer_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    bind_asset_transfer_lane_output_to_release_route_v1,
)
from src.core.receipt_backed_asset_lane_composition_v1 import (
    ReceiptBackedAssetLaneCompositionCandidateV1,
    compose_receipt_backed_asset_lane_single_v1,
)
from src.core.route_composition_receipt_verification_v1 import (
    RouteCompositionReceiptCandidateV1,
    RouteCompositionReceiptEnvelopeV1,
    VerifiedRouteCompositionV1,
    derive_route_composition_assumption_root_v1,
    verify_route_composition_receipt_v1,
)
from src.integration.global_economic_commit_v1 import (
    CommitOutcomeStatusV1,
    EconomicEpochBodyAndStateV1,
    GlobalEconomicCommitPortV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _active_evidence() -> tuple[EvidenceStatusV1, ...]:
    return tuple(
        sorted(
            (
                EvidenceStatusV1.SPECIFIED,
                EvidenceStatusV1.IMPLEMENTED,
                EvidenceStatusV1.PROVED,
                EvidenceStatusV1.MOUNTED,
                EvidenceStatusV1.TESTED,
                EvidenceStatusV1.TERMINAL_COMPLETE,
                EvidenceStatusV1.MIGRATABLE,
                EvidenceStatusV1.NO_BYPASS,
                EvidenceStatusV1.RELEASE_BACKED,
            ),
            key=lambda item: item.value,
        )
    )


def _module_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    command = (
        ASSET_TRANSFER_COMMAND_KIND_V1
        if lane_id is LaneIdV1.ASSET_TRANSFER
        else f"cmd_{lane_id.value.lower()}"
    )
    offset = ordinal * 16
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0",
        state_schema_root=_root(100 + offset),
        command_variants=(command,),
        terminal_command_variants=(command,),
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_objects=True,
        evidence_statuses=_active_evidence(),
    )


def _coordinator_release(lane_id: LaneIdV1, ordinal: int) -> LaneCoordinatorReleaseV1:
    active = lane_id is LaneIdV1.ASSET_TRANSFER
    offset = ordinal * 16
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0",
        coordinator_schema_root=_root(300 + offset),
        guest_image_id=_root(301 + offset),
        specification_root=_root(302 + offset),
        source_root=_root(303 + offset),
        toolchain_root=_root(304 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if active else ReleaseStatusV1.SHADOW,
        accepts_new_objects=active,
        evidence_statuses=(
            _active_evidence() if active else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _profile() -> tuple[EconomicProfileSnapshotV1, RouteReleaseV1]:
    releases = tuple(
        _module_release(lane_id, ordinal)
        for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
    )
    lane_registry = LaneRegistryV1(releases)
    lane_coordinator_registry = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    asset_release = lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    route = RouteReleaseV1.build(
        semantic_version="1.0.0",
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
        ordered_lanes=(LaneIdV1.ASSET_TRANSFER,),
        module_release_ids=(asset_release.release_id,),
        dependency_roles=("VALUE_OWNER",),
        port_schema_roots=(_root(400),),
        guest_image_id=_root(403),
        specification_root=_root(404),
        source_root=_root(405),
        toolchain_root=_root(406),
        oracle_policy_root=_root(401),
        issue_burn_policy_root=_root(402),
        max_cycles=2_000_000,
        max_journal_bytes=131_072,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_objects=True,
        evidence_statuses=_active_evidence(),
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=7,
        lane_registry=lane_registry,
        lane_coordinator_registry=lane_coordinator_registry,
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(410),
        root_image_id=_root(411),
        verifier_registry_root=_root(412),
        migration_registry_root=_root(413),
        policy_registry_root=_root(414),
        terminal_registry_root=_root(415),
        status=ProfileStatusV1.ACTIVE,
    )
    return profile, route


def _state(profile: EconomicProfileSnapshotV1, *, height: int) -> GlobalEconomicStateV1:
    lane_roots = tuple(
        LaneStateRootV1(
            lane_id=release.lane_id,
            module_release_id=release.release_id,
            enabled=True,
            state_root=_root(1_000 + ordinal),
        )
        for ordinal, release in enumerate(profile.lane_registry.releases)
    )
    return GlobalEconomicStateV1(
        chain_id="zeno-test-chain",
        deployment_root=_root(500),
        writer_epoch=profile.authority_epoch,
        height=height,
        profile_root=profile.profile_id,
        lane_roots=lane_roots,
        supplies=(AssetSupplyV1("USD", 100),),
    )


def _occurrence(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    pre_state: GlobalEconomicStateV1,
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        height=pre_state.height + 1,
        tx_index=0,
        op_index=0,
        command_kind=route.command_kind,
        route_release_id=route.route_release_id,
        subject_id="alice",
        grant_root=_root(600),
        nonce=1,
        profile_root=profile.profile_id,
        pre_state_root=pre_state.state_root,
        consumed_object_ids=(),
    )


def _valid_effect_plan() -> GlobalEconomicEffectPlanV1:
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ISSUE,
                    "issuer",
                    "USD",
                    "supply",
                    5,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.FEE_ALLOCATION,
                    "treasury",
                    "USD",
                    "reserve",
                    1,
                ),
            ),
            key=lambda item: item.key,
        )
    )
    return GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=(
            AssetConservationRowV1(
                asset="USD",
                owned_and_custodied_pre_atoms=100,
                owned_and_custodied_post_atoms=105,
                supply_pre_atoms=100,
                supply_post_atoms=105,
                authorized_issue_atoms=5,
                authorized_burn_atoms=0,
            ),
        ),
        fee_conservation=(FeeConservationRowV1("USD", 2, 1, 1),),
        lane_writes=(),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )


class _RecordingReceiptVerifier:
    def __init__(self) -> None:
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))


@dataclass(frozen=True, slots=True)
class _VerifiedRouteEffectFixture:
    route_journal: RouteCompositionJournalV1
    verified_route: VerifiedRouteCompositionV1
    effect_plan: GlobalEconomicEffectPlanV1
    post_module_state: AssetTransferStateV1


@dataclass(frozen=True, slots=True)
class _EpochRouteFixture:
    occurrences: tuple[EconomicCommandOccurrenceV1, ...]
    route_journals: tuple[RouteCompositionJournalV1, ...]
    verified_routes: tuple[VerifiedRouteCompositionV1, ...]
    route_effect_plans: tuple[GlobalEconomicEffectPlanV1, ...]
    post_state_root: str


def _default_asset_module_state(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
) -> AssetTransferStateV1:
    release = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    return AssetTransferStateV1(
        module_release_id=release.release_id,
        policies=(AssetTransferPolicyV1("USD", "treasury", 2, True),),
        balances=tuple(
            sorted(
                (
                    EconomicAmountV1(occurrence.subject_id, "USD", "accounts", 100),
                    EconomicAmountV1("recipient", "USD", "accounts", 10),
                    EconomicAmountV1("treasury", "USD", "accounts", 5),
                ),
                key=lambda item: item.key,
            )
        ),
        supplies=(AssetSupplyV1("USD", 115),),
    )


def _asset_module_input_for_occurrence(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    pre_module_state: AssetTransferStateV1,
) -> AssetTransferLaneModuleInputV1:
    return AssetTransferLaneModuleInputV1(
        context=AssetTransferContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=profile.authority_epoch,
            module_release_id=pre_module_state.module_release_id,
            command_occurrence_id=occurrence.occurrence_id,
            subject_id=occurrence.subject_id,
            grant_root=occurrence.grant_root,
        ),
        pre_state=pre_module_state,
        command=AssetTransferCommandV1(
            command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
            asset="USD",
            sender=occurrence.subject_id,
            recipient="recipient",
            amount_atoms=30,
            max_fee_atoms=2,
        ),
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        custody=(),
    )


def _verified_asset_module_for_occurrence(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
) -> tuple[AssetTransferLaneModuleAcceptedV1, VerifiedLaneModuleTransitionV1]:
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    release_binding = bind_asset_transfer_lane_output_to_release_route_v1(
        profile,
        occurrence,
        module_input,
        accepted,
    )
    verified_module = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            occurrence,
            module_input,
            accepted,
            release_binding,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"module:" + occurrence.occurrence_id.encode("ascii"),
            ),
        ),
        _RecordingReceiptVerifier(),
    )
    return accepted, verified_module


def _asset_lane_context(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> AssetLaneCoordinatorContextV1:
    coordinator = profile.lane_coordinator_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    return AssetLaneCoordinatorContextV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        coordinator_release_id=coordinator.coordinator_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        compatible_modules=(
            AssetLaneModuleCompatibilityV1(
                accepted.module_journal.module_release_id,
                ASSET_TRANSFER_MODULE_SCHEMA_V1,
            ),
        ),
    )


def _verified_asset_lane_for_occurrence(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
    verified_module: VerifiedLaneModuleTransitionV1,
) -> tuple[
    LaneCompositionJournalV1,
    VerifiedLaneCompositionV1,
    GlobalEconomicEffectPlanV1,
]:
    coordinator_context = _asset_lane_context(
        profile,
        occurrence,
        module_input,
        accepted,
    )
    lane_result = compose_asset_lane_single_v1(
        coordinator_context,
        accepted.module_journal,
        accepted.private_port,
        accepted.effects,
    )
    assert isinstance(lane_result, AssetLaneCompositionAcceptedV1)
    structural_lane = compose_receipt_backed_asset_lane_single_v1(
        ReceiptBackedAssetLaneCompositionCandidateV1(
            profile,
            occurrence,
            coordinator_context,
            accepted.module_journal,
            accepted.private_port,
            accepted.effects,
            verified_module,
        )
    )
    lane_journal = lane_result.lane_journal
    verified_lane = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1(
            profile,
            occurrence,
            structural_lane,
            lane_journal,
            LaneCompositionReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"lane:" + occurrence.occurrence_id.encode("ascii"),
            ),
        ),
        _RecordingReceiptVerifier(),
    )
    return lane_journal, verified_lane, lane_result.effects


def _verified_route_effect_fixture(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    post_state_root: str,
    pre_module_state: AssetTransferStateV1 | None = None,
) -> _VerifiedRouteEffectFixture:
    """Build the opaque module -> lane -> route chain and retain its effects."""

    module_state = pre_module_state or _default_asset_module_state(profile, occurrence)
    module_input = _asset_module_input_for_occurrence(profile, occurrence, module_state)
    accepted, verified_module = _verified_asset_module_for_occurrence(
        profile, occurrence, module_input
    )
    lane_journal, verified_lane, lane_effects = _verified_asset_lane_for_occurrence(
        profile, occurrence, module_input, accepted, verified_module
    )
    route_journal = RouteCompositionJournalV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        route_release_id=occurrence.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        ordered_lane_journal_roots=(lane_journal.journal_root,),
        pre_state_root=occurrence.pre_state_root,
        post_state_root=post_state_root,
        effect_plan_root=lane_journal.effect_plan_root,
        terminal_obligations_root=lane_journal.terminal_obligations_root,
    )
    verified_route = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane_journal,),
            (verified_lane,),
            route_journal,
            RouteCompositionReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"route:" + occurrence.occurrence_id.encode("ascii"),
            ),
        ),
        _RecordingReceiptVerifier(),
    )
    return _VerifiedRouteEffectFixture(
        route_journal,
        verified_route,
        lane_effects,
        accepted.post_state,
    )


def _verified_route_for_occurrence(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    post_state_root: str,
) -> tuple[RouteCompositionJournalV1, VerifiedRouteCompositionV1]:
    fixture = _verified_route_effect_fixture(
        profile,
        occurrence,
        post_state_root=post_state_root,
    )
    return fixture.route_journal, fixture.verified_route


def _verified_epoch(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    *,
    receipt_bytes: bytes = b"succinct-receipt-one",
) -> tuple[
    VerifiedEconomicEpochV1,
    EconomicEpochBodyAndStateV1,
    _RecordingReceiptVerifier,
    EconomicCommandOccurrenceV1,
    RouteCompositionJournalV1,
]:
    occurrence = _occurrence(profile, route, pre_state)
    body = EconomicEpochBodyAndStateV1(
        pre_state_root=pre_state.state_root,
        post_state=post_state,
        ordered_command_body_hashes=(_root(700),),
        receipt_archive_root=_root(701),
        data_availability_root=_root(702),
        finality_root=_root(703),
    )
    route_fixture = _verified_route_effect_fixture(
        profile,
        occurrence,
        post_state_root=post_state.state_root,
    )
    route_journal = route_fixture.route_journal
    verified_route = route_fixture.verified_route
    route_effect_plans = (route_fixture.effect_plan,)
    effects = compose_asset_lane_epoch_effect_plans_v1(route_effect_plans)
    receipt_root = "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    certificate = GlobalEconomicEpochCertificateV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        height=post_state.height,
        pre_state_root=pre_state.state_root,
        post_state_root=post_state.state_root,
        ordered_occurrence_ids=(occurrence.occurrence_id,),
        ordered_route_journal_roots=(route_journal.journal_root,),
        ordered_route_assumption_roots=(verified_route.assumption_root,),
        module_leaf_occurrences=1,
        aggregation_fanout=8,
        aggregation_levels=0,
        effect_plan_root=effects.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
        body_commitment=body.body_commitment,
        data_availability_root=body.data_availability_root,
        finality_root=body.finality_root,
        source_manifest_root=_root(705),
        toolchain_manifest_root=_root(706),
        root_image_id=profile.root_image_id,
        receipt_root=receipt_root,
        receipt_kind=ReceiptKindV1.SUCCINCT,
        journal_bytes=1,
        cycle_budget=1_000_000,
    )
    certificate = replace(certificate, journal_bytes=len(certificate.canonical_journal_bytes))
    verifier = _RecordingReceiptVerifier()
    verified = verify_economic_epoch_v1(
        _epoch_candidate(
            profile,
            certificate,
            (occurrence,),
            (route_journal,),
            (verified_route,),
            route_effect_plans,
            effects,
            receipt_bytes,
        ),
        verifier,
    )
    return verified, body, verifier, occurrence, route_journal


def _epoch_candidate(
    profile: EconomicProfileSnapshotV1,
    certificate: GlobalEconomicEpochCertificateV1,
    occurrences: tuple[EconomicCommandOccurrenceV1, ...],
    route_journals: tuple[RouteCompositionJournalV1, ...],
    verified_routes: tuple[VerifiedRouteCompositionV1, ...],
    route_effect_plans: tuple[GlobalEconomicEffectPlanV1, ...],
    effect_plan: GlobalEconomicEffectPlanV1,
    receipt_bytes: bytes,
) -> EconomicEpochReceiptCandidateV1:
    return EconomicEpochReceiptCandidateV1(
        profile=profile,
        certificate=certificate,
        command_occurrences=occurrences,
        route_journals=route_journals,
        verified_routes=verified_routes,
        route_effect_plans=route_effect_plans,
        effect_plan=effect_plan,
        receipt_bytes=receipt_bytes,
        expected_chain_id=certificate.chain_id,
        expected_deployment_root=certificate.deployment_root,
        expected_pre_state_root=certificate.pre_state_root,
        expected_body_commitment=certificate.body_commitment,
    )


def _epoch_asset_module_state(profile: EconomicProfileSnapshotV1) -> AssetTransferStateV1:
    release = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    alice_atoms = MAX_EPOCH_COMMANDS_V1 * 32 + 100
    return AssetTransferStateV1(
        module_release_id=release.release_id,
        policies=(AssetTransferPolicyV1("USD", "treasury", 2, True),),
        balances=tuple(
            sorted(
                (
                    EconomicAmountV1("alice", "USD", "accounts", alice_atoms),
                    EconomicAmountV1("recipient", "USD", "accounts", 10),
                    EconomicAmountV1("treasury", "USD", "accounts", 5),
                ),
                key=lambda item: item.key,
            )
        ),
        supplies=(AssetSupplyV1("USD", alice_atoms + 15),),
    )


def _epoch_route_fixture(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    pre_state: GlobalEconomicStateV1,
    count: int,
) -> _EpochRouteFixture:
    occurrences: list[EconomicCommandOccurrenceV1] = []
    route_journals: list[RouteCompositionJournalV1] = []
    verified_routes: list[VerifiedRouteCompositionV1] = []
    route_effect_plans: list[GlobalEconomicEffectPlanV1] = []
    module_state = _epoch_asset_module_state(profile)
    current_root = pre_state.state_root
    for index in range(count):
        occurrence = replace(
            _occurrence(profile, route, pre_state),
            tx_index=index,
            nonce=index + 1,
            pre_state_root=current_root,
        )
        next_root = _root(30_000 + index)
        route_fixture = _verified_route_effect_fixture(
            profile,
            occurrence,
            post_state_root=next_root,
            pre_module_state=module_state,
        )
        occurrences.append(occurrence)
        route_journals.append(route_fixture.route_journal)
        verified_routes.append(route_fixture.verified_route)
        route_effect_plans.append(route_fixture.effect_plan)
        module_state = route_fixture.post_module_state
        current_root = next_root
    return _EpochRouteFixture(
        tuple(occurrences),
        tuple(route_journals),
        tuple(verified_routes),
        tuple(route_effect_plans),
        current_root,
    )


def _epoch_admission_fixture(
    count: int,
) -> EconomicEpochReceiptCandidateV1:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    routes = _epoch_route_fixture(profile, route, pre_state, count)
    effects = compose_asset_lane_epoch_effect_plans_v1(routes.route_effect_plans)
    receipt_bytes = f"succinct-epoch-receipt-{count}".encode("ascii")
    certificate = GlobalEconomicEpochCertificateV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        height=1,
        pre_state_root=pre_state.state_root,
        post_state_root=routes.post_state_root,
        ordered_occurrence_ids=tuple(item.occurrence_id for item in routes.occurrences),
        ordered_route_journal_roots=tuple(item.journal_root for item in routes.route_journals),
        ordered_route_assumption_roots=tuple(
            item.assumption_root for item in routes.verified_routes
        ),
        module_leaf_occurrences=count,
        aggregation_fanout=8,
        aggregation_levels=0 if count <= 8 else 1,
        effect_plan_root=effects.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
        body_commitment=_root(40_000 + count),
        data_availability_root=_root(41_000 + count),
        finality_root=_root(42_000 + count),
        source_manifest_root=_root(43_000 + count),
        toolchain_manifest_root=_root(44_000 + count),
        root_image_id=profile.root_image_id,
        receipt_root="0x" + hashlib.sha256(receipt_bytes).hexdigest(),
        receipt_kind=ReceiptKindV1.SUCCINCT,
        journal_bytes=1,
        cycle_budget=1_000_000,
    )
    certificate = replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )
    return _epoch_candidate(
        profile,
        certificate,
        routes.occurrences,
        routes.route_journals,
        routes.verified_routes,
        routes.route_effect_plans,
        effects,
        receipt_bytes,
    )


def test_closed_lane_registry_and_global_state_require_every_lane() -> None:
    profile, _ = _profile()
    assert tuple(item.lane_id for item in profile.lane_registry.releases) == ALL_LANE_IDS_V1
    state = _state(profile, height=0)
    assert tuple(item.lane_id for item in state.lane_roots) == ALL_LANE_IDS_V1
    assert GlobalEconomicStateRootV1.from_state(state).root == state.state_root
    validate_global_state_profile_v1(state, profile)
    with pytest.raises(ValueError, match="every ABI V1 lane"):
        replace(state, lane_roots=state.lane_roots[:-1])
    foreign_lane = replace(state.lane_roots[0], module_release_id=_root(8_888))
    with pytest.raises(ValueError, match="lane release mismatch"):
        validate_global_state_profile_v1(
            replace(state, lane_roots=(foreign_lane, *state.lane_roots[1:])),
            profile,
        )


def test_enabled_lane_requires_a_nonzero_state_commitment() -> None:
    # Arrange
    profile, _ = _profile()
    state = _state(profile, height=0)

    # Act / Assert: kills a mutant that lets an enabled lane commit no state.
    with pytest.raises(ValueError, match="enabled lane state root must be nonzero"):
        replace(state.lane_roots[0], state_root=ZERO_ROOT_V1)

    disabled_empty = replace(
        state.lane_roots[1],
        enabled=False,
        state_root=ZERO_ROOT_V1,
    )
    assert disabled_empty.state_root == ZERO_ROOT_V1


def test_release_ids_bind_content_while_semver_remains_descriptive() -> None:
    release = _module_release(LaneIdV1.ZUSD_MONETARY, 1)
    renamed = replace(release, semantic_version="descriptive-label")
    assert renamed.release_id == release.release_id
    with pytest.raises(ValueError, match="content-derived"):
        replace(release, state_schema_root=_root(9_999))


def test_coordinator_release_ids_bind_profile_selected_images() -> None:
    profile, _ = _profile()
    release = profile.lane_coordinator_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    renamed = replace(release, semantic_version="descriptive-label")
    assert renamed.coordinator_release_id == release.coordinator_release_id
    with pytest.raises(ValueError, match="content-derived"):
        replace(release, guest_image_id=_root(9_999))

    disabled = profile.lane_coordinator_registry.release_for(LaneIdV1.SPOT_LIQUIDITY)
    assert disabled.status is ReleaseStatusV1.SHADOW
    assert not disabled.accepts_new_objects
    assert disabled.evidence_statuses == (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)

    disabled_asset_coordinator = replace(
        release,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
        evidence_statuses=(EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,),
    )
    coordinator_registry = LaneCoordinatorRegistryV1(
        (disabled_asset_coordinator, *profile.lane_coordinator_registry.releases[1:])
    )
    with pytest.raises(ValueError, match="coordinator unavailable for new objects"):
        EconomicProfileSnapshotV1.build(
            authority_epoch=profile.authority_epoch,
            lane_registry=profile.lane_registry,
            lane_coordinator_registry=coordinator_registry,
            route_registry=profile.route_registry,
            proof_shape_root=profile.proof_shape_root,
            root_image_id=profile.root_image_id,
            verifier_registry_root=profile.verifier_registry_root,
            migration_registry_root=profile.migration_registry_root,
            policy_registry_root=profile.policy_registry_root,
            terminal_registry_root=profile.terminal_registry_root,
            status=ProfileStatusV1.SHADOW,
        )


def test_route_release_ids_bind_composer_image_and_source_manifests() -> None:
    # Arrange
    _, route = _profile()
    renamed = replace(route, semantic_version="descriptive-label")

    # Act / Assert
    assert renamed.route_release_id == route.route_release_id
    for field_name in (
        "guest_image_id",
        "specification_root",
        "source_root",
        "toolchain_root",
    ):
        with pytest.raises(ValueError, match="content-derived"):
            replace(route, **{field_name: _root(9_900)})


def test_governed_route_rejects_unknown_disabled_and_caller_selected_routes() -> None:
    profile, route = _profile()
    assert profile.route_registry.route_for_command(route.command_kind) == route
    with pytest.raises(ValueError, match="caller-selected"):
        profile.route_registry.route_for_command(
            route.command_kind,
            claimed_route_release_id=_root(9_998),
        )
    with pytest.raises(ValueError, match="unknown or unregistered"):
        profile.route_registry.route_for_command("research_only_command")
    disabled = replace(
        route,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
        evidence_statuses=(),
    )
    with pytest.raises(ValueError, match="disabled"):
        RouteRegistryV1((disabled,)).route_for_command(disabled.command_kind)
    disabled_lane = replace(
        profile.lane_registry.releases[0],
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
        evidence_statuses=(),
    )
    with pytest.raises(ValueError, match="unavailable for new objects"):
        EconomicProfileSnapshotV1.build(
            authority_epoch=profile.authority_epoch,
            lane_registry=LaneRegistryV1((disabled_lane, *profile.lane_registry.releases[1:])),
            lane_coordinator_registry=profile.lane_coordinator_registry,
            route_registry=profile.route_registry,
            proof_shape_root=profile.proof_shape_root,
            root_image_id=profile.root_image_id,
            verifier_registry_root=profile.verifier_registry_root,
            migration_registry_root=profile.migration_registry_root,
            policy_registry_root=profile.policy_registry_root,
            terminal_registry_root=profile.terminal_registry_root,
            status=ProfileStatusV1.SHADOW,
        )


def test_active_profile_requires_release_backing_or_proved_no_writer() -> None:
    profile, _ = _profile()
    disabled = replace(
        profile.lane_registry.releases[0],
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
        evidence_statuses=(),
    )
    lane_registry = LaneRegistryV1((disabled, *profile.lane_registry.releases[1:]))
    with pytest.raises(ValueError, match="neither release-backed nor proved disabled"):
        EconomicProfileSnapshotV1.build(
            authority_epoch=profile.authority_epoch,
            lane_registry=lane_registry,
            lane_coordinator_registry=profile.lane_coordinator_registry,
            route_registry=RouteRegistryV1(()),
            proof_shape_root=profile.proof_shape_root,
            root_image_id=profile.root_image_id,
            verifier_registry_root=profile.verifier_registry_root,
            migration_registry_root=profile.migration_registry_root,
            policy_registry_root=profile.policy_registry_root,
            terminal_registry_root=profile.terminal_registry_root,
            status=ProfileStatusV1.ACTIVE,
        )


def test_effect_plan_enforces_conservation_fee_projection_and_external_only_outbox() -> None:
    plan = _valid_effect_plan()
    assert plan.asset_conservation[0].supply_post_atoms == 105
    with pytest.raises(ValueError, match="authorized issue"):
        replace(
            plan,
            asset_conservation=(AssetConservationRowV1("USD", 100, 104, 100, 104, 4, 0),),
        )
    with pytest.raises(ValueError, match="same-ledger"):
        ExternalOutboxEnqueueV1(
            effect_id=_root(800),
            destination_id="zenoledger:alice",
            payload_hash=_root(801),
            adapter_profile_root=_root(802),
        )
    with pytest.raises(ValueError, match="non-negative integer"):
        AssetSupplyV1("USD", True)


def test_rejected_transition_is_exact_noop_with_empty_effects() -> None:
    rejected = LaneTransitionRejectedV1.reject(
        LaneTransitionRejectCodeV1.DISABLED_FEATURE,
        _root(900),
    )
    assert rejected.pre_state_root == rejected.post_state_root
    assert rejected.effects.is_empty
    with pytest.raises(ValueError, match="preserve the exact pre-state"):
        LaneTransitionRejectedV1(
            LaneTransitionRejectCodeV1.POLICY_REJECT,
            _root(900),
            _root(901),
            GlobalEconomicEffectPlanV1.empty(),
        )


def test_epoch_verifier_binds_profile_image_receipt_journal_and_opaque_handle() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    verified, body, verifier, occurrence, route_journal = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )
    assert verified.certificate.post_state_root == post_state.state_root
    assert len(verifier.calls) == 1
    assert verifier.calls[0][1] == profile.root_image_id
    with pytest.raises(AttributeError, match="immutable"):
        verified._receipt_digest = _root(8_999)
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedEconomicEpochV1(
            object(),
            verified.certificate,
            verified.effect_plan,
            verified.ordered_route_binding_roots,
            verified.receipt_digest,
        )
    rebuilt_route = _verified_route_effect_fixture(
        profile,
        occurrence,
        post_state_root=post_state.state_root,
    )
    rebuilt_route_journal = rebuilt_route.route_journal
    verified_route = rebuilt_route.verified_route
    assert rebuilt_route_journal == route_journal
    candidate = _epoch_candidate(
        profile,
        verified.certificate,
        (occurrence,),
        (route_journal,),
        (verified_route,),
        (rebuilt_route.effect_plan,),
        verified.effect_plan,
        b"succinct-receipt-one",
    )
    with pytest.raises(FrozenInstanceError):
        candidate.receipt_bytes = b"caller-mutation"
    with pytest.raises(ValueError, match="receipt root mismatch"):
        verify_economic_epoch_v1(
            replace(candidate, receipt_bytes=b"tampered-receipt"),
            _RecordingReceiptVerifier(),
        )
    wrong_image = replace(verified.certificate, root_image_id=_root(9_000))
    wrong_image = replace(wrong_image, journal_bytes=len(wrong_image.canonical_journal_bytes))
    with pytest.raises(ValueError, match="root image id mismatch"):
        verify_economic_epoch_v1(
            replace(
                candidate,
                certificate=wrong_image,
                command_occurrences=(),
                route_journals=(),
                verified_routes=(),
                expected_body_commitment=wrong_image.body_commitment,
            ),
            _RecordingReceiptVerifier(),
        )


def test_epoch_rejects_global_effect_plan_unrelated_to_verified_route_effects() -> None:
    # Arrange: preserve the route proof while relabeling the epoch as effect-free.
    valid = _epoch_admission_fixture(1)
    empty_effects = GlobalEconomicEffectPlanV1.empty()
    certificate = replace(valid.certificate, effect_plan_root=empty_effects.effect_plan_root)
    certificate = replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )
    candidate = replace(valid, certificate=certificate, effect_plan=empty_effects)
    assert candidate.route_journals[0].effect_plan_root != candidate.effect_plan.effect_plan_root
    verifier = _RecordingReceiptVerifier()

    # Act / Assert: admission must stop before cryptographic root verification.
    with pytest.raises(ValueError, match="route effect plan"):
        verify_economic_epoch_v1(candidate, verifier)
    assert verifier.calls == []


def test_epoch_rejects_route_effect_plan_with_wrong_committed_root() -> None:
    # Arrange: mutate a valid disclosed plan while preserving the route proof.
    valid = _epoch_admission_fixture(1)
    lane_write = replace(valid.route_effect_plans[0].lane_writes[0], post_root=_root(99_002))
    substituted_plan = replace(valid.route_effect_plans[0], lane_writes=(lane_write,))
    candidate = replace(valid, route_effect_plans=(substituted_plan,))
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="route effect plan root mismatch"):
        verify_economic_epoch_v1(candidate, verifier)
    assert verifier.calls == []


def test_asset_lane_epoch_effect_composer_applies_count_bva() -> None:
    # Arrange
    valid = _epoch_admission_fixture(1).route_effect_plans[0]

    # Act / Assert
    with pytest.raises(ValueError, match="between one and 64"):
        compose_asset_lane_epoch_effect_plans_v1(())
    with pytest.raises(ValueError, match="between one and 64"):
        compose_asset_lane_epoch_effect_plans_v1((valid,) * 65)


def test_asset_lane_epoch_effect_composer_rejects_disconnected_histories() -> None:
    # Arrange: mutate only the second route's lane-history precondition.
    plans = _epoch_admission_fixture(2).route_effect_plans
    second_lane_write = replace(plans[1].lane_writes[0], pre_root=_root(99_001))
    disconnected_lane = (
        plans[0],
        replace(plans[1], lane_writes=(second_lane_write,)),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="lane-write history is disconnected"):
        compose_asset_lane_epoch_effect_plans_v1(disconnected_lane)

    # Arrange: keep each route conserved while disconnecting adjacent snapshots.
    conservation = plans[1].asset_conservation[0]
    disconnected_row = replace(
        conservation,
        owned_and_custodied_pre_atoms=conservation.owned_and_custodied_pre_atoms + 1,
        owned_and_custodied_post_atoms=conservation.owned_and_custodied_post_atoms + 1,
        supply_pre_atoms=conservation.supply_pre_atoms + 1,
        supply_post_atoms=conservation.supply_post_atoms + 1,
    )
    disconnected_conservation = (
        plans[0],
        replace(plans[1], asset_conservation=(disconnected_row,)),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="conservation history is disconnected"):
        compose_asset_lane_epoch_effect_plans_v1(disconnected_conservation)


def test_asset_lane_epoch_effect_composer_rejects_duplicate_and_overflowed_totals() -> None:
    # Arrange: preserve individually valid plans while repeating one consumption.
    plans = _epoch_admission_fixture(2).route_effect_plans
    duplicate = (
        plans[0],
        replace(plans[1], occurrence_consumptions=plans[0].occurrence_consumptions),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="repeats an occurrence"):
        compose_asset_lane_epoch_effect_plans_v1(duplicate)

    # Arrange: each signed row is valid alone; their aggregate exceeds i128.
    alice_row_index = next(
        index
        for index, row in enumerate(plans[0].rows)
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT and row.principal == "alice"
    )
    first_rows = list(plans[0].rows)
    second_rows = list(plans[1].rows)
    first_rows[alice_row_index] = replace(
        first_rows[alice_row_index],
        delta_atoms=MAX_DELTA_ATOMS_V1,
    )
    second_rows[alice_row_index] = replace(
        second_rows[alice_row_index],
        delta_atoms=1,
    )
    overflow = (
        replace(plans[0], rows=tuple(first_rows)),
        replace(plans[1], rows=tuple(second_rows)),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="signed 128-bit"):
        compose_asset_lane_epoch_effect_plans_v1(overflow)

    # Arrange: distinct fee principals avoid signed-row aggregation while the
    # common asset fee total exceeds u128 on the third individually valid plan.
    fee_overflow_plans: list[GlobalEconomicEffectPlanV1] = []
    for index, plan in enumerate(_epoch_admission_fixture(3).route_effect_plans):
        fee_rows = [
            replace(
                row,
                principal=f"fee_owner_{index}",
                delta_atoms=MAX_DELTA_ATOMS_V1,
            )
            if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
            else row
            for row in plan.rows
        ]
        fee_overflow_plans.append(
            replace(
                plan,
                rows=tuple(sorted(fee_rows, key=lambda row: row.key)),
                fee_conservation=(
                    FeeConservationRowV1(
                        "USD",
                        MAX_DELTA_ATOMS_V1,
                        MAX_DELTA_ATOMS_V1,
                        0,
                    ),
                ),
            )
        )

    # Act / Assert
    with pytest.raises(ValueError, match="unsigned 128-bit"):
        compose_asset_lane_epoch_effect_plans_v1(tuple(fee_overflow_plans))


def test_asset_lane_epoch_effect_composer_rejects_outbox_and_terminal_scope_expansion() -> None:
    # Arrange: the current single-ledger composer has no external-delivery law.
    valid = _epoch_admission_fixture(1)
    outbox_plan = replace(
        valid.route_effect_plans[0],
        external_outbox_enqueue=(
            ExternalOutboxEnqueueV1(
                effect_id=_root(99_010),
                destination_id="ethereum:test",
                payload_hash=_root(99_011),
                adapter_profile_root=_root(99_012),
            ),
        ),
    )

    # Act / Assert
    with pytest.raises(ValueError, match="forbids external outbox"):
        compose_asset_lane_epoch_effect_plans_v1((outbox_plan,))

    # Arrange: terminal-obligation aggregation remains outside this release.
    certificate = replace(valid.certificate, terminal_obligations_root=_root(99_013))
    certificate = replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )
    candidate = replace(valid, certificate=certificate)
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="terminal composition is unsupported"):
        verify_economic_epoch_v1(candidate, verifier)
    assert verifier.calls == []


def test_command_aggregation_journal_uses_canonical_fanout_bva() -> None:
    def journal(
        command_count: int, *, module_leaf_occurrences: int | None = None
    ) -> CommandAggregationJournalV1:
        return CommandAggregationJournalV1(
            chain_id="zeno-command-aggregation-test",
            deployment_root=_root(18_000),
            profile_root=_root(18_001),
            writer_epoch=7,
            epoch_height=42,
            group_index=0,
            first_command_index=0,
            ordered_occurrence_ids=tuple(
                _root(18_100 + index) for index in range(command_count)
            ),
            ordered_route_journal_roots=tuple(
                _root(18_200 + index) for index in range(command_count)
            ),
            ordered_route_assumption_roots=tuple(
                _root(18_300 + index) for index in range(command_count)
            ),
            pre_state_root=_root(18_400),
            post_state_root=_root(18_401),
            module_leaf_occurrences=(
                command_count if module_leaf_occurrences is None else module_leaf_occurrences
            ),
        )

    # Arrange / Act / Assert: exact fanout lower and upper boundaries.
    for count in (1, 8):
        accepted = journal(count)
        assert accepted.to_canonical()["first_command_index"] == 0
        assert accepted.journal_root.startswith("0x")

    for rejected_count in (0, 9):
        with pytest.raises(ValueError, match="between one and eight"):
            journal(rejected_count)
    with pytest.raises(ValueError, match="module leaf count"):
        journal(2, module_leaf_occurrences=1)
    with pytest.raises(ValueError, match="group position"):
        replace(journal(1), group_index=1, first_command_index=7)


def test_epoch_shape_rejects_zero_65_and_route_width_9() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    verified, _, _, _, _ = _verified_epoch(profile, route, pre_state, post_state)
    certificate = verified.certificate
    with pytest.raises(ValueError, match="between one and 64"):
        replace(
            certificate,
            ordered_occurrence_ids=(),
            ordered_route_journal_roots=(),
            ordered_route_assumption_roots=(),
        )
    roots = tuple(_root(10_000 + index) for index in range(MAX_EPOCH_COMMANDS_V1 + 1))
    with pytest.raises(ValueError, match="between one and 64"):
        replace(
            certificate,
            ordered_occurrence_ids=roots,
            ordered_route_journal_roots=tuple(_root(20_000 + index) for index in range(65)),
            ordered_route_assumption_roots=tuple(
                _root(21_000 + index) for index in range(65)
            ),
            module_leaf_occurrences=65,
        )
    lanes = ALL_LANE_IDS_V1[:9]
    release_ids = tuple(profile.lane_registry.release_for(lane).release_id for lane in lanes)
    with pytest.raises(ValueError, match="one and eight"):
        RouteReleaseV1.build(
            semantic_version="1.0.0",
            command_kind="too_wide",
            ordered_lanes=lanes,
            module_release_ids=release_ids,
            dependency_roles=tuple(f"ROLE_{index}" for index in range(9)),
            port_schema_roots=tuple(_root(30_000 + index) for index in range(9)),
            guest_image_id=_root(30_102),
            specification_root=_root(30_103),
            source_root=_root(30_104),
            toolchain_root=_root(30_105),
            oracle_policy_root=_root(30_100),
            issue_burn_policy_root=_root(30_101),
            max_cycles=1,
            max_journal_bytes=1,
            status=ReleaseStatusV1.SHADOW,
            accepts_new_objects=False,
        )


@pytest.mark.parametrize("count", (1, 8, 9, 64))
def test_epoch_route_witness_boundary_counts_are_admitted(count: int) -> None:
    # Arrange
    candidate = _epoch_admission_fixture(count)
    verifier = _RecordingReceiptVerifier()

    # Act
    verified = verify_economic_epoch_v1(candidate, verifier)

    # Assert
    assert verified.ordered_route_binding_roots == tuple(
        item.binding_root for item in candidate.verified_routes
    )
    assert len(verifier.calls) == 1


def test_epoch_certificate_binds_exact_guest_route_assumption_roots() -> None:
    # Arrange
    candidate = _epoch_admission_fixture(1)
    witness = candidate.verified_routes[0]
    expected = derive_route_composition_assumption_root_v1(
        profile_id=witness.profile_id,
        route_release_id=witness.route_release_id,
        command_occurrence_id=witness.command_occurrence_id,
        writer_epoch=witness.writer_epoch,
        route_journal_root=witness.route_journal_root,
        route_journal_digest=witness.route_journal_digest,
        expected_image_id=witness.expected_image_id,
    )
    assert witness.assumption_root == expected
    assert candidate.certificate.ordered_route_assumption_roots == (expected,)
    substituted = replace(
        candidate.certificate,
        ordered_route_assumption_roots=(_root(48_999),),
    )
    substituted = replace(
        substituted,
        journal_bytes=len(substituted.canonical_journal_bytes),
    )
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="route assumption root"):
        verify_economic_epoch_v1(
            replace(candidate, certificate=substituted),
            verifier,
        )
    assert verifier.calls == []


def test_epoch_rejects_missing_foreign_and_journal_substituted_route_witnesses() -> None:
    # Arrange
    candidate = _epoch_admission_fixture(1)
    occurrence = candidate.command_occurrences[0]
    route_journal = candidate.route_journals[0]
    foreign_occurrence = replace(
        occurrence,
        subject_id="mallory",
        nonce=occurrence.nonce + 1,
    )
    _, foreign_verified_route = _verified_route_for_occurrence(
        candidate.profile,
        foreign_occurrence,
        post_state_root=route_journal.post_state_root,
    )

    for witnesses, error_type, message in (
        ((), ValueError, "route witness count"),
        ((foreign_verified_route,), ValueError, "route witness occurrence"),
        ((object(),), TypeError, "invalid verified route"),
    ):
        verifier = _RecordingReceiptVerifier()

        # Act / Assert
        with pytest.raises(error_type, match=message):
            verify_economic_epoch_v1(
                replace(
                    candidate,
                    verified_routes=witnesses,
                ),
                verifier,
            )
        assert verifier.calls == []

    substituted_route_journal = replace(
        route_journal,
        post_state_root=_root(49_999),
    )
    substituted_certificate = replace(
        candidate.certificate,
        post_state_root=substituted_route_journal.post_state_root,
        ordered_route_journal_roots=(substituted_route_journal.journal_root,),
    )
    substituted_certificate = replace(
        substituted_certificate,
        journal_bytes=len(substituted_certificate.canonical_journal_bytes),
    )
    verifier = _RecordingReceiptVerifier()

    # Act / Assert: a valid witness for the old journal cannot authorize a new one.
    with pytest.raises(ValueError, match="route witness journal"):
        verify_economic_epoch_v1(
            replace(
                candidate,
                certificate=substituted_certificate,
                route_journals=(substituted_route_journal,),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_epoch_rejects_noncanonical_command_and_route_witness_order() -> None:
    # Arrange
    candidate = _epoch_admission_fixture(2)
    reversed_occurrences = tuple(reversed(candidate.command_occurrences))
    reversed_journals = tuple(reversed(candidate.route_journals))
    reversed_witnesses = tuple(reversed(candidate.verified_routes))
    reversed_certificate = replace(
        candidate.certificate,
        ordered_occurrence_ids=tuple(item.occurrence_id for item in reversed_occurrences),
        ordered_route_journal_roots=tuple(item.journal_root for item in reversed_journals),
    )
    reversed_certificate = replace(
        reversed_certificate,
        journal_bytes=len(reversed_certificate.canonical_journal_bytes),
    )
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="canonically ordered"):
        verify_economic_epoch_v1(
            replace(
                candidate,
                certificate=reversed_certificate,
                command_occurrences=reversed_occurrences,
                route_journals=reversed_journals,
                verified_routes=reversed_witnesses,
            ),
            verifier,
        )
    assert verifier.calls == []


def test_migration_certificate_rejects_skipped_predecessor_and_epoch_jump() -> None:
    row = MigrationObjectRowV1(
        source_object_id="vault-1",
        source_release_id=_root(40_000),
        target_release_id=_root(40_001),
        classification=MigrationObjectClassV1.MIGRATED,
        source_object_root=_root(40_002),
        target_object_root=_root(40_003),
        continuity_root=_root(40_004),
    )
    certificate = StateMigrationCertificateV1(
        source_profile_root=_root(40_010),
        target_profile_root=_root(40_011),
        predecessor_profile_root=_root(40_010),
        source_state_root=_root(40_012),
        target_state_root=_root(40_013),
        source_writer_epoch=7,
        target_writer_epoch=8,
        object_rows=(row,),
        custody_continuity_root=_root(40_014),
        liability_continuity_root=_root(40_015),
        terminal_continuity_root=_root(40_016),
        replay_continuity_root=_root(40_017),
        root_image_id=_root(40_018),
        proof_receipt_root=_root(40_019),
        receipt_kind=ReceiptKindV1.SUCCINCT,
    )
    assert certificate.target_writer_epoch == certificate.source_writer_epoch + 1
    with pytest.raises(ValueError, match="predecessor"):
        replace(certificate, predecessor_profile_root=_root(40_020))
    with pytest.raises(ValueError, match="exactly once"):
        replace(certificate, target_writer_epoch=9)


def test_atomic_commit_is_idempotent_and_binding_rejects_are_noops() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    verified, body, _, _, _ = _verified_epoch(profile, route, pre_state, post_state)
    port = GlobalEconomicCommitPortV1(profile, pre_state)
    bad_body = replace(body, finality_root=_root(50_000))
    rejected = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=bad_body,
    )
    assert rejected.status is CommitOutcomeStatusV1.BINDING_REJECTED
    assert port.state == pre_state
    committed = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert committed.status is CommitOutcomeStatusV1.COMMITTED
    assert port.state == post_state
    retry = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert retry.status is CommitOutcomeStatusV1.ALREADY_COMMITTED
    assert retry.record == committed.record


def test_commit_rejects_certificate_chain_and_deployment_drift_as_noop() -> None:
    """RIPR: verifier journals cannot move a foreign chain into local state."""

    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    verified, body, _, occurrence, _route_journal = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )

    substitutions = (
        ("chain_id", "foreign-chain", "certificate chain mismatch"),
        ("deployment_root", _root(88_001), "certificate deployment mismatch"),
    )
    for field_name, foreign_value, expected_reason in substitutions:
        port = GlobalEconomicCommitPortV1(profile, pre_state)
        foreign_occurrence = replace(occurrence, **{field_name: foreign_value})
        foreign_route = _verified_route_effect_fixture(
            profile,
            foreign_occurrence,
            post_state_root=post_state.state_root,
        )
        foreign_route_journal = foreign_route.route_journal
        foreign_verified_route = foreign_route.verified_route
        foreign_effects = compose_asset_lane_epoch_effect_plans_v1(
            (foreign_route.effect_plan,)
        )
        foreign_certificate = replace(
            verified.certificate,
            **{
                    field_name: foreign_value,
                    "ordered_occurrence_ids": (foreign_occurrence.occurrence_id,),
                    "ordered_route_journal_roots": (foreign_route_journal.journal_root,),
                    "ordered_route_assumption_roots": (
                        foreign_verified_route.assumption_root,
                    ),
                    "effect_plan_root": foreign_effects.effect_plan_root,
                },
            )
        foreign_certificate = replace(
            foreign_certificate,
            journal_bytes=len(foreign_certificate.canonical_journal_bytes),
        )
        foreign_verified = verify_economic_epoch_v1(
            _epoch_candidate(
                profile,
                foreign_certificate,
                (foreign_occurrence,),
                (foreign_route_journal,),
                (foreign_verified_route,),
                (foreign_route.effect_plan,),
                foreign_effects,
                b"succinct-receipt-one",
            ),
            _RecordingReceiptVerifier(),
        )
        before = (port.state, port.records)

        rejected = port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=foreign_verified,
            body_and_state=body,
        )

        assert rejected.status is CommitOutcomeStatusV1.BINDING_REJECTED
        assert rejected.reason == expected_reason
        assert rejected.record is None
        assert rejected.state == before[0]
        assert (port.state, port.records) == before


def test_committed_replay_requires_exact_context_and_binding_tuple() -> None:
    """BDD/RIPR: a committed ID cannot authorize substituted replay inputs."""

    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    verified, body, _, _, _ = _verified_epoch(profile, route, pre_state, post_state)
    port = GlobalEconomicCommitPortV1(profile, pre_state)

    committed = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert committed.status is CommitOutcomeStatusV1.COMMITTED

    before_exact_retry = (port.state, port.records)
    exact_retry = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert exact_retry.status is CommitOutcomeStatusV1.ALREADY_COMMITTED
    assert exact_retry.record == committed.record
    assert exact_retry.state == before_exact_retry[0]
    assert (port.state, port.records) == before_exact_retry

    before_rejected_retries = (port.state, port.records)
    substitutions = (
        (
            "body finality root",
            pre_state.state_root,
            profile.profile_id,
            replace(body, finality_root=_root(50_000)),
            CommitOutcomeStatusV1.BINDING_REJECTED,
            "finality root mismatch",
        ),
        (
            "ordered command body hashes",
            pre_state.state_root,
            profile.profile_id,
            replace(body, ordered_command_body_hashes=(_root(50_003),)),
            CommitOutcomeStatusV1.BINDING_REJECTED,
            "body commitment mismatch",
        ),
        (
            "data availability root",
            pre_state.state_root,
            profile.profile_id,
            replace(body, data_availability_root=_root(50_004)),
            CommitOutcomeStatusV1.BINDING_REJECTED,
            "data availability root mismatch",
        ),
        (
            "receipt archive root",
            pre_state.state_root,
            profile.profile_id,
            replace(body, receipt_archive_root=_root(50_005)),
            CommitOutcomeStatusV1.BINDING_REJECTED,
            "receipt archive root mismatch",
        ),
        (
            "expected profile",
            pre_state.state_root,
            _root(50_001),
            body,
            CommitOutcomeStatusV1.PROFILE_MISMATCH,
            "expected profile is inactive",
        ),
        (
            "expected head",
            _root(50_002),
            profile.profile_id,
            body,
            CommitOutcomeStatusV1.STALE_HEAD,
            "expected head is stale",
        ),
    )
    for (
        label,
        expected_head,
        expected_profile,
        replay_body,
        expected_status,
        expected_reason,
    ) in substitutions:
        replay = port.commit_verified_economic_epoch(
            expected_head=expected_head,
            expected_profile=expected_profile,
            verified_epoch=verified,
            body_and_state=replay_body,
        )
        assert replay.status is expected_status, label
        assert replay.reason == expected_reason, label
        assert replay.record is None, label
        assert replay.state == before_rejected_retries[0], label
        assert (port.state, port.records) == before_rejected_retries, label


def test_concurrent_roots_have_one_atomic_winner_and_one_stale_noop() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    first, body, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=b"succinct-receipt-first",
    )
    second, _, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=b"succinct-receipt-second",
    )
    port = GlobalEconomicCommitPortV1(profile, pre_state)

    def publish(verified: VerifiedEconomicEpochV1) -> CommitOutcomeStatusV1:
        return port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=verified,
            body_and_state=body,
        ).status

    with ThreadPoolExecutor(max_workers=2) as executor:
        statuses = tuple(executor.map(publish, (first, second)))
    assert sorted(status.value for status in statuses) == ["COMMITTED", "STALE_HEAD"]
    assert port.state == post_state
    assert len(port.records) == 1
