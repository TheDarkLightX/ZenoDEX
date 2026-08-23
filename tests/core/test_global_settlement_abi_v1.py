from __future__ import annotations

import hashlib
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import FrozenInstanceError, dataclass, replace
from threading import Event

import pytest

import src.core.global_economic_state_effect_refinement_v1 as refinement_module
import src.core.route_global_state_projection_v1 as route_projection_module
import src.integration.global_economic_commit_v1 as commit_module
from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
    project_asset_transfer_state_v1,
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
from src.core.economic_command_authentication_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    AuthenticatedEconomicCommandV1,
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
    EconomicCommandIntentV1,
    authenticate_economic_command_intent_v1,
    bind_authenticated_intent_to_occurrence_v1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    CommandSignatureVerifierEvidenceArtifactV1,
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    bind_economic_command_signature_verifier_deployment_v1,
    command_signature_verifier_backend_protocol_root_v1,
    command_signature_verifier_implementation_root_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
    CommandSignatureVerifierEvidenceStatusV1,
    EconomicCommandSignatureVerifierRegistryV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from src.core.economic_initial_state_publisher_verification_v1 import (
    _verify_economic_migration_for_publisher_v1,
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
    EconomicEpochRouteStateDisclosureV1,
    EconomicInitialStateAdmissionV1,
    EconomicInitialStateAtomClassificationV1,
    EconomicInitialStateAtomKindV1,
    EconomicInitialStateAtomSourceV1,
    EconomicInitialStateCertificateV1,
    EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
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
    OutboxStateV1,
    OutboxStatusV1,
    ProfileStatusV1,
    ReceiptKindV1,
    ReleaseStatusV1,
    ReplayStateV1,
    RouteCompositionJournalV1,
    RouteRegistryV1,
    RouteReleaseV1,
    StateMigrationCertificateV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    VerifiedEconomicEpochV1,
    canonical_economic_command_body_bytes_v1,
    compose_asset_lane_epoch_effect_plans_v1,
    derive_economic_initial_state_atom_occurrences_v1,
    derive_economic_initial_state_outbox_continuity_root_v1,
    derive_economic_initial_state_replay_continuity_root_v1,
    derive_economic_initial_state_terminal_continuity_root_v1,
    economic_initial_state_atom_coverage_policy_binding_v1,
    economic_initial_state_atom_occurrence_v1,
    m6_asset_precision_policy_binding_v1,
    m6_capability_policy_binding_v1,
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


_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1 = (
    b"global-abi-command-signature-verifier-test-artifact-v1"
)


def _signature_verifier_manifest_v1() -> EconomicCommandSignatureVerifierEvidenceManifestV1:
    evidence_artifacts = tuple(
        CommandSignatureVerifierEvidenceArtifactV1(status, _root(430 + index))
        for index, status in enumerate(
            sorted(CommandSignatureVerifierEvidenceStatusV1, key=lambda item: item.value)
        )
    )
    return EconomicCommandSignatureVerifierEvidenceManifestV1(
        signature_algorithm="BLS12_381_G2_BASIC_V1",
        implementation_root=command_signature_verifier_implementation_root_v1(
            _COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1
        ),
        public_key_schema_root=_root(417),
        signature_schema_root=_root(418),
        message_schema_root=_root(419),
        specification_root=_root(420),
        source_root=_root(421),
        toolchain_root=_root(422),
        backend_protocol_root=command_signature_verifier_backend_protocol_root_v1(),
        max_public_key_bytes=160,
        max_signature_bytes=4_096,
        evidence_artifacts=evidence_artifacts,
    )


def _signature_verifier_registry_v1() -> EconomicCommandSignatureVerifierRegistryV1:
    manifest = _signature_verifier_manifest_v1()
    return EconomicCommandSignatureVerifierRegistryV1(
        (
            EconomicCommandSignatureVerifierReleaseV1.build(
                semantic_version="1.0.0-global-abi-test",
                signature_algorithm="BLS12_381_G2_BASIC_V1",
                implementation_root=manifest.implementation_root,
                public_key_schema_root=manifest.public_key_schema_root,
                signature_schema_root=manifest.signature_schema_root,
                message_schema_root=manifest.message_schema_root,
                specification_root=manifest.specification_root,
                source_root=manifest.source_root,
                toolchain_root=manifest.toolchain_root,
                evidence_manifest_root=manifest.manifest_root,
                max_public_key_bytes=manifest.max_public_key_bytes,
                max_signature_bytes=manifest.max_signature_bytes,
                status=ReleaseStatusV1.ACTIVE_NEW,
                accepts_new_authentications=True,
                evidence_statuses=tuple(row.status for row in manifest.evidence_artifacts),
            ),
        )
    )


def _initial_asset_rows_v1(
) -> tuple[tuple[EconomicAmountV1, ...], tuple[AssetSupplyV1, ...]]:
    alice_atoms = MAX_EPOCH_COMMANDS_V1 * 32 + 100
    balances = tuple(
        sorted(
            (
                EconomicAmountV1("alice", "USD", "accounts", alice_atoms),
                EconomicAmountV1("recipient", "USD", "accounts", 10),
                EconomicAmountV1("treasury", "USD", "accounts", 5),
            ),
            key=lambda item: item.key,
        )
    )
    return balances, (AssetSupplyV1("USD", alice_atoms + 15),)


def _source_manifest_for_rows_v1(
    kind: EconomicInitialStateKindV1,
    balances: tuple[EconomicAmountV1, ...],
    supplies: tuple[AssetSupplyV1, ...],
) -> EconomicInitialStateSourceManifestV1:
    classification = (
        EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION
        if kind is EconomicInitialStateKindV1.GENESIS
        else EconomicInitialStateAtomClassificationV1.MIGRATED_TARGET
    )
    occurrences = (
        *(
            economic_initial_state_atom_occurrence_v1(
                EconomicInitialStateAtomKindV1.BALANCE,
                index,
                row,
            )
            for index, row in enumerate(balances)
        ),
        *(
            economic_initial_state_atom_occurrence_v1(
                EconomicInitialStateAtomKindV1.SUPPLY,
                index,
                row,
            )
            for index, row in enumerate(supplies)
        ),
    )
    return EconomicInitialStateSourceManifestV1(
        kind,
        tuple(
            EconomicInitialStateAtomSourceV1(
                occurrence,
                classification,
                _root(700 + index),
            )
            for index, occurrence in enumerate(occurrences)
        ),
    )


def _genesis_source_manifest_v1() -> EconomicInitialStateSourceManifestV1:
    balances, supplies = _initial_asset_rows_v1()
    return _source_manifest_for_rows_v1(
        EconomicInitialStateKindV1.GENESIS,
        balances,
        supplies,
    )


def _source_manifest_for_state_v1(
    kind: EconomicInitialStateKindV1,
    state: GlobalEconomicStateV1,
) -> EconomicInitialStateSourceManifestV1:
    classification = (
        EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION
        if kind is EconomicInitialStateKindV1.GENESIS
        else EconomicInitialStateAtomClassificationV1.MIGRATED_TARGET
    )
    return EconomicInitialStateSourceManifestV1(
        kind,
        tuple(
            EconomicInitialStateAtomSourceV1(
                occurrence,
                classification,
                _root(700 + index),
            )
            for index, occurrence in enumerate(
                derive_economic_initial_state_atom_occurrences_v1(state)
            )
        ),
    )


def _policy_registry_for_route_v1(
    route: RouteReleaseV1,
    source_manifest: EconomicInitialStateSourceManifestV1 | None = None,
) -> EconomicPolicyRegistryV1:
    source_manifest = source_manifest or _genesis_source_manifest_v1()
    authorization_registry = EconomicCommandAuthorizationRegistryV1(
        (
            EconomicCommandAuthorizationV1(
                command_kind=route.command_kind,
                subject_id="alice",
                grant_root=_root(600),
                route_release_id=route.route_release_id,
                signer_key_id="alice-key-1",
                signer_public_key="bls12-381-g2:alice-public-key",
                signature_algorithm="BLS12_381_G2_BASIC_V1",
                valid_from_height=0,
                valid_through_height=(1 << 64) - 1,
                min_nonce=0,
                max_nonce=(1 << 64) - 1,
                enabled=True,
            ),
        )
    )
    signature_verifier_registry = _signature_verifier_registry_v1()
    return EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (
                    EconomicPolicyBindingV1(
                        ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
                        route.command_kind,
                        authorization_registry.registry_root,
                    ),
                    EconomicPolicyBindingV1(
                        ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
                        route.command_kind,
                        signature_verifier_registry.registry_root,
                    ),
                    m6_asset_precision_policy_binding_v1(),
                    m6_capability_policy_binding_v1(),
                    economic_initial_state_atom_coverage_policy_binding_v1(
                        source_manifest
                    ),
                ),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
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


def _profile(
    *,
    source_manifest: EconomicInitialStateSourceManifestV1 | None = None,
    authority_epoch: int = 7,
    verifier_registry_root: str | None = None,
    status: ProfileStatusV1 = ProfileStatusV1.ACTIVE,
) -> tuple[EconomicProfileSnapshotV1, RouteReleaseV1]:
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
    policy_registry = _policy_registry_for_route_v1(route, source_manifest)
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=authority_epoch,
        lane_registry=lane_registry,
        lane_coordinator_registry=lane_coordinator_registry,
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(410),
        root_image_id=_root(411),
        verifier_registry_root=verifier_registry_root or _root(412),
        migration_registry_root=_root(413),
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=_root(415),
        status=status,
    )
    return profile, route


def _state(profile: EconomicProfileSnapshotV1, *, height: int) -> GlobalEconomicStateV1:
    if height not in (0, 1):
        raise ValueError("test economic state supports only adjacent epoch heights")
    module_state = _epoch_asset_module_state(profile)
    pre_state = _global_state_from_asset_module(profile, module_state, height=0)
    if height == 0:
        return pre_state
    route = profile.route_registry.routes[0]
    occurrence = _occurrence(profile, route, pre_state)
    module_input = _asset_module_input_for_occurrence(profile, occurrence, module_state)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    replay = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
    return _global_state_from_asset_module(
        profile,
        accepted.post_state,
        height=1,
        replay_state=(replay,),
    )


def _initial_state_admission(
    profile: EconomicProfileSnapshotV1,
    state: GlobalEconomicStateV1,
    *,
    receipt_bytes: bytes = b"succinct-initial-state-receipt",
    kind: EconomicInitialStateKindV1 = EconomicInitialStateKindV1.GENESIS,
    source_manifest: EconomicInitialStateSourceManifestV1 | None = None,
    source_profile_root: str = ZERO_ROOT_V1,
    source_state_root: str = ZERO_ROOT_V1,
    source_writer_epoch: int = 0,
    source_height: int = 0,
    predecessor_state: GlobalEconomicStateV1 | None = None,
) -> EconomicInitialStateAdmissionV1:
    source_manifest = source_manifest or _source_manifest_for_state_v1(kind, state)
    receipt_root = "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    certificate = EconomicInitialStateCertificateV1(
        kind=kind,
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        height=state.height,
        state_root=state.state_root,
        source_profile_root=source_profile_root,
        source_state_root=source_state_root,
        source_writer_epoch=source_writer_epoch,
        source_height=source_height,
        state_atom_coverage_root=source_manifest.manifest_root,
        lane_object_coverage_root=_root(451),
        replay_continuity_root=derive_economic_initial_state_replay_continuity_root_v1(
            kind,
            state,
            predecessor_state,
        ),
        terminal_continuity_root=(
            derive_economic_initial_state_terminal_continuity_root_v1(
                kind,
                state,
                predecessor_state,
            )
        ),
        outbox_continuity_root=derive_economic_initial_state_outbox_continuity_root_v1(
            kind,
            state,
            predecessor_state,
        ),
        source_manifest_root=_root(455),
        toolchain_manifest_root=_root(456),
        root_image_id=profile.root_image_id,
        receipt_root=receipt_root,
        receipt_kind=ReceiptKindV1.SUCCINCT,
        journal_bytes=1,
        cycle_budget=1_000_000,
    )
    certificate = replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )
    return EconomicInitialStateAdmissionV1(
        profile=profile,
        policy_registry=_policy_registry_for_route_v1(
            profile.route_registry.routes[0],
            source_manifest,
        ),
        state=state,
        predecessor_state=predecessor_state,
        source_manifest=source_manifest,
        certificate=certificate,
        receipt_bytes=receipt_bytes,
    )


def _commit_port(
    profile: EconomicProfileSnapshotV1,
    state: GlobalEconomicStateV1,
    receipt_verifier: _RecordingReceiptVerifier | None = None,
) -> GlobalEconomicCommitPortV1:
    verifier = receipt_verifier or _RecordingReceiptVerifier()
    return GlobalEconomicCommitPortV1(
        _initial_state_admission(profile, state),
        verifier,
    )


def _migration_admission_for_source_head(
    source_profile: EconomicProfileSnapshotV1,
    source_state: GlobalEconomicStateV1,
) -> tuple[
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    EconomicInitialStateAdmissionV1,
]:
    provisional_target = replace(
        _state(source_profile, height=1),
        replay_state=source_state.replay_state,
        terminal_obligations=source_state.terminal_obligations,
        outbox=source_state.outbox,
    )
    source_manifest = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.MIGRATION,
        provisional_target,
    )
    target_profile, _ = _profile(
        source_manifest=source_manifest,
        authority_epoch=source_profile.authority_epoch + 1,
    )
    migrated_state = replace(
        _state(target_profile, height=1),
        replay_state=source_state.replay_state,
        terminal_obligations=source_state.terminal_obligations,
        outbox=source_state.outbox,
    )
    admission = _initial_state_admission(
        target_profile,
        migrated_state,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=source_manifest,
        source_profile_root=source_profile.profile_id,
        source_state_root=source_state.state_root,
        source_writer_epoch=source_state.writer_epoch,
        source_height=source_state.height,
        predecessor_state=source_state,
    )
    return target_profile, migrated_state, admission


def _verify_migration_admission_for_test(
    admission: EconomicInitialStateAdmissionV1,
    expected_source_state: GlobalEconomicStateV1,
    verifier: _RecordingReceiptVerifier,
) -> None:
    _verify_economic_migration_for_publisher_v1(
        admission,
        expected_source_state,
        verifier,
    )


def _occurrence(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    pre_state: GlobalEconomicStateV1,
) -> EconomicCommandOccurrenceV1:
    command = AssetTransferCommandV1(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
        asset="USD",
        sender="alice",
        recipient="recipient",
        amount_atoms=30,
        max_fee_atoms=2,
    )
    return EconomicCommandOccurrenceV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        height=pre_state.height + 1,
        tx_index=0,
        op_index=0,
        command_kind=route.command_kind,
        command_body_hash=command.command_body_hash,
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


class _AcceptingCommandSignatureVerifierV1:
    def verify_command_signature(
        self,
        *,
        signature_algorithm: str,
        signer_public_key: str,
        message_bytes: bytes,
        signature_bytes: bytes,
    ) -> bool:
        return bool(
            signature_algorithm
            and signer_public_key
            and message_bytes
            and signature_bytes
        )


def _authenticate_occurrence_for_test(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    command: AssetTransferCommandV1,
) -> AuthenticatedEconomicCommandV1:
    route = profile.route_registry.route_for_command(occurrence.command_kind)
    authorization = EconomicCommandAuthorizationV1(
        command_kind=occurrence.command_kind,
        subject_id=occurrence.subject_id,
        grant_root=occurrence.grant_root,
        route_release_id=route.route_release_id,
        signer_key_id="alice-key-1",
        signer_public_key="bls12-381-g2:alice-public-key",
        signature_algorithm="BLS12_381_G2_BASIC_V1",
        valid_from_height=0,
        valid_through_height=(1 << 64) - 1,
        min_nonce=0,
        max_nonce=(1 << 64) - 1,
        enabled=True,
    )
    authorization_registry = EconomicCommandAuthorizationRegistryV1((authorization,))
    signature_verifier_registry = _signature_verifier_registry_v1()
    policy_registry = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (
                    EconomicPolicyBindingV1(
                        ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
                        occurrence.command_kind,
                        authorization_registry.registry_root,
                    ),
                    EconomicPolicyBindingV1(
                        ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
                        occurrence.command_kind,
                        signature_verifier_registry.registry_root,
                    ),
                    m6_asset_precision_policy_binding_v1(),
                    m6_capability_policy_binding_v1(),
                    economic_initial_state_atom_coverage_policy_binding_v1(
                        _genesis_source_manifest_v1()
                    ),
                ),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )
    authenticated_intent = authenticate_economic_command_intent_v1(
        EconomicCommandAuthenticationCandidateV1(
            profile=profile,
            policy_registry=policy_registry,
            authorization_registry=authorization_registry,
            signature_verifier_registry=signature_verifier_registry,
            intent=EconomicCommandIntentV1(
                chain_id=occurrence.chain_id,
                deployment_root=occurrence.deployment_root,
                profile_root=occurrence.profile_root,
                command_kind=occurrence.command_kind,
                command_body_hash=occurrence.command_body_hash,
                route_release_id=occurrence.route_release_id,
                subject_id=occurrence.subject_id,
                grant_root=occurrence.grant_root,
                nonce=occurrence.nonce,
                consumed_object_ids=occurrence.consumed_object_ids,
                valid_from_height=0,
                valid_through_height=(1 << 64) - 1,
            ),
            envelope=EconomicCommandAuthenticationEnvelopeV1(
                command_body_bytes=canonical_economic_command_body_bytes_v1(
                    occurrence.command_kind,
                    command,
                ),
                signer_key_id=authorization.signer_key_id,
                signer_public_key=authorization.signer_public_key,
                signature_algorithm=authorization.signature_algorithm,
                signature_bytes=b"test-command-signature-v1",
            ),
        ),
        bind_economic_command_signature_verifier_deployment_v1(
            release=signature_verifier_registry.releases[0],
            evidence_manifest=_signature_verifier_manifest_v1(),
            measured_artifact_bytes=_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            backend=_AcceptingCommandSignatureVerifierV1(),
        ),
    )
    return bind_authenticated_intent_to_occurrence_v1(
        authenticated_intent,
        occurrence,
    )


@dataclass(frozen=True, slots=True)
class _VerifiedRouteEffectFixture:
    route_journal: RouteCompositionJournalV1
    verified_route: VerifiedRouteCompositionV1
    lane_journals: tuple[LaneCompositionJournalV1, ...]
    effect_plan: GlobalEconomicEffectPlanV1
    post_module_state: AssetTransferStateV1


@dataclass(frozen=True, slots=True)
class _EpochRouteFixture:
    pre_state: GlobalEconomicStateV1
    post_state: GlobalEconomicStateV1
    occurrences: tuple[EconomicCommandOccurrenceV1, ...]
    route_journals: tuple[RouteCompositionJournalV1, ...]
    route_state_disclosures: tuple[EconomicEpochRouteStateDisclosureV1, ...]
    verified_routes: tuple[VerifiedRouteCompositionV1, ...]
    route_effect_plans: tuple[GlobalEconomicEffectPlanV1, ...]


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
            _authenticate_occurrence_for_test(
                profile,
                occurrence,
                module_input.command,
            ),
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
    candidate, lane_effects = _lane_receipt_candidate_fixture(
        profile,
        occurrence,
        module_input,
        accepted,
        verified_module,
    )
    verified_lane = verify_asset_lane_composition_receipt_v1(
        candidate,
        _RecordingReceiptVerifier(),
    )
    return candidate.lane_journal, verified_lane, lane_effects


def _lane_receipt_candidate_fixture(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
    verified_module: VerifiedLaneModuleTransitionV1,
) -> tuple[LaneCompositionReceiptCandidateV1, GlobalEconomicEffectPlanV1]:
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
    return (
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
        lane_result.effects,
    )


def _verified_route_effect_fixture(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    post_state_root: str,
    pre_module_state: AssetTransferStateV1 | None = None,
) -> _VerifiedRouteEffectFixture:
    """Build the opaque module -> lane -> route chain and retain its effects."""

    candidate, lane_effects, post_module_state = _route_receipt_candidate_fixture(
        profile,
        occurrence,
        post_state_root=post_state_root,
        pre_module_state=pre_module_state,
    )
    verified_route = verify_route_composition_receipt_v1(
        candidate,
        _RecordingReceiptVerifier(),
    )
    return _VerifiedRouteEffectFixture(
        candidate.route_journal,
        verified_route,
        candidate.lane_journals,
        lane_effects,
        post_module_state,
    )


def _route_receipt_candidate_fixture(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    post_state_root: str,
    pre_module_state: AssetTransferStateV1 | None = None,
) -> tuple[
    RouteCompositionReceiptCandidateV1,
    GlobalEconomicEffectPlanV1,
    AssetTransferStateV1,
]:
    """Build one valid route candidate without verifying its final receipt."""

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
    return (
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
    publisher: GlobalEconomicCommitPortV1 | None = None,
    receipt_verifier: _RecordingReceiptVerifier | None = None,
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
        ordered_command_body_hashes=(occurrence.command_body_hash,),
        receipt_archive_root=_root(701),
        data_availability_root=_root(702),
        finality_root=_root(703),
    )
    route_fixture = _verified_route_effect_fixture(
        profile,
        occurrence,
        post_state_root=post_state.state_root,
        pre_module_state=_epoch_asset_module_state(profile),
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
    verifier = receipt_verifier or _RecordingReceiptVerifier()
    candidate = _epoch_candidate(
        profile,
        certificate,
        pre_state,
        post_state,
        (occurrence,),
        (route_journal,),
        (
            EconomicEpochRouteStateDisclosureV1(
                route_fixture.lane_journals,
                post_state,
            ),
        ),
        (verified_route,),
        route_effect_plans,
        effects,
        receipt_bytes,
    )
    verified = (
        publisher.verify_economic_epoch(candidate)
        if publisher is not None
        else verify_economic_epoch_v1(candidate, verifier)
    )
    return verified, body, verifier, occurrence, route_journal


def _publisher_verified_epoch(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    *,
    receipt_bytes: bytes = b"succinct-receipt-one",
) -> tuple[
    GlobalEconomicCommitPortV1,
    VerifiedEconomicEpochV1,
    EconomicEpochBodyAndStateV1,
    _RecordingReceiptVerifier,
    EconomicCommandOccurrenceV1,
    RouteCompositionJournalV1,
]:
    verifier = _RecordingReceiptVerifier()
    publisher = _commit_port(profile, pre_state, verifier)
    verified, body, _, occurrence, journal = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=receipt_bytes,
        publisher=publisher,
        receipt_verifier=verifier,
    )
    return publisher, verified, body, verifier, occurrence, journal


def _epoch_candidate(
    profile: EconomicProfileSnapshotV1,
    certificate: GlobalEconomicEpochCertificateV1,
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    occurrences: tuple[EconomicCommandOccurrenceV1, ...],
    route_journals: tuple[RouteCompositionJournalV1, ...],
    route_state_disclosures: tuple[EconomicEpochRouteStateDisclosureV1, ...],
    verified_routes: tuple[VerifiedRouteCompositionV1, ...],
    route_effect_plans: tuple[GlobalEconomicEffectPlanV1, ...],
    effect_plan: GlobalEconomicEffectPlanV1,
    receipt_bytes: bytes,
) -> EconomicEpochReceiptCandidateV1:
    return EconomicEpochReceiptCandidateV1(
        profile=profile,
        certificate=certificate,
        pre_state=pre_state,
        post_state=post_state,
        command_occurrences=occurrences,
        ordered_command_body_hashes=tuple(
            occurrence.command_body_hash for occurrence in occurrences
        ),
        route_journals=route_journals,
        route_state_disclosures=route_state_disclosures,
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
    balances, supplies = _initial_asset_rows_v1()
    return AssetTransferStateV1(
        module_release_id=release.release_id,
        policies=(AssetTransferPolicyV1("USD", "treasury", 2, True),),
        balances=balances,
        supplies=supplies,
    )


def _global_state_from_asset_module(
    profile: EconomicProfileSnapshotV1,
    module_state: AssetTransferStateV1,
    *,
    height: int,
    replay_state: tuple[ReplayStateV1, ...] = (),
) -> GlobalEconomicStateV1:
    asset_lane_state = project_asset_transfer_state_v1(
        module_state,
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
    )
    lane_roots = tuple(
        LaneStateRootV1(
            lane_id=release.lane_id,
            module_release_id=release.release_id,
            enabled=(
                release.status is ReleaseStatusV1.ACTIVE_NEW
                and release.accepts_new_objects
            ),
            state_root=(
                asset_lane_state.state_root
                if release.lane_id is LaneIdV1.ASSET_TRANSFER
                else _root(1_000 + ordinal)
            ),
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
        balances=module_state.balances,
        supplies=module_state.supplies,
        replay_state=replay_state,
    )


def _epoch_route_fixture(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    pre_state: GlobalEconomicStateV1,
    count: int,
    *,
    nonce_start: int = 1,
    pre_module_state: AssetTransferStateV1 | None = None,
    hidden_balance_after: int | None = None,
    hidden_height_after: int | None = None,
) -> _EpochRouteFixture:
    occurrences: list[EconomicCommandOccurrenceV1] = []
    route_journals: list[RouteCompositionJournalV1] = []
    route_state_disclosures: list[EconomicEpochRouteStateDisclosureV1] = []
    verified_routes: list[VerifiedRouteCompositionV1] = []
    route_effect_plans: list[GlobalEconomicEffectPlanV1] = []
    module_state = pre_module_state or _epoch_asset_module_state(profile)
    current_state = pre_state
    for index in range(count):
        occurrence = replace(
            _occurrence(profile, route, pre_state),
            tx_index=index,
            nonce=nonce_start + index,
            pre_state_root=current_state.state_root,
        )
        module_input = _asset_module_input_for_occurrence(
            profile,
            occurrence,
            module_state,
        )
        accepted, verified_module = _verified_asset_module_for_occurrence(
            profile,
            occurrence,
            module_input,
        )
        lane_journal, verified_lane, lane_effects = _verified_asset_lane_for_occurrence(
            profile,
            occurrence,
            module_input,
            accepted,
            verified_module,
        )
        replay = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
        next_state = _global_state_from_asset_module(
            profile,
            accepted.post_state,
            height=pre_state.height + 1,
            replay_state=tuple(
                sorted(
                    (*current_state.replay_state, replay),
                    key=lambda row: row.replay_id,
                )
            ),
        )
        if hidden_balance_after == index:
            first_balance = next_state.balances[0]
            next_state = replace(
                next_state,
                balances=(
                    replace(first_balance, amount_atoms=first_balance.amount_atoms + 1),
                    *next_state.balances[1:],
                ),
            )
        if hidden_height_after == index:
            next_state = replace(next_state, height=next_state.height + 1)
        route_journal = RouteCompositionJournalV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=profile.profile_id,
            writer_epoch=profile.authority_epoch,
            route_release_id=occurrence.route_release_id,
            command_occurrence_id=occurrence.occurrence_id,
            ordered_lane_journal_roots=(lane_journal.journal_root,),
            pre_state_root=occurrence.pre_state_root,
            post_state_root=next_state.state_root,
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
        occurrences.append(occurrence)
        route_journals.append(route_journal)
        route_state_disclosures.append(
            EconomicEpochRouteStateDisclosureV1((lane_journal,), next_state)
        )
        verified_routes.append(verified_route)
        route_effect_plans.append(lane_effects)
        module_state = accepted.post_state
        current_state = next_state
    return _EpochRouteFixture(
        pre_state,
        current_state,
        tuple(occurrences),
        tuple(route_journals),
        tuple(route_state_disclosures),
        tuple(verified_routes),
        tuple(route_effect_plans),
    )


def _epoch_admission_fixture(
    count: int,
    *,
    pre_state: GlobalEconomicStateV1 | None = None,
    nonce_start: int = 1,
    hidden_balance_after: int | None = None,
    hidden_height_after: int | None = None,
    verifier_registry_root: str | None = None,
) -> EconomicEpochReceiptCandidateV1:
    profile, route = _profile(verifier_registry_root=verifier_registry_root)
    selected_pre_state = pre_state or _state(profile, height=0)
    if selected_pre_state.profile_root != profile.profile_id:
        raise ValueError("epoch admission fixture pre-state profile mismatch")
    module_state = _epoch_asset_module_state(profile)
    if pre_state is not None:
        module_state = replace(
            module_state,
            balances=selected_pre_state.balances,
            supplies=selected_pre_state.supplies,
        )
    routes = _epoch_route_fixture(
        profile,
        route,
        selected_pre_state,
        count,
        nonce_start=nonce_start,
        pre_module_state=module_state,
        hidden_balance_after=hidden_balance_after,
        hidden_height_after=hidden_height_after,
    )
    effects = compose_asset_lane_epoch_effect_plans_v1(routes.route_effect_plans)
    receipt_bytes = f"succinct-epoch-receipt-{count}".encode("ascii")
    certificate = GlobalEconomicEpochCertificateV1(
        chain_id=selected_pre_state.chain_id,
        deployment_root=selected_pre_state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        height=selected_pre_state.height + 1,
        pre_state_root=selected_pre_state.state_root,
        post_state_root=routes.post_state.state_root,
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
        routes.pre_state,
        routes.post_state,
        routes.occurrences,
        routes.route_journals,
        routes.route_state_disclosures,
        routes.verified_routes,
        routes.route_effect_plans,
        effects,
        receipt_bytes,
    )


def _epoch_candidate_with_rebound_post_state(
    candidate: EconomicEpochReceiptCandidateV1,
    post_state: GlobalEconomicStateV1,
) -> EconomicEpochReceiptCandidateV1:
    occurrence = candidate.command_occurrences[0]
    route_fixture = _verified_route_effect_fixture(
        candidate.profile,
        occurrence,
        post_state_root=post_state.state_root,
        pre_module_state=_epoch_asset_module_state(candidate.profile),
    )
    effects = compose_asset_lane_epoch_effect_plans_v1((route_fixture.effect_plan,))
    certificate = replace(
        candidate.certificate,
        post_state_root=post_state.state_root,
        ordered_route_journal_roots=(route_fixture.route_journal.journal_root,),
        ordered_route_assumption_roots=(route_fixture.verified_route.assumption_root,),
        effect_plan_root=effects.effect_plan_root,
    )
    certificate = replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )
    return _epoch_candidate(
        candidate.profile,
        certificate,
        candidate.pre_state,
        post_state,
        (occurrence,),
        (route_fixture.route_journal,),
        (
            EconomicEpochRouteStateDisclosureV1(
                route_fixture.lane_journals,
                post_state,
            ),
        ),
        (route_fixture.verified_route,),
        (route_fixture.effect_plan,),
        effects,
        candidate.receipt_bytes,
    )


def test_occurrence_identity_binds_exact_command_body_hash() -> None:
    # Arrange: one authenticated occurrence coordinate and two distinct command bodies.
    profile, route = _profile()
    occurrence = _occurrence(profile, route, _state(profile, height=0))

    # Act
    changed_body = replace(occurrence, command_body_hash=_root(799))

    # Assert: module/lane/route journals cannot reuse the old occurrence identity.
    assert changed_body.occurrence_id != occurrence.occurrence_id
    assert changed_body.replay_id == occurrence.replay_id


@pytest.mark.parametrize(
    ("body_hashes", "message"),
    (
        ((), "count mismatch"),
        ((_root(700), _root(701)), "count mismatch"),
        ((_root(799),), "binding mismatch"),
    ),
)
def test_epoch_rejects_unpaired_command_body_hashes_before_receipt(
    body_hashes: tuple[str, ...],
    message: str,
) -> None:
    # Arrange: bypass the frozen candidate constructor to model hostile retained input.
    candidate = _epoch_admission_fixture(1)
    verifier = _RecordingReceiptVerifier()
    object.__setattr__(candidate, "ordered_command_body_hashes", body_hashes)

    # Act / Assert
    with pytest.raises(ValueError, match=message):
        verify_economic_epoch_v1(candidate, verifier)
    assert verifier.calls == []


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


def test_route_receipt_candidate_rejects_subclassed_envelope_before_verification() -> None:
    """A caller-defined receipt type cannot cross the route authority boundary."""

    profile, route = _profile()
    pre_state = _state(profile, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    candidate, _, _ = _route_receipt_candidate_fixture(
        profile,
        occurrence,
        post_state_root=_state(profile, height=1).state_root,
    )

    class HostileReceiptEnvelope(RouteCompositionReceiptEnvelopeV1):
        pass

    hostile_receipt = HostileReceiptEnvelope(
        candidate.receipt.receipt_kind,
        candidate.receipt.receipt_bytes,
    )

    with pytest.raises(TypeError, match="receipt envelope must be exact typed data"):
        RouteCompositionReceiptCandidateV1(
            candidate.profile,
            candidate.occurrence,
            candidate.lane_journals,
            candidate.verified_lanes,
            candidate.route_journal,
            hostile_receipt,
        )


def test_lane_receipt_candidate_rejects_subclassed_envelope_before_verification() -> None:
    """A caller-defined receipt type cannot cross the lane authority boundary."""

    profile, route = _profile()
    pre_state = _state(profile, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    module_input = _asset_module_input_for_occurrence(
        profile,
        occurrence,
        _default_asset_module_state(profile, occurrence),
    )
    accepted, verified_module = _verified_asset_module_for_occurrence(
        profile,
        occurrence,
        module_input,
    )
    candidate, _ = _lane_receipt_candidate_fixture(
        profile,
        occurrence,
        module_input,
        accepted,
        verified_module,
    )

    class HostileLaneReceiptEnvelope(LaneCompositionReceiptEnvelopeV1):
        pass

    hostile_receipt = HostileLaneReceiptEnvelope(
        candidate.receipt.receipt_kind,
        candidate.receipt.receipt_bytes,
    )

    with pytest.raises(TypeError, match="receipt envelope must be exact typed data"):
        LaneCompositionReceiptCandidateV1(
            candidate.profile,
            candidate.occurrence,
            candidate.structural_composition,
            candidate.lane_journal,
            hostile_receipt,
        )


def test_lane_verifier_owns_all_bindings_across_receipt_callback() -> None:
    """Lane callback alias mutation cannot change the authenticated witness."""

    # Arrange: retain every caller-owned object read by lane verification.
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    module_input = _asset_module_input_for_occurrence(
        profile,
        occurrence,
        _default_asset_module_state(profile, occurrence),
    )
    accepted, verified_module = _verified_asset_module_for_occurrence(
        profile,
        occurrence,
        module_input,
    )
    candidate, _ = _lane_receipt_candidate_fixture(
        profile,
        occurrence,
        module_input,
        accepted,
        verified_module,
    )
    expected = {
        "profile_id": candidate.profile.profile_id,
        "route_release_id": candidate.structural_composition.route_release_id,
        "command_occurrence_id": candidate.occurrence.occurrence_id,
        "structural_composition_root": candidate.structural_composition.binding_root,
        "lane_journal_root": candidate.lane_journal.journal_root,
    }

    class MutatingLaneReceiptVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(candidate.profile, "profile_id", _root(79_001))
            object.__setattr__(candidate.occurrence, "nonce", 79_002)
            object.__setattr__(
                candidate.structural_composition._fields,
                "route_release_id",
                _root(79_003),
            )
            object.__setattr__(
                candidate.structural_composition._fields,
                "verified_module_binding_root",
                _root(79_004),
            )
            object.__setattr__(
                candidate.lane_journal,
                "post_lane_root",
                _root(79_005),
            )
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-after-check")

    # Act
    verified = verify_asset_lane_composition_receipt_v1(
        candidate,
        MutatingLaneReceiptVerifier(),
    )

    # Assert: all witness coordinates derive from one pre-callback snapshot.
    assert verified.profile_id == expected["profile_id"]
    assert verified.route_release_id == expected["route_release_id"]
    assert verified.command_occurrence_id == expected["command_occurrence_id"]
    assert verified.structural_composition_root == expected["structural_composition_root"]
    assert verified.lane_journal_root == expected["lane_journal_root"]


def test_route_verifier_rechecks_post_construction_type_substitution() -> None:
    """A frozen-candidate bypass still rejects before the verifier callback."""

    # Arrange: construct an honest candidate, then bypass its frozen field guard.
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    candidate, _, _ = _route_receipt_candidate_fixture(
        profile,
        occurrence,
        post_state_root=_state(profile, height=1).state_root,
    )

    class HostileReceiptEnvelope(RouteCompositionReceiptEnvelopeV1):
        pass

    object.__setattr__(
        candidate,
        "receipt",
        HostileReceiptEnvelope(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )
    verifier = _RecordingReceiptVerifier()

    # Act / Assert: use-time ownership rejects before cryptographic admission.
    with pytest.raises(TypeError, match="receipt envelope must be exact typed data"):
        verify_route_composition_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_route_verifier_owns_all_bindings_across_receipt_callback() -> None:
    """Verifier-side alias mutation cannot change the authenticated route witness."""

    # Arrange: retain every caller-owned object the route witness reads.
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    occurrence = _occurrence(profile, route, pre_state)
    candidate, _, _ = _route_receipt_candidate_fixture(
        profile,
        occurrence,
        post_state_root=_state(profile, height=1).state_root,
    )
    expected = {
        "profile_id": candidate.profile.profile_id,
        "command_occurrence_id": candidate.occurrence.occurrence_id,
        "ordered_lane_binding_roots": tuple(
            lane.binding_root for lane in candidate.verified_lanes
        ),
        "ordered_lane_journal_roots": tuple(
            lane.journal_root for lane in candidate.lane_journals
        ),
        "route_journal_root": candidate.route_journal.journal_root,
    }

    class MutatingRouteReceiptVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(candidate.profile, "profile_id", _root(78_001))
            object.__setattr__(candidate.occurrence, "nonce", 78_002)
            object.__setattr__(
                candidate.lane_journals[0],
                "post_lane_root",
                _root(78_003),
            )
            object.__setattr__(
                candidate.verified_lanes[0]._fields,
                "receipt_digest",
                _root(78_004),
            )
            object.__setattr__(
                candidate.route_journal,
                "post_state_root",
                _root(78_005),
            )
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-after-check")

    # Act
    verified = verify_route_composition_receipt_v1(
        candidate,
        MutatingRouteReceiptVerifier(),
    )

    # Assert: every returned authority coordinate comes from one owned snapshot.
    assert verified.profile_id == expected["profile_id"]
    assert verified.command_occurrence_id == expected["command_occurrence_id"]
    assert verified.ordered_lane_binding_roots == expected["ordered_lane_binding_roots"]
    assert verified.ordered_lane_journal_roots == expected["ordered_lane_journal_roots"]
    assert verified.route_journal_root == expected["route_journal_root"]


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
    assert verified.state_effect_refinement.pre_state_root == pre_state.state_root
    assert verified.state_effect_refinement.post_state_root == post_state.state_root
    assert (
        verified.state_effect_refinement.effect_plan_root
        == verified.effect_plan.effect_plan_root
    )
    assert len(verified.route_state_projection_roots) == 1
    assert len(verified.route_state_effect_refinement_roots) == 1
    assert verified.recheck_route_state_projections(
        pre_state=pre_state,
        post_state=post_state,
    ) == verified.route_state_projection_roots
    assert len(verifier.calls) == 1
    assert verifier.calls[0][1] == profile.root_image_id
    with pytest.raises(AttributeError, match="immutable"):
        verified._receipt_digest = _root(8_999)
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedEconomicEpochV1(object(), object())  # type: ignore[arg-type]
    forged = object.__new__(VerifiedEconomicEpochV1)
    with pytest.raises(TypeError, match="not verifier-registered"):
        _ = forged.commit_id
    forged_port = _commit_port(
        profile,
        pre_state,
        _RecordingReceiptVerifier(),
    )
    with pytest.raises(TypeError, match="not verifier-registered"):
        forged_port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=forged,
            body_and_state=body,
        )
    assert forged_port.state == pre_state
    assert forged_port.records == ()
    rebuilt_route = _verified_route_effect_fixture(
        profile,
        occurrence,
        post_state_root=post_state.state_root,
        pre_module_state=_epoch_asset_module_state(profile),
    )
    rebuilt_route_journal = rebuilt_route.route_journal
    verified_route = rebuilt_route.verified_route
    assert rebuilt_route_journal == route_journal
    candidate = _epoch_candidate(
        profile,
        verified.certificate,
        pre_state,
        post_state,
        (occurrence,),
        (route_journal,),
        (
            EconomicEpochRouteStateDisclosureV1(
                rebuilt_route.lane_journals,
                post_state,
            ),
        ),
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


def test_epoch_state_refinement_kills_replay_and_balance_mutants_before_receipt() -> None:
    # Arrange: rebuild all route/certificate roots around semantically invalid full states.
    valid = _epoch_admission_fixture(1)
    missing_replay = replace(valid.post_state, replay_state=())
    first_balance = valid.post_state.balances[0]
    wrong_balances = (
        replace(first_balance, amount_atoms=first_balance.amount_atoms + 1),
        *valid.post_state.balances[1:],
    )
    wrong_balance = replace(valid.post_state, balances=wrong_balances)

    for post_state, message in (
        (missing_replay, "replay state delta mismatch"),
        (wrong_balance, "balance delta mismatch"),
    ):
        candidate = _epoch_candidate_with_rebound_post_state(valid, post_state)
        verifier = _RecordingReceiptVerifier()

        # Act / Assert: structural route receipts cannot authorize a false state/effect relation.
        with pytest.raises(ValueError, match=message):
            verify_economic_epoch_v1(candidate, verifier)
        assert verifier.calls == []


def test_epoch_rejects_foreign_checker_witness_before_receipt(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    valid = _epoch_admission_fixture(1)
    foreign = verify_economic_epoch_v1(
        _epoch_admission_fixture(2),
        _RecordingReceiptVerifier(),
    ).state_effect_refinement
    monkeypatch.setattr(
        refinement_module,
        "refine_global_economic_state_effects_v1",
        lambda _candidate: foreign,
    )
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(ValueError, match="state/effect refinement root mismatch"):
        verify_economic_epoch_v1(valid, verifier)
    assert verifier.calls == []


def test_epoch_rejects_hostile_refinement_subclass_before_receipt(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    valid = _epoch_admission_fixture(1)

    class ForgedRefinement(refinement_module.GlobalEconomicStateEffectRefinementV1):
        def __init__(self) -> None:
            pass

        @property
        def pre_state_root(self) -> str:
            return valid.certificate.pre_state_root

        @property
        def post_state_root(self) -> str:
            return valid.certificate.post_state_root

        @property
        def effect_plan_root(self) -> str:
            return valid.certificate.effect_plan_root

    monkeypatch.setattr(
        refinement_module,
        "refine_global_economic_state_effects_v1",
        lambda _candidate: ForgedRefinement(),
    )
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(TypeError, match="exact checker-constructed type"):
        verify_economic_epoch_v1(valid, verifier)
    assert verifier.calls == []


def test_epoch_route_state_projection_rejects_hostile_witness_before_receipt(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    valid = _epoch_admission_fixture(1)

    class ForgedProjection(route_projection_module.RouteGlobalStateProjectionV1):
        def __init__(self) -> None:
            pass

        @property
        def projection_root(self) -> str:
            return _root(88_100)

    monkeypatch.setattr(
        route_projection_module,
        "project_route_global_state_v1",
        lambda _candidate: ForgedProjection(),
    )
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(TypeError, match="exact checker-constructed type"):
        verify_economic_epoch_v1(valid, verifier)
    assert verifier.calls == []


def test_epoch_route_state_disclosures_apply_count_and_intermediate_mutation_bva() -> None:
    valid = _epoch_admission_fixture(2)

    with pytest.raises(ValueError, match="route state disclosure count mismatch"):
        replace(valid, route_state_disclosures=())
    with pytest.raises(ValueError, match="route state disclosure count mismatch"):
        replace(
            valid,
            route_state_disclosures=(
                *valid.route_state_disclosures,
                valid.route_state_disclosures[-1],
            ),
        )

    first = valid.route_state_disclosures[0]
    unselected = first.post_state.lane_roots[1]
    hidden_post_state = replace(
        first.post_state,
        lane_roots=(
            first.post_state.lane_roots[0],
            replace(unselected, state_root=_root(88_101)),
            *first.post_state.lane_roots[2:],
        ),
    )
    candidate = replace(
        valid,
        route_state_disclosures=(
            replace(first, post_state=hidden_post_state),
            valid.route_state_disclosures[1],
        ),
    )
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(ValueError, match="global state root mismatch"):
        verify_economic_epoch_v1(candidate, verifier)
    assert verifier.calls == []


def test_epoch_route_refinement_rejects_transient_hidden_balance_before_receipt() -> None:
    # Arrange: route one injects an unlabelled atom into full state and route two
    # restores the honest endpoint. Route/lane roots and witnesses are coherent.
    candidate = _epoch_admission_fixture(2, hidden_balance_after=0)
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="balance delta mismatch"):
        verify_economic_epoch_v1(candidate, verifier)
    assert verifier.calls == []


def test_epoch_route_refinement_rejects_transient_hidden_height_before_receipt() -> None:
    # Arrange: route one temporarily advances to the wrong height while route
    # two restores the valid epoch endpoint and all state roots are rebuilt.
    candidate = _epoch_admission_fixture(2, hidden_height_after=0)
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="epoch height context mismatch"):
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
    assert len(verified.effect_occurrences) == sum(
        len(plan.rows) for plan in candidate.route_effect_plans
    )
    assert len(
        {item.effect_occurrence_id for item in verified.effect_occurrences}
    ) == len(verified.effect_occurrences)
    offset = 0
    for occurrence, plan in zip(
        candidate.command_occurrences,
        candidate.route_effect_plans,
        strict=True,
    ):
        route_occurrences = verified.effect_occurrences[
            offset : offset + len(plan.rows)
        ]
        assert tuple(item.command_occurrence_id for item in route_occurrences) == (
            occurrence.occurrence_id,
        ) * len(plan.rows)
        assert tuple(item.effect_index for item in route_occurrences) == tuple(
            range(len(plan.rows))
        )
        offset += len(plan.rows)


def test_epoch_two_route_state_evidence_has_stable_python_golden_roots() -> None:
    candidate = _epoch_admission_fixture(2)
    assert candidate.ordered_command_body_hashes == (
        candidate.command_occurrences[0].command_body_hash,
        candidate.command_occurrences[0].command_body_hash,
    )
    verified = verify_economic_epoch_v1(candidate, _RecordingReceiptVerifier())

    assert verified.route_state_projection_roots == (
        "0x78b7b302ab293d7bb992779182e08673f45c531fcffa9a4f5a19f4e621fdbe80",
        "0x0dd8dd74f449f56fa991baaafc61b76115f953874d7f0fc50be78510017836bc",
    )
    assert verified.route_state_effect_refinement_roots == (
        "0xf32bf976a6fd7a54a74054fa25cdd7364e7792fb6852eb480cf0ed60caf5a163",
        "0xddb28263b51f66b4ee6a451a5301393ecd6c0afd5ea30fcb4ca8eee4b6f8a86e",
    )


def test_epoch_candidate_rejects_sixty_five_occurrences_at_typed_ingress() -> None:
    valid = _epoch_admission_fixture(1)

    with pytest.raises(ValueError, match="between one and 64 command occurrences"):
        replace(valid, command_occurrences=valid.command_occurrences * 65)


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
                ordered_command_body_hashes=tuple(
                    occurrence.command_body_hash
                    for occurrence in reversed_occurrences
                ),
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
    port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )
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


def test_epoch_verifier_owns_certificate_and_effect_snapshots_across_callback() -> None:
    # Arrange: the verifier callback retains aliases to the caller's frozen-looking values.
    candidate = _epoch_admission_fixture(1)
    expected_post_root = candidate.certificate.post_state_root
    expected_effect_root = candidate.effect_plan.effect_plan_root

    class MutatingReceiptVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(candidate.certificate, "post_state_root", _root(77_001))
            row = candidate.effect_plan.rows[0]
            object.__setattr__(row, "delta_atoms", row.delta_atoms + 1)

    # Act
    verified = verify_economic_epoch_v1(candidate, MutatingReceiptVerifier())

    # Assert: callback mutation cannot alter the authority-bearing returned values.
    assert verified.certificate.post_state_root == expected_post_root
    assert verified.effect_plan.effect_plan_root == expected_effect_root
    assert verified.state_effect_refinement.post_state_root == expected_post_root
    assert verified.state_effect_refinement.effect_plan_root == expected_effect_root

    exposed_certificate = verified.certificate
    exposed_effect_plan = verified.effect_plan
    exposed_refinement = verified.state_effect_refinement
    object.__setattr__(exposed_certificate, "post_state_root", _root(77_002))
    object.__setattr__(exposed_effect_plan.rows[0], "delta_atoms", 77_003)
    object.__setattr__(exposed_refinement._fields, "post_state_root", _root(77_004))

    assert verified.certificate.post_state_root == expected_post_root
    assert verified.effect_plan.effect_plan_root == expected_effect_root
    assert verified.state_effect_refinement.post_state_root == expected_post_root


def test_epoch_verifier_owns_profile_snapshot_across_callback() -> None:
    candidate = _epoch_admission_fixture(1)
    expected_image_id = candidate.profile.root_image_id
    observed_images: list[str] = []

    class ProfileMutatingReceiptVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_journal_bytes
            observed_images.append(expected_image_id)
            object.__setattr__(candidate.profile, "root_image_id", _root(77_010))

    verified = verify_economic_epoch_v1(candidate, ProfileMutatingReceiptVerifier())

    assert observed_images == [expected_image_id]
    assert verified.certificate.root_image_id == expected_image_id


def test_commit_rebinds_refinement_against_post_return_certificate_mutation() -> None:
    # Arrange: coherently re-root the exposed certificate around an unbalanced post-state.
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )
    original_commit_id = verified.commit_id
    first_balance = post_state.balances[0]
    unbalanced_state = replace(
        post_state,
        balances=(
            replace(first_balance, amount_atoms=first_balance.amount_atoms + 1),
            *post_state.balances[1:],
        ),
    )
    unbalanced_body = replace(body, post_state=unbalanced_state)
    for field_name, value in (
        ("_certificate", replace(verified.certificate, post_state_root=unbalanced_state.state_root)),
        ("_state_effect_refinement", verified.state_effect_refinement),
    ):
        with pytest.raises(AttributeError):
            object.__setattr__(verified, field_name, value)
    assert verified.commit_id == original_commit_id
    # Act
    result = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=unbalanced_body,
    )

    # Assert: the commit lock rebinds the original checker witness and remains a no-op.
    assert result.status is CommitOutcomeStatusV1.BINDING_REJECTED
    assert result.reason is not None
    assert result.reason.startswith("route state projection recheck rejected:")
    assert port.state == pre_state
    assert port.records == ()


def test_opaque_handle_blocks_route_disclosure_replacement_before_commit() -> None:
    # Arrange: the handle has no writable or visible route-disclosure slot.
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )
    projection_roots = verified.route_state_projection_roots
    with pytest.raises(AttributeError):
        object.__setattr__(verified, "_route_state_disclosures", ())
    assert verified.recheck_route_state_projections(
        pre_state=pre_state,
        post_state=post_state,
    ) == projection_roots
    # Act
    result = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )

    # Assert: rejected field injection cannot alter the verifier-owned authority record.
    assert result.status is CommitOutcomeStatusV1.COMMITTED
    assert result.record is not None
    assert result.record.route_state_projection_roots == projection_roots
    assert port.state == post_state
    retry = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert retry.status is CommitOutcomeStatusV1.ALREADY_COMMITTED
    assert retry.record == result.record


def test_caller_selected_verifier_witness_cannot_reach_the_publisher() -> None:
    def verified_epoch_and_body(
        count: int,
    ) -> tuple[
        VerifiedEconomicEpochV1,
        EconomicEpochBodyAndStateV1,
        EconomicEpochReceiptCandidateV1,
    ]:
        candidate = _epoch_admission_fixture(count)
        body = EconomicEpochBodyAndStateV1(
            pre_state_root=candidate.pre_state.state_root,
            post_state=candidate.post_state,
            ordered_command_body_hashes=tuple(
                _root(77_100 + index) for index in range(count)
            ),
            receipt_archive_root=_root(77_200 + count),
            data_availability_root=candidate.certificate.data_availability_root,
            finality_root=candidate.certificate.finality_root,
        )
        certificate = replace(
            candidate.certificate,
            body_commitment=body.body_commitment,
        )
        certificate = replace(
            certificate,
            journal_bytes=len(certificate.canonical_journal_bytes),
        )
        rebound = replace(
            candidate,
            certificate=certificate,
            expected_body_commitment=body.body_commitment,
        )
        return (
            verify_economic_epoch_v1(rebound, _RecordingReceiptVerifier()),
            body,
            rebound,
        )

    # Arrange: reproduce the former attack by replacing every visible private
    # authority field with a coherent two-command witness except the old receipt digest.
    original, _original_body, _original_candidate = verified_epoch_and_body(1)
    foreign, foreign_body, foreign_candidate = verified_epoch_and_body(2)
    original_commit_id = original.commit_id
    attack_certificate = replace(
        foreign.certificate,
        receipt_root=original.receipt_digest,
    )
    attack_certificate = replace(
        attack_certificate,
        journal_bytes=len(attack_certificate.canonical_journal_bytes),
    )
    substitutions = {
        "_certificate": attack_certificate,
        "_certificate_root": attack_certificate.certificate_root,
        "_command_occurrences": foreign_candidate.command_occurrences,
        "_effect_plan": foreign.effect_plan,
        "_effect_plan_root": foreign.verified_effect_plan_root,
        "_ordered_route_binding_roots": foreign.ordered_route_binding_roots,
        "_profile": foreign_candidate.profile,
        "_route_effect_plans": foreign_candidate.route_effect_plans,
        "_route_journals": foreign_candidate.route_journals,
        "_route_state_disclosures": foreign_candidate.route_state_disclosures,
        "_route_state_effect_refinement_roots": foreign.route_state_effect_refinement_roots,
        "_route_state_projection_roots": foreign.route_state_projection_roots,
        "_state_effect_refinement": foreign.state_effect_refinement,
        "_state_effect_refinement_root": foreign.verified_state_effect_refinement_root,
    }
    for field_name, value in substitutions.items():
        with pytest.raises(AttributeError):
            object.__setattr__(original, field_name, value)
    assert original.commit_id == original_commit_id
    port = _commit_port(
        foreign_candidate.profile,
        _epoch_admission_fixture(1).pre_state,
        _RecordingReceiptVerifier(),
    )
    before = (port.state, port.records)

    # Act and assert: caller-selected receipt acceptance cannot mint publication authority.
    with pytest.raises(TypeError, match="verified by this exact commit port"):
        port.commit_verified_economic_epoch(
            expected_head=foreign_body.pre_state_root,
            expected_profile=foreign_candidate.profile.profile_id,
            verified_epoch=original,
            body_and_state=foreign_body,
        )
    assert (port.state, port.records) == before


def test_release_selected_witness_is_bound_to_one_exact_publisher() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    first_port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )
    second_port = _commit_port(
        profile,
        pre_state,
        _RecordingReceiptVerifier(),
    )

    with pytest.raises(TypeError, match="verified by this exact commit port"):
        second_port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=verified,
            body_and_state=body,
        )
    object.__setattr__(
        first_port,
        "_receipt_verifier",
        _RecordingReceiptVerifier(),
    )
    with pytest.raises(TypeError, match="verified by this exact commit port"):
        first_port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=profile.profile_id,
            verified_epoch=verified,
            body_and_state=body,
        )

    assert first_port.state == pre_state
    assert second_port.state == pre_state
    assert first_port.records == second_port.records == ()


def test_commit_owns_published_state_against_retained_body_alias() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )
    committed = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    published_root = committed.state.state_root
    assert committed.record is not None
    stored_record = port.records[0]

    object.__setattr__(body.post_state.balances[0], "amount_atoms", 99_999)
    object.__setattr__(committed.record, "post_state_root", _root(88_880))

    assert port.state.state_root == published_root
    assert committed.state.state_root == published_root
    assert port.records[0] == stored_record


def test_commit_port_owns_initial_state_before_validation_returns() -> None:
    profile, _ = _profile()
    initial_state = _state(profile, height=0)
    expected_root = initial_state.state_root
    verifier = _RecordingReceiptVerifier()
    port = _commit_port(profile, initial_state, verifier)

    object.__setattr__(initial_state.balances[0], "amount_atoms", 99_999)

    assert port.state.state_root == expected_root
    assert len(verifier.calls) == 1
    assert port.initial_state_certificate_root != ZERO_ROOT_V1


def test_commit_port_rejects_plain_or_mismatched_initial_state_before_receipt() -> None:
    profile, _ = _profile()
    initial_state = _state(profile, height=0)
    admission = _initial_state_admission(profile, initial_state)
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(TypeError, match="initial-state admission"):
        GlobalEconomicCommitPortV1(initial_state, verifier)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="state root mismatch"):
        GlobalEconomicCommitPortV1(
            replace(
                admission,
                certificate=replace(admission.certificate, state_root=_root(77_100)),
            ),
            verifier,
        )
    with pytest.raises(ValueError, match="receipt root mismatch"):
        GlobalEconomicCommitPortV1(
            replace(
                admission,
                certificate=replace(admission.certificate, receipt_root=_root(77_101)),
            ),
            verifier,
        )
    with pytest.raises(ValueError, match="ACTIVE profile"):
        GlobalEconomicCommitPortV1(
            replace(admission, profile=replace(profile, status=ProfileStatusV1.SHADOW)),
            verifier,
        )
    without_capability = EconomicPolicyRegistryV1(
        tuple(
            binding
            for binding in admission.policy_registry.bindings
            if binding != m6_capability_policy_binding_v1()
        )
    )
    with pytest.raises(ValueError, match="policy registry root mismatch"):
        GlobalEconomicCommitPortV1(
            replace(admission, policy_registry=without_capability),
            verifier,
        )
    wrong_capability = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (
                    replace(binding, policy_root=_root(77_102))
                    if binding == m6_capability_policy_binding_v1()
                    else binding
                    for binding in admission.policy_registry.bindings
                ),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )
    wrong_profile = EconomicProfileSnapshotV1.build(
        authority_epoch=profile.authority_epoch,
        lane_registry=profile.lane_registry,
        lane_coordinator_registry=profile.lane_coordinator_registry,
        route_registry=profile.route_registry,
        proof_shape_root=profile.proof_shape_root,
        root_image_id=profile.root_image_id,
        verifier_registry_root=profile.verifier_registry_root,
        migration_registry_root=profile.migration_registry_root,
        policy_registry_root=wrong_capability.registry_root,
        terminal_registry_root=profile.terminal_registry_root,
        status=profile.status,
    )
    wrong_state = _state(wrong_profile, height=0)
    wrong_admission = replace(
        _initial_state_admission(wrong_profile, wrong_state),
        policy_registry=wrong_capability,
    )
    with pytest.raises(ValueError, match="capability manifest root mismatch"):
        GlobalEconomicCommitPortV1(wrong_admission, verifier)

    without_precision = EconomicPolicyRegistryV1(
        tuple(
            binding
            for binding in admission.policy_registry.bindings
            if binding != m6_asset_precision_policy_binding_v1()
        )
    )
    with pytest.raises(ValueError, match="policy registry root mismatch"):
        GlobalEconomicCommitPortV1(
            replace(admission, policy_registry=without_precision),
            verifier,
        )
    wrong_precision = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (
                    replace(binding, policy_root=_root(77_103))
                    if binding == m6_asset_precision_policy_binding_v1()
                    else binding
                    for binding in admission.policy_registry.bindings
                ),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )
    wrong_precision_profile = EconomicProfileSnapshotV1.build(
        authority_epoch=profile.authority_epoch,
        lane_registry=profile.lane_registry,
        lane_coordinator_registry=profile.lane_coordinator_registry,
        route_registry=profile.route_registry,
        proof_shape_root=profile.proof_shape_root,
        root_image_id=profile.root_image_id,
        verifier_registry_root=profile.verifier_registry_root,
        migration_registry_root=profile.migration_registry_root,
        policy_registry_root=wrong_precision.registry_root,
        terminal_registry_root=profile.terminal_registry_root,
        status=profile.status,
    )
    wrong_precision_state = _state(wrong_precision_profile, height=0)
    wrong_precision_admission = replace(
        _initial_state_admission(wrong_precision_profile, wrong_precision_state),
        policy_registry=wrong_precision,
    )
    with pytest.raises(ValueError, match="asset precision policy root mismatch"):
        GlobalEconomicCommitPortV1(wrong_precision_admission, verifier)

    assert verifier.calls == []


def test_initial_state_atom_coverage_rejects_omission_before_receipt_verification() -> None:
    provisional_profile, _ = _profile()
    provisional_state = _state(provisional_profile, height=0)
    complete = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.GENESIS,
        provisional_state,
    )
    omitted = replace(complete, rows=complete.rows[:-1])
    profile, _ = _profile(source_manifest=omitted)
    state = _state(profile, height=0)
    admission = _initial_state_admission(
        profile,
        state,
        source_manifest=omitted,
    )
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(ValueError, match="does not classify the exact target state"):
        GlobalEconomicCommitPortV1(admission, verifier)

    assert verifier.calls == []


def test_initial_state_atom_manifest_substitution_rejects_before_receipt_verification() -> None:
    profile, _ = _profile()
    state = _state(profile, height=0)
    admission = _initial_state_admission(profile, state)
    substituted_row = replace(
        admission.source_manifest.rows[0],
        source_authorization_root=_root(77_104),
    )
    substituted = replace(
        admission.source_manifest,
        rows=(substituted_row, *admission.source_manifest.rows[1:]),
    )
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(ValueError, match="atom coverage manifest root mismatch"):
        GlobalEconomicCommitPortV1(
            replace(admission, source_manifest=substituted),
            verifier,
        )

    assert verifier.calls == []


def test_initial_state_certificate_coverage_root_mismatch_rejects_before_receipt() -> None:
    profile, _ = _profile()
    state = _state(profile, height=0)
    admission = _initial_state_admission(profile, state)
    verifier = _RecordingReceiptVerifier()

    with pytest.raises(ValueError, match="atom coverage root mismatch"):
        GlobalEconomicCommitPortV1(
            replace(
                admission,
                certificate=replace(
                    admission.certificate,
                    state_atom_coverage_root=_root(77_105),
                ),
            ),
            verifier,
        )

    assert verifier.calls == []


def test_initial_state_callback_cannot_mutate_publisher_owned_state() -> None:
    profile, _ = _profile()
    initial_state = _state(profile, height=0)
    admission = _initial_state_admission(profile, initial_state)
    expected_state_root = initial_state.state_root
    expected_certificate_root = admission.certificate.certificate_root

    class MutatingInitialStateVerifier:
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            del receipt_bytes, expected_image_id, expected_journal_bytes
            object.__setattr__(initial_state.balances[0], "amount_atoms", 99_999)
            object.__setattr__(admission.certificate, "state_root", _root(77_102))
            object.__setattr__(
                admission.source_manifest.rows[0].occurrence,
                "row_root",
                _root(77_106),
            )

    port = GlobalEconomicCommitPortV1(admission, MutatingInitialStateVerifier())

    assert port.state.state_root == expected_state_root
    assert port.initial_state_certificate_root == expected_certificate_root


def test_commit_port_constructor_rejects_migration_without_owned_source_head() -> None:
    # Arrange
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    _, _, migration_admission = _migration_admission_for_source_head(
        source_profile,
        source_state,
    )
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="construction requires a genesis admission"):
        GlobalEconomicCommitPortV1(migration_admission, verifier)
    assert verifier.calls == []


def test_migration_activation_requires_exact_publisher_owned_source_head() -> None:
    # Arrange
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    verifier = _RecordingReceiptVerifier()
    port = _commit_port(source_profile, source_state, verifier)
    initial_certificate_root = port.initial_state_certificate_root
    foreign_source_state = replace(source_state, history_root=_root(88_200))
    _, _, foreign_admission = _migration_admission_for_source_head(
        source_profile,
        foreign_source_state,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="publisher-owned source head"):
        port.activate_migration(
            expected_head=source_state.state_root,
            expected_profile=source_profile.profile_id,
            migration_admission=foreign_admission,
        )
    assert port.state == source_state
    assert port.profile == source_profile
    assert port.initial_state_certificate_root == initial_certificate_root
    assert len(verifier.calls) == 1


def test_migration_activation_rechecks_head_and_profile_before_receipt() -> None:
    # Arrange
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    target_profile, migrated_state, migration_admission = (
        _migration_admission_for_source_head(source_profile, source_state)
    )
    verifier = _RecordingReceiptVerifier()
    port = _commit_port(source_profile, source_state, verifier)
    initial_certificate_root = port.initial_state_certificate_root

    # Act / Assert
    for expected_head, expected_profile, message in (
        (_root(88_201), source_profile.profile_id, "expected source head is stale"),
        (source_state.state_root, _root(88_202), "expected source profile is inactive"),
    ):
        with pytest.raises(ValueError, match=message):
            port.activate_migration(
                expected_head=expected_head,
                expected_profile=expected_profile,
                migration_admission=migration_admission,
            )
    assert port.state == source_state
    assert port.profile == source_profile
    assert port.initial_state_certificate_root == initial_certificate_root
    assert len(verifier.calls) == 1

    port.activate_migration(
        expected_head=source_state.state_root,
        expected_profile=source_profile.profile_id,
        migration_admission=migration_admission,
    )

    assert port.state == migrated_state
    assert port.profile == target_profile
    assert port.initial_state_certificate_root == (
        migration_admission.certificate.certificate_root
    )
    assert len(verifier.calls) == 2


def test_migration_activation_rechecks_source_head_after_receipt_callback() -> None:
    # Arrange
    source_profile, route = _profile()
    source_state = _state(source_profile, height=0)
    next_state = _state(source_profile, height=1)

    class CallbackReceiptVerifier(_RecordingReceiptVerifier):
        def __init__(self) -> None:
            super().__init__()
            self.callback: Callable[[], None] | None = None

        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            callback = self.callback
            self.callback = None
            if callback is not None:
                callback()

    verifier = CallbackReceiptVerifier()
    port = _commit_port(source_profile, source_state, verifier)
    verified_epoch, body, _, _, _ = _verified_epoch(
        source_profile,
        route,
        source_state,
        next_state,
        publisher=port,
        receipt_verifier=verifier,
    )
    _, _, migration_admission = _migration_admission_for_source_head(
        source_profile,
        source_state,
    )
    initial_certificate_root = port.initial_state_certificate_root

    def advance_source_head() -> None:
        committed = port.commit_verified_economic_epoch(
            expected_head=source_state.state_root,
            expected_profile=source_profile.profile_id,
            verified_epoch=verified_epoch,
            body_and_state=body,
        )
        assert committed.status is CommitOutcomeStatusV1.COMMITTED

    verifier.callback = advance_source_head

    # Act / Assert
    with pytest.raises(ValueError, match="source head changed during verification"):
        port.activate_migration(
            expected_head=source_state.state_root,
            expected_profile=source_profile.profile_id,
            migration_admission=migration_admission,
        )
    assert port.state == next_state
    assert port.profile == source_profile
    assert port.initial_state_certificate_root == initial_certificate_root
    assert len(verifier.calls) == 3


def test_migration_activation_hides_partial_publisher_tuple_from_readers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    target_profile, migrated_state, migration_admission = _migration_admission_for_source_head(
        source_profile, source_state
    )
    verifier = _RecordingReceiptVerifier()
    port = _commit_port(source_profile, source_state, verifier)
    source_certificate_root = port.initial_state_certificate_root
    target_certificate_root = migration_admission.certificate.certificate_root
    assert source_certificate_root != target_certificate_root
    migration_paused, release_migration = Event(), Event()
    reader_started, reader_finished = Event(), Event()
    class PausingVerifiedMigration:
        profile = target_profile
        certificate_root = target_certificate_root

        @property
        def state(self) -> GlobalEconomicStateV1:
            migration_paused.set()
            if not release_migration.wait(timeout=5):
                raise RuntimeError("migration tuple test timed out")
            return migrated_state

    monkeypatch.setattr(
        commit_module,
        "_verify_economic_migration_for_publisher_v1",
        lambda *_args: PausingVerifiedMigration(),
    )

    def read_publisher_tuple() -> tuple[EconomicProfileSnapshotV1, str]:
        reader_started.set()
        observed = (port.profile, port.initial_state_certificate_root)
        reader_finished.set()
        return observed

    # Act
    with ThreadPoolExecutor(max_workers=2) as executor:
        activation = executor.submit(
            port.activate_migration,
            expected_head=source_state.state_root,
            expected_profile=source_profile.profile_id,
            migration_admission=migration_admission,
        )
        assert migration_paused.wait(timeout=5)
        reader = executor.submit(read_publisher_tuple)
        try:
            assert reader_started.wait(timeout=5)
            reader_finished_while_migration_paused = reader_finished.wait(timeout=0.1)
        finally:
            release_migration.set()
        activation.result(timeout=5)
        observed = reader.result(timeout=5)

    # Assert
    assert reader_finished_while_migration_paused is False
    assert observed == (target_profile, target_certificate_root)


def test_migration_initial_state_requires_adjacent_writer_epoch_and_height() -> None:
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    provisional_target = replace(
        _state(source_profile, height=1),
        replay_state=source_state.replay_state,
    )
    source_manifest = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.MIGRATION,
        provisional_target,
    )
    target_profile, _ = _profile(
        source_manifest=source_manifest,
        authority_epoch=source_profile.authority_epoch + 1,
    )
    migrated_state = replace(
        _state(target_profile, height=1),
        replay_state=source_state.replay_state,
    )
    admission = _initial_state_admission(
        target_profile,
        migrated_state,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=source_manifest,
        source_profile_root=source_profile.profile_id,
        source_state_root=source_state.state_root,
        source_writer_epoch=source_profile.authority_epoch,
        source_height=source_state.height,
        predecessor_state=source_state,
    )
    migration_certificate = admission.certificate

    verifier = _RecordingReceiptVerifier()
    port = _commit_port(source_profile, source_state, verifier)
    port.activate_migration(
        expected_head=source_state.state_root,
        expected_profile=source_profile.profile_id,
        migration_admission=admission,
    )

    assert port.state.state_root == migrated_state.state_root
    assert len(verifier.calls) == 2
    replay_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="replay continuity root mismatch"):
        _verify_migration_admission_for_test(
            replace(
                admission,
                certificate=replace(
                    admission.certificate,
                    replay_continuity_root=_root(88_204),
                ),
            ),
            source_state,
            replay_verifier,
        )
    assert replay_verifier.calls == []
    outbox_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="outbox continuity root mismatch"):
        _verify_migration_admission_for_test(
            replace(
                admission,
                certificate=replace(
                    admission.certificate,
                    outbox_continuity_root=_root(88_206),
                ),
            ),
            source_state,
            outbox_verifier,
        )
    assert outbox_verifier.calls == []
    with pytest.raises(ValueError, match="writer epoch exactly once"):
        replace(
            migration_certificate,
            source_writer_epoch=target_profile.authority_epoch - 2,
        )
    with pytest.raises(ValueError, match="one transition height"):
        replace(migration_certificate, source_height=migrated_state.height)


def test_migration_rejects_target_only_replay_row_before_receipt() -> None:
    # Arrange
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    provisional_target = replace(
        _state(source_profile, height=1),
        replay_state=source_state.replay_state,
    )
    source_manifest = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.MIGRATION,
        provisional_target,
    )
    target_profile, _ = _profile(
        source_manifest=source_manifest,
        authority_epoch=source_profile.authority_epoch + 1,
    )
    exact_target = replace(
        _state(target_profile, height=1),
        replay_state=source_state.replay_state,
    )
    exact_admission = _initial_state_admission(
        target_profile,
        exact_target,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=source_manifest,
        source_profile_root=source_profile.profile_id,
        source_state_root=source_state.state_root,
        source_writer_epoch=source_state.writer_epoch,
        source_height=source_state.height,
        predecessor_state=source_state,
    )
    target_only_row = ReplayStateV1("migration-injected", _root(88_207))
    changed_target = replace(exact_target, replay_state=(target_only_row,))
    changed_certificate = replace(
        exact_admission.certificate,
        state_root=changed_target.state_root,
        replay_continuity_root=exact_admission.certificate.replay_continuity_root,
        terminal_continuity_root=(
            derive_economic_initial_state_terminal_continuity_root_v1(
                EconomicInitialStateKindV1.MIGRATION,
                changed_target,
                source_state,
            )
        ),
        outbox_continuity_root=(
            derive_economic_initial_state_outbox_continuity_root_v1(
                EconomicInitialStateKindV1.MIGRATION,
                changed_target,
                source_state,
            )
        ),
    )
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(
        ValueError,
        match="preserve the exact predecessor replay state",
    ):
        _verify_migration_admission_for_test(
            replace(
                exact_admission,
                state=changed_target,
                certificate=changed_certificate,
            ),
            source_state,
            verifier,
        )
    assert verifier.calls == []


def test_migration_initial_state_rejects_predecessor_substitution_before_receipt() -> None:
    # Arrange
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    provisional_target = replace(
        _state(source_profile, height=1),
        replay_state=source_state.replay_state,
    )
    source_manifest = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.MIGRATION,
        provisional_target,
    )
    target_profile, _ = _profile(
        source_manifest=source_manifest,
        authority_epoch=source_profile.authority_epoch + 1,
    )
    migrated_state = replace(
        _state(target_profile, height=1),
        replay_state=source_state.replay_state,
    )
    admission = _initial_state_admission(
        target_profile,
        migrated_state,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=source_manifest,
        source_profile_root=source_profile.profile_id,
        source_state_root=source_state.state_root,
        source_writer_epoch=source_state.writer_epoch,
        source_height=source_state.height,
        predecessor_state=source_state,
    )
    substituted_balance = replace(
        source_state.balances[0],
        amount_atoms=source_state.balances[0].amount_atoms + 1,
    )
    substituted_state = replace(
        source_state,
        balances=(substituted_balance, *source_state.balances[1:]),
    )
    verifier = _RecordingReceiptVerifier()

    # Act / Assert: the committed source root must be recomputed from the witness.
    with pytest.raises(ValueError, match="predecessor state root mismatch"):
        _verify_migration_admission_for_test(
            replace(admission, predecessor_state=substituted_state),
            substituted_state,
            verifier,
        )
    with pytest.raises(ValueError, match="requires a predecessor state"):
        replace(admission, predecessor_state=None)

    coordinate_substitutions = (
        ("chain id", replace(source_state, chain_id="other-chain")),
        ("deployment root", replace(source_state, deployment_root=_root(88_201))),
        ("profile root", replace(source_state, profile_root=_root(88_202))),
        ("writer epoch", replace(source_state, writer_epoch=source_state.writer_epoch + 1)),
        ("height", replace(source_state, height=source_state.height + 1)),
    )
    for label, substituted_coordinate_state in coordinate_substitutions:
        rebound_certificate = replace(
            admission.certificate,
            source_state_root=substituted_coordinate_state.state_root,
        )
        with pytest.raises(ValueError, match=rf"predecessor {label} mismatch"):
            _verify_migration_admission_for_test(
                replace(
                    admission,
                    predecessor_state=substituted_coordinate_state,
                    certificate=rebound_certificate,
                ),
                substituted_coordinate_state,
                verifier,
            )

    predecessor_with_unpreserved_replay = replace(
        source_state,
        replay_state=(ReplayStateV1("source-replay-1", _root(88_203)),),
    )
    replay_rebound_certificate = replace(
        admission.certificate,
        source_state_root=predecessor_with_unpreserved_replay.state_root,
    )
    with pytest.raises(ValueError, match="preserve the exact predecessor replay state"):
        _verify_migration_admission_for_test(
            replace(
                admission,
                predecessor_state=predecessor_with_unpreserved_replay,
                certificate=replay_rebound_certificate,
            ),
            predecessor_with_unpreserved_replay,
            verifier,
        )

    target_replay_row = ReplayStateV1("source-replay-2", _root(88_206))
    predecessor_with_rewritten_occurrence = replace(
        source_state,
        replay_state=(
            replace(
                target_replay_row,
                occurrence_id=_root(88_204),
            ),
        ),
    )
    rewritten_occurrence_certificate = replace(
        admission.certificate,
        source_state_root=predecessor_with_rewritten_occurrence.state_root,
    )
    with pytest.raises(ValueError, match="preserve the exact predecessor replay state"):
        _verify_migration_admission_for_test(
            replace(
                admission,
                predecessor_state=predecessor_with_rewritten_occurrence,
                certificate=rewritten_occurrence_certificate,
            ),
            predecessor_with_rewritten_occurrence,
            verifier,
        )

    pending_outbox = OutboxStateV1(
        effect_id=_root(88_207),
        destination_id="bridge:test",
        payload_hash=_root(88_208),
        commit_id=_root(88_209),
        status=OutboxStatusV1.PENDING,
    )
    predecessor_with_outbox = replace(source_state, outbox=(pending_outbox,))
    migrated_with_outbox = replace(migrated_state, outbox=(pending_outbox,))
    exact_outbox_admission = _initial_state_admission(
        target_profile,
        migrated_with_outbox,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=source_manifest,
        source_profile_root=source_profile.profile_id,
        source_state_root=predecessor_with_outbox.state_root,
        source_writer_epoch=predecessor_with_outbox.writer_epoch,
        source_height=predecessor_with_outbox.height,
        predecessor_state=predecessor_with_outbox,
    )
    _verify_migration_admission_for_test(
        exact_outbox_admission,
        predecessor_with_outbox,
        _RecordingReceiptVerifier(),
    )
    acknowledged_target = replace(
        migrated_with_outbox,
        outbox=(replace(pending_outbox, status=OutboxStatusV1.ACKNOWLEDGED),),
    )
    rewritten_outbox_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="preserve the exact predecessor outbox"):
        _verify_migration_admission_for_test(
            replace(
                exact_outbox_admission,
                state=acknowledged_target,
                certificate=replace(
                    exact_outbox_admission.certificate,
                    state_root=acknowledged_target.state_root,
                    replay_continuity_root=(
                        derive_economic_initial_state_replay_continuity_root_v1(
                            EconomicInitialStateKindV1.MIGRATION,
                            acknowledged_target,
                            predecessor_with_outbox,
                        )
                    ),
                    terminal_continuity_root=(
                        derive_economic_initial_state_terminal_continuity_root_v1(
                            EconomicInitialStateKindV1.MIGRATION,
                            acknowledged_target,
                            predecessor_with_outbox,
                        )
                    ),
                ),
            ),
            predecessor_with_outbox,
            rewritten_outbox_verifier,
        )
    assert rewritten_outbox_verifier.calls == []

    genesis_profile, _ = _profile()
    genesis_state = _state(genesis_profile, height=0)
    genesis_admission = _initial_state_admission(genesis_profile, genesis_state)
    with pytest.raises(ValueError, match="must not include a predecessor state"):
        replace(genesis_admission, predecessor_state=source_state)
    genesis_with_replay = replace(
        genesis_state,
        replay_state=(ReplayStateV1("genesis-replay-1", _root(88_205)),),
    )
    with pytest.raises(ValueError, match="genesis replay state must be empty"):
        _initial_state_admission(genesis_profile, genesis_with_replay)
    genesis_with_outbox = replace(
        genesis_state,
        outbox=(pending_outbox,),
    )
    with pytest.raises(ValueError, match="genesis outbox must be empty"):
        _initial_state_admission(genesis_profile, genesis_with_outbox)

    oversized_outbox_predecessor = replace(source_state)
    object.__setattr__(
        oversized_outbox_predecessor,
        "outbox",
        tuple(pending_outbox for _ in range(4_097)),
    )
    with pytest.raises(ValueError, match="outbox exceeds the continuity row bound"):
        _verify_migration_admission_for_test(
            replace(admission, predecessor_state=oversized_outbox_predecessor),
            oversized_outbox_predecessor,
            verifier,
        )

    oversized_predecessor = replace(
        source_state,
        balances=tuple(
            EconomicAmountV1(
                f"owner-{index:04}",
                "ZDEX",
                "accounts",
                index,
            )
            for index in range(4_097)
        ),
        supplies=(),
    )
    object.__setattr__(
        oversized_predecessor.balances[0],
        "owner",
        "invalid unicode ☃",
    )
    with pytest.raises(ValueError, match="explicit value rows exceed the coverage bound"):
        _verify_migration_admission_for_test(
            replace(admission, predecessor_state=oversized_predecessor),
            oversized_predecessor,
            verifier,
        )
    assert verifier.calls == []


def test_migration_initial_state_rejects_each_outbox_mutation_before_receipt() -> None:
    # Arrange
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    provisional_target = replace(
        _state(source_profile, height=1),
        replay_state=source_state.replay_state,
    )
    source_manifest = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.MIGRATION,
        provisional_target,
    )
    target_profile, _ = _profile(
        source_manifest=source_manifest,
        authority_epoch=source_profile.authority_epoch + 1,
    )
    target_state = replace(
        _state(target_profile, height=1),
        replay_state=source_state.replay_state,
    )
    first = OutboxStateV1(
        effect_id=_root(89_001),
        destination_id="bridge:test",
        payload_hash=_root(89_002),
        commit_id=_root(89_003),
        status=OutboxStatusV1.PENDING,
    )
    second = OutboxStateV1(
        effect_id=_root(89_004),
        destination_id="bridge:test",
        payload_hash=_root(89_005),
        commit_id=_root(89_006),
        status=OutboxStatusV1.ACKNOWLEDGED,
    )
    predecessor = replace(source_state, outbox=(first, second))
    exact_target = replace(target_state, outbox=(first, second))
    exact_admission = _initial_state_admission(
        target_profile,
        exact_target,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=source_manifest,
        source_profile_root=source_profile.profile_id,
        source_state_root=predecessor.state_root,
        source_writer_epoch=predecessor.writer_epoch,
        source_height=predecessor.height,
        predecessor_state=predecessor,
    )
    mutation_rows = (
        ("deletion", (first,)),
        (
            "addition",
            (
                first,
                second,
                OutboxStateV1(
                    _root(89_007),
                    "bridge:test",
                    _root(89_008),
                    _root(89_009),
                    OutboxStatusV1.PENDING,
                ),
            ),
        ),
        ("effect", (replace(first, effect_id=_root(89_000)), second)),
        ("destination", (replace(first, destination_id="bridge:evil"), second)),
        ("payload", (replace(first, payload_hash=_root(89_010)), second)),
        ("commit", (replace(first, commit_id=_root(89_011)), second)),
        ("status", (replace(first, status=OutboxStatusV1.ACKNOWLEDGED), second)),
    )

    # Act / Assert
    _verify_migration_admission_for_test(
        exact_admission,
        predecessor,
        _RecordingReceiptVerifier(),
    )
    for label, changed_rows in mutation_rows:
        changed_target = replace(exact_target, outbox=changed_rows)
        changed_certificate = replace(
            exact_admission.certificate,
            state_root=changed_target.state_root,
            replay_continuity_root=(
                derive_economic_initial_state_replay_continuity_root_v1(
                    EconomicInitialStateKindV1.MIGRATION,
                    changed_target,
                    predecessor,
                )
            ),
            terminal_continuity_root=(
                derive_economic_initial_state_terminal_continuity_root_v1(
                    EconomicInitialStateKindV1.MIGRATION,
                    changed_target,
                    predecessor,
                )
            ),
        )
        verifier = _RecordingReceiptVerifier()
        with pytest.raises(
            ValueError,
            match="preserve the exact predecessor outbox",
        ):
            _verify_migration_admission_for_test(
                replace(
                    exact_admission,
                    state=changed_target,
                    certificate=changed_certificate,
                ),
                predecessor,
                verifier,
            )
        assert verifier.calls == [], label

    reordered_target = replace(exact_target)
    object.__setattr__(reordered_target, "outbox", (second, first))
    reorder_verifier = _RecordingReceiptVerifier()
    with pytest.raises(ValueError, match="outbox must be canonically ordered"):
        _verify_migration_admission_for_test(
            replace(exact_admission, state=reordered_target),
            predecessor,
            reorder_verifier,
        )
    assert reorder_verifier.calls == []


def test_initial_state_rejects_unbound_terminal_continuity_root_before_receipt() -> None:
    # Arrange
    profile, _ = _profile()
    state = _state(profile, height=0)
    admission = _initial_state_admission(profile, state)
    verifier = _RecordingReceiptVerifier()

    # Act / Assert
    with pytest.raises(ValueError, match="terminal continuity root mismatch"):
        GlobalEconomicCommitPortV1(
            replace(
                admission,
                certificate=replace(
                    admission.certificate,
                    terminal_continuity_root=_root(89_101),
                ),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_migration_rejects_each_terminal_mutation_before_receipt() -> None:
    # Arrange
    source_profile, _ = _profile()
    first = TerminalObligationV1(
        "obligation-1",
        LaneIdV1.ZUSD_MONETARY,
        "alice",
        "zUSD",
        17,
        TerminalObligationStatusV1.OPEN,
    )
    second = TerminalObligationV1(
        "obligation-2",
        LaneIdV1.PROOF_REWARDS,
        "bob",
        "ZDEX",
        23,
        TerminalObligationStatusV1.DRAINED,
    )
    source_state = replace(
        _state(source_profile, height=0),
        terminal_obligations=(first, second),
    )
    provisional_target = replace(
        _state(source_profile, height=1),
        replay_state=source_state.replay_state,
        terminal_obligations=(first, second),
    )
    source_manifest = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.MIGRATION,
        provisional_target,
    )
    target_profile, _ = _profile(
        source_manifest=source_manifest,
        authority_epoch=source_profile.authority_epoch + 1,
    )
    exact_target = replace(
        _state(target_profile, height=1),
        replay_state=source_state.replay_state,
        terminal_obligations=(first, second),
    )
    exact_admission = _initial_state_admission(
        target_profile,
        exact_target,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=source_manifest,
        source_profile_root=source_profile.profile_id,
        source_state_root=source_state.state_root,
        source_writer_epoch=source_state.writer_epoch,
        source_height=source_state.height,
        predecessor_state=source_state,
    )
    changed_first_rows = (
        replace(first, obligation_id="obligation-0"),
        replace(first, lane_id=LaneIdV1.PERPS_MARKET),
        replace(first, claimant="mallory"),
        replace(first, asset="ZDEX"),
        replace(first, amount_atoms=18),
        replace(first, status=TerminalObligationStatusV1.TOMBSTONED),
    )
    changed_tables = (
        (first,),
        (
            first,
            second,
            TerminalObligationV1(
                "obligation-3",
                LaneIdV1.FARM_INCENTIVES,
                "carol",
                "ZDEX",
                29,
                TerminalObligationStatusV1.OPEN,
            ),
        ),
        *((changed, second) for changed in changed_first_rows),
    )

    # Act / Assert
    _verify_migration_admission_for_test(
        exact_admission,
        source_state,
        _RecordingReceiptVerifier(),
    )
    for changed_rows in changed_tables:
        changed_target = replace(exact_target, terminal_obligations=changed_rows)
        changed_certificate = replace(
            exact_admission.certificate,
            state_root=changed_target.state_root,
            replay_continuity_root=(
                derive_economic_initial_state_replay_continuity_root_v1(
                    EconomicInitialStateKindV1.MIGRATION,
                    changed_target,
                    source_state,
                )
            ),
            outbox_continuity_root=(
                derive_economic_initial_state_outbox_continuity_root_v1(
                    EconomicInitialStateKindV1.MIGRATION,
                    changed_target,
                    source_state,
                )
            ),
        )
        verifier = _RecordingReceiptVerifier()
        with pytest.raises(
            ValueError,
            match="preserve the exact predecessor terminal obligations",
        ):
            _verify_migration_admission_for_test(
                replace(
                    exact_admission,
                    state=changed_target,
                    certificate=changed_certificate,
                ),
                source_state,
                verifier,
            )
        assert verifier.calls == []


def test_commit_port_owns_and_revalidates_active_profile_graph() -> None:
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )
    expected_profile_id = profile.profile_id
    expected_image_id = profile.root_image_id
    expected_lane_root = profile.lane_registry.registry_root
    expected_coordinator_root = profile.lane_coordinator_registry.registry_root
    expected_route_root = profile.route_registry.registry_root

    object.__setattr__(profile, "root_image_id", _root(77_020))
    object.__setattr__(
        profile.lane_registry.releases[0],
        "guest_image_id",
        _root(77_021),
    )
    object.__setattr__(
        profile.lane_coordinator_registry.releases[0],
        "guest_image_id",
        _root(77_022),
    )
    object.__setattr__(
        profile.route_registry.routes[0],
        "guest_image_id",
        _root(77_023),
    )
    exposed_profile = port.profile
    object.__setattr__(exposed_profile, "root_image_id", _root(77_024))
    object.__setattr__(
        exposed_profile.lane_registry.releases[0],
        "guest_image_id",
        _root(77_025),
    )
    object.__setattr__(
        exposed_profile.lane_coordinator_registry.releases[0],
        "guest_image_id",
        _root(77_026),
    )
    object.__setattr__(
        exposed_profile.route_registry.routes[0],
        "guest_image_id",
        _root(77_027),
    )

    assert port.profile.profile_id == expected_profile_id
    assert port.profile.root_image_id == expected_image_id
    assert port.profile.lane_registry.registry_root == expected_lane_root
    assert (
        port.profile.lane_coordinator_registry.registry_root
        == expected_coordinator_root
    )
    assert port.profile.route_registry.registry_root == expected_route_root
    committed = port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=expected_profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert committed.status is CommitOutcomeStatusV1.COMMITTED

    poisoned_profile = port.profile
    poisoned_route = poisoned_profile.route_registry.routes[0]
    poisoned_verifier = _RecordingReceiptVerifier()
    poisoned_port = _commit_port(
        poisoned_profile,
        pre_state,
        poisoned_verifier,
    )
    poisoned_verified, _, _, _, _ = _verified_epoch(
        poisoned_profile,
        poisoned_route,
        pre_state,
        post_state,
        publisher=poisoned_port,
        receipt_verifier=poisoned_verifier,
    )
    object.__setattr__(poisoned_port._profile, "root_image_id", _root(77_028))
    rejected = poisoned_port.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=expected_profile_id,
        verified_epoch=poisoned_verified,
        body_and_state=body,
    )
    assert rejected.status is CommitOutcomeStatusV1.BINDING_REJECTED
    assert rejected.reason == "active profile content binding is invalid"
    assert poisoned_port.state == pre_state
    assert poisoned_port.records == ()


def test_commit_rejects_hostile_expected_root_subclasses_before_lock() -> None:
    class AlwaysEqual(str):
        def __eq__(self, other: object) -> bool:
            return other != ZERO_ROOT_V1

        def __ne__(self, other: object) -> bool:
            return not self.__eq__(other)

        __hash__ = str.__hash__

    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )

    with pytest.raises(TypeError, match="expected head must be exact str"):
        port.commit_verified_economic_epoch(
            expected_head=AlwaysEqual(_root(77_030)),
            expected_profile=profile.profile_id,
            verified_epoch=verified,
            body_and_state=body,
        )
    with pytest.raises(TypeError, match="expected profile must be exact str"):
        port.commit_verified_economic_epoch(
            expected_head=pre_state.state_root,
            expected_profile=AlwaysEqual(_root(77_031)),
            verified_epoch=verified,
            body_and_state=body,
        )
    assert port.state == pre_state
    assert port.records == ()


def test_epoch_verifier_rejects_chain_and_deployment_drift_before_commit() -> None:
    """RIPR: no opaque epoch witness exists for a foreign execution context."""

    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    verified, _body, _, occurrence, _route_journal = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )

    substitutions = (
        ("chain_id", "foreign-chain", "pre-state chain mismatch"),
        ("deployment_root", _root(88_001), "pre-state deployment mismatch"),
    )
    for field_name, foreign_value, expected_reason in substitutions:
        port = _commit_port(
            profile,
            pre_state,
            _RecordingReceiptVerifier(),
        )
        foreign_occurrence = replace(occurrence, **{field_name: foreign_value})
        foreign_route = _verified_route_effect_fixture(
            profile,
            foreign_occurrence,
            post_state_root=post_state.state_root,
            pre_module_state=_epoch_asset_module_state(profile),
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
        before = (port.state, port.records)
        with pytest.raises(ValueError, match=expected_reason):
            verify_economic_epoch_v1(
                _epoch_candidate(
                    profile,
                    foreign_certificate,
                    pre_state,
                    post_state,
                    (foreign_occurrence,),
                    (foreign_route_journal,),
                    (
                        EconomicEpochRouteStateDisclosureV1(
                            foreign_route.lane_journals,
                            post_state,
                        ),
                    ),
                    (foreign_verified_route,),
                    (foreign_route.effect_plan,),
                    foreign_effects,
                    b"succinct-receipt-one",
                ),
                _RecordingReceiptVerifier(),
            )
        assert (port.state, port.records) == before


def test_committed_replay_requires_exact_context_and_binding_tuple() -> None:
    """BDD/RIPR: a committed ID cannot authorize substituted replay inputs."""

    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    port, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
    )

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
    verifier = _RecordingReceiptVerifier()
    port = _commit_port(profile, pre_state, verifier)
    first, body, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=b"succinct-receipt-first",
        publisher=port,
        receipt_verifier=verifier,
    )
    second, _, _, _, _ = _verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=b"succinct-receipt-second",
        publisher=port,
        receipt_verifier=verifier,
    )

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
