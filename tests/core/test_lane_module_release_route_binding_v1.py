from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from types import SimpleNamespace

import pytest

import src.core.managed_asset_lifecycle_lane_module_v1 as managed_lane_module
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
from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
    ReceiptKindV1,
    RouteCompositionJournalV1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_economic_command_body_bytes_v1,
    canonical_global_bytes_v1,
    hash_global_v1,
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
    ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
    VerifiedLaneModuleTransitionV1,
    verify_asset_transfer_lane_module_receipt_v1,
    verify_managed_asset_lifecycle_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    ManagedAssetLifecycleReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
    bind_asset_transfer_lane_output_to_release_route_v1,
    bind_managed_asset_lifecycle_lane_output_to_release_route_v1,
)
from src.core.managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    transition_managed_asset_lifecycle_lane_module_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleStateV1,
)
from src.core.managed_asset_policy_registry_v1 import (
    MANAGED_ASSET_POLICY_KIND_V1,
    ManagedAssetPolicyRegistryV1,
)
from src.core.receipt_backed_asset_lane_composition_v1 import (
    LaneCompositionAuthorityLevelV1,
    ReceiptBackedAssetLaneCompositionCandidateV1,
    ReceiptBackedAssetLaneCompositionV1,
    compose_receipt_backed_asset_lane_single_v1,
)
from src.core.route_composition_receipt_verification_v1 import (
    RouteCompositionReceiptCandidateV1,
    RouteCompositionReceiptEnvelopeV1,
    VerifiedRouteCompositionV1,
    verify_route_composition_receipt_v1,
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
    b"lane-binding-command-signature-verifier-test-artifact-v1"
)
_MANAGED_COMMAND_KINDS_V1 = (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
)


def _signature_verifier_manifest_v1() -> EconomicCommandSignatureVerifierEvidenceManifestV1:
    evidence_artifacts = tuple(
        CommandSignatureVerifierEvidenceArtifactV1(status, _root(540 + index))
        for index, status in enumerate(
            sorted(CommandSignatureVerifierEvidenceStatusV1, key=lambda item: item.value)
        )
    )
    return EconomicCommandSignatureVerifierEvidenceManifestV1(
        signature_algorithm="BLS12_381_G2_BASIC_V1",
        implementation_root=command_signature_verifier_implementation_root_v1(
            _COMMAND_SIGNATURE_VERIFIER_ARTIFACT_V1
        ),
        public_key_schema_root=_root(527),
        signature_schema_root=_root(528),
        message_schema_root=_root(529),
        specification_root=_root(530),
        source_root=_root(531),
        toolchain_root=_root(532),
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
                semantic_version="1.0.0-lane-binding-test",
                signature_algorithm=manifest.signature_algorithm,
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


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    is_asset_lane = lane_id is LaneIdV1.ASSET_TRANSFER
    command_variants = (
        (
            ASSET_TRANSFER_COMMAND_KIND_V1,
            MANAGED_ASSET_BURN_COMMAND_KIND_V1,
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        )
        if is_asset_lane
        else ()
    )
    offset = ordinal * 16
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-test",
        state_schema_root=_root(100 + offset),
        command_variants=command_variants,
        terminal_command_variants=(MANAGED_ASSET_BURN_COMMAND_KIND_V1,)
        if is_asset_lane
        else (),
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW
        if is_asset_lane
        else ReleaseStatusV1.SHADOW,
        accepts_new_objects=is_asset_lane,
        evidence_statuses=(
            _active_evidence()
            if is_asset_lane
            else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _coordinator_release(lane_id: LaneIdV1, ordinal: int) -> LaneCoordinatorReleaseV1:
    is_asset_lane = lane_id is LaneIdV1.ASSET_TRANSFER
    offset = ordinal * 16
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-test",
        coordinator_schema_root=_root(300 + offset),
        guest_image_id=_root(301 + offset),
        specification_root=_root(302 + offset),
        source_root=_root(303 + offset),
        toolchain_root=_root(304 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if is_asset_lane else ReleaseStatusV1.SHADOW,
        accepts_new_objects=is_asset_lane,
        evidence_statuses=(
            _active_evidence() if is_asset_lane else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _asset_lane_registry_v1() -> LaneRegistryV1:
    return LaneRegistryV1(
        tuple(
            _lane_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )


def _asset_transfer_release_id_v1() -> str:
    return _asset_lane_registry_v1().release_for(LaneIdV1.ASSET_TRANSFER).release_id


def _route_issue_burn_policy_root_v1(
    command_kind: str,
    asset_policy_registry: ManagedAssetPolicyRegistryV1 | None,
    override: str | None,
) -> str:
    """Managed issue/burn routes own the governed registry root; others keep a stub."""

    if command_kind not in _MANAGED_COMMAND_KINDS_V1 or asset_policy_registry is None:
        return _root(511)
    return asset_policy_registry.registry_root if override is None else override


def _profile(
    *,
    asset_policy_registry: ManagedAssetPolicyRegistryV1 | None = None,
    managed_command_kinds: tuple[str, ...] = _MANAGED_COMMAND_KINDS_V1,
    route_issue_burn_policy_root: str | None = None,
) -> tuple[EconomicProfileSnapshotV1, dict[str, RouteReleaseV1]]:
    """Build the synthetic ACTIVE profile; managed bindings only when requested.

    The default (no managed-asset policy registry) keeps the transfer golden
    binding roots stable; managed tests use ``_managed_governance_v1``, whose
    issue and burn routes carry the typed registry root as their
    ``issue_burn_policy_root`` unless a test overrides it.
    """

    lane_registry = _asset_lane_registry_v1()
    lane_coordinator_registry = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    asset_release = lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    routes = tuple(
        RouteReleaseV1.build(
            semantic_version="1.0.0-test",
            command_kind=command_kind,
            ordered_lanes=(LaneIdV1.ASSET_TRANSFER,),
            module_release_ids=(asset_release.release_id,),
            dependency_roles=("VALUE_OWNER",),
            port_schema_roots=(_root(500 + index),),
            guest_image_id=_root(520 + index),
            specification_root=_root(530 + index),
            source_root=_root(540 + index),
            toolchain_root=_root(550 + index),
            oracle_policy_root=_root(510),
            issue_burn_policy_root=_route_issue_burn_policy_root_v1(
                command_kind,
                asset_policy_registry,
                route_issue_burn_policy_root,
            ),
            max_cycles=2_000_000,
            max_journal_bytes=131_072,
            status=ReleaseStatusV1.ACTIVE_NEW,
            accepts_new_objects=True,
            evidence_statuses=_active_evidence(),
        )
        for index, command_kind in enumerate(
            (
                ASSET_TRANSFER_COMMAND_KIND_V1,
                MANAGED_ASSET_BURN_COMMAND_KIND_V1,
                MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
            )
        )
    )
    route_registry = RouteRegistryV1(routes)
    authorization_registry = _authorization_registry_v1(route_registry)
    signature_verifier_registry = _signature_verifier_registry_v1()
    policy_registry = _authentication_policy_registry_v1(
        authorization_registry,
        signature_verifier_registry,
        asset_policy_registry=asset_policy_registry,
        managed_command_kinds=managed_command_kinds,
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=7,
        lane_registry=lane_registry,
        lane_coordinator_registry=lane_coordinator_registry,
        route_registry=route_registry,
        proof_shape_root=_root(520),
        root_image_id=_root(521),
        verifier_registry_root=_root(522),
        migration_registry_root=_root(523),
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=_root(525),
        status=ProfileStatusV1.ACTIVE,
    )
    return profile, {route.command_kind: route for route in routes}


def _authorization_registry_v1(
    routes: RouteRegistryV1,
) -> EconomicCommandAuthorizationRegistryV1:
    identities = {
        ASSET_TRANSFER_COMMAND_KIND_V1: ("alice", _root(7)),
        MANAGED_ASSET_BURN_COMMAND_KIND_V1: ("alice", _root(6)),
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1: ("issuer", _root(5)),
    }
    authorizations = tuple(
        sorted(
            (
                EconomicCommandAuthorizationV1(
                    command_kind=route.command_kind,
                    subject_id=identities[route.command_kind][0],
                    grant_root=identities[route.command_kind][1],
                    route_release_id=route.route_release_id,
                    signer_key_id=f"{identities[route.command_kind][0]}-key-1",
                    signer_public_key=(
                        f"bls12-381-g2:{identities[route.command_kind][0]}-public-key"
                    ),
                    signature_algorithm="BLS12_381_G2_BASIC_V1",
                    valid_from_height=0,
                    valid_through_height=(1 << 64) - 1,
                    min_nonce=0,
                    max_nonce=(1 << 64) - 1,
                    enabled=True,
                )
                for route in routes.routes
            ),
            key=lambda item: item.key,
        )
    )
    return EconomicCommandAuthorizationRegistryV1(authorizations)


def _authentication_policy_registry_v1(
    authorizations: EconomicCommandAuthorizationRegistryV1,
    signature_verifiers: EconomicCommandSignatureVerifierRegistryV1,
    *,
    asset_policy_registry: ManagedAssetPolicyRegistryV1 | None = None,
    managed_command_kinds: tuple[str, ...] = _MANAGED_COMMAND_KINDS_V1,
) -> EconomicPolicyRegistryV1:
    authentication_bindings = tuple(
        EconomicPolicyBindingV1(policy_kind, command_kind, policy_root)
        for command_kind in sorted(
            authorization.command_kind for authorization in authorizations.authorizations
        )
        for policy_kind, policy_root in (
            (
                ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
                authorizations.registry_root,
            ),
            (
                ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
                signature_verifiers.registry_root,
            ),
        )
    )
    managed_bindings = (
        ()
        if asset_policy_registry is None
        else tuple(
            EconomicPolicyBindingV1(
                MANAGED_ASSET_POLICY_KIND_V1,
                command_kind,
                asset_policy_registry.registry_root,
            )
            for command_kind in managed_command_kinds
        )
    )
    return EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (*authentication_bindings, *managed_bindings),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )


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
    command: AssetTransferCommandV1 | ManagedAssetLifecycleCommandV1,
    *,
    policy_registry: EconomicPolicyRegistryV1 | None = None,
) -> AuthenticatedEconomicCommandV1:
    authorization_registry = _authorization_registry_v1(profile.route_registry)
    signature_verifier_registry = _signature_verifier_registry_v1()
    if policy_registry is None:
        policy_registry = _authentication_policy_registry_v1(
            authorization_registry,
            signature_verifier_registry,
        )
    authorization = authorization_registry.authorization_for(
        occurrence,
        signer_key_id=f"{occurrence.subject_id}-key-1",
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


def _occurrence(
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    *,
    subject_id: str,
    grant_root: str,
) -> EconomicCommandOccurrenceV1:
    if route.command_kind == ASSET_TRANSFER_COMMAND_KIND_V1:
        command_body_hash = AssetTransferCommandV1(
            ASSET_TRANSFER_COMMAND_KIND_V1,
            "USD",
            "alice",
            "bob",
            30,
            2,
        ).command_body_hash
    elif route.command_kind in {
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    }:
        command_body_hash = ManagedAssetLifecycleCommandV1(
            command_kind=route.command_kind,
            asset="USD",
            account_owner="alice",
            amount_atoms=(
                7 if route.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 else 4
            ),
        ).command_body_hash
    else:
        raise ValueError("test occurrence command kind is unsupported")
    return EconomicCommandOccurrenceV1(
        chain_id="zeno-release-route-test",
        deployment_root=_root(1),
        height=11,
        tx_index=2,
        op_index=3,
        command_kind=route.command_kind,
        command_body_hash=command_body_hash,
        route_release_id=route.route_release_id,
        subject_id=subject_id,
        grant_root=grant_root,
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=_root(2),
        consumed_object_ids=(),
    )


def _asset_input(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    module_release_id: str | None = None,
) -> AssetTransferLaneModuleInputV1:
    release_id = (
        profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER).release_id
        if module_release_id is None
        else module_release_id
    )
    return AssetTransferLaneModuleInputV1(
        context=AssetTransferContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=profile.authority_epoch,
            module_release_id=release_id,
            command_occurrence_id=occurrence.occurrence_id,
            subject_id=occurrence.subject_id,
            grant_root=occurrence.grant_root,
        ),
        pre_state=AssetTransferStateV1(
            module_release_id=release_id,
            policies=(AssetTransferPolicyV1("USD", "treasury", 2, True),),
            balances=(
                EconomicAmountV1("alice", "USD", "accounts", 100),
                EconomicAmountV1("bob", "USD", "accounts", 10),
                EconomicAmountV1("treasury", "USD", "accounts", 5),
            ),
            supplies=(AssetSupplyV1("USD", 115),),
        ),
        command=AssetTransferCommandV1(
            ASSET_TRANSFER_COMMAND_KIND_V1,
            "USD",
            "alice",
            "bob",
            30,
            2,
        ),
        asset_policy_registry_root=_root(11),
        fee_policy_registry_root=_root(12),
        custody=(),
    )


def _managed_asset_policy_v1() -> ManagedAssetLifecyclePolicyV1:
    return ManagedAssetLifecyclePolicyV1(
        asset="USD",
        asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
        issue_authority_subject="issuer",
        issue_policy_root=_root(5),
        burn_policy_root=_root(6),
        enabled=True,
    )


def _managed_asset_policy_registry_v1(
    module_release_id: str | None = None,
) -> ManagedAssetPolicyRegistryV1:
    """Governed USD policy row bound to the fixture ASSET_TRANSFER release."""

    return ManagedAssetPolicyRegistryV1(
        _asset_transfer_release_id_v1() if module_release_id is None else module_release_id,
        (_managed_asset_policy_v1(),),
    )


@dataclass(frozen=True, slots=True)
class _ManagedGovernanceV1:
    """One ACTIVE profile whose economic policy registry governs managed assets."""

    profile: EconomicProfileSnapshotV1
    routes: dict[str, RouteReleaseV1]
    policy_registry: EconomicPolicyRegistryV1
    asset_policy_registry: ManagedAssetPolicyRegistryV1


def _managed_governance_v1(
    *,
    asset_policy_registry: ManagedAssetPolicyRegistryV1 | None = None,
    managed_command_kinds: tuple[str, ...] = _MANAGED_COMMAND_KINDS_V1,
    route_issue_burn_policy_root: str | None = None,
) -> _ManagedGovernanceV1:
    governed = (
        _managed_asset_policy_registry_v1()
        if asset_policy_registry is None
        else asset_policy_registry
    )
    profile, routes = _profile(
        asset_policy_registry=governed,
        managed_command_kinds=managed_command_kinds,
        route_issue_burn_policy_root=route_issue_burn_policy_root,
    )
    policy_registry = _authentication_policy_registry_v1(
        _authorization_registry_v1(profile.route_registry),
        _signature_verifier_registry_v1(),
        asset_policy_registry=governed,
        managed_command_kinds=managed_command_kinds,
    )
    return _ManagedGovernanceV1(profile, routes, policy_registry, governed)


def _managed_binding_candidate(
    governance: _ManagedGovernanceV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1,
) -> ManagedAssetLifecycleReleaseRouteBindingCandidateV1:
    return ManagedAssetLifecycleReleaseRouteBindingCandidateV1(
        governance.profile,
        governance.policy_registry,
        governance.asset_policy_registry,
        occurrence,
        module_input,
        accepted,
    )


def _managed_receipt_candidate(
    governance: _ManagedGovernanceV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1,
    bound: ReleaseRouteBoundLaneTransitionV1,
    receipt: LaneModuleReceiptEnvelopeV1,
) -> ManagedAssetLifecycleLaneModuleReceiptCandidateV1:
    return ManagedAssetLifecycleLaneModuleReceiptCandidateV1(
        governance.profile,
        governance.policy_registry,
        governance.asset_policy_registry,
        _authenticate_occurrence_for_test(
            governance.profile,
            occurrence,
            module_input.command,
            policy_registry=governance.policy_registry,
        ),
        module_input,
        accepted,
        bound,
        receipt,
    )


def _managed_input(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    command_kind: str,
) -> ManagedAssetLifecycleLaneModuleInputV1:
    release_id = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER).release_id
    return ManagedAssetLifecycleLaneModuleInputV1(
        context=ManagedAssetLifecycleContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=profile.authority_epoch,
            module_release_id=release_id,
            command_occurrence_id=occurrence.occurrence_id,
            subject_id=occurrence.subject_id,
            grant_root=occurrence.grant_root,
        ),
        pre_state=ManagedAssetLifecycleStateV1(
            module_release_id=release_id,
            policies=(_managed_asset_policy_v1(),),
            balances=(EconomicAmountV1("alice", "USD", "accounts", 10),),
            supplies=(AssetSupplyV1("USD", 10),),
        ),
        command=ManagedAssetLifecycleCommandV1(
            command_kind=command_kind,
            asset="USD",
            account_owner="alice",
            amount_atoms=7 if command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 else 4,
        ),
        asset_policy_registry_root=_managed_asset_policy_registry_v1().registry_root,
        fee_policy_registry_root=_root(12),
        custody=(),
    )


def test_asset_output_gets_opaque_active_profile_release_route_binding() -> None:
    profile, routes = _profile()
    occurrence = _occurrence(profile, routes[ASSET_TRANSFER_COMMAND_KIND_V1], subject_id="alice", grant_root=_root(7))
    module_input = _asset_input(profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)

    bound = bind_asset_transfer_lane_output_to_release_route_v1(
        profile,
        occurrence,
        module_input,
        accepted,
    )

    assert bound.profile_id == profile.profile_id
    assert bound.route_release_id == routes[ASSET_TRANSFER_COMMAND_KIND_V1].route_release_id
    assert bound.lane_id is LaneIdV1.ASSET_TRANSFER
    assert bound.module_release_id == accepted.module_journal.module_release_id
    assert bound.command_occurrence_id == occurrence.occurrence_id
    assert bound.module_journal_root == accepted.module_journal.journal_root
    assert bound.statement_root == module_input.statement_root
    assert bound.producer_module_schema == ASSET_TRANSFER_MODULE_SCHEMA_V1
    assert bound.route_lane_index == 0
    assert bound.port_schema_root == routes[ASSET_TRANSFER_COMMAND_KIND_V1].port_schema_roots[0]
    assert bound.binding_root == "0xcff38651027da371035b33cb7173ba002b9b942e1dc11436485f69d25aebf9f7"
    with pytest.raises(AttributeError, match="immutable"):
        bound._profile_id = _root(999)


def test_authenticated_command_body_hashes_match_rust_golden_vectors() -> None:
    transfer = AssetTransferCommandV1(
        ASSET_TRANSFER_COMMAND_KIND_V1,
        "USD",
        "alice",
        "bob",
        30,
        2,
    )
    issue = ManagedAssetLifecycleCommandV1(
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
        "USD",
        "alice",
        7,
    )
    burn = ManagedAssetLifecycleCommandV1(
        MANAGED_ASSET_BURN_COMMAND_KIND_V1,
        "USD",
        "alice",
        4,
    )

    assert transfer.command_body_hash == (
        "0x86c77102b725de42ba4928542495129ab51bbfa71d3ebf14218d16c403f4f9c6"
    )
    assert issue.command_body_hash == (
        "0xba582530e63ec9b3646fae1a361fb8b3aaa7cf4f9ea98d3c47d09d717fcb8983"
    )
    assert burn.command_body_hash == (
        "0xfea954a9c050efcb620a3971bdd7fabed19a56b82cb5ad6aacfaa8db6df847b6"
    )


def test_same_kind_transfer_body_substitution_rejects_before_receipt_binding() -> None:
    # Arrange: Alice authenticated a transfer to Bob, while the module executes Mallory.
    profile, routes = _profile()
    occurrence = _occurrence(
        profile,
        routes[ASSET_TRANSFER_COMMAND_KIND_V1],
        subject_id="alice",
        grant_root=_root(7),
    )
    authenticated = _asset_input(profile, occurrence)
    substituted = replace(
        authenticated,
        command=replace(authenticated.command, recipient="mallory"),
    )
    accepted = transition_asset_transfer_lane_module_v1(substituted)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)

    # Act / Assert: same command kind and valid economics cannot reuse Alice's body hash.
    with pytest.raises(ValueError, match="command body hash mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            occurrence,
            substituted,
            accepted,
        )


def test_hostile_transfer_command_subclass_cannot_forge_body_hash() -> None:
    # Arrange: a retained exact input and a subclass advertising Bob's hash.
    profile, routes = _profile()
    occurrence = _occurrence(
        profile,
        routes[ASSET_TRANSFER_COMMAND_KIND_V1],
        subject_id="alice",
        grant_root=_root(7),
    )
    authenticated = _asset_input(profile, occurrence)
    advertised_hash = authenticated.command.command_body_hash

    class ForgedBodyHashCommand(AssetTransferCommandV1):
        @property
        def command_body_hash(self) -> str:
            return advertised_hash

    forged = ForgedBodyHashCommand(
        command_kind=authenticated.command.command_kind,
        asset=authenticated.command.asset,
        sender=authenticated.command.sender,
        recipient="mallory",
        amount_atoms=authenticated.command.amount_atoms,
        max_fee_atoms=authenticated.command.max_fee_atoms,
    )

    # Act / Assert: post-construction injection before execution rejects.
    object.__setattr__(authenticated, "command", forged)
    with pytest.raises(TypeError, match="command must have the exact typed value"):
        transition_asset_transfer_lane_module_v1(authenticated)

    # Arrange / Act: mutation after transition also rejects at binding.
    retained = _asset_input(profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(retained)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    object.__setattr__(retained, "command", forged)
    with pytest.raises(TypeError, match="command must have the exact typed value"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            occurrence,
            retained,
            accepted,
        )


def test_hostile_managed_command_subclass_cannot_forge_body_hash() -> None:
    # Arrange: a retained exact input and a subclass advertising the approved hash.
    governance = _managed_governance_v1()
    profile = governance.profile
    occurrence = _occurrence(
        profile,
        governance.routes[MANAGED_ASSET_ISSUE_COMMAND_KIND_V1],
        subject_id="issuer",
        grant_root=_root(5),
    )
    authenticated = _managed_input(
        profile,
        occurrence,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    )
    advertised_hash = authenticated.command.command_body_hash

    class ForgedBodyHashCommand(ManagedAssetLifecycleCommandV1):
        @property
        def command_body_hash(self) -> str:
            return advertised_hash

    forged = ForgedBodyHashCommand(
        command_kind=authenticated.command.command_kind,
        asset=authenticated.command.asset,
        account_owner=authenticated.command.account_owner,
        amount_atoms=authenticated.command.amount_atoms + 1,
    )

    # Act / Assert: post-construction injection before execution rejects.
    object.__setattr__(authenticated, "command", forged)
    with pytest.raises(TypeError, match="command must have the exact typed value"):
        transition_managed_asset_lifecycle_lane_module_v1(authenticated)

    # Arrange / Act: mutation after transition also rejects at binding.
    retained = _managed_input(
        profile,
        occurrence,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    )
    accepted = transition_managed_asset_lifecycle_lane_module_v1(retained)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    object.__setattr__(retained, "command", forged)
    with pytest.raises(TypeError, match="command must have the exact typed value"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            _managed_binding_candidate(governance, occurrence, retained, accepted)
        )


@pytest.mark.parametrize(
    "command_kind",
    (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_BURN_COMMAND_KIND_V1),
)
def test_same_kind_managed_body_substitution_rejects_before_receipt_binding(
    command_kind: str,
) -> None:
    # Arrange
    governance = _managed_governance_v1()
    profile = governance.profile
    subject = "issuer" if command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1 else "alice"
    occurrence = _occurrence(
        profile,
        governance.routes[command_kind],
        subject_id=subject,
        grant_root=(
            _root(5)
            if command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
            else _root(6)
        ),
    )
    authenticated = _managed_input(profile, occurrence, command_kind)
    substituted = replace(
        authenticated,
        command=replace(
            authenticated.command,
            amount_atoms=authenticated.command.amount_atoms + 1,
        ),
    )
    accepted = transition_managed_asset_lifecycle_lane_module_v1(substituted)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)

    # Act / Assert
    with pytest.raises(ValueError, match="command body hash mismatch"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            _managed_binding_candidate(governance, occurrence, substituted, accepted)
        )


@pytest.mark.parametrize(
    ("command_kind", "subject_id", "grant_root"),
    (
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", _root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", _root(6)),
    ),
)
def test_managed_issue_and_burn_bind_to_their_exact_governed_routes(
    command_kind: str,
    subject_id: str,
    grant_root: str,
) -> None:
    governance = _managed_governance_v1()
    profile, routes = governance.profile, governance.routes
    occurrence = _occurrence(profile, routes[command_kind], subject_id=subject_id, grant_root=grant_root)
    module_input = _managed_input(profile, occurrence, command_kind)
    accepted = transition_managed_asset_lifecycle_lane_module_v1(module_input)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)

    bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        _managed_binding_candidate(governance, occurrence, module_input, accepted)
    )

    assert bound.route_release_id == routes[command_kind].route_release_id
    assert bound.statement_root == module_input.statement_root
    assert bound.producer_module_schema == MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1
    # Cross-language vector: the Rust route-binding suite asserts the same
    # release-bound registry root for the same fixture.
    assert governance.asset_policy_registry.module_release_id == (
        profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER).release_id
    )
    assert governance.asset_policy_registry.registry_root == (
        "0xba06d1d7425a1dff6633b077ad7da33eb7ff681a8623607e9cbda353d87c2879"
    )
    # Managed issue/burn routes own that registry root as issue_burn_policy_root.
    assert routes[command_kind].issue_burn_policy_root == (
        governance.asset_policy_registry.registry_root
    )
    assert routes[MANAGED_ASSET_BURN_COMMAND_KIND_V1].route_release_id == (
        "0xf9a0bf0ff296f198c5da915b0e612dcec24eee16b5fb7c65168b63c8b1db4fbc"
    )
    assert routes[MANAGED_ASSET_ISSUE_COMMAND_KIND_V1].route_release_id == (
        "0x13a98232cd5861c444fc022c3419967dc488f99ad636202599621f586344962f"
    )
    assert profile.profile_id == (
        "0x8f65206657c02a3677706d7835b94da55e653c45d04abf035e4acd9fdc7a12bd"
    )


def test_caller_selected_route_and_inactive_profile_fail_closed() -> None:
    profile, routes = _profile()
    route = routes[ASSET_TRANSFER_COMMAND_KIND_V1]
    occurrence = _occurrence(profile, route, subject_id="alice", grant_root=_root(7))
    wrong_route_occurrence = replace(occurrence, route_release_id=_root(998))
    module_input = _asset_input(profile, wrong_route_occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)

    with pytest.raises(ValueError, match="caller-selected route"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            wrong_route_occurrence,
            module_input,
            accepted,
        )

    valid_input = _asset_input(profile, occurrence)
    valid_accepted = transition_asset_transfer_lane_module_v1(valid_input)
    assert isinstance(valid_accepted, AssetTransferLaneModuleAcceptedV1)
    with pytest.raises(ValueError, match="profile is not ACTIVE"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            replace(profile, status=ProfileStatusV1.SHADOW),
            occurrence,
            valid_input,
            valid_accepted,
        )


def test_command_substitution_and_unregistered_module_release_fail_closed() -> None:
    governance = _managed_governance_v1()
    profile, routes = governance.profile, governance.routes
    issue_route = routes[MANAGED_ASSET_ISSUE_COMMAND_KIND_V1]
    occurrence = _occurrence(profile, issue_route, subject_id="alice", grant_root=_root(6))
    burn_input = _managed_input(profile, occurrence, MANAGED_ASSET_BURN_COMMAND_KIND_V1)
    burn_accepted = transition_managed_asset_lifecycle_lane_module_v1(burn_input)
    assert isinstance(burn_accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    with pytest.raises(ValueError, match="command kind mismatch"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            _managed_binding_candidate(governance, occurrence, burn_input, burn_accepted)
        )

    transfer_occurrence = _occurrence(
        profile,
        routes[ASSET_TRANSFER_COMMAND_KIND_V1],
        subject_id="alice",
        grant_root=_root(7),
    )
    foreign_input = _asset_input(profile, transfer_occurrence, module_release_id=_root(997))
    foreign_accepted = transition_asset_transfer_lane_module_v1(foreign_input)
    assert isinstance(foreign_accepted, AssetTransferLaneModuleAcceptedV1)
    with pytest.raises(ValueError, match="module release mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            transfer_occurrence,
            foreign_input,
            foreign_accepted,
        )


def test_occurrence_subject_and_cross_domain_substitution_fail_closed() -> None:
    profile, routes = _profile()
    route = routes[ASSET_TRANSFER_COMMAND_KIND_V1]
    occurrence = _occurrence(profile, route, subject_id="alice", grant_root=_root(7))
    module_input = _asset_input(profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)

    wrong_subject = replace(occurrence, subject_id="mallory")
    with pytest.raises(ValueError, match="subject mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            wrong_subject,
            module_input,
            accepted,
        )
    wrong_chain = replace(occurrence, chain_id="other-chain")
    with pytest.raises(ValueError, match="chain id mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            wrong_chain,
            module_input,
            accepted,
        )


def test_release_route_bound_witness_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="binder-constructed"):
        ReleaseRouteBoundLaneTransitionV1(
            object(),
            _root(1),
            _root(2),
            LaneIdV1.ASSET_TRANSFER,
            _root(3),
            _root(4),
            _root(5),
            _root(6),
            ASSET_TRANSFER_MODULE_SCHEMA_V1,
            0,
            _root(7),
        )


class _RecordingModuleReceiptVerifier:
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
            raise ValueError("test verifier rejected module receipt")


def _accepted_transfer_with_binding() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleAcceptedV1,
    ReleaseRouteBoundLaneTransitionV1,
]:
    profile, routes = _profile()
    occurrence = _occurrence(
        profile,
        routes[ASSET_TRANSFER_COMMAND_KIND_V1],
        subject_id="alice",
        grant_root=_root(7),
    )
    module_input = _asset_input(profile, occurrence)
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    bound = bind_asset_transfer_lane_output_to_release_route_v1(
        profile,
        occurrence,
        module_input,
        accepted,
    )
    return profile, occurrence, module_input, accepted, bound


def _accepted_managed_issue_with_binding() -> tuple[
    _ManagedGovernanceV1,
    EconomicCommandOccurrenceV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ReleaseRouteBoundLaneTransitionV1,
]:
    governance = _managed_governance_v1()
    occurrence = _occurrence(
        governance.profile,
        governance.routes[MANAGED_ASSET_ISSUE_COMMAND_KIND_V1],
        subject_id="issuer",
        grant_root=_root(5),
    )
    module_input = _managed_input(
        governance.profile,
        occurrence,
        MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    )
    accepted = transition_managed_asset_lifecycle_lane_module_v1(module_input)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        _managed_binding_candidate(governance, occurrence, module_input, accepted)
    )
    return governance, occurrence, module_input, accepted, bound


def _structurally_rebind_managed_statement(
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1,
    statement_root: str,
) -> ManagedAssetLifecycleLaneModuleAcceptedV1:
    receipt_root = hash_global_v1(
        "managed-asset-lifecycle-lane-module-receipt-v1",
        {
            "statement_root": statement_root,
            "pre_state_root": accepted.module_journal.pre_lane_root,
            "post_state_root": accepted.module_journal.post_lane_root,
            "effect_plan_root": accepted.effects.effect_plan_root,
            "private_port_root": accepted.private_port.port_root,
            "terminal_obligations_root": accepted.private_port.terminal_obligations_root,
        },
    )
    return replace(
        accepted,
        statement_root=statement_root,
        module_journal=replace(accepted.module_journal, receipt_root=receipt_root),
    )


def test_module_receipt_verification_uses_release_image_and_exact_journal() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    receipt_bytes = b"succinct-asset-transfer-module-receipt-v1"
    verifier = _RecordingModuleReceiptVerifier()
    authenticated = _authenticate_occurrence_for_test(
        profile,
        occurrence,
        module_input.command,
    )
    assert authenticated.authentication_message_digest == (
        "0x3e13b70eb1e4ca23683d911dd5179575069d275c83575fcf1723cde0429ab723"
    )
    assert authenticated.binding_root == (
        "0xfe6a9ea24267f83b12ddfcd8c5ad87686d82c1ba148313f964b3ca534c81fb8a"
    )

    verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            authenticated,
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
        ),
        verifier,
    )

    release = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    journal_bytes = canonical_global_bytes_v1(accepted.module_journal)
    assert verifier.calls == [(receipt_bytes, release.guest_image_id, journal_bytes)]
    assert verified.authenticated_command_binding_root == authenticated.binding_root
    assert verified.release_route_binding_root == bound.binding_root
    assert verified.expected_image_id == release.guest_image_id
    assert verified.module_journal_root == accepted.module_journal.journal_root
    assert verified.module_journal_digest == "0x" + hashlib.sha256(journal_bytes).hexdigest()
    assert verified.receipt_digest == "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    assert verified.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified.receipt_digest != accepted.module_journal.receipt_root
    assert verified.binding_root == "0x9ca1eb63ba22b9a214266eea3a3ee2b9b7f1d09c92b202fa063ab06e7bf2dbdb"
    with pytest.raises(AttributeError, match="immutable"):
        verified._receipt_digest = _root(999)


@pytest.mark.parametrize(
    ("command_kind", "subject_id", "grant_root"),
    (
        (MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, "issuer", _root(5)),
        (MANAGED_ASSET_BURN_COMMAND_KIND_V1, "alice", _root(6)),
    ),
)
def test_managed_module_receipts_gain_only_release_image_bound_authority(
    command_kind: str,
    subject_id: str,
    grant_root: str,
) -> None:
    governance = _managed_governance_v1()
    profile, routes = governance.profile, governance.routes
    occurrence = _occurrence(
        profile,
        routes[command_kind],
        subject_id=subject_id,
        grant_root=grant_root,
    )
    module_input = _managed_input(profile, occurrence, command_kind)
    accepted = transition_managed_asset_lifecycle_lane_module_v1(module_input)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    bound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        _managed_binding_candidate(governance, occurrence, module_input, accepted)
    )
    verifier = _RecordingModuleReceiptVerifier()

    verified = verify_managed_asset_lifecycle_lane_module_receipt_v1(
        _managed_receipt_candidate(
            governance,
            occurrence,
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                ("receipt:" + command_kind).encode("ascii"),
            ),
        ),
        verifier,
    )

    assert verified.command_occurrence_id == occurrence.occurrence_id
    assert verified.statement_root == module_input.statement_root
    assert len(verifier.calls) == 1


def test_module_receipt_rejects_empty_nonsuccinct_and_verifier_failure() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()

    for receipt_kind, receipt_bytes, message in (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"composite", "succinct"),
    ):
        verifier = _RecordingModuleReceiptVerifier()
        with pytest.raises(ValueError, match=message):
            verify_asset_transfer_lane_module_receipt_v1(
                AssetTransferLaneModuleReceiptCandidateV1(
                    profile,
                    _authenticate_occurrence_for_test(
                        profile,
                        occurrence,
                        module_input.command,
                    ),
                    module_input,
                    accepted,
                    bound,
                    LaneModuleReceiptEnvelopeV1(receipt_kind, receipt_bytes),
                ),
                verifier,
            )
        assert verifier.calls == []

    rejecting_verifier = _RecordingModuleReceiptVerifier(reject=True)
    with pytest.raises(ValueError, match="test verifier rejected"):
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1(
                profile,
                _authenticate_occurrence_for_test(
                    profile,
                    occurrence,
                    module_input.command,
                ),
                module_input,
                accepted,
                bound,
                LaneModuleReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"cryptographically-invalid",
                ),
            ),
            rejecting_verifier,
        )
    assert len(rejecting_verifier.calls) == 1


def test_structural_binding_cannot_authorize_a_mutated_module_journal() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    with pytest.raises(ValueError, match="receipt root mismatch"):
        replace(
            accepted,
            module_journal=replace(accepted.module_journal, receipt_root=_root(999)),
        )
    substituted_input = replace(
        module_input,
        command=replace(module_input.command, amount_atoms=29),
    )
    substituted = transition_asset_transfer_lane_module_v1(substituted_input)
    assert isinstance(substituted, AssetTransferLaneModuleAcceptedV1)
    verifier = _RecordingModuleReceiptVerifier()

    with pytest.raises(ValueError, match="command body hash mismatch"):
        verify_asset_transfer_lane_module_receipt_v1(
            AssetTransferLaneModuleReceiptCandidateV1(
                profile,
                _authenticate_occurrence_for_test(
                    profile,
                    occurrence,
                    module_input.command,
                ),
                substituted_input,
                substituted,
                bound,
                LaneModuleReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"succinct-module-receipt",
                ),
            ),
            verifier,
        )

    assert verifier.calls == []


def test_transfer_accepted_output_cannot_be_rerooted_to_another_command() -> None:
    # Arrange: execute Mallory's payload, then advertise Bob's statement root.
    profile, occurrence, authenticated, _, _ = _accepted_transfer_with_binding()
    executed = replace(
        authenticated,
        command=replace(authenticated.command, recipient="mallory"),
    )
    accepted = transition_asset_transfer_lane_module_v1(executed)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    object.__setattr__(accepted, "statement_root", authenticated.statement_root)

    # Act / Assert: full deterministic recomputation rejects the reroot.
    with pytest.raises(ValueError, match="receipt root mismatch"):
        bind_asset_transfer_lane_output_to_release_route_v1(
            profile,
            occurrence,
            authenticated,
            accepted,
        )


def test_managed_accepted_output_cannot_be_rerooted_to_another_command() -> None:
    # Arrange: execute an eight-atom issue, then advertise the seven-atom statement.
    governance, occurrence, authenticated, _, _ = _accepted_managed_issue_with_binding()
    executed = replace(
        authenticated,
        command=replace(
            authenticated.command,
            amount_atoms=authenticated.command.amount_atoms + 1,
        ),
    )
    accepted = transition_managed_asset_lifecycle_lane_module_v1(executed)
    assert isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1)
    object.__setattr__(accepted, "statement_root", authenticated.statement_root)

    # Act / Assert
    with pytest.raises(ValueError, match="receipt root mismatch"):
        bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
            _managed_binding_candidate(governance, occurrence, authenticated, accepted)
        )


def test_managed_receipt_structural_binding_rejects_coherent_foreign_output_first() -> None:
    # Arrange: retain the honest release-route witness while supplying a
    # coherent amount+1 output whose public statement is rebound to the honest
    # input. Rust exercises the same vector and rejection precedence.
    governance, occurrence, module_input, accepted, bound = (
        _accepted_managed_issue_with_binding()
    )
    foreign_input = replace(
        module_input,
        command=replace(
            module_input.command,
            amount_atoms=module_input.command.amount_atoms + 1,
        ),
    )
    foreign = transition_managed_asset_lifecycle_lane_module_v1(foreign_input)
    assert isinstance(foreign, ManagedAssetLifecycleLaneModuleAcceptedV1)
    forged = _structurally_rebind_managed_statement(
        foreign,
        module_input.statement_root,
    )
    candidate = _managed_receipt_candidate(
        governance,
        occurrence,
        module_input,
        forged,
        bound,
        LaneModuleReceiptEnvelopeV1(
            ReceiptKindV1.SUCCINCT,
            b"coherent-foreign-managed-output",
        ),
    )
    verifier = _RecordingModuleReceiptVerifier()

    # Act / Assert: structural binding has precedence over deterministic
    # recomputation, and the cryptographic verifier is never invoked.
    with pytest.raises(ValueError, match="lane module structural binding mismatch"):
        verify_managed_asset_lifecycle_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_managed_receipt_recomputes_the_transition_exactly_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: build the honest structural witness before instrumenting the
    # deterministic transition used by receipt admission.
    governance, occurrence, module_input, accepted, bound = (
        _accepted_managed_issue_with_binding()
    )
    real_transition = (
        managed_lane_module._transition_owned_managed_asset_lifecycle_lane_module_v1
    )
    transition_calls: list[ManagedAssetLifecycleLaneModuleInputV1] = []

    def counted_transition(
        owned_input: ManagedAssetLifecycleLaneModuleInputV1,
    ) -> ManagedAssetLifecycleLaneModuleAcceptedV1:
        transition_calls.append(owned_input)
        result = real_transition(owned_input)
        assert isinstance(result, ManagedAssetLifecycleLaneModuleAcceptedV1)
        return result

    monkeypatch.setattr(
        managed_lane_module,
        "_transition_owned_managed_asset_lifecycle_lane_module_v1",
        counted_transition,
    )
    verifier = _RecordingModuleReceiptVerifier()

    # Act
    verify_managed_asset_lifecycle_lane_module_receipt_v1(
        _managed_receipt_candidate(
            governance,
            occurrence,
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"one-managed-transition",
            ),
        ),
        verifier,
    )

    # Assert: structural policy/binding checks are transition-free; admission
    # recomputes the economic transition once before one verifier call.
    assert len(transition_calls) == 1
    assert len(verifier.calls) == 1


def _mutate_retained_accepted_output(accepted: object, mutation: str) -> None:
    if mutation == "statement":
        object.__setattr__(accepted, "statement_root", _root(91_001))
    elif mutation == "journal":
        object.__setattr__(accepted.module_journal, "receipt_root", _root(91_002))
    elif mutation == "private_port":
        object.__setattr__(
            accepted.private_port,
            "module_effect_plan_root",
            _root(91_003),
        )
    elif mutation == "effects":
        object.__setattr__(accepted.effects, "occurrence_consumptions", ())
    else:
        raise AssertionError(f"unknown test mutation: {mutation}")


@pytest.mark.parametrize("mutation", ("statement", "journal", "private_port", "effects"))
def test_transfer_candidate_revalidates_retained_accepted_output_before_verifier(
    mutation: str,
) -> None:
    # Arrange: retain a valid candidate, then mutate one accepted-output layer.
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    candidate = AssetTransferLaneModuleReceiptCandidateV1(
        profile,
        _authenticate_occurrence_for_test(profile, occurrence, module_input.command),
        module_input,
        accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"mutated-transfer"),
    )
    _mutate_retained_accepted_output(accepted, mutation)
    verifier = _RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises((TypeError, ValueError)):
        verify_asset_transfer_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


@pytest.mark.parametrize("mutation", ("statement", "journal", "private_port", "effects"))
def test_managed_candidate_revalidates_retained_accepted_output_before_verifier(
    mutation: str,
) -> None:
    # Arrange
    governance, occurrence, module_input, accepted, bound = (
        _accepted_managed_issue_with_binding()
    )
    candidate = _managed_receipt_candidate(
        governance,
        occurrence,
        module_input,
        accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"mutated-issue"),
    )
    _mutate_retained_accepted_output(accepted, mutation)
    verifier = _RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises((TypeError, ValueError)):
        verify_managed_asset_lifecycle_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_transfer_receipt_rejects_retained_command_subclass_before_verifier() -> None:
    # Arrange: construct the candidate, then mutate its retained input alias.
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    advertised_hash = module_input.command.command_body_hash

    class ForgedBodyHashCommand(AssetTransferCommandV1):
        @property
        def command_body_hash(self) -> str:
            return advertised_hash

    candidate = AssetTransferLaneModuleReceiptCandidateV1(
        profile,
        _authenticate_occurrence_for_test(profile, occurrence, module_input.command),
        module_input,
        accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"forged-transfer"),
    )
    object.__setattr__(
        module_input,
        "command",
        ForgedBodyHashCommand(
            module_input.command.command_kind,
            module_input.command.asset,
            module_input.command.sender,
            "mallory",
            module_input.command.amount_atoms,
            module_input.command.max_fee_atoms,
        ),
    )
    verifier = _RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises(TypeError, match="command must have the exact typed value"):
        verify_asset_transfer_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_managed_receipt_rejects_retained_command_subclass_before_verifier() -> None:
    # Arrange
    governance, occurrence, module_input, accepted, bound = (
        _accepted_managed_issue_with_binding()
    )
    advertised_hash = module_input.command.command_body_hash

    class ForgedBodyHashCommand(ManagedAssetLifecycleCommandV1):
        @property
        def command_body_hash(self) -> str:
            return advertised_hash

    candidate = _managed_receipt_candidate(
        governance,
        occurrence,
        module_input,
        accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"forged-issue"),
    )
    object.__setattr__(
        module_input,
        "command",
        ForgedBodyHashCommand(
            module_input.command.command_kind,
            module_input.command.asset,
            module_input.command.account_owner,
            module_input.command.amount_atoms + 1,
        ),
    )
    verifier = _RecordingModuleReceiptVerifier()

    # Act / Assert
    with pytest.raises(TypeError, match="command must have the exact typed value"):
        verify_managed_asset_lifecycle_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_verified_module_witness_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedLaneModuleTransitionV1(
            object(),
            object(),
        )


def test_raw_occurrence_cannot_enter_module_receipt_authority() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    with pytest.raises(TypeError, match="authenticated economic command"):
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            occurrence,  # type: ignore[arg-type]
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"raw-occurrence"),
        )


def test_duck_typed_candidate_cannot_inject_authentication_root_at_verification() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    forged_authentication = SimpleNamespace(
        occurrence=occurrence,
        binding_root=_root(98_001),
    )
    candidate = SimpleNamespace(
        profile=profile,
        authenticated_command=forged_authentication,
        module_input=module_input,
        accepted=accepted,
        release_route_binding=bound,
        receipt=LaneModuleReceiptEnvelopeV1(
            ReceiptKindV1.SUCCINCT,
            b"duck-typed-authentication",
        ),
    )
    verifier = _RecordingModuleReceiptVerifier()

    with pytest.raises(TypeError, match="candidate must have the exact type"):
        verify_asset_transfer_lane_module_receipt_v1(
            candidate,  # type: ignore[arg-type]
            verifier,
        )
    assert verifier.calls == []


def test_mutated_candidate_cannot_inject_authentication_root_at_verification() -> None:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    candidate = AssetTransferLaneModuleReceiptCandidateV1(
        profile,
        _authenticate_occurrence_for_test(profile, occurrence, module_input.command),
        module_input,
        accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(
            ReceiptKindV1.SUCCINCT,
            b"mutated-authentication",
        ),
    )
    object.__setattr__(
        candidate,
        "authenticated_command",
        SimpleNamespace(occurrence=occurrence, binding_root=_root(98_002)),
    )
    verifier = _RecordingModuleReceiptVerifier()

    with pytest.raises(TypeError, match="authenticated economic command"):
        verify_asset_transfer_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def test_managed_candidate_cannot_inject_authentication_root_at_verification() -> None:
    governance, occurrence, module_input, accepted, bound = (
        _accepted_managed_issue_with_binding()
    )
    candidate = _managed_receipt_candidate(
        governance,
        occurrence,
        module_input,
        accepted,
        bound,
        LaneModuleReceiptEnvelopeV1(
            ReceiptKindV1.SUCCINCT,
            b"mutated-managed-authentication",
        ),
    )
    object.__setattr__(
        candidate,
        "authenticated_command",
        SimpleNamespace(occurrence=occurrence, binding_root=_root(98_003)),
    )
    verifier = _RecordingModuleReceiptVerifier()

    with pytest.raises(TypeError, match="authenticated economic command"):
        verify_managed_asset_lifecycle_lane_module_receipt_v1(candidate, verifier)
    assert verifier.calls == []


def _verified_transfer_and_coordinator_context() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleAcceptedV1,
    VerifiedLaneModuleTransitionV1,
    AssetLaneCoordinatorContextV1,
]:
    profile, occurrence, module_input, accepted, bound = _accepted_transfer_with_binding()
    coordinator_release = profile.lane_coordinator_registry.release_for(
        LaneIdV1.ASSET_TRANSFER
    )
    verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            _authenticate_occurrence_for_test(profile, occurrence, module_input.command),
            module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"succinct-asset-transfer-module-receipt-v1",
            ),
        ),
        _RecordingModuleReceiptVerifier(),
    )
    coordinator_context = AssetLaneCoordinatorContextV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        coordinator_release_id=coordinator_release.coordinator_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        compatible_modules=(
            AssetLaneModuleCompatibilityV1(
                accepted.module_journal.module_release_id,
                accepted.private_port.producer_module_schema,
            ),
        ),
    )
    return profile, occurrence, module_input, accepted, verified, coordinator_context


class _RecordingCompositionReceiptVerifier:
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
            raise ValueError("test verifier rejected lane composition receipt")


def _structural_asset_lane_composition_fixture() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    AssetTransferLaneModuleAcceptedV1,
    VerifiedLaneModuleTransitionV1,
    AssetLaneCoordinatorContextV1,
    LaneCompositionJournalV1,
    ReceiptBackedAssetLaneCompositionV1,
]:
    profile, occurrence, _, accepted, verified, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )
    result = compose_asset_lane_single_v1(
        coordinator_context,
        accepted.module_journal,
        accepted.private_port,
        accepted.effects,
    )
    assert isinstance(result, AssetLaneCompositionAcceptedV1)
    structural_composition = compose_receipt_backed_asset_lane_single_v1(
        ReceiptBackedAssetLaneCompositionCandidateV1(
            profile,
            occurrence,
            coordinator_context,
            accepted.module_journal,
            accepted.private_port,
            accepted.effects,
            verified,
        )
    )
    return (
        profile,
        occurrence,
        accepted,
        verified,
        coordinator_context,
        result.lane_journal,
        structural_composition,
    )


def test_verified_module_receipt_backs_only_exact_structural_lane_composition() -> None:
    profile, occurrence, _, accepted, verified, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )

    composition = compose_receipt_backed_asset_lane_single_v1(
        ReceiptBackedAssetLaneCompositionCandidateV1(
            profile,
            occurrence,
            coordinator_context,
            accepted.module_journal,
            accepted.private_port,
            accepted.effects,
            verified,
        )
    )

    assert composition.authority_level is (
        LaneCompositionAuthorityLevelV1.RECEIPT_BACKED_STRUCTURAL_ONLY
    )
    assert composition.profile_id == profile.profile_id
    assert composition.command_occurrence_id == occurrence.occurrence_id
    assert composition.verified_module_binding_root == verified.binding_root
    assert composition.module_receipt_digest == verified.receipt_digest
    assert composition.lane_journal_root != accepted.module_journal.journal_root
    assert composition.binding_root == (
        "0x2b876b91b371e648dc5104f5641e58cc7990ef42be4121aed3ffac12bb2ebf19"
    )


def test_structural_composition_rejects_caller_selected_coordinator_release() -> None:
    profile, occurrence, _, accepted, verified, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )
    with pytest.raises(ValueError, match="selected coordinator release mismatch"):
        compose_receipt_backed_asset_lane_single_v1(
            ReceiptBackedAssetLaneCompositionCandidateV1(
                profile,
                occurrence,
                replace(coordinator_context, coordinator_release_id=_root(999)),
                accepted.module_journal,
                accepted.private_port,
                accepted.effects,
                verified,
            )
        )


def test_lane_composition_receipt_uses_selected_image_and_exact_journal() -> None:
    (
        profile,
        occurrence,
        _accepted,
        _verified,
        _coordinator_context,
        lane_journal,
        structural_composition,
    ) = _structural_asset_lane_composition_fixture()
    receipt_bytes = b"x"
    verifier = _RecordingCompositionReceiptVerifier()

    verified_composition = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1(
            profile,
            occurrence,
            structural_composition,
            lane_journal,
            LaneCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
        ),
        verifier,
    )

    coordinator_release = profile.lane_coordinator_registry.release_for(
        LaneIdV1.ASSET_TRANSFER
    )
    lane_journal_bytes = canonical_global_bytes_v1(lane_journal)
    assert verifier.calls == [
        (receipt_bytes, coordinator_release.guest_image_id, lane_journal_bytes)
    ]
    assert verified_composition.profile_id == profile.profile_id
    assert verified_composition.route_release_id == structural_composition.route_release_id
    assert verified_composition.lane_id is LaneIdV1.ASSET_TRANSFER
    assert (
        verified_composition.coordinator_release_id
        == coordinator_release.coordinator_release_id
    )
    assert verified_composition.command_occurrence_id == occurrence.occurrence_id
    assert verified_composition.writer_epoch == profile.authority_epoch
    assert verified_composition.structural_composition_root == structural_composition.binding_root
    assert verified_composition.lane_journal_root == lane_journal.journal_root
    assert verified_composition.lane_journal_digest == (
        "0x" + hashlib.sha256(lane_journal_bytes).hexdigest()
    )
    assert verified_composition.expected_image_id == coordinator_release.guest_image_id
    assert verified_composition.receipt_digest == (
        "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    )
    assert verified_composition.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified_composition.binding_root == (
        "0x70363a4537639144d050cb091b67b04447e9615c2526eb70e110c76c112cf88a"
    )


def test_lane_composition_receipt_rejects_empty_nonsuccinct_and_verifier_failure() -> None:
    profile, occurrence, _, _, _, lane_journal, structural_composition = (
        _structural_asset_lane_composition_fixture()
    )
    for receipt_kind, receipt_bytes, message in (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"composite", "succinct"),
    ):
        verifier = _RecordingCompositionReceiptVerifier()
        with pytest.raises(ValueError, match=message):
            verify_asset_lane_composition_receipt_v1(
                LaneCompositionReceiptCandidateV1(
                    profile,
                    occurrence,
                    structural_composition,
                    lane_journal,
                    LaneCompositionReceiptEnvelopeV1(receipt_kind, receipt_bytes),
                ),
                verifier,
            )
        assert verifier.calls == []

    rejecting_verifier = _RecordingCompositionReceiptVerifier(reject=True)
    with pytest.raises(ValueError, match="test verifier rejected"):
        verify_asset_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1(
                profile,
                occurrence,
                structural_composition,
                lane_journal,
                LaneCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"cryptographically-invalid",
                ),
            ),
            rejecting_verifier,
        )
    assert len(rejecting_verifier.calls) == 1


def test_lane_composition_receipt_rejects_wrong_journal_without_verifier_bypass() -> None:
    profile, occurrence, _, _, _, lane_journal, structural_composition = (
        _structural_asset_lane_composition_fixture()
    )
    verifier = _RecordingCompositionReceiptVerifier()

    with pytest.raises(ValueError, match="journal post-lane root mismatch"):
        verify_asset_lane_composition_receipt_v1(
            LaneCompositionReceiptCandidateV1(
                profile,
                occurrence,
                structural_composition,
                replace(lane_journal, post_lane_root=_root(999)),
                LaneCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"succinct-lane-composition-receipt",
                ),
            ),
            verifier,
        )

    assert verifier.calls == []


def test_verified_lane_composition_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedLaneCompositionV1(
            object(),
            object(),
        )


def test_valid_module_receipt_cannot_back_a_different_lane_journal() -> None:
    profile, occurrence, module_input, accepted, _, coordinator_context = (
        _verified_transfer_and_coordinator_context()
    )
    substituted_input = replace(
        module_input,
        pre_state=replace(
            module_input.pre_state,
            policies=(
                replace(
                    module_input.pre_state.policies[0],
                    transfer_fee_atoms=1,
                ),
            ),
        ),
    )
    substituted = transition_asset_transfer_lane_module_v1(substituted_input)
    assert isinstance(substituted, AssetTransferLaneModuleAcceptedV1)
    substituted_bound = bind_asset_transfer_lane_output_to_release_route_v1(
        profile,
        occurrence,
        substituted_input,
        substituted,
    )
    substituted_verified = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            profile,
            _authenticate_occurrence_for_test(
                profile,
                occurrence,
                substituted_input.command,
            ),
            substituted_input,
            substituted,
            substituted_bound,
            LaneModuleReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"succinct-substituted-module-receipt-v1",
            ),
        ),
        _RecordingModuleReceiptVerifier(),
    )

    with pytest.raises(ValueError, match="verified module journal root mismatch"):
        compose_receipt_backed_asset_lane_single_v1(
            ReceiptBackedAssetLaneCompositionCandidateV1(
                profile,
                occurrence,
                coordinator_context,
                accepted.module_journal,
                accepted.private_port,
                accepted.effects,
                substituted_verified,
            )
        )


def test_receipt_backed_lane_composition_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="composition-constructed"):
        ReceiptBackedAssetLaneCompositionV1(
            object(),
            object(),  # type: ignore[arg-type]
        )


def _verified_route_composition_fixture() -> tuple[
    EconomicProfileSnapshotV1,
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
    VerifiedLaneCompositionV1,
    RouteCompositionJournalV1,
]:
    (
        profile,
        occurrence,
        _accepted,
        _verified_module,
        _coordinator_context,
        lane_journal,
        structural_composition,
    ) = _structural_asset_lane_composition_fixture()
    verified_lane = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1(
            profile,
            occurrence,
            structural_composition,
            lane_journal,
            LaneCompositionReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"succinct-lane-composition-receipt-v1",
            ),
        ),
        _RecordingCompositionReceiptVerifier(),
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
        post_state_root=_root(8_001),
        effect_plan_root=lane_journal.effect_plan_root,
        terminal_obligations_root=lane_journal.terminal_obligations_root,
    )
    return profile, occurrence, lane_journal, verified_lane, route_journal


def test_route_composition_receipt_uses_selected_image_and_exact_lane_witness() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    receipt_bytes = b"x"
    verifier = _RecordingCompositionReceiptVerifier()

    # Act
    verified_route = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane_journal,),
            (verified_lane,),
            route_journal,
            RouteCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
        ),
        verifier,
    )

    # Assert
    route = profile.route_registry.route_for_command(occurrence.command_kind)
    route_journal_bytes = canonical_global_bytes_v1(route_journal)
    assert verifier.calls == [(receipt_bytes, route.guest_image_id, route_journal_bytes)]
    assert verified_route.profile_id == profile.profile_id
    assert verified_route.route_release_id == route.route_release_id
    assert verified_route.command_occurrence_id == occurrence.occurrence_id
    assert verified_route.writer_epoch == profile.authority_epoch
    assert verified_route.ordered_lane_ids == route.ordered_lanes
    assert verified_route.ordered_lane_binding_roots == (verified_lane.binding_root,)
    assert verified_route.ordered_lane_journal_roots == (lane_journal.journal_root,)
    assert verified_route.route_journal_root == route_journal.journal_root
    assert verified_route.route_journal_digest == (
        "0x" + hashlib.sha256(route_journal_bytes).hexdigest()
    )
    assert verified_route.expected_image_id == route.guest_image_id
    assert verified_route.receipt_digest == "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    assert verified_route.receipt_kind is ReceiptKindV1.SUCCINCT
    assert verified_route.binding_root == (
        "0x2ad537543e4e87d7420cc0a2631855cf5565ada7c9798981e25697d44d7ea279"
    )


def test_route_composition_rejects_structural_duplicate_and_journal_substitution() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    receipt = RouteCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"route-receipt")

    for lane_journals, verified_lanes, selected_journal, message in (
        ((lane_journal,), (), route_journal, "lane witness count"),
        (
            (lane_journal, lane_journal),
            (verified_lane, verified_lane),
            route_journal,
            "lane journal count",
        ),
        (
            (lane_journal,),
            (verified_lane,),
            replace(route_journal, command_occurrence_id=_root(8_002)),
            "journal occurrence",
        ),
        (
            (lane_journal,),
            (verified_lane,),
            replace(route_journal, writer_epoch=profile.authority_epoch - 1),
            "writer epoch",
        ),
        (
            (lane_journal,),
            (verified_lane,),
            replace(route_journal, writer_epoch=profile.authority_epoch + 1),
            "writer epoch",
        ),
    ):
        verifier = _RecordingCompositionReceiptVerifier()

        # Act / Assert
        with pytest.raises(ValueError, match=message):
            verify_route_composition_receipt_v1(
                RouteCompositionReceiptCandidateV1(
                    profile,
                    occurrence,
                    lane_journals,
                    verified_lanes,
                    selected_journal,
                    receipt,
                ),
                verifier,
            )
        assert verifier.calls == []

    with pytest.raises(
        TypeError,
        match="verified lane witnesses must be exact typed",
    ):
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane_journal,),
            (object(),),
            route_journal,
            receipt,
        )


def test_valid_lane_witness_cannot_back_a_different_route_lane_journal() -> None:
    # Arrange: preserve the route shape while changing the consumed lane statement.
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    substituted_lane_journal = replace(lane_journal, post_lane_root=_root(8_004))
    substituted_route_journal = replace(
        route_journal,
        ordered_lane_journal_roots=(substituted_lane_journal.journal_root,),
    )
    verifier = _RecordingCompositionReceiptVerifier()

    # Act / Assert: the old opaque lane witness cannot authorize the new journal.
    with pytest.raises(ValueError, match="lane witness journal"):
        verify_route_composition_receipt_v1(
            RouteCompositionReceiptCandidateV1(
                profile,
                occurrence,
                (substituted_lane_journal,),
                (verified_lane,),
                substituted_route_journal,
                RouteCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"route-receipt",
                ),
            ),
            verifier,
        )
    assert verifier.calls == []


def test_route_composition_receipt_rejects_empty_wrong_kind_and_verifier_failure() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )

    for receipt_kind, receipt_bytes, message in (
        (ReceiptKindV1.SUCCINCT, b"", "non-empty"),
        (ReceiptKindV1.COMPOSITE, b"composite", "succinct"),
    ):
        verifier = _RecordingCompositionReceiptVerifier()

        # Act / Assert
        with pytest.raises(ValueError, match=message):
            verify_route_composition_receipt_v1(
                RouteCompositionReceiptCandidateV1(
                    profile,
                    occurrence,
                    (lane_journal,),
                    (verified_lane,),
                    route_journal,
                    RouteCompositionReceiptEnvelopeV1(receipt_kind, receipt_bytes),
                ),
                verifier,
            )
        assert verifier.calls == []

    rejecting_verifier = _RecordingCompositionReceiptVerifier(reject=True)
    with pytest.raises(ValueError, match="test verifier rejected"):
        verify_route_composition_receipt_v1(
            RouteCompositionReceiptCandidateV1(
                profile,
                occurrence,
                (lane_journal,),
                (verified_lane,),
                route_journal,
                RouteCompositionReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"cryptographically-invalid-route-receipt",
                ),
            ),
            rejecting_verifier,
        )
    assert len(rejecting_verifier.calls) == 1


def test_verified_route_composition_rejects_public_construction() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        VerifiedRouteCompositionV1(object(), object())


def test_semantically_identical_route_rebuild_preserves_verified_binding_root() -> None:
    # Arrange
    profile, occurrence, lane_journal, verified_lane, route_journal = (
        _verified_route_composition_fixture()
    )
    receipt = RouteCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"x")

    # Act
    first = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane_journal,),
            (verified_lane,),
            route_journal,
            receipt,
        ),
        _RecordingCompositionReceiptVerifier(),
    )
    rebuilt = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (replace(lane_journal),),
            (verified_lane,),
            replace(route_journal),
            receipt,
        ),
        _RecordingCompositionReceiptVerifier(),
    )

    # Assert
    assert rebuilt.binding_root == first.binding_root
