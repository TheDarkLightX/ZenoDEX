"""Rebuild one isolated ASSET receipt chain from raw, unauthenticated evidence.

The factory fixes a concrete BLS backend, measured receipt ports and an owned
profile/policy snapshot. Each call snapshots disclosures, reauthenticates the
signed intent and recomputes the module before verifying its three receipts.
Caller-provided authentication, module and route witnesses supply no authority.

This adapter performs no allocation admission, epoch proof verification, store
acquisition, replay consumption or publication. Its caller acquires the explicit
predecessor and must check allocation and epoch admission before atomic commit.
The current isolated scope has one occurrence; the existing coordinator retains
its nonzero-custody limitation. Interpreter/dependency integrity and the BLS
artifact-to-loaded-code correspondence remain external premises.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from pathlib import Path
from threading import Lock
from typing import NoReturn, SupportsIndex
from weakref import WeakKeyDictionary

from src.core.asset_lane_projection_v1 import (
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    _snapshot_asset_transfer_lane_module_input_v1,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_policy_registry_v1 import (
    AssetTransferPolicyRegistryV1,
    snapshot_asset_transfer_policy_registry_v1,
)
from src.core.asset_transfer_types_v1 import ASSET_TRANSFER_COMMAND_KIND_V1
from src.core.economic_command_authentication_snapshot_v1 import (
    snapshot_command_authentication_candidate_v1,
)
from src.core.economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandIntentV1,
)
from src.core.economic_command_authentication_v1 import (
    _authenticate_isolated_economic_command_intent_v1,
    bind_authenticated_intent_to_occurrence_v1,
)
from src.core.economic_command_authorization_registry_v1 import (
    EconomicCommandAuthorizationRegistryV1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    BoundEconomicCommandSignatureVerifierV1,
    EconomicCommandSignatureVerifierEvidenceManifestV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierRegistryV1,
    EconomicCommandSignatureVerifierReleaseV1,
    EconomicCommandSignatureVerifierSelectionPurposeV1,
)
from src.core.economic_receipt_verifier_registry_v1 import MAX_ECONOMIC_RECEIPT_BYTES_V1
from src.core.global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    EconomicEpochReceiptCandidateV1,
    EconomicEpochRouteStateDisclosureV1,
    ReceiptKindV1,
    _snapshot_economic_epoch_candidate_v1,
    _validate_command_occurrences,
)
from src.core.global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from src.core.global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    canonical_global_bytes_v1,
)
from src.core.lane_composition_receipt_verification_v1 import (
    LaneCompositionReceiptCandidateV1,
    LaneCompositionReceiptEnvelopeV1,
    verify_asset_lane_composition_receipt_v1,
)
from src.core.lane_module_receipt_verification_v1 import (
    AssetTransferLaneModuleReceiptCandidateV1,
    LaneModuleReceiptEnvelopeV1,
    VerifiedLaneModuleTransitionV1,
    verify_asset_transfer_lane_module_receipt_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    AssetTransferReleaseRouteBindingCandidateV1,
    bind_asset_transfer_lane_output_to_release_route_v1,
)
from src.core.managed_asset_policy_registry_v1 import snapshot_exact_economic_policy_registry_v1
from src.core.receipt_backed_asset_lane_composition_v1 import (
    ReceiptBackedAssetLaneCompositionCandidateV1,
    compose_receipt_backed_asset_lane_single_v1,
)
from src.core.route_composition_receipt_verification_v1 import (
    RouteCompositionReceiptCandidateV1,
    RouteCompositionReceiptEnvelopeV1,
    VerifiedRouteCompositionV1,
    verify_route_composition_receipt_v1,
)
from src.integration.economic_command_bls_signature_verifier_v1 import (
    bind_deployed_bls_economic_command_signature_verifier_v1,
)
from src.integration.isolated_profile_receipt_ports_v1 import (
    IsolatedProfileReceiptPortsV1,
    _bound_isolated_profile_receipt_verifier_v1,
)


@dataclass(frozen=True, slots=True)
class RawAssetTransferReceiptEvidenceV1:
    """Untrusted disclosures and encoded receipts; no opaque witnesses accepted."""

    intent: EconomicCommandIntentV1
    envelope: EconomicCommandAuthenticationEnvelopeV1
    authorization_registry: EconomicCommandAuthorizationRegistryV1
    signature_verifier_registry: EconomicCommandSignatureVerifierRegistryV1
    asset_policy_registry: AssetTransferPolicyRegistryV1
    module_input: AssetTransferLaneModuleInputV1
    module_receipt_bytes: bytes
    coordinator_receipt_bytes: bytes
    route_receipt_bytes: bytes


@dataclass(frozen=True, slots=True)
class IsolatedAssetReceiptPipelineResultV1:
    """Owned checked values, consumed directly by the caller's next admission."""

    candidate: EconomicEpochReceiptCandidateV1
    module_evidence: tuple[
        tuple[AssetTransferLaneModuleAcceptedV1, VerifiedLaneModuleTransitionV1], ...
    ]


@dataclass(frozen=True, slots=True)
class _PipelineAuthorityV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    deployment_root: str
    signature_verifier: BoundEconomicCommandSignatureVerifierV1
    receipt_ports: IsolatedProfileReceiptPortsV1


class IsolatedAssetReceiptPipelineV1:
    """Exact factory origin fixes verifier implementations and selected context."""

    __slots__ = ("__weakref__",)

    def __new__(cls, *args: object, **kwargs: object) -> IsolatedAssetReceiptPipelineV1:
        raise TypeError("isolated asset pipeline requires the fixed verifier factory")

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("isolated asset pipeline is immutable")

    def __reduce_ex__(self, protocol: SupportsIndex) -> NoReturn:
        raise TypeError("isolated asset pipeline cannot be copied or serialized")

    def verify(
        self,
        *,
        candidate: EconomicEpochReceiptCandidateV1,
        predecessor: GlobalEconomicStateV1,
        raw_evidence: tuple[RawAssetTransferReceiptEvidenceV1, ...],
    ) -> IsolatedAssetReceiptPipelineResultV1:
        authority = _authority_v1(self)
        owned, raw = _snapshot_inputs_v1(authority, candidate, predecessor, raw_evidence)
        return _verify_owned_v1(authority, owned, raw)


_LOCK = Lock()
_AUTHORITIES: WeakKeyDictionary[IsolatedAssetReceiptPipelineV1, _PipelineAuthorityV1] = (
    WeakKeyDictionary()
)


def _authority_v1(pipeline: IsolatedAssetReceiptPipelineV1) -> _PipelineAuthorityV1:
    if type(pipeline) is not IsolatedAssetReceiptPipelineV1:
        raise TypeError("isolated asset pipeline must be the exact factory type")
    with _LOCK:
        authority = _AUTHORITIES.get(pipeline)
    if authority is None:
        raise ValueError("isolated asset pipeline was not factory-minted")
    return authority


def _isolated_asset_pipeline_mount_v1(
    pipeline: IsolatedAssetReceiptPipelineV1,
    *,
    profile: EconomicProfileSnapshotV1,
    deployment_root: str,
    policy_registry_bytes: bytes,
) -> IsolatedProfileReceiptPortsV1:
    """Bind the minted pipeline to the publisher's acquired activation policy."""
    authority = _authority_v1(pipeline)
    selected = snapshot_economic_profile_v1(profile)
    if canonical_global_bytes_v1(selected) != canonical_global_bytes_v1(authority.profile):
        raise ValueError("isolated asset pipeline selected profile mismatch")
    if type(deployment_root) is not str or deployment_root != authority.deployment_root:
        raise ValueError("isolated asset pipeline deployment mismatch")
    if type(
        policy_registry_bytes
    ) is not bytes or policy_registry_bytes != canonical_global_bytes_v1(authority.policy_registry):
        raise ValueError("isolated asset pipeline acquired policy bytes mismatch")
    _bound_isolated_profile_receipt_verifier_v1(
        authority.receipt_ports,
        profile=selected,
        verifier_registry_root=selected.verifier_registry_root,
        deployment_root=deployment_root,
    )
    return authority.receipt_ports


def bind_isolated_asset_receipt_pipeline_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    receipt_ports: IsolatedProfileReceiptPortsV1,
    deployment_root: str,
    signature_artifact_path: Path,
    signature_release: EconomicCommandSignatureVerifierReleaseV1,
    signature_evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
) -> IsolatedAssetReceiptPipelineV1:
    """Acquire the BLS artifact and retain only factory-minted measured ports."""
    if type(deployment_root) is not str:
        raise TypeError("isolated asset pipeline deployment root must be an exact string")
    owned_profile = snapshot_economic_profile_v1(profile)
    owned_policy = snapshot_exact_economic_policy_registry_v1(policy_registry)
    if owned_policy.registry_root != owned_profile.policy_registry_root:
        raise ValueError("isolated asset pipeline policy registry is not selected")
    _bound_isolated_profile_receipt_verifier_v1(
        receipt_ports,
        profile=owned_profile,
        verifier_registry_root=owned_profile.verifier_registry_root,
        deployment_root=deployment_root,
    )
    signature_verifier = bind_deployed_bls_economic_command_signature_verifier_v1(
        artifact_path=signature_artifact_path,
        release=signature_release,
        evidence_manifest=signature_evidence_manifest,
        deployment_root=deployment_root,
        profile_root=owned_profile.profile_id,
        selection_purpose=EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION,
    )
    pipeline = object.__new__(IsolatedAssetReceiptPipelineV1)
    with _LOCK:
        _AUTHORITIES[pipeline] = _PipelineAuthorityV1(
            owned_profile,
            owned_policy,
            deployment_root,
            signature_verifier,
            receipt_ports,
        )
    return pipeline


def _snapshot_inputs_v1(
    authority: _PipelineAuthorityV1,
    candidate: EconomicEpochReceiptCandidateV1,
    predecessor: GlobalEconomicStateV1,
    evidence: tuple[RawAssetTransferReceiptEvidenceV1, ...],
) -> tuple[EconomicEpochReceiptCandidateV1, RawAssetTransferReceiptEvidenceV1]:
    if type(candidate) is not EconomicEpochReceiptCandidateV1:
        raise TypeError("isolated asset epoch candidate must have the exact type")
    if type(evidence) is not tuple or len(evidence) != 1:
        raise ValueError("isolated asset pipeline requires exactly one raw occurrence")
    if type(evidence[0]) is not RawAssetTransferReceiptEvidenceV1:
        raise TypeError("isolated asset evidence must have the exact raw type")
    _require_single_occurrence_shape_v1(candidate)
    # Discard all caller route witnesses before any witness field can be read.
    owned = _snapshot_economic_epoch_candidate_v1(replace(candidate, verified_routes=()))
    source = _snapshot_state_v1(predecessor)
    if owned.pre_state != source or source.deployment_root != authority.deployment_root:
        raise ValueError("isolated asset pipeline acquired predecessor mismatch")
    if canonical_global_bytes_v1(owned.profile) != canonical_global_bytes_v1(authority.profile):
        raise ValueError("isolated asset pipeline candidate profile mismatch")
    occurrence = owned.command_occurrences[0]
    if occurrence.command_kind != ASSET_TRANSFER_COMMAND_KIND_V1:
        raise ValueError("isolated asset pipeline supports asset_transfer only")
    _validate_command_occurrences(
        owned.certificate, owned.command_occurrences, owned.ordered_command_body_hashes
    )
    return replace(owned, pre_state=source), _snapshot_raw_v1(authority, evidence[0])


def _require_single_occurrence_shape_v1(candidate: EconomicEpochReceiptCandidateV1) -> None:
    # Bound the parallel vectors before a deep snapshot iterates over them.
    rows = (
        candidate.command_occurrences,
        candidate.ordered_command_body_hashes,
        candidate.route_journals,
        candidate.route_state_disclosures,
        candidate.route_effect_plans,
    )
    if any(type(row) is not tuple or len(row) != 1 for row in rows):
        raise ValueError("isolated asset pipeline supports one occurrence and one lane")
    disclosure = candidate.route_state_disclosures[0]
    if type(disclosure) is not EconomicEpochRouteStateDisclosureV1:
        raise TypeError("isolated asset route disclosure must have the exact type")
    if type(disclosure.lane_journals) is not tuple or len(disclosure.lane_journals) != 1:
        raise ValueError("isolated asset pipeline supports one occurrence and one lane")


def _snapshot_raw_v1(
    authority: _PipelineAuthorityV1,
    raw: RawAssetTransferReceiptEvidenceV1,
) -> RawAssetTransferReceiptEvidenceV1:
    receipt_bytes = (
        raw.module_receipt_bytes,
        raw.coordinator_receipt_bytes,
        raw.route_receipt_bytes,
    )
    if any(
        type(item) is not bytes or not 1 <= len(item) <= MAX_ECONOMIC_RECEIPT_BYTES_V1
        for item in receipt_bytes
    ):
        raise ValueError("isolated asset raw receipts must be bounded exact bytes")
    authentication = snapshot_command_authentication_candidate_v1(
        EconomicCommandAuthenticationCandidateV1(
            authority.profile,
            authority.policy_registry,
            raw.authorization_registry,
            raw.signature_verifier_registry,
            raw.intent,
            raw.envelope,
        )
    )
    return RawAssetTransferReceiptEvidenceV1(
        authentication.intent,
        authentication.envelope,
        authentication.authorization_registry,
        authentication.signature_verifier_registry,
        snapshot_asset_transfer_policy_registry_v1(raw.asset_policy_registry),
        _snapshot_asset_transfer_lane_module_input_v1(raw.module_input),
        *receipt_bytes,
    )


def _verify_owned_v1(
    authority: _PipelineAuthorityV1,
    candidate: EconomicEpochReceiptCandidateV1,
    raw: RawAssetTransferReceiptEvidenceV1,
) -> IsolatedAssetReceiptPipelineResultV1:
    evidence = _verify_module_v1(authority, candidate.command_occurrences[0], raw)
    route = _verify_route_v1(authority, candidate, raw, evidence)
    return IsolatedAssetReceiptPipelineResultV1(
        replace(candidate, verified_routes=(route,)),
        (evidence,),
    )


def _verify_module_v1(
    authority: _PipelineAuthorityV1,
    occurrence: EconomicCommandOccurrenceV1,
    raw: RawAssetTransferReceiptEvidenceV1,
) -> tuple[AssetTransferLaneModuleAcceptedV1, VerifiedLaneModuleTransitionV1]:
    authenticated = bind_authenticated_intent_to_occurrence_v1(
        _authenticate_isolated_economic_command_intent_v1(
            EconomicCommandAuthenticationCandidateV1(
                authority.profile,
                authority.policy_registry,
                raw.authorization_registry,
                raw.signature_verifier_registry,
                raw.intent,
                raw.envelope,
            ),
            authority.signature_verifier,
        ),
        occurrence,
    )
    accepted = transition_asset_transfer_lane_module_v1(raw.module_input)
    if not isinstance(accepted, AssetTransferLaneModuleAcceptedV1):
        raise ValueError(f"isolated asset module rejected: {accepted.code.value}")
    if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
        raise TypeError("isolated asset module returned an unexpected acceptance type")
    bound = bind_asset_transfer_lane_output_to_release_route_v1(
        AssetTransferReleaseRouteBindingCandidateV1(
            authority.profile,
            authority.policy_registry,
            raw.asset_policy_registry,
            occurrence,
            raw.module_input,
            accepted,
        )
    )
    module = verify_asset_transfer_lane_module_receipt_v1(
        AssetTransferLaneModuleReceiptCandidateV1(
            authority.profile,
            authority.policy_registry,
            raw.asset_policy_registry,
            authenticated,
            raw.module_input,
            accepted,
            bound,
            LaneModuleReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, raw.module_receipt_bytes),
        ),
        authority.receipt_ports.module_port(LaneIdV1.ASSET_TRANSFER),
    )
    return accepted, module


def _coordinator_context_v1(
    authority: _PipelineAuthorityV1,
    occurrence: EconomicCommandOccurrenceV1,
    raw: RawAssetTransferReceiptEvidenceV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> AssetLaneCoordinatorContextV1:
    coordinator = authority.profile.lane_coordinator_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    return AssetLaneCoordinatorContextV1(
        occurrence.chain_id,
        authority.deployment_root,
        authority.profile.profile_id,
        authority.profile.authority_epoch,
        coordinator.coordinator_release_id,
        occurrence.occurrence_id,
        raw.module_input.asset_policy_registry_root,
        raw.module_input.fee_policy_registry_root,
        (
            AssetLaneModuleCompatibilityV1(
                accepted.module_journal.module_release_id,
                accepted.private_port.producer_module_schema,
            ),
        ),
    )


def _verify_route_v1(
    authority: _PipelineAuthorityV1,
    candidate: EconomicEpochReceiptCandidateV1,
    raw: RawAssetTransferReceiptEvidenceV1,
    evidence: tuple[AssetTransferLaneModuleAcceptedV1, VerifiedLaneModuleTransitionV1],
) -> VerifiedRouteCompositionV1:
    occurrence = candidate.command_occurrences[0]
    accepted, module = evidence
    composition = compose_receipt_backed_asset_lane_single_v1(
        ReceiptBackedAssetLaneCompositionCandidateV1(
            authority.profile,
            occurrence,
            _coordinator_context_v1(authority, occurrence, raw, accepted),
            accepted.module_journal,
            accepted.private_port,
            accepted.effects,
            module,
        )
    )
    lane_journal = candidate.route_state_disclosures[0].lane_journals[0]
    lane = verify_asset_lane_composition_receipt_v1(
        LaneCompositionReceiptCandidateV1(
            authority.profile,
            occurrence,
            composition,
            lane_journal,
            LaneCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, raw.coordinator_receipt_bytes),
        ),
        authority.receipt_ports.coordinator_port(LaneIdV1.ASSET_TRANSFER),
    )
    return verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            authority.profile,
            occurrence,
            (lane_journal,),
            (lane,),
            candidate.route_journals[0],
            RouteCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, raw.route_receipt_bytes),
        ),
        authority.receipt_ports.route_port(occurrence.route_release_id),
    )
