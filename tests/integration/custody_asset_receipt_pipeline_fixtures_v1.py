"""Custody-complete isolated receipt fixtures with real BLS authentication.

The receipt endpoints remain the measured synthetic transport owned by
``publisher_receipt_port_fixtures_v1``.  This fixture supplies the complete
global state that transport consumes: a nonzero custody row is paired with a
precommitted liability row having the same asset and control domain.  The
fixture is evidence for the bounded Python integration path only; it does not
qualify a RISC0 image or a live publisher.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, fields, replace
from pathlib import Path
from typing import Any, Callable, Mapping

from py_ecc.bls import G2Basic

import tests.core.test_global_settlement_abi_v1 as abi_fixtures
from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core import global_economic_proof_v1 as proof
from src.core import global_settlement_types_v1 as abi
from src.core.asset_lane_coordinator_v1 import (
    AssetLaneCompositionAcceptedV1,
    compose_asset_lane_single_v1,
)
from src.core.asset_lane_projection_v1 import project_asset_transfer_state_v1
from src.core.asset_transfer_custody_semantics_v1 import (
    ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1,
)
from src.core.asset_transfer_lane_module_custody_v1 import (
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import AssetTransferLaneModuleAcceptedV1
from src.core.asset_transfer_policy_registry_v1 import (
    ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
    ASSET_TRANSFER_FEE_POLICY_KIND_V1,
    AssetTransferPolicyRegistryV1,
)
from src.core.asset_transfer_types_v1 import ASSET_TRANSFER_COMMAND_KIND_V1
from src.core.economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandIntentV1,
)
from src.core.economic_command_authentication_v1 import (
    _isolated_economic_command_authentication_message_bytes_v1,
)
from src.core.economic_command_authorization_registry_v1 import (
    ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1,
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1,
    REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1,
    EconomicCommandSignatureVerifierRegistryV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1,
    EconomicInitialStateKindV1,
)
from src.core.economic_initial_state_v1 import EconomicInitialStateAdmissionV1
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
)
from src.core.route_composition_receipt_verification_v1 import (
    derive_route_composition_assumption_root_v1,
)
from src.integration import economic_command_bls_signature_verifier_v1 as bls
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from tests.core.test_asset_transfer_global_allocation_v1 import (
    _global_allocation_fixture,
)
from tests.core.test_economic_command_authentication_v1 import (
    _signature_verifier_manifest,
    _signature_verifier_release,
)
from tests.core.test_economic_receipt_verifier_release_v1 import _release
from tests.core.test_global_settlement_abi_v1 import (
    _asset_lane_context,
    _asset_module_input_for_occurrence,
    _asset_transfer_policy_registry_for_route_v1,
    _epoch_admission_fixture,
    _epoch_asset_module_state,
    _epoch_candidate,
    _governed_policy_registry_for_profile_v1,
)

_SECRET = 25  # Public deterministic test scalar only.
_DEFAULT_CUSTODY_ATOMS_V1 = 7
_CUSTODY_OWNER_V1 = "custodian"
_CUSTODY_ASSET_V1 = "USD"
_CUSTODY_DOMAIN_V1 = "vault"
_CLAIMANT_V1 = "alice"


@dataclass(frozen=True, slots=True)
class CustodyAssetReceiptActivationV1:
    """Immutable activation context reused by forward-epoch fixtures."""

    profile: abi.EconomicProfileSnapshotV1
    policy: abi.EconomicPolicyRegistryV1
    authorization_registry: EconomicCommandAuthorizationRegistryV1
    signature_verifier_registry: EconomicCommandSignatureVerifierRegistryV1
    asset_policy_registry: AssetTransferPolicyRegistryV1
    signature_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1
    signature_release: EconomicCommandSignatureVerifierReleaseV1
    signature_artifact_path: Path
    initial_state_admission: EconomicInitialStateAdmissionV1
    source_state: abi.GlobalEconomicStateV1


@dataclass
class _Fixture:
    """Existing publisher-fixture shape plus explicit custody rows."""

    candidate: proof.EconomicEpochReceiptCandidateV1
    raw: pipeline.RawAssetTransferReceiptEvidenceV1
    policy: abi.EconomicPolicyRegistryV1
    signature_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1
    signature_release: EconomicCommandSignatureVerifierReleaseV1
    expected: tuple[tuple[bytes, str, bytes], ...]
    calls: list[tuple[bytes, str, bytes]]
    custody_atoms: int
    custody_rows: tuple[abi.EconomicAmountV1, ...]
    liability_rows: tuple[abi.EconomicAmountV1, ...]
    activation: CustodyAssetReceiptActivationV1
    fail_at: str | None = None
    on_call: Callable[[], None] | None = None

    def verify_succinct_receipt(
        self,
        receipt: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        row = (receipt, expected_image_id, expected_journal_bytes)
        self.calls.append(row)
        if self.on_call is not None:
            self.on_call()
        name = receipt.decode()
        if name == self.fail_at:
            raise RuntimeError(f"synthetic {name} verifier unavailable")
        if row not in self.expected:
            raise ValueError("synthetic receipt statement rejected")


def _rebind_module_release_v1(
    release: abi.LaneModuleReleaseV1,
    specification_root: str,
) -> abi.LaneModuleReleaseV1:
    values = {
        field.name: getattr(release, field.name)
        for field in fields(release)
        if field.name != "release_id"
    }
    values["specification_root"] = specification_root
    return abi.LaneModuleReleaseV1.build(**values)


def _rebind_coordinator_release_v1(
    release: abi.LaneCoordinatorReleaseV1,
    specification_root: str,
) -> abi.LaneCoordinatorReleaseV1:
    values = {
        field.name: getattr(release, field.name)
        for field in fields(release)
        if field.name != "coordinator_release_id"
    }
    values["specification_root"] = specification_root
    return abi.LaneCoordinatorReleaseV1.build(**values)


def _rebind_route_release_v1(
    route: abi.RouteReleaseV1,
    *,
    module_release_id: str,
    specification_root: str,
) -> abi.RouteReleaseV1:
    values = {
        field.name: getattr(route, field.name)
        for field in fields(route)
        if field.name != "route_release_id"
    }
    values.update(
        module_release_ids=(module_release_id,),
        specification_root=specification_root,
    )
    return abi.RouteReleaseV1.build(**values)


def _custody_profile_v1(
    base: abi.EconomicProfileSnapshotV1,
    *,
    root_overrides: Mapping[str, str] | None,
    policy: abi.EconomicPolicyRegistryV1,
    verifier_registry_root: str,
) -> tuple[abi.EconomicProfileSnapshotV1, abi.RouteReleaseV1]:
    roots = {
        "module": ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1,
        "coordinator": ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1,
        "route": ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1,
    }
    if root_overrides is not None:
        unknown = set(root_overrides) - set(roots)
        if unknown:
            raise ValueError(f"unknown custody semantic root role: {sorted(unknown)!r}")
        roots.update(root_overrides)
    asset_module = base.lane_registry.release_for(abi.LaneIdV1.ASSET_TRANSFER)
    module_releases = tuple(
        _rebind_module_release_v1(asset_module, roots["module"])
        if row.lane_id is abi.LaneIdV1.ASSET_TRANSFER
        else row
        for row in base.lane_registry.releases
    )
    module = next(
        row for row in module_releases if row.lane_id is abi.LaneIdV1.ASSET_TRANSFER
    )
    coordinator_releases = tuple(
        _rebind_coordinator_release_v1(row, roots["coordinator"])
        if row.lane_id is abi.LaneIdV1.ASSET_TRANSFER
        else row
        for row in base.lane_coordinator_registry.releases
    )
    old_route = base.route_registry.routes[0]
    route = _rebind_route_release_v1(
        old_route,
        module_release_id=module.release_id,
        specification_root=roots["route"],
    )
    values = {
        field.name: getattr(base, field.name)
        for field in fields(base)
        if field.name != "profile_id"
    }
    values.update(
        lane_registry=abi.LaneRegistryV1(module_releases),
        lane_coordinator_registry=abi.LaneCoordinatorRegistryV1(coordinator_releases),
        route_registry=abi.RouteRegistryV1((route,)),
        policy_registry_root=policy.registry_root,
        verifier_registry_root=verifier_registry_root,
    )
    profile = abi.EconomicProfileSnapshotV1.build(**values)
    abi_fixtures._POLICY_REGISTRY_BY_PROFILE_ID_V1[profile.profile_id] = policy
    return profile, route


def _signature_coordinates_v1(
    artifact: Path,
    *,
    manifest_factory: Callable[[bytes], EconomicCommandSignatureVerifierEvidenceManifestV1]
    | None,
    release_factory: Callable[
        [EconomicCommandSignatureVerifierEvidenceManifestV1],
        EconomicCommandSignatureVerifierReleaseV1,
    ]
    | None,
) -> tuple[
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    EconomicCommandSignatureVerifierReleaseV1,
]:
    artifact_bytes = artifact.read_bytes()
    manifest = (
        _signature_verifier_manifest(artifact_bytes=artifact_bytes)
        if manifest_factory is None
        else manifest_factory(artifact_bytes)
    )
    if manifest_factory is None:
        manifest = replace(
            manifest,
            max_public_key_bytes=98,
            max_signature_bytes=96,
        )
    initial_release = (
        _signature_verifier_release(manifest)
        if release_factory is None
        else None
    )
    manifest = replace(
        manifest,
        evidence_artifacts=tuple(
            row
            for row in manifest.evidence_artifacts
            if row.status in REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1
        ),
    )
    if initial_release is None:
        if release_factory is None:
            raise AssertionError("signature release factory is required")
        release = release_factory(manifest)
    else:
        release = initial_release
    release_values = {
        field.name: getattr(release, field.name)
        for field in fields(release)
        if field.name != "release_id"
    }
    release_values.update(
        evidence_manifest_root=manifest.manifest_root,
        evidence_statuses=tuple(row.status for row in manifest.evidence_artifacts),
        status=abi.ReleaseStatusV1.SHADOW,
        accepts_new_authentications=False,
    )
    release = EconomicCommandSignatureVerifierReleaseV1.build(**release_values)
    return manifest, release


def _build_fixture_from_context_v1(
    *,
    profile: abi.EconomicProfileSnapshotV1,
    route: abi.RouteReleaseV1,
    policy: abi.EconomicPolicyRegistryV1,
    authorizations: EconomicCommandAuthorizationRegistryV1,
    signatures: EconomicCommandSignatureVerifierRegistryV1,
    transfer_registry: AssetTransferPolicyRegistryV1,
    authorization: EconomicCommandAuthorizationV1,
    signature_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    signature_release: EconomicCommandSignatureVerifierReleaseV1,
    pre: abi.GlobalEconomicStateV1,
    custody_rows: tuple[abi.EconomicAmountV1, ...],
    liability_rows: tuple[abi.EconomicAmountV1, ...],
    custody_atoms: int,
    nonce_start: int,
    activation: CustodyAssetReceiptActivationV1,
) -> _Fixture:
    """Build a candidate from one already-authenticated activation context."""

    if pre.profile_root != profile.profile_id:
        raise ValueError("pipeline fixture predecessor profile mismatch")
    if pre.custody != custody_rows or pre.liabilities != liability_rows:
        raise ValueError("pipeline fixture predecessor rows mismatch")
    module_state = replace(
        _epoch_asset_module_state(profile),
        balances=pre.balances,
        supplies=pre.supplies,
    )
    occurrence = replace(
        abi_fixtures._occurrence(profile, route, pre),
        nonce=nonce_start,
    )
    module_input = _asset_module_input_for_occurrence(
        profile,
        occurrence,
        _epoch_asset_module_state(profile),
    )
    module_input = replace(module_input, pre_state=module_state, custody=custody_rows)
    accepted = transition_asset_transfer_lane_module_custody_v1(module_input)
    if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
        raise ValueError("custody fixture module rejected")
    lane = compose_asset_lane_single_v1(
        _asset_lane_context(profile, occurrence, module_input, accepted),
        accepted.module_journal,
        accepted.private_port,
        accepted.effects,
    )
    if type(lane) is not AssetLaneCompositionAcceptedV1:
        raise ValueError("custody fixture lane composition rejected")
    projected = accepted.private_port.post_state
    post = replace(
        pre,
        height=pre.height + 1,
        balances=projected.balances,
        custody=projected.custody,
        supplies=projected.supplies,
        lane_roots=(
            replace(pre.lane_roots[0], state_root=projected.state_root),
            *pre.lane_roots[1:],
        ),
        replay_state=tuple(
            sorted(
                (
                    *pre.replay_state,
                    abi.ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id),
                )
            )
        ),
    )
    journal = proof.RouteCompositionJournalV1(
        pre.chain_id,
        pre.deployment_root,
        profile.profile_id,
        pre.writer_epoch,
        route.route_release_id,
        occurrence.occurrence_id,
        (lane.lane_journal.journal_root,),
        pre.state_root,
        post.state_root,
        lane.effects.effect_plan_root,
        lane.lane_journal.terminal_obligations_root,
    )
    assumption = derive_route_composition_assumption_root_v1(
        profile_id=profile.profile_id,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        writer_epoch=pre.writer_epoch,
        route_journal_root=journal.journal_root,
        route_journal_digest="0x"
        + hashlib.sha256(abi.canonical_global_bytes_v1(journal)).hexdigest(),
        expected_image_id=route.guest_image_id,
    )
    template = _epoch_admission_fixture(1)
    certificate = replace(
        template.certificate,
        profile_root=profile.profile_id,
        height=post.height,
        pre_state_root=pre.state_root,
        post_state_root=post.state_root,
        ordered_occurrence_ids=(occurrence.occurrence_id,),
        ordered_route_journal_roots=(journal.journal_root,),
        ordered_route_assumption_roots=(assumption,),
        effect_plan_root=lane.effects.effect_plan_root,
        root_image_id=profile.root_image_id,
    )
    certificate = replace(certificate, journal_bytes=len(certificate.canonical_journal_bytes))
    candidate = _epoch_candidate(
        profile,
        certificate,
        pre,
        post,
        (occurrence,),
        (journal,),
        (proof.EconomicEpochRouteStateDisclosureV1((lane.lane_journal,), post),),
        (),
        (lane.effects,),
        lane.effects,
        template.receipt_bytes,
    )
    intent = EconomicCommandIntentV1(
        occurrence.chain_id,
        occurrence.deployment_root,
        profile.profile_id,
        occurrence.command_kind,
        occurrence.command_body_hash,
        occurrence.route_release_id,
        occurrence.subject_id,
        occurrence.grant_root,
        occurrence.nonce,
        occurrence.consumed_object_ids,
        0,
        10,
    )
    envelope = EconomicCommandAuthenticationEnvelopeV1(
        abi.canonical_economic_command_body_bytes_v1(
            ASSET_TRANSFER_COMMAND_KIND_V1,
            module_input.command,
        ),
        authorization.signer_key_id,
        authorization.signer_public_key,
        authorization.signature_algorithm,
        b"x",
    )
    message = _isolated_economic_command_authentication_message_bytes_v1(
        EconomicCommandAuthenticationCandidateV1(
            profile,
            policy,
            authorizations,
            signatures,
            intent,
            envelope,
        ),
        authorization,
    )
    raw = pipeline.RawAssetTransferReceiptEvidenceV1(
        intent,
        replace(envelope, signature_bytes=G2Basic.Sign(_SECRET, message)),
        authorizations,
        signatures,
        transfer_registry,
        module_input,
        b"module",
        b"coordinator",
        b"route",
    )
    expected = tuple(
        (receipt, image, abi.canonical_global_bytes_v1(value))
        for receipt, image, value in (
            (
                b"module",
                profile.lane_registry.release_for(
                    abi.LaneIdV1.ASSET_TRANSFER
                ).guest_image_id,
                accepted.module_journal,
            ),
            (
                b"coordinator",
                profile.lane_coordinator_registry.release_for(
                    abi.LaneIdV1.ASSET_TRANSFER
                ).guest_image_id,
                lane.lane_journal,
            ),
            (b"route", route.guest_image_id, journal),
        )
    )
    return _Fixture(
        candidate=candidate,
        raw=raw,
        policy=policy,
        signature_manifest=signature_manifest,
        signature_release=signature_release,
        expected=expected,
        calls=[],
        custody_atoms=custody_atoms,
        custody_rows=custody_rows,
        liability_rows=liability_rows,
        activation=activation,
    )


def custody_asset_receipt_fixture_v1(
    owner: Any,
    *,
    custody_atoms: int = _DEFAULT_CUSTODY_ATOMS_V1,
    claimant_liabilities: tuple[abi.EconomicAmountV1, ...] | None = None,
    semantic_root_overrides: Mapping[str, str] | None = None,
    signature_artifact_path: Path | None = None,
    signature_manifest_factory: Callable[[bytes], EconomicCommandSignatureVerifierEvidenceManifestV1]
    | None = None,
    signature_release_factory: Callable[
        [EconomicCommandSignatureVerifierEvidenceManifestV1],
        EconomicCommandSignatureVerifierReleaseV1,
    ]
    | None = None,
    activation: CustodyAssetReceiptActivationV1 | None = None,
    pre_state: abi.GlobalEconomicStateV1 | None = None,
    nonce_start: int = 1,
) -> _Fixture:
    """Build one custody profile and its receipt-backed epoch candidate.

    ``custody_atoms`` changes the committed supply and custody projection.  A
    positive default also commits the exact liability row consumed later by
    allocation admission.  Passing ``claimant_liabilities=()`` deliberately
    leaves custody unbacked for the publisher/allocation rejection test.

    Forward epochs pass the prior fixture's ``activation`` together with a
    later ``pre_state``.  That path reuses the original activation evidence.
    """

    if activation is not None:
        if type(activation) is not CustodyAssetReceiptActivationV1:
            raise TypeError("pipeline fixture activation type is not closed")
        if semantic_root_overrides is not None:
            raise ValueError("forward fixture cannot rebind activation semantic roots")
        if signature_manifest_factory is not None or signature_release_factory is not None:
            raise ValueError("forward fixture cannot rebuild activation signature coordinates")
        if (
            signature_artifact_path is not None
            and signature_artifact_path != activation.signature_artifact_path
        ):
            raise ValueError("forward fixture signature artifact does not match activation")
        pre = activation.source_state if pre_state is None else pre_state
        forward_custody_rows = pre.custody
        forward_liability_rows = pre.liabilities
        if (
            claimant_liabilities is not None
            and claimant_liabilities != forward_liability_rows
        ):
            raise ValueError("forward fixture cannot rebind activation liabilities")
        actual_custody_atoms = sum(row.amount_atoms for row in forward_custody_rows)
        if (
            custody_atoms != _DEFAULT_CUSTODY_ATOMS_V1
            and custody_atoms != actual_custody_atoms
        ):
            raise ValueError("forward fixture custody atoms do not match predecessor")
        route = activation.profile.route_registry.routes[0]
        authorization = activation.authorization_registry.authorizations[0]
        return _build_fixture_from_context_v1(
            profile=activation.profile,
            route=route,
            policy=activation.policy,
            authorizations=activation.authorization_registry,
            signatures=activation.signature_verifier_registry,
            transfer_registry=activation.asset_policy_registry,
            authorization=authorization,
            signature_manifest=activation.signature_manifest,
            signature_release=activation.signature_release,
            pre=pre,
            custody_rows=forward_custody_rows,
            liability_rows=forward_liability_rows,
            custody_atoms=actual_custody_atoms,
            nonce_start=nonce_start,
            activation=activation,
        )
    if pre_state is not None:
        raise ValueError("forward fixture requires an immutable activation context")

    base, route_seed, _, _, _, _, _ = _global_allocation_fixture()
    owner.template = owner.artifacts(base, None)
    artifact = signature_artifact_path or Path(bls.__file__)
    signature_manifest, signature_release = _signature_coordinates_v1(
        artifact,
        manifest_factory=signature_manifest_factory,
        release_factory=signature_release_factory,
    )
    signatures = EconomicCommandSignatureVerifierRegistryV1((signature_release,))
    verifier_registry_root = EconomicReceiptVerifierRegistryV1(
        (_release(owner.manifest()),)
    ).registry_root
    # The policy bindings are inherited from the measured global fixture, then
    # rebound to this fixture's authorization, signature and transfer rows.
    authorization = EconomicCommandAuthorizationV1(
        ASSET_TRANSFER_COMMAND_KIND_V1,
        _CLAIMANT_V1,
        abi_fixtures._root(600),
        route_seed.route_release_id,
        "alice-key-1",
        "0x" + G2Basic.SkToPk(_SECRET).hex(),
        "BLS12_381_G2_BASIC_V1",
        0,
        10,
        0,
        10,
        True,
    )
    authorizations = EconomicCommandAuthorizationRegistryV1((authorization,))

    custody_rows: tuple[abi.EconomicAmountV1, ...] = (
        ()
        if custody_atoms == 0
        else (
            abi.EconomicAmountV1(
                _CUSTODY_OWNER_V1,
                _CUSTODY_ASSET_V1,
                _CUSTODY_DOMAIN_V1,
                custody_atoms,
            ),
        )
    )
    liability_rows = (
        (
            abi.EconomicAmountV1(
                _CLAIMANT_V1,
                _CUSTODY_ASSET_V1,
                _CUSTODY_DOMAIN_V1,
                custody_atoms,
            ),
        )
        if custody_atoms and claimant_liabilities is None
        else (() if claimant_liabilities is None else claimant_liabilities)
    )

    # Build the profile once with a provisional route, then rebind the route
    # and module ids together.  Policy rows depend only on the selected route's
    # module id and are replaced after that route is available.
    _provisional_profile, provisional_route = _custody_profile_v1(
        base,
        root_overrides=semantic_root_overrides,
        policy=_governed_policy_registry_for_profile_v1(base),
        verifier_registry_root=verifier_registry_root,
    )
    authorization = replace(
        authorization,
        route_release_id=provisional_route.route_release_id,
    )
    authorizations = EconomicCommandAuthorizationRegistryV1((authorization,))
    transfer_registry = _asset_transfer_policy_registry_for_route_v1(provisional_route)
    provisional_module_state = _epoch_asset_module_state(_provisional_profile)
    if custody_atoms:
        provisional_module_state = replace(
            provisional_module_state,
            supplies=tuple(
                replace(row, amount_atoms=row.amount_atoms + custody_atoms)
                if row.asset == _CUSTODY_ASSET_V1
                else row
                for row in provisional_module_state.supplies
            ),
        )
    provisional_pre = abi_fixtures._global_state_from_asset_module(
        _provisional_profile,
        _epoch_asset_module_state(_provisional_profile),
        height=0,
    )
    provisional_projection = project_asset_transfer_state_v1(
        provisional_module_state,
        asset_policy_registry_root=transfer_registry.asset_policy_root,
        fee_policy_registry_root=transfer_registry.fee_policy_root,
        custody=custody_rows,
    )
    provisional_pre = replace(
        provisional_pre,
        lane_roots=(
            tuple(
                replace(
                    row,
                    state_root=(
                        provisional_projection.state_root
                        if row.lane_id is abi.LaneIdV1.ASSET_TRANSFER
                        else cert.REGISTERED_EMPTY_LANE_ROOTS_V1.get(
                            row.lane_id, row.state_root
                        )
                    ),
                )
                for row in provisional_pre.lane_roots
            )
        ),
        balances=provisional_projection.balances,
        custody=provisional_projection.custody,
        liabilities=liability_rows,
        supplies=provisional_projection.supplies,
    )
    source_manifest = abi_fixtures._source_manifest_for_state_v1(
        EconomicInitialStateKindV1.GENESIS,
        provisional_pre,
    )
    bindings = _governed_policy_registry_for_profile_v1(base).bindings
    roots = {
        ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1: authorizations.registry_root,
        ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1: signatures.registry_root,
        ASSET_TRANSFER_ASSET_POLICY_KIND_V1: transfer_registry.asset_policy_root,
        ASSET_TRANSFER_FEE_POLICY_KIND_V1: transfer_registry.fee_policy_root,
    }
    # Match by policy kind; the two transfer rows have distinct governed kinds.
    policy = abi.EconomicPolicyRegistryV1(
        tuple(
            replace(
                row,
                policy_root=(
                    authorizations.registry_root
                    if row.policy_kind == ECONOMIC_COMMAND_AUTHENTICATION_POLICY_KIND_V1
                    else (
                        signatures.registry_root
                        if row.policy_kind == ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1
                        else (
                            transfer_registry.asset_policy_root
                            if row.policy_kind == ASSET_TRANSFER_ASSET_POLICY_KIND_V1
                            else (
                                transfer_registry.fee_policy_root
                                if row.policy_kind == ASSET_TRANSFER_FEE_POLICY_KIND_V1
                                else (
                                    source_manifest.manifest_root
                                    if row.policy_kind
                                    == M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1
                                    else row.policy_root
                                )
                            )
                        )
                    )
                ),
            )
            for row in bindings
        )
    )
    profile, route = _custody_profile_v1(
        base,
        root_overrides=semantic_root_overrides,
        policy=policy,
        verifier_registry_root=verifier_registry_root,
    )
    # ``_custody_profile_v1`` derives the route from base, so its final route
    # is the one whose module id the policy transfer registry names.
    transfer_registry = _asset_transfer_policy_registry_for_route_v1(route)
    if transfer_registry.asset_policy_root != roots[ASSET_TRANSFER_ASSET_POLICY_KIND_V1]:
        raise AssertionError("custody fixture transfer policy route was not rebound")

    module_state = _epoch_asset_module_state(profile)
    if custody_atoms:
        module_state = replace(
            module_state,
            supplies=tuple(
                replace(row, amount_atoms=row.amount_atoms + custody_atoms)
                if row.asset == _CUSTODY_ASSET_V1
                else row
                for row in module_state.supplies
            ),
        )
    complete_pre = abi_fixtures._global_state_from_asset_module(
        profile,
        # The generic helper projects an accounts-only state.  Build its
        # headers from the unextended rows, then replace all economic tables
        # with the custody-aware projection below.
        _epoch_asset_module_state(profile),
        height=0,
    )
    projection = project_asset_transfer_state_v1(
        module_state,
        asset_policy_registry_root=transfer_registry.asset_policy_root,
        fee_policy_registry_root=transfer_registry.fee_policy_root,
        custody=custody_rows,
    )
    complete_pre = replace(
        complete_pre,
        lane_roots=(
            tuple(
                replace(
                    row,
                    state_root=(
                        projection.state_root
                        if row.lane_id is abi.LaneIdV1.ASSET_TRANSFER
                        else cert.REGISTERED_EMPTY_LANE_ROOTS_V1.get(
                            row.lane_id, row.state_root
                        )
                    ),
                )
                for row in complete_pre.lane_roots
            )
        ),
        balances=projection.balances,
        custody=projection.custody,
        liabilities=liability_rows,
        supplies=projection.supplies,
    )
    initial_admission = replace(
        abi_fixtures._initial_state_admission(
            profile,
            complete_pre,
            source_manifest=source_manifest,
        ),
        policy_registry=policy,
    )
    activation = CustodyAssetReceiptActivationV1(
        profile=profile,
        policy=policy,
        authorization_registry=authorizations,
        signature_verifier_registry=signatures,
        asset_policy_registry=transfer_registry,
        signature_manifest=signature_manifest,
        signature_release=signature_release,
        signature_artifact_path=artifact,
        initial_state_admission=initial_admission,
        source_state=complete_pre,
    )
    return _build_fixture_from_context_v1(
        profile=profile,
        route=route,
        policy=policy,
        authorizations=authorizations,
        signatures=signatures,
        transfer_registry=transfer_registry,
        authorization=authorization,
        signature_manifest=signature_manifest,
        signature_release=signature_release,
        pre=complete_pre,
        custody_rows=custody_rows,
        liability_rows=liability_rows,
        custody_atoms=custody_atoms,
        nonce_start=nonce_start,
        activation=activation,
    )


_fixture = custody_asset_receipt_fixture_v1


__all__ = [
    "CustodyAssetReceiptActivationV1",
    "_Fixture",
    "custody_asset_receipt_fixture_v1",
    "_fixture",
]
