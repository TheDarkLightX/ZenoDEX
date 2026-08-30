"""Release selection and measured capability tests for epoch receipt verification."""

from __future__ import annotations

from dataclasses import replace
from typing import Any, cast

import pytest

import src.core.economic_receipt_verifier_deployment_v1 as deployment_module
from src.core.economic_receipt_verifier_deployment_v1 import (
    BoundEconomicReceiptVerifierV1,
    EconomicReceiptVerifierBackendV1,
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
    select_profile_governed_economic_receipt_verifier_release_v1,
)
from src.core.global_settlement_types_v1 import ProfileStatusV1, ReleaseStatusV1
from tests.core.test_global_settlement_abi_v1 import _profile

_ARTIFACT_BYTES = b"test-risc0-3.0.6-verifier-artifact"
_PROOF_SYSTEM = "RISC0_ZKVM_3_0_6"
_SHADOW_EVIDENCE = tuple(
    sorted(
        (
            EconomicReceiptVerifierEvidenceStatusV1.IMPLEMENTED,
            EconomicReceiptVerifierEvidenceStatusV1.SOURCE_PINNED,
            EconomicReceiptVerifierEvidenceStatusV1.SPECIFIED,
            EconomicReceiptVerifierEvidenceStatusV1.TESTED,
            EconomicReceiptVerifierEvidenceStatusV1.TOOLCHAIN_PINNED,
        ),
        key=lambda status: status.value,
    )
)
_ACTIVE_EVIDENCE = tuple(
    sorted(EconomicReceiptVerifierEvidenceStatusV1, key=lambda status: status.value)
)


def _root(index: int) -> str:
    return "0x" + f"{index:064x}"


class _RecordingBackend(EconomicReceiptVerifierBackendV1):
    def __init__(self, *, result: object = None) -> None:
        self.calls: list[tuple[bytes, str, bytes]] = []
        self.result = result

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object:
        self.calls.append(
            (receipt_bytes, expected_image_id, expected_journal_bytes)
        )
        return self.result


def _manifest(
    *,
    implementation_root: str | None = None,
    root_image_id: str = _root(411),
    max_receipt_bytes: int = 16,
    max_journal_bytes: int = 32,
    evidence_statuses: tuple[EconomicReceiptVerifierEvidenceStatusV1, ...] = (
        _SHADOW_EVIDENCE
    ),
) -> EconomicReceiptVerifierEvidenceManifestV1:
    implementation_root = implementation_root or (
        economic_receipt_verifier_implementation_root_v1(_ARTIFACT_BYTES)
    )
    artifacts = tuple(
        EconomicReceiptVerifierEvidenceArtifactV1(status, _root(600 + index))
        for index, status in enumerate(evidence_statuses)
    )
    return EconomicReceiptVerifierEvidenceManifestV1(
        proof_system=_PROOF_SYSTEM,
        implementation_root=implementation_root,
        receipt_schema_root=_root(501),
        journal_schema_root=_root(502),
        root_image_id=root_image_id,
        specification_root=_root(503),
        source_root=_root(504),
        toolchain_root=_root(505),
        backend_protocol_root=economic_receipt_verifier_backend_protocol_root_v1(),
        max_receipt_bytes=max_receipt_bytes,
        max_journal_bytes=max_journal_bytes,
        evidence_artifacts=artifacts,
    )


def _release(
    manifest: EconomicReceiptVerifierEvidenceManifestV1,
    *,
    semantic_version: str = "3.0.6-shadow.1",
    status: ReleaseStatusV1 = ReleaseStatusV1.SHADOW,
    accepts_new_receipts: bool = False,
    evidence_statuses: tuple[EconomicReceiptVerifierEvidenceStatusV1, ...] = (
        _SHADOW_EVIDENCE
    ),
) -> EconomicReceiptVerifierReleaseV1:
    return EconomicReceiptVerifierReleaseV1.build(
        semantic_version=semantic_version,
        proof_system=manifest.proof_system,
        implementation_root=manifest.implementation_root,
        receipt_schema_root=manifest.receipt_schema_root,
        journal_schema_root=manifest.journal_schema_root,
        root_image_id=manifest.root_image_id,
        specification_root=manifest.specification_root,
        source_root=manifest.source_root,
        toolchain_root=manifest.toolchain_root,
        evidence_manifest_root=manifest.manifest_root,
        backend_protocol_root=manifest.backend_protocol_root,
        max_receipt_bytes=manifest.max_receipt_bytes,
        max_journal_bytes=manifest.max_journal_bytes,
        status=status,
        accepts_new_receipts=accepts_new_receipts,
        evidence_statuses=evidence_statuses,
    )


def _bound(
    *,
    backend: _RecordingBackend | None = None,
    artifact_bytes: bytes = _ARTIFACT_BYTES,
) -> tuple[BoundEconomicReceiptVerifierV1, _RecordingBackend]:
    manifest = _manifest()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    profile, _ = _profile(verifier_registry_root=registry.registry_root)
    selected_backend = backend or _RecordingBackend()
    bound = bind_economic_receipt_verifier_deployment_v1(
        profile=profile,
        verifier_registry=registry,
        selection_purpose=(
            EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
        ),
        evidence_manifest=manifest,
        measured_artifact_bytes=artifact_bytes,
        deployment_root=_root(7),
        backend=selected_backend,
    )
    return bound, selected_backend


def test_profile_selects_exactly_one_shadow_release() -> None:
    # Arrange: one profile commits one content-derived shadow verifier registry.
    manifest = _manifest()
    release = _release(manifest)
    registry = EconomicReceiptVerifierRegistryV1((release,))
    profile, _ = _profile(verifier_registry_root=registry.registry_root)

    # Act: select for the explicitly research-only publisher purpose.
    selected = select_profile_governed_economic_receipt_verifier_release_v1(
        profile=profile,
        verifier_registry=registry,
        selection_purpose=(
            EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
        ),
    )

    # Assert: the exact profile/image-bound release is selected.
    assert selected == release
    assert selected.root_image_id == profile.root_image_id


def test_wrong_profile_registry_root_rejects_before_selection() -> None:
    # Arrange: the profile commits a different registry root.
    manifest = _manifest()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    profile, _ = _profile(verifier_registry_root=_root(999))

    # Act and assert: registry substitution fails closed.
    with pytest.raises(ValueError, match="profile governed"):
        select_profile_governed_economic_receipt_verifier_release_v1(
            profile=profile,
            verifier_registry=registry,
            selection_purpose=(
                EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
            ),
        )


def test_two_shadow_releases_for_one_proof_system_fail_closed() -> None:
    # Arrange: two distinct shadow implementations claim the same proof system.
    first_manifest = _manifest()
    second_manifest = _manifest(implementation_root=_root(777))
    registry = EconomicReceiptVerifierRegistryV1(
        tuple(
            sorted(
                (_release(first_manifest), _release(second_manifest)),
                key=lambda release: release.key,
            )
        )
    )
    profile, _ = _profile(verifier_registry_root=registry.registry_root)

    # Act and assert: ambiguity cannot choose verifier authority.
    with pytest.raises(ValueError, match="one shadow verifier release"):
        select_profile_governed_economic_receipt_verifier_release_v1(
            profile=profile,
            verifier_registry=registry,
            selection_purpose=(
                EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
            ),
        )


def test_active_release_requires_complete_release_evidence() -> None:
    # Arrange: a shadow evidence set is relabeled as active.
    manifest = _manifest()

    # Act and assert: incomplete evidence cannot create an active verifier release.
    with pytest.raises(ValueError, match="lacks release evidence"):
        _release(
            manifest,
            status=ReleaseStatusV1.ACTIVE_NEW,
            accepts_new_receipts=True,
        )


def test_complete_active_labels_cannot_mint_production_authority() -> None:
    # Arrange: Mallory supplies every producer-controlled evidence label.
    manifest = _manifest(evidence_statuses=_ACTIVE_EVIDENCE)
    release = _release(
        manifest,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_receipts=True,
        evidence_statuses=_ACTIVE_EVIDENCE,
    )
    registry = EconomicReceiptVerifierRegistryV1((release,))
    profile, _ = _profile(verifier_registry_root=registry.registry_root)
    backend = _RecordingBackend()

    # Act and assert: labels cannot replace an objective activation certificate.
    with pytest.raises(ValueError, match="activation certificate is not implemented"):
        bind_economic_receipt_verifier_deployment_v1(
            profile=profile,
            verifier_registry=registry,
            selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.PRODUCTION_NEW,
            evidence_manifest=manifest,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_root(7),
            backend=backend,
        )
    assert backend.calls == []


def test_production_selection_rejects_inactive_profile() -> None:
    # Arrange: a shadow profile contains a structurally active verifier release.
    manifest = _manifest(evidence_statuses=_ACTIVE_EVIDENCE)
    release = _release(
        manifest,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_receipts=True,
        evidence_statuses=_ACTIVE_EVIDENCE,
    )
    registry = EconomicReceiptVerifierRegistryV1((release,))
    profile, _ = _profile(
        verifier_registry_root=registry.registry_root,
        status=ProfileStatusV1.SHADOW,
    )

    # Act and assert: release labels cannot activate an inactive profile.
    with pytest.raises(ValueError, match="active profile"):
        select_profile_governed_economic_receipt_verifier_release_v1(
            profile=profile,
            verifier_registry=registry,
            selection_purpose=(
                EconomicReceiptVerifierSelectionPurposeV1.PRODUCTION_NEW
            ),
        )


def test_measured_bound_capability_verifies_exact_image_and_bytes() -> None:
    # Arrange: one measured shadow release is bound to its profile and deployment.
    bound, backend = _bound()

    # Act: verify one receipt at both release-configured byte ceilings.
    bound.verify_succinct_receipt(
        b"r" * 16,
        expected_image_id=_root(411),
        expected_journal_bytes=b"j" * 32,
    )

    # Assert: exact None means success and the backend receives exact bytes.
    assert backend.calls == [(b"r" * 16, _root(411), b"j" * 32)]


@pytest.mark.parametrize(
    ("receipt_length", "accepted"),
    ((0, False), (1, True), (16, True), (17, False)),
)
def test_receipt_length_uses_zero_one_maximum_neighbor_bva(
    receipt_length: int,
    accepted: bool,
) -> None:
    # Arrange: a release fixes a 16-byte receipt ceiling.
    bound, backend = _bound()

    # Act: submit each closed-boundary neighbor.
    if accepted:
        bound.verify_succinct_receipt(
            b"r" * receipt_length,
            expected_image_id=_root(411),
            expected_journal_bytes=b"j",
        )
    else:
        with pytest.raises(ValueError, match="receipt byte length"):
            bound.verify_succinct_receipt(
                b"r" * receipt_length,
                expected_image_id=_root(411),
                expected_journal_bytes=b"j",
            )

    # Assert: rejected boundaries never invoke the backend.
    assert len(backend.calls) == int(accepted)


@pytest.mark.parametrize(
    ("journal_length", "accepted"),
    ((0, False), (1, True), (32, True), (33, False)),
)
def test_journal_length_uses_zero_one_maximum_neighbor_bva(
    journal_length: int,
    accepted: bool,
) -> None:
    # Arrange: a release fixes a 32-byte journal ceiling.
    bound, backend = _bound()

    # Act: submit each closed-boundary neighbor.
    if accepted:
        bound.verify_succinct_receipt(
            b"r",
            expected_image_id=_root(411),
            expected_journal_bytes=b"j" * journal_length,
        )
    else:
        with pytest.raises(ValueError, match="journal byte length"):
            bound.verify_succinct_receipt(
                b"r",
                expected_image_id=_root(411),
                expected_journal_bytes=b"j" * journal_length,
            )

    # Assert: rejected boundaries never invoke the backend.
    assert len(backend.calls) == int(accepted)


def test_wrong_artifact_rejects_before_backend_use() -> None:
    # Arrange: the registry commits the expected implementation measurement.
    backend = _RecordingBackend()

    # Act and assert: a different measured artifact cannot bind the backend.
    with pytest.raises(ValueError, match="measured implementation root"):
        _bound(backend=backend, artifact_bytes=b"wrong-artifact")
    assert backend.calls == []


def test_wrong_image_rejects_before_backend_use() -> None:
    # Arrange: one exact image is selected by profile and release.
    bound, backend = _bound()

    # Act and assert: cross-image verification never reaches the backend.
    with pytest.raises(ValueError, match="image binding"):
        bound.verify_succinct_receipt(
            b"receipt",
            expected_image_id=_root(999),
            expected_journal_bytes=b"journal",
        )
    assert backend.calls == []


def test_hostile_release_identifiers_reject_before_equality_or_backend_use() -> None:
    # Arrange: Mallory supplies an object whose equality claims every release id.
    class AlwaysEqual:
        def __eq__(self, other: object) -> bool:
            return True

    profile, _ = _profile()
    bound, backend = _bound()
    lane = profile.lane_registry.releases[0]
    coordinator = profile.lane_coordinator_registry.releases[0]
    route = profile.route_registry.routes[0]
    hostile = cast(Any, AlwaysEqual())

    # Act / Assert: exact-type checks precede comparison and registry search.
    with pytest.raises(TypeError, match="module release id must be exact str"):
        bound.verify_profile_lane_receipt(
            b"r",
            profile=profile,
            lane_id=lane.lane_id,
            expected_module_release_id=hostile,
            expected_image_id=lane.guest_image_id,
            expected_journal_bytes=b"j",
        )
    with pytest.raises(TypeError, match="coordinator release id must be exact str"):
        bound.verify_profile_lane_coordinator_receipt(
            b"r",
            profile=profile,
            lane_id=coordinator.lane_id,
            expected_coordinator_release_id=hostile,
            expected_image_id=coordinator.guest_image_id,
            expected_journal_bytes=b"j",
        )
    with pytest.raises(TypeError, match="route release id must be exact str"):
        bound.verify_profile_route_receipt(
            b"r",
            profile=profile,
            expected_route_release_id=hostile,
            expected_image_id=route.guest_image_id,
            expected_journal_bytes=b"j",
        )
    assert backend.calls == []


def test_wrong_deployment_binding_rejects_before_backend_use() -> None:
    # Arrange: one capability is bound to the profile's exact deployment root.
    manifest = _manifest()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    profile, _ = _profile(verifier_registry_root=registry.registry_root)
    backend = _RecordingBackend()
    bound = bind_economic_receipt_verifier_deployment_v1(
        profile=profile,
        verifier_registry=registry,
        selection_purpose=(
            EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
        ),
        evidence_manifest=manifest,
        measured_artifact_bytes=_ARTIFACT_BYTES,
        deployment_root=_root(7),
        backend=backend,
    )

    # Act and assert: deployment substitution fails before receipt verification.
    with pytest.raises(ValueError, match="deployment binding"):
        bound.require_binding(
            verifier_registry_root=registry.registry_root,
            deployment_root=_root(8),
            profile_root=profile.profile_id,
            root_image_id=profile.root_image_id,
            selection_purpose=(
                EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
            ),
        )
    assert backend.calls == []


def test_truthy_backend_result_is_not_cryptographic_success() -> None:
    # Arrange: a hostile backend returns True instead of the exact None contract.
    backend = _RecordingBackend(result=True)
    bound, _ = _bound(backend=backend)

    # Act and assert: truthiness cannot forge verifier success.
    with pytest.raises(ValueError, match="success contract"):
        bound.verify_succinct_receipt(
            b"receipt",
            expected_image_id=_root(411),
            expected_journal_bytes=b"journal",
        )
    assert len(backend.calls) == 1


def test_bound_verifier_pins_backend_callable_against_method_replacement() -> None:
    # Arrange: Mallory binds a rejecting backend, then replaces its method in place.
    class RejectingBackend:
        def __init__(self) -> None:
            self.original_calls = 0
            self.replacement_calls = 0

        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> None:
            self.original_calls += 1
            raise ValueError("pinned backend rejected receipt")

    backend = RejectingBackend()
    bound, _ = _bound(backend=cast(Any, backend))

    def accept_replacement(
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        backend.replacement_calls += 1

    cast(Any, backend).verify_succinct_receipt = accept_replacement

    # Act and assert: verifier authority stays with the callable pinned at binding.
    with pytest.raises(ValueError, match="pinned backend rejected receipt"):
        bound.verify_succinct_receipt(
            b"receipt",
            expected_image_id=_root(411),
            expected_journal_bytes=b"journal",
        )
    assert backend.original_calls == 1
    assert backend.replacement_calls == 0


def test_bound_capability_is_loader_constructed_and_has_no_data_slots() -> None:
    # Arrange: a valid capability has a stable release/profile binding root.
    bound, _ = _bound()
    baseline = bound.binding_root

    # Act and assert: direct construction and authority-field injection fail.
    with pytest.raises(TypeError, match="deployment-constructed"):
        BoundEconomicReceiptVerifierV1(object(), cast(Any, object()))
    with pytest.raises((AttributeError, TypeError)):
        object.__setattr__(bound, "release_id", _root(999))
    assert bound.binding_root == baseline


def test_private_mint_rechecks_selected_release_and_coordinates() -> None:
    # Arrange: Mallory imports private mint state and forges release coordinates.
    manifest = _manifest()
    release = _release(manifest)
    registry = EconomicReceiptVerifierRegistryV1((release,))
    profile, _ = _profile(verifier_registry_root=registry.registry_root)
    backend = _RecordingBackend()
    authority = deployment_module._BoundEconomicReceiptVerifierAuthorityV1(
        release_id=_root(999),
        verifier_registry_root=registry.registry_root,
        verifier_registry=registry,
        deployment_root=_root(7),
        profile_root=profile.profile_id,
        implementation_root=release.implementation_root,
        evidence_manifest_root=release.evidence_manifest_root,
        backend_protocol_root=release.backend_protocol_root,
        root_image_id=release.root_image_id,
        max_receipt_bytes=release.max_receipt_bytes,
        max_journal_bytes=release.max_journal_bytes,
        selection_purpose=(
            EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
        ),
        backend=backend,
        verify_call=backend.verify_succinct_receipt,
    )

    # Act and assert: private construction still enforces registry membership.
    with pytest.raises(ValueError, match="release is not selected by registry"):
        BoundEconomicReceiptVerifierV1(
            deployment_module._BOUND_RECEIPT_VERIFIER_TOKEN_V1,
            authority,
        )
    mismatched = replace(
        authority,
        release_id=release.release_id,
        implementation_root=_root(998),
    )
    with pytest.raises(ValueError, match="release coordinates mismatch"):
        BoundEconomicReceiptVerifierV1(
            deployment_module._BOUND_RECEIPT_VERIFIER_TOKEN_V1,
            mismatched,
        )
    assert backend.calls == []


def test_mutated_release_is_revalidated_before_registry_hashing() -> None:
    # Arrange: frozen data is reflectively changed after construction.
    manifest = _manifest()
    release = _release(manifest)
    registry = EconomicReceiptVerifierRegistryV1((release,))
    object.__setattr__(release, "root_image_id", _root(999))

    # Act and assert: current validation rejects the stale content-derived id.
    with pytest.raises(ValueError, match="content-derived"):
        _ = registry.registry_root


def test_manifest_coordinate_mutation_breaks_release_binding() -> None:
    # Arrange: Mallory changes one coordinate after the release commits the manifest.
    manifest = _manifest()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    profile, _ = _profile(verifier_registry_root=registry.registry_root)
    mutated = replace(manifest, journal_schema_root=_root(888))

    # Act and assert: coherent backend behavior cannot bypass manifest identity.
    with pytest.raises(ValueError, match="evidence manifest root"):
        bind_economic_receipt_verifier_deployment_v1(
            profile=profile,
            verifier_registry=registry,
            selection_purpose=(
                EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
            ),
            evidence_manifest=mutated,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=_root(7),
            backend=_RecordingBackend(),
        )
