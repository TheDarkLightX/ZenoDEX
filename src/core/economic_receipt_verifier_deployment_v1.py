"""Measured process-local capability for economic receipt verification."""

from __future__ import annotations

from dataclasses import dataclass
from threading import Lock
from typing import Final, Protocol, cast
from weakref import WeakKeyDictionary

from .economic_receipt_verifier_evidence_v1 import (
    MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1,
    EconomicReceiptVerifierEvidenceArtifactV1,
    EconomicReceiptVerifierEvidenceManifestV1,
    _require_manifest_release_coordinates_v1,
    _snapshot_economic_receipt_verifier_manifest_v1,
    economic_receipt_verifier_backend_protocol_root_v1,
    economic_receipt_verifier_implementation_root_v1,
)
from .economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierReleaseV1,
    EconomicReceiptVerifierSelectionPurposeV1,
    select_profile_governed_economic_receipt_verifier_release_v1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    _require_positive_int,
    _require_root,
    hash_global_v1,
)

_DEPLOYMENT_BINDING_ROOT_DOMAIN_V1: Final = "economic-receipt-verifier-deployment-binding-v1"


class EconomicReceiptVerifierBackendV1(Protocol):
    """External verifier implementation wrapped by measured release binding."""

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object: ...


class _EconomicReceiptVerifierCallV1(Protocol):
    """Exact callable retained when one backend deployment is bound."""

    def __call__(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object: ...


@dataclass(frozen=True, slots=True)
class _BoundEconomicReceiptVerifierAuthorityV1:
    release_id: str
    verifier_registry_root: str
    verifier_registry: EconomicReceiptVerifierRegistryV1
    deployment_root: str
    profile_root: str
    implementation_root: str
    evidence_manifest_root: str
    backend_protocol_root: str
    root_image_id: str
    max_receipt_bytes: int
    max_journal_bytes: int
    selection_purpose: EconomicReceiptVerifierSelectionPurposeV1
    backend: EconomicReceiptVerifierBackendV1
    verify_call: _EconomicReceiptVerifierCallV1


_BOUND_RECEIPT_VERIFIER_TOKEN_V1: Final = object()
_BOUND_RECEIPT_VERIFIER_LOCK_V1 = Lock()
_BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1: WeakKeyDictionary[
    BoundEconomicReceiptVerifierV1,
    _BoundEconomicReceiptVerifierAuthorityV1,
] = WeakKeyDictionary()


class BoundEconomicReceiptVerifierV1:
    """Data-slot-free handle for one profile-selected verifier deployment."""

    __slots__ = ("__weakref__",)

    def __init__(
        self,
        token: object,
        authority: _BoundEconomicReceiptVerifierAuthorityV1,
    ) -> None:
        if token is not _BOUND_RECEIPT_VERIFIER_TOKEN_V1:
            raise TypeError("bound economic receipt verifier must be deployment-constructed")
        _register_bound_receipt_verifier_authority_v1(self, authority)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("bound economic receipt verifier is immutable")

    @property
    def release_id(self) -> str:
        return _bound_receipt_verifier_authority_v1(self).release_id

    @property
    def binding_root(self) -> str:
        return _bound_receipt_verifier_binding_root_v1(_bound_receipt_verifier_authority_v1(self))

    @property
    def selection_purpose(self) -> EconomicReceiptVerifierSelectionPurposeV1:
        return _bound_receipt_verifier_authority_v1(self).selection_purpose

    def require_binding(
        self,
        *,
        verifier_registry_root: str,
        deployment_root: str,
        profile_root: str,
        root_image_id: str,
        selection_purpose: EconomicReceiptVerifierSelectionPurposeV1,
    ) -> None:
        authority = _snapshot_bound_receipt_verifier_authority_v1(
            _bound_receipt_verifier_authority_v1(self)
        )
        coordinates = (
            (
                verifier_registry_root,
                authority.verifier_registry_root,
                "registry",
            ),
            (deployment_root, authority.deployment_root, "deployment"),
            (profile_root, authority.profile_root, "profile"),
            (root_image_id, authority.root_image_id, "root image"),
            (selection_purpose, authority.selection_purpose, "selection purpose"),
        )
        for actual, expected, label in coordinates:
            if type(actual) is not type(expected) or actual != expected:
                raise ValueError(f"economic receipt verifier {label} binding mismatch")

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        authority = _snapshot_bound_receipt_verifier_authority_v1(
            _bound_receipt_verifier_authority_v1(self)
        )
        if type(expected_image_id) is not str or expected_image_id != authority.root_image_id:
            raise ValueError("economic receipt verifier image binding mismatch")
        self._verify_exact_receipt(
            authority,
            receipt_bytes,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )

    def verify_profile_lane_receipt(
        self,
        receipt_bytes: bytes,
        *,
        profile: EconomicProfileSnapshotV1,
        lane_id: LaneIdV1,
        expected_module_release_id: str,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        """Verify one receipt only under a profile-selected lane image.

        This closes the caller-selected-image gap for recursive leaf admission.
        The capability remains process-local; durable publication must also fence
        the current authority head.
        """

        authority = _snapshot_bound_receipt_verifier_authority_v1(
            _bound_receipt_verifier_authority_v1(self)
        )
        owned_profile = snapshot_economic_profile_v1(profile)
        if type(lane_id) is not LaneIdV1:
            raise TypeError("economic receipt verifier lane id is not closed")
        release = owned_profile.lane_registry.release_for(lane_id)
        if (
            owned_profile.profile_id != authority.profile_root
            or owned_profile.verifier_registry_root != authority.verifier_registry_root
            or owned_profile.root_image_id != authority.root_image_id
            or expected_module_release_id != release.release_id
            or expected_image_id != release.guest_image_id
        ):
            raise ValueError("economic receipt verifier lane image is outside the profile")
        if authority.selection_purpose is EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW:
            if (
                owned_profile.status is not ProfileStatusV1.SHADOW
                or release.status is not ReleaseStatusV1.SHADOW
                or release.accepts_new_objects
            ):
                raise ValueError("economic receipt verifier lane is outside shadow status")
        else:
            raise ValueError("production lane receipt verification is not implemented")
        self._verify_exact_receipt(
            authority,
            receipt_bytes,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )

    def verify_profile_lane_coordinator_receipt(
        self,
        receipt_bytes: bytes,
        *,
        profile: EconomicProfileSnapshotV1,
        lane_id: LaneIdV1,
        expected_coordinator_release_id: str,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        """Verify one profile-selected lane-coordinator receipt in SHADOW."""

        authority = _snapshot_bound_receipt_verifier_authority_v1(
            _bound_receipt_verifier_authority_v1(self)
        )
        owned_profile = snapshot_economic_profile_v1(profile)
        if type(lane_id) is not LaneIdV1:
            raise TypeError("economic receipt verifier coordinator lane is not closed")
        release = owned_profile.lane_coordinator_registry.release_for(lane_id)
        if (
            owned_profile.profile_id != authority.profile_root
            or owned_profile.verifier_registry_root != authority.verifier_registry_root
            or owned_profile.root_image_id != authority.root_image_id
            or expected_coordinator_release_id != release.coordinator_release_id
            or expected_image_id != release.guest_image_id
        ):
            raise ValueError(
                "economic receipt verifier coordinator image is outside the profile"
            )
        if authority.selection_purpose is EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW:
            if (
                owned_profile.status is not ProfileStatusV1.SHADOW
                or release.status is not ReleaseStatusV1.SHADOW
                or release.accepts_new_objects
            ):
                raise ValueError(
                    "economic receipt verifier coordinator is outside shadow status"
                )
        else:
            raise ValueError("production coordinator receipt verification is not implemented")
        self._verify_exact_receipt(
            authority,
            receipt_bytes,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )

    def verify_profile_route_receipt(
        self,
        receipt_bytes: bytes,
        *,
        profile: EconomicProfileSnapshotV1,
        expected_route_release_id: str,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        """Verify one profile-selected route-composer receipt in SHADOW."""

        authority = _snapshot_bound_receipt_verifier_authority_v1(
            _bound_receipt_verifier_authority_v1(self)
        )
        owned_profile = snapshot_economic_profile_v1(profile)
        selected = tuple(
            route
            for route in owned_profile.route_registry.routes
            if route.route_release_id == expected_route_release_id
        )
        if len(selected) != 1:
            raise ValueError("economic receipt verifier route is outside the profile")
        release = selected[0]
        if (
            owned_profile.profile_id != authority.profile_root
            or owned_profile.verifier_registry_root != authority.verifier_registry_root
            or owned_profile.root_image_id != authority.root_image_id
            or expected_image_id != release.guest_image_id
        ):
            raise ValueError("economic receipt verifier route image is outside the profile")
        if authority.selection_purpose is EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW:
            if (
                owned_profile.status is not ProfileStatusV1.SHADOW
                or release.status is not ReleaseStatusV1.SHADOW
                or release.accepts_new_objects
            ):
                raise ValueError("economic receipt verifier route is outside shadow status")
        else:
            raise ValueError("production route receipt verification is not implemented")
        self._verify_exact_receipt(
            authority,
            receipt_bytes,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )

    def _verify_exact_receipt(
        self,
        authority: _BoundEconomicReceiptVerifierAuthorityV1,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        if type(receipt_bytes) is not bytes or not (
            1 <= len(receipt_bytes) <= authority.max_receipt_bytes
        ):
            raise ValueError("economic receipt verifier receipt byte length is out of bounds")
        if type(expected_image_id) is not str:
            raise TypeError("economic receipt verifier image id must be exact str")
        _require_root(expected_image_id, name="economic receipt verifier image id")
        if type(expected_journal_bytes) is not bytes or not (
            1 <= len(expected_journal_bytes) <= authority.max_journal_bytes
        ):
            raise ValueError("economic receipt verifier journal byte length is out of bounds")
        baseline = _bound_receipt_verifier_authority_baseline_v1(authority)
        backend = authority.backend
        verify_call = authority.verify_call
        result = verify_call(
            receipt_bytes,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )
        retained = _snapshot_bound_receipt_verifier_authority_v1(
            _bound_receipt_verifier_authority_v1(self)
        )
        if (
            retained.backend is not backend
            or retained.verify_call is not verify_call
            or _bound_receipt_verifier_authority_baseline_v1(retained) != baseline
        ):
            raise ValueError("economic receipt verifier authority changed during verification")
        if result is not None:
            raise ValueError("economic receipt verifier backend violated success contract")


def bind_economic_receipt_verifier_deployment_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    verifier_registry: EconomicReceiptVerifierRegistryV1,
    selection_purpose: EconomicReceiptVerifierSelectionPurposeV1,
    evidence_manifest: EconomicReceiptVerifierEvidenceManifestV1,
    measured_artifact_bytes: bytes,
    deployment_root: str,
    backend: EconomicReceiptVerifierBackendV1,
) -> BoundEconomicReceiptVerifierV1:
    """Construct one measured capability from profile-selected release data."""

    owned_profile = snapshot_economic_profile_v1(profile)
    owned_registry = _snapshot_economic_receipt_verifier_registry_v1(verifier_registry)
    release = select_profile_governed_economic_receipt_verifier_release_v1(
        profile=owned_profile,
        verifier_registry=owned_registry,
        selection_purpose=selection_purpose,
    )
    owned_release = _snapshot_economic_receipt_verifier_release_v1(release)
    owned_manifest = _snapshot_economic_receipt_verifier_manifest_v1(evidence_manifest)
    if owned_manifest.manifest_root != owned_release.evidence_manifest_root:
        raise ValueError("economic receipt verifier evidence manifest root mismatch")
    _require_manifest_release_coordinates_v1(owned_manifest, owned_release)
    if owned_manifest.backend_protocol_root != (
        economic_receipt_verifier_backend_protocol_root_v1()
    ):
        raise ValueError("economic receipt verifier backend protocol root mismatch")
    measured_root = economic_receipt_verifier_implementation_root_v1(measured_artifact_bytes)
    if measured_root != owned_release.implementation_root:
        raise ValueError("economic receipt verifier measured implementation root mismatch")
    if type(deployment_root) is not str:
        raise TypeError("economic receipt verifier deployment root must be exact str")
    _require_root(deployment_root, name="economic receipt verifier deployment root")
    verify_method = getattr(backend, "verify_succinct_receipt", None)
    if not callable(verify_method):
        raise TypeError("economic receipt verifier backend is invalid")
    return BoundEconomicReceiptVerifierV1(
        _BOUND_RECEIPT_VERIFIER_TOKEN_V1,
        _BoundEconomicReceiptVerifierAuthorityV1(
            release_id=owned_release.release_id,
            verifier_registry_root=owned_registry.registry_root,
            verifier_registry=owned_registry,
            deployment_root=deployment_root,
            profile_root=owned_profile.profile_id,
            implementation_root=owned_release.implementation_root,
            evidence_manifest_root=owned_release.evidence_manifest_root,
            backend_protocol_root=owned_release.backend_protocol_root,
            root_image_id=owned_release.root_image_id,
            max_receipt_bytes=owned_release.max_receipt_bytes,
            max_journal_bytes=owned_release.max_journal_bytes,
            selection_purpose=selection_purpose,
            backend=backend,
            verify_call=cast(_EconomicReceiptVerifierCallV1, verify_method),
        ),
    )


def _register_bound_receipt_verifier_authority_v1(
    handle: BoundEconomicReceiptVerifierV1,
    authority: _BoundEconomicReceiptVerifierAuthorityV1,
) -> None:
    owned = _snapshot_bound_receipt_verifier_authority_v1(authority)
    with _BOUND_RECEIPT_VERIFIER_LOCK_V1:
        if handle in _BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1:
            raise TypeError("economic receipt verifier handle is already registered")
        _BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1[handle] = owned


def _bound_receipt_verifier_authority_v1(
    handle: BoundEconomicReceiptVerifierV1,
) -> _BoundEconomicReceiptVerifierAuthorityV1:
    if type(handle) is not BoundEconomicReceiptVerifierV1:
        raise TypeError("economic receipt verifier capability must be exactly typed")
    with _BOUND_RECEIPT_VERIFIER_LOCK_V1:
        authority = _BOUND_RECEIPT_VERIFIER_AUTHORITIES_V1.get(handle)
    if authority is None:
        raise TypeError("economic receipt verifier capability is not registered")
    return authority


def _snapshot_bound_receipt_verifier_authority_v1(
    authority: _BoundEconomicReceiptVerifierAuthorityV1,
) -> _BoundEconomicReceiptVerifierAuthorityV1:
    if type(authority) is not _BoundEconomicReceiptVerifierAuthorityV1:
        raise TypeError("economic receipt verifier authority is not closed")
    owned_registry = _snapshot_economic_receipt_verifier_registry_v1(authority.verifier_registry)
    string_fields = (
        authority.release_id,
        authority.verifier_registry_root,
        authority.deployment_root,
        authority.profile_root,
        authority.implementation_root,
        authority.evidence_manifest_root,
        authority.backend_protocol_root,
        authority.root_image_id,
    )
    if any(type(value) is not str for value in string_fields):
        raise TypeError("economic receipt verifier authority strings must be exact")
    for index, value in enumerate(string_fields):
        _require_root(value, name=f"economic receipt verifier authority root {index}")
    _require_positive_int(
        authority.max_receipt_bytes,
        name="economic receipt verifier authority receipt ceiling",
    )
    _require_positive_int(
        authority.max_journal_bytes,
        name="economic receipt verifier authority journal ceiling",
    )
    if type(authority.selection_purpose) is not EconomicReceiptVerifierSelectionPurposeV1:
        raise TypeError("economic receipt verifier authority purpose is not closed")
    if owned_registry.registry_root != authority.verifier_registry_root:
        raise ValueError("economic receipt verifier authority registry root mismatch")
    selected_release = owned_registry.release_for(authority.selection_purpose)
    if selected_release.release_id != authority.release_id:
        raise ValueError("economic receipt verifier authority release is not selected by registry")
    release_coordinates = (
        (selected_release.implementation_root, authority.implementation_root),
        (selected_release.evidence_manifest_root, authority.evidence_manifest_root),
        (selected_release.backend_protocol_root, authority.backend_protocol_root),
        (selected_release.root_image_id, authority.root_image_id),
        (selected_release.max_receipt_bytes, authority.max_receipt_bytes),
        (selected_release.max_journal_bytes, authority.max_journal_bytes),
    )
    if any(actual != expected for actual, expected in release_coordinates):
        raise ValueError("economic receipt verifier authority release coordinates mismatch")
    if not callable(authority.verify_call):
        raise TypeError("economic receipt verifier authority callable is invalid")
    return _BoundEconomicReceiptVerifierAuthorityV1(
        release_id=authority.release_id,
        verifier_registry_root=authority.verifier_registry_root,
        verifier_registry=owned_registry,
        deployment_root=authority.deployment_root,
        profile_root=authority.profile_root,
        implementation_root=authority.implementation_root,
        evidence_manifest_root=authority.evidence_manifest_root,
        backend_protocol_root=authority.backend_protocol_root,
        root_image_id=authority.root_image_id,
        max_receipt_bytes=authority.max_receipt_bytes,
        max_journal_bytes=authority.max_journal_bytes,
        selection_purpose=authority.selection_purpose,
        backend=authority.backend,
        verify_call=authority.verify_call,
    )


def _bound_receipt_verifier_authority_baseline_v1(
    authority: _BoundEconomicReceiptVerifierAuthorityV1,
) -> tuple[object, ...]:
    return (
        authority.release_id,
        authority.verifier_registry_root,
        authority.deployment_root,
        authority.profile_root,
        authority.implementation_root,
        authority.evidence_manifest_root,
        authority.backend_protocol_root,
        authority.root_image_id,
        authority.max_receipt_bytes,
        authority.max_journal_bytes,
        authority.selection_purpose,
    )


def _bound_receipt_verifier_binding_root_v1(
    authority: _BoundEconomicReceiptVerifierAuthorityV1,
) -> str:
    owned = _snapshot_bound_receipt_verifier_authority_v1(authority)
    return hash_global_v1(
        _DEPLOYMENT_BINDING_ROOT_DOMAIN_V1,
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "release_id": owned.release_id,
            "verifier_registry_root": owned.verifier_registry_root,
            "deployment_root": owned.deployment_root,
            "profile_root": owned.profile_root,
            "implementation_root": owned.implementation_root,
            "evidence_manifest_root": owned.evidence_manifest_root,
            "backend_protocol_root": owned.backend_protocol_root,
            "root_image_id": owned.root_image_id,
            "max_receipt_bytes": owned.max_receipt_bytes,
            "max_journal_bytes": owned.max_journal_bytes,
            "selection_purpose": owned.selection_purpose,
        },
    )


def _snapshot_economic_receipt_verifier_release_v1(
    release: EconomicReceiptVerifierReleaseV1,
) -> EconomicReceiptVerifierReleaseV1:
    if type(release) is not EconomicReceiptVerifierReleaseV1:
        raise TypeError("economic receipt verifier release must be exactly typed")
    return EconomicReceiptVerifierReleaseV1(
        release_id=release.release_id,
        semantic_version=release.semantic_version,
        proof_system=release.proof_system,
        implementation_root=release.implementation_root,
        receipt_schema_root=release.receipt_schema_root,
        journal_schema_root=release.journal_schema_root,
        root_image_id=release.root_image_id,
        specification_root=release.specification_root,
        source_root=release.source_root,
        toolchain_root=release.toolchain_root,
        evidence_manifest_root=release.evidence_manifest_root,
        backend_protocol_root=release.backend_protocol_root,
        max_receipt_bytes=release.max_receipt_bytes,
        max_journal_bytes=release.max_journal_bytes,
        status=release.status,
        accepts_new_receipts=release.accepts_new_receipts,
        evidence_statuses=tuple(release.evidence_statuses),
    )


def _snapshot_economic_receipt_verifier_registry_v1(
    registry: EconomicReceiptVerifierRegistryV1,
) -> EconomicReceiptVerifierRegistryV1:
    if type(registry) is not EconomicReceiptVerifierRegistryV1:
        raise TypeError("economic receipt verifier registry must be exactly typed")
    return EconomicReceiptVerifierRegistryV1(
        tuple(
            _snapshot_economic_receipt_verifier_release_v1(release) for release in registry.releases
        )
    )


__all__ = [
    "BoundEconomicReceiptVerifierV1",
    "EconomicReceiptVerifierBackendV1",
    "EconomicReceiptVerifierEvidenceArtifactV1",
    "EconomicReceiptVerifierEvidenceManifestV1",
    "MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1",
    "bind_economic_receipt_verifier_deployment_v1",
    "economic_receipt_verifier_backend_protocol_root_v1",
    "economic_receipt_verifier_implementation_root_v1",
]
