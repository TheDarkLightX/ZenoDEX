"""Measure a complete profile-selected set of fixed-image verifier executables.

The artifact commitment owns every endpoint's image and ELF bytes. Paths are
local acquisition coordinates and are excluded from that commitment. Each call
remeasures and seals the selected executable. This is isolated research setup;
review provenance, process integrity and deployment mediation remain premises.
The set covers the root and ACTIVE_NEW leaves that accept new objects.
Historical verification and draining require separately qualified selection.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from ..core.economic_receipt_verifier_deployment_v1 import (
    BoundEconomicReceiptVerifierV1,
    bind_economic_receipt_verifier_deployment_v1,
)
from ..core.economic_receipt_verifier_evidence_v1 import (
    MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1,
    EconomicReceiptVerifierEvidenceManifestV1,
)
from ..core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierSelectionPurposeV1,
    select_profile_governed_economic_receipt_verifier_release_v1,
)
from ..core.global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from ..core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneModuleReleaseV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    _require_root,
)
from .global_receipt_verifier_v1 import GlobalReceiptVerifierV1
from .isolated_economic_receipt_verifier_v1 import _acquire_artifact_v1


@dataclass(frozen=True, slots=True)
class IsolatedVerifierArtifactV1:
    """Untrusted acquisition coordinates, never a verification witness."""

    image_id: str
    executable_path: str

    def __post_init__(self) -> None:
        if type(self.image_id) is not str or type(self.executable_path) is not str:
            raise TypeError("verifier artifact coordinates must be exact strings")
        _require_root(self.image_id, name="verifier artifact image")
        if self.image_id == ZERO_ROOT_V1:
            raise ValueError("verifier artifact image must be nonzero")


def _snapshot_artifacts_v1(
    artifacts: tuple[IsolatedVerifierArtifactV1, ...],
) -> tuple[IsolatedVerifierArtifactV1, ...]:
    if type(artifacts) is not tuple:
        raise TypeError("verifier artifacts must be exact typed tuple")
    if not 1 <= len(artifacts) <= 65535:
        raise ValueError("verifier artifact count exceeds private frame limit")
    if any(type(row) is not IsolatedVerifierArtifactV1 for row in artifacts):
        raise TypeError("verifier artifacts must be exact typed tuple")
    owned = tuple(
        IsolatedVerifierArtifactV1(row.image_id, row.executable_path) for row in artifacts
    )
    images = tuple(row.image_id for row in owned)
    if images != tuple(sorted(set(images))):
        raise ValueError("verifier artifact images must be sorted and unique")
    return owned


def _selected_images_v1(profile: EconomicProfileSnapshotV1) -> tuple[str, ...]:
    images = {profile.root_image_id}
    releases: tuple[LaneModuleReleaseV1 | LaneCoordinatorReleaseV1 | RouteReleaseV1, ...] = (
        *profile.lane_registry.releases,
        *profile.lane_coordinator_registry.releases,
        *profile.route_registry.routes,
    )
    images.update(
        row.guest_image_id
        for row in releases
        if row.status is ReleaseStatusV1.ACTIVE_NEW and row.accepts_new_objects
    )
    if ZERO_ROOT_V1 in images:
        raise ValueError("selected verifier image must be nonzero")
    return tuple(sorted(images))


def read_isolated_verifier_artifact_set_v1(
    artifacts: tuple[IsolatedVerifierArtifactV1, ...],
) -> bytes:
    """Read the versioned artifact preimage for review/manifest preparation only.

    Encoding: magic ZDXVSET1, u16le count, then sorted image32, u32le ELF length
    and exact ELF bytes per row. Binding independently reacquires this material.
    """
    owned = _snapshot_artifacts_v1(artifacts)
    encoded = bytearray(b"ZDXVSET1" + len(owned).to_bytes(2, "little"))
    for row in owned:
        raw = _acquire_artifact_v1(row.executable_path)
        if len(encoded) + 36 + len(raw) > MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1:
            raise ValueError("complete verifier artifact exceeds byte limit")
        encoded.extend(bytes.fromhex(row.image_id[2:]))
        encoded.extend(len(raw).to_bytes(4, "little"))
        encoded.extend(raw)
    return bytes(encoded)


@dataclass(frozen=True, slots=True)
class _MeasuredVerifierSetV1:
    endpoints: tuple[GlobalReceiptVerifierV1, ...]

    def verify_succinct_receipt(
        self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
    ) -> None:
        for endpoint in self.endpoints:
            if endpoint.expected_image_id == expected_image_id:
                endpoint.verify_succinct_receipt(
                    receipt_bytes,
                    expected_image_id=expected_image_id,
                    expected_journal_bytes=expected_journal_bytes,
                )
                return
        raise ValueError("receipt image has no measured verifier endpoint")


def bind_isolated_economic_verifier_set_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    verifier_registry: EconomicReceiptVerifierRegistryV1,
    evidence_manifest: EconomicReceiptVerifierEvidenceManifestV1,
    artifacts: tuple[IsolatedVerifierArtifactV1, ...],
    deployment_root: str,
    timeout_ms: int,
) -> BoundEconomicReceiptVerifierV1:
    """Measure the root and every selected ACTIVE_NEW accepting leaf endpoint.

    The public low-level binder still accepts an external backend. This factory
    connects measurement to execution on its own path; complete publication
    mediation remains a separate obligation.
    """
    owned_profile = snapshot_economic_profile_v1(profile)
    purpose = EconomicReceiptVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
    select_profile_governed_economic_receipt_verifier_release_v1(
        profile=owned_profile,
        verifier_registry=verifier_registry,
        selection_purpose=purpose,
    )
    owned = _snapshot_artifacts_v1(artifacts)
    if tuple(row.image_id for row in owned) != _selected_images_v1(owned_profile):
        raise ValueError("verifier artifact set does not exactly cover selected profile images")
    measured = read_isolated_verifier_artifact_set_v1(owned)
    endpoints = []
    offset = 10
    for row in owned:
        size = int.from_bytes(measured[offset + 32 : offset + 36], "little")
        raw = measured[offset + 36 : offset + 36 + size]
        endpoints.append(
            GlobalReceiptVerifierV1(
                row.executable_path, hashlib.sha256(raw).hexdigest(), row.image_id, timeout_ms
            )
        )
        offset += 36 + size
    return bind_economic_receipt_verifier_deployment_v1(
        profile=owned_profile,
        verifier_registry=verifier_registry,
        selection_purpose=purpose,
        evidence_manifest=evidence_manifest,
        measured_artifact_bytes=measured,
        deployment_root=deployment_root,
        backend=_MeasuredVerifierSetV1(tuple(endpoints)),
    )
