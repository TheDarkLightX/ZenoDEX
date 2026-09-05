"""Construct a research root verifier from the very artifact that it measures.

This shell owns read-only artifact acquisition and backend construction. The
core validates profile, release and evidence bindings. A purpose label does not
establish physical store isolation, reviewed evidence provenance, or production
authority. The caller must supply the explicitly selected isolated deployment.
"""

from __future__ import annotations

import hashlib
import os
import stat

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
from ..core.global_settlement_types_v1 import EconomicProfileSnapshotV1
from .global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierRejectV1,
    GlobalReceiptVerifierV1,
)


def _acquire_artifact_v1(path: str) -> bytes:
    if type(path) is not str or not os.path.isabs(path) or "\x00" in path:
        raise ValueError("isolated verifier requires an absolute executable path")
    descriptor = None
    limit = MAX_ECONOMIC_RECEIPT_VERIFIER_ARTIFACT_BYTES_V1
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode) or not 1 <= metadata.st_size <= limit:
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
        chunks: list[bytes] = []
        count = 0
        while chunk := os.read(descriptor, min(65536, limit + 1 - count)):
            count += len(chunk)
            if count > limit:
                raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
            chunks.append(chunk)
        raw = b"".join(chunks)
        if count != metadata.st_size or not raw.startswith(b"\x7fELF"):
            raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
        return raw
    except OSError:
        raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_UNAVAILABLE) from None
    finally:
        if descriptor is not None:
            os.close(descriptor)


def bind_isolated_economic_root_verifier_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    verifier_registry: EconomicReceiptVerifierRegistryV1,
    evidence_manifest: EconomicReceiptVerifierEvidenceManifestV1,
    executable_path: str,
    deployment_root: str,
    timeout_ms: int,
) -> BoundEconomicReceiptVerifierV1:
    """Bind one selected root image; there is no caller backend or measured-byte port.

    Every later verification remeasures and seals the executable against this
    snapshot's digest, so replacement after binding fails closed. Module,
    coordinator and route images require their own measured endpoint selection.
    This function does not certify the supplied release-evidence provenance.
    """
    owned_profile = snapshot_economic_profile_v1(profile)
    purpose = EconomicReceiptVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
    release = select_profile_governed_economic_receipt_verifier_release_v1(
        profile=owned_profile, verifier_registry=verifier_registry, selection_purpose=purpose,
    )
    raw = _acquire_artifact_v1(executable_path)
    backend = GlobalReceiptVerifierV1(
        executable_path=executable_path,
        executable_sha256=hashlib.sha256(raw).hexdigest(),
        expected_image_id=release.root_image_id,
        timeout_ms=timeout_ms,
    )
    return bind_economic_receipt_verifier_deployment_v1(
        profile=owned_profile, verifier_registry=verifier_registry,
        selection_purpose=purpose, evidence_manifest=evidence_manifest,
        measured_artifact_bytes=raw, deployment_root=deployment_root, backend=backend,
    )
