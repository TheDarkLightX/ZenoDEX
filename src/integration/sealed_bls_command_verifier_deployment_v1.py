"""Release binder for one acquired standalone BLS verifier snapshot.

The shell reads one regular artifact once, constructs the sealed process
backend from those owned bytes, and gives the same bytes object to the
deterministic release binder. The resulting capability is process local and
inherits the Python interpreter, OS, dynamic loader, and system-library TCB.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

from src.core.economic_command_signature_verifier_capability_v1 import (
    BoundEconomicCommandSignatureVerifierV1,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    bind_bls_command_signature_verifier_deployment_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierReleaseV1,
    EconomicCommandSignatureVerifierSelectionPurposeV1,
)

from .economic_command_signature_verifier_deployment_v1 import (
    _read_regular_artifact_bytes_v1,
)
from .sealed_bls_command_verifier_v1 import SealedBlsCommandVerifierV1


def bind_deployed_sealed_bls_command_verifier_v1(
    *,
    artifact_path: Path,
    release: EconomicCommandSignatureVerifierReleaseV1,
    evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    deployment_root: str,
    profile_root: str,
    timeout_ms: int,
    selection_purpose: EconomicCommandSignatureVerifierSelectionPurposeV1 = EconomicCommandSignatureVerifierSelectionPurposeV1.PRODUCTION_NEW,
) -> BoundEconomicCommandSignatureVerifierV1:
    """Acquire once and bind execution and release admission to the same bytes."""

    artifact_bytes = _read_regular_artifact_bytes_v1(artifact_path)
    backend = SealedBlsCommandVerifierV1(
        executable_bytes=artifact_bytes,
        executable_sha256=hashlib.sha256(artifact_bytes).hexdigest(),
        timeout_ms=timeout_ms,
    )
    return bind_bls_command_signature_verifier_deployment_v1(
        release=release,
        evidence_manifest=evidence_manifest,
        measured_artifact_bytes=artifact_bytes,
        deployment_root=deployment_root,
        profile_root=profile_root,
        backend=backend,
        selection_purpose=selection_purpose,
    )


__all__ = ["bind_deployed_sealed_bls_command_verifier_v1"]
