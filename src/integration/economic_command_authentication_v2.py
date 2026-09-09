"""Check a V2 signed intent using one internally acquired sealed BLS verifier.

The supplied profile, activation status and release selection are deployment
premises. This isolated check creates no reusable authentication handle and
consumes no replay state. A later protected operation must check its own exact
inputs; a successful call does not authorize later use of mutable originals.
"""

from __future__ import annotations

from pathlib import Path

from ..core.economic_command_authentication_types_v2 import EconomicCommandAuthenticationCandidateV2
from ..core.economic_command_authentication_v2 import (
    prepare_isolated_economic_command_authentication_v2,
    require_economic_command_intent_occurrence_v2,
)
from ..core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
)
from ..core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierSelectionPurposeV1,
)
from ..core.global_economic_proof_v2 import EconomicCommandOccurrenceV2, _snapshot_occurrence_v2
from .sealed_bls_command_verifier_deployment_v1 import bind_deployed_sealed_bls_command_verifier_v1


def verify_isolated_economic_command_occurrence_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
    occurrence: EconomicCommandOccurrenceV2,
    *,
    signature_artifact_path: Path,
    signature_evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    signature_timeout_ms: int,
) -> None:
    """Verify the signed fields and validity of the owned occurrence snapshot.

    Core failures precede artifact access. Verification errors propagate, and
    only exact cryptographic success returns normally. Sequencer indices and
    predecessor remain unsigned and need separate admission checks.
    """
    owned_occurrence = _snapshot_occurrence_v2(occurrence)
    owned, release, message = prepare_isolated_economic_command_authentication_v2(candidate)
    require_economic_command_intent_occurrence_v2(owned.intent, owned_occurrence)
    purpose = EconomicCommandSignatureVerifierSelectionPurposeV1.ISOLATED_QUALIFICATION
    verifier = bind_deployed_sealed_bls_command_verifier_v1(
        artifact_path=signature_artifact_path,
        release=release,
        evidence_manifest=signature_evidence_manifest,
        deployment_root=owned.intent.deployment_root,
        profile_root=owned.intent.profile_root,
        timeout_ms=signature_timeout_ms,
        selection_purpose=purpose,
    )
    verifier.require_binding(
        release_id=release.release_id,
        deployment_root=owned.intent.deployment_root,
        profile_root=owned.intent.profile_root,
        selection_purpose=purpose,
    )
    verified = verifier.verify_command_signature(
        signature_algorithm=owned.envelope.signature_algorithm,
        signer_public_key=owned.envelope.signer_public_key,
        message_bytes=message,
        signature_bytes=owned.envelope.signature_bytes,
    )
    if verified is not True:
        raise ValueError("command authentication signature rejected")


__all__ = ["verify_isolated_economic_command_occurrence_v2"]
