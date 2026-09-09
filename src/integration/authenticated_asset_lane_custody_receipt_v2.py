"""Authenticate a V2 command before conditionally verifying its custody statement.

This adapter returns only existing statement bytes or a typed custody rejection.
It creates no replay record, store write, authorization witness, or publication
authority.  The selected verifier configuration and external binaries remain
trusted premises.
"""

from __future__ import annotations

from pathlib import Path

from ..core.asset_lane_coordinator_v2 import _route_and_owned_command_v2
from ..core.asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from ..core.asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from ..core.asset_lane_state_v2 import AssetLaneContextV2, _snapshot_asset_lane_context_v2
from ..core.economic_command_authentication_types_v2 import (
    EconomicCommandAuthenticationCandidateV2,
    snapshot_command_authentication_candidate_v2,
)
from ..core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
)
from ..core.global_economic_state_v2 import (
    GlobalEconomicStateV2,
    snapshot_global_economic_state_v2,
)
from ..core.global_settlement_primitives_v2 import canonical_economic_command_body_bytes_v2
from .asset_lane_custody_receipt_verification_v2 import (
    verify_asset_lane_custody_global_receipt_v2,
)
from .economic_command_authentication_v2 import (
    verify_isolated_economic_command_occurrence_v2,
)
from .global_receipt_verifier_v1 import GlobalReceiptVerifierV1


def verify_isolated_authenticated_asset_lane_custody_receipt_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
    context: AssetLaneContextV2,
    pre_state: AssetLaneCustodyStateV2,
    command: AssetLaneCommandV2,
    global_pre: GlobalEconomicStateV2,
    global_post: GlobalEconomicStateV2,
    *,
    signature_artifact_path: Path,
    signature_evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    signature_timeout_ms: int,
    receipt_bytes: bytes,
    receipt_verifier: GlobalReceiptVerifierV1,
) -> bytes | AssetLaneRejectedV2:
    """Authenticate one owned command, then verify its exact custody statement.

    Structural snapshot errors precede authentication, and signature failure
    precedes economic execution. Authenticated leaf rejection returns unchanged
    without receipt verification. Full profile and current-store admission are
    separate requirements; a successful return grants no authority.
    """

    owned_candidate = snapshot_command_authentication_candidate_v2(candidate)
    owned_context = _snapshot_asset_lane_context_v2(context)
    _, owned_command = _route_and_owned_command_v2(command)
    owned_pre_state = snapshot_asset_lane_custody_state_v2(pre_state)
    owned_global_pre = snapshot_global_economic_state_v2(global_pre)
    owned_global_post = snapshot_global_economic_state_v2(global_post)
    if type(receipt_bytes) is not bytes:
        raise TypeError("authenticated custody receipt must be exact bytes")
    if type(receipt_verifier) is not GlobalReceiptVerifierV1:
        raise TypeError("authenticated custody receipt requires an exact V1 verifier")
    owned_receipt_verifier = GlobalReceiptVerifierV1(
        receipt_verifier.executable_path,
        receipt_verifier.executable_sha256,
        receipt_verifier.expected_image_id,
        receipt_verifier.timeout_ms,
    )
    occurrence = owned_context.occurrence
    if occurrence is None:
        raise ValueError("authenticated custody receipt requires an occurrence")
    if owned_candidate.envelope.command_body_bytes != canonical_economic_command_body_bytes_v2(
        owned_command.command_kind,
        owned_command,
    ):
        raise ValueError("authenticated command body does not match the custody command")
    verify_isolated_economic_command_occurrence_v2(
        owned_candidate,
        occurrence,
        signature_artifact_path=signature_artifact_path,
        signature_evidence_manifest=signature_evidence_manifest,
        signature_timeout_ms=signature_timeout_ms,
    )
    return verify_asset_lane_custody_global_receipt_v2(
        owned_context,
        owned_pre_state,
        owned_command,
        owned_global_pre,
        owned_global_post,
        receipt_bytes=receipt_bytes,
        verifier=owned_receipt_verifier,
    )


__all__ = ["verify_isolated_authenticated_asset_lane_custody_receipt_v2"]
