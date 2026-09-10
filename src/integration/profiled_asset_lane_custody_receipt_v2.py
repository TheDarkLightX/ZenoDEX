"""Consume a separately selected custody guest role on one owned input snapshot.

The expected binding root and active profile are trusted isolated configuration
premises. This function authenticates and verifies ordinary statement bytes;
it grants no writer, replay, activation or publication authority. Receipt
evidence labels do not qualify the selected build or prove its provenance.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

from ..core.asset_lane_coordinator_v2 import _route_and_owned_command_v2
from ..core.asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from ..core.asset_lane_custody_guest_role_v2 import (
    AssetLaneCustodyGuestRoleBindingV2,
    require_asset_lane_custody_guest_role_binding_v2,
)
from ..core.asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from ..core.asset_lane_custody_statement_v2 import prepare_asset_lane_custody_global_statement_v2
from ..core.asset_lane_state_v2 import AssetLaneContextV2, _snapshot_asset_lane_context_v2
from ..core.economic_command_authentication_types_v2 import (
    EconomicCommandAuthenticationCandidateV2,
    snapshot_command_authentication_candidate_v2,
)
from ..core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    _snapshot_signature_verifier_manifest_v1,
)
from ..core.economic_receipt_verifier_evidence_v1 import (
    EconomicReceiptVerifierEvidenceManifestV1,
    economic_receipt_verifier_implementation_root_v1,
)
from ..core.global_economic_state_v2 import (
    GlobalEconomicStateV2,
    snapshot_global_economic_state_v2,
)
from ..core.global_settlement_primitives_v2 import canonical_economic_command_body_bytes_v2
from .economic_command_authentication_v2 import verify_isolated_economic_command_occurrence_v2
from .global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierRejectV1,
    GlobalReceiptVerifierV1,
)
from .isolated_economic_receipt_verifier_v1 import _acquire_artifact_v1


def verify_isolated_profiled_asset_lane_custody_receipt_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
    context: AssetLaneContextV2,
    pre_state: AssetLaneCustodyStateV2,
    command: AssetLaneCommandV2,
    global_pre: GlobalEconomicStateV2,
    global_post: GlobalEconomicStateV2,
    *,
    guest_role_binding: AssetLaneCustodyGuestRoleBindingV2,
    expected_guest_role_binding_root: str,
    receipt_executable_path: str,
    receipt_timeout_ms: int,
    signature_artifact_path: Path,
    signature_evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    signature_timeout_ms: int,
    receipt_bytes: bytes,
) -> bytes | AssetLaneRejectedV2:
    """Check selection, authenticate, derive the statement, then verify its proof.

    Select the expected binding root independently from trusted configuration.
    Deriving that argument from an untrusted candidate supplies no authority.
    Every caller-owned economic and evidence value is captured before verifier
    I/O. An economic rejection needs no receipt artifact and has no effects.
    """
    owned_candidate = snapshot_command_authentication_candidate_v2(candidate)
    owned_context = _snapshot_asset_lane_context_v2(context)
    _, owned_command = _route_and_owned_command_v2(command)
    owned_pre = snapshot_asset_lane_custody_state_v2(pre_state)
    owned_global_pre = snapshot_global_economic_state_v2(global_pre)
    owned_global_post = snapshot_global_economic_state_v2(global_post)
    owned_signature_manifest = _snapshot_signature_verifier_manifest_v1(signature_evidence_manifest)
    owned_binding = require_asset_lane_custody_guest_role_binding_v2(
        guest_role_binding,
        expected_guest_role_binding_root,
        owned_candidate.profile,
        owned_context,
        owned_global_pre,
    )
    if type(receipt_bytes) is not bytes:
        raise TypeError("profiled custody receipt must be exact bytes")
    if type(receipt_executable_path) is not str:
        raise TypeError("profiled custody receipt executable path must be exact str")
    if type(receipt_timeout_ms) is not int or not 1 <= receipt_timeout_ms <= 60_000:
        raise ValueError("profiled custody receipt timeout must be between 1 and 60000 ms")
    occurrence = owned_context.occurrence
    if occurrence is None:
        raise ValueError("profiled custody receipt requires an occurrence")
    if owned_candidate.envelope.command_body_bytes != canonical_economic_command_body_bytes_v2(
        owned_command.command_kind, owned_command
    ):
        raise ValueError("authenticated command body does not match the custody command")
    verify_isolated_economic_command_occurrence_v2(
        owned_candidate,
        occurrence,
        signature_artifact_path=signature_artifact_path,
        signature_evidence_manifest=owned_signature_manifest,
        signature_timeout_ms=signature_timeout_ms,
    )
    statement = prepare_asset_lane_custody_global_statement_v2(
        owned_context, owned_pre, owned_command, owned_global_pre, owned_global_post
    )
    if type(statement) is AssetLaneRejectedV2:
        return statement
    if type(statement) is not bytes:
        raise TypeError("profiled custody producer returned an unsupported value")
    _verify_selected_custody_statement_v2(
        statement,
        receipt_bytes,
        owned_binding.evidence_manifest,
        receipt_executable_path,
        receipt_timeout_ms,
    )
    return statement


def _verify_selected_custody_statement_v2(
    statement: bytes,
    receipt_bytes: bytes,
    manifest: EconomicReceiptVerifierEvidenceManifestV1,
    receipt_executable_path: str,
    receipt_timeout_ms: int,
) -> None:
    """Measure and invoke the selected endpoint after exact statement preparation."""
    if not 1 <= len(receipt_bytes) <= manifest.max_receipt_bytes or not (
        1 <= len(statement) <= manifest.max_journal_bytes
    ):
        raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.INPUT_BOUNDS)
    artifact = _acquire_artifact_v1(receipt_executable_path)
    if economic_receipt_verifier_implementation_root_v1(artifact) != manifest.implementation_root:
        raise GlobalReceiptVerifierErrorV1(GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING)
    verifier = GlobalReceiptVerifierV1(
        receipt_executable_path,
        hashlib.sha256(artifact).hexdigest(),
        manifest.root_image_id,
        receipt_timeout_ms,
    )
    verifier.verify_succinct_receipt(
        receipt_bytes,
        expected_image_id=manifest.root_image_id,
        expected_journal_bytes=statement,
    )


__all__ = ["verify_isolated_profiled_asset_lane_custody_receipt_v2"]
