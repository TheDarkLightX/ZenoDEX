"""Consume one selected perps-margin guest on an immutable V2 input snapshot.

The adapter authenticates the signed command occurrence, asks the pure margin
successor for its exact statement, and sends that statement to the selected
sealed receipt endpoint.  The endpoint result remains qualification evidence;
this function grants no publication, settlement, or production authority.
"""

from __future__ import annotations

from pathlib import Path

from ..core.asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from ..core.economic_command_authentication_types_v2 import (
    EconomicCommandAuthenticationCandidateV2,
    snapshot_command_authentication_candidate_v2,
)
from ..core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1,
    _snapshot_signature_verifier_manifest_v1,
)
from ..core.global_economic_state_v2 import (
    GlobalEconomicStateV2,
    snapshot_global_economic_state_v2,
)
from ..core.global_settlement_primitives_v2 import canonical_economic_command_body_bytes_v2
from ..core.perps_margin_global_v2 import PerpsMarginGlobalRejectedV2
from ..core.perps_margin_guest_role_v2 import (
    PerpsMarginGuestRoleBindingV2,
    require_perps_margin_guest_role_binding_v2,
)
from ..core.perps_margin_receipt_v2 import prepare_perps_margin_statement_v2
from ..core.perps_margin_state_v2 import PerpsMarginStateV2
from ..core.perps_margin_wire_v2 import PerpsMarginRequestV2
from .economic_command_authentication_v2 import verify_isolated_economic_command_occurrence_v2
from .profiled_asset_lane_custody_receipt_v2 import _verify_selected_custody_statement_v2


def verify_isolated_profiled_perps_margin_receipt_v2(
    candidate: EconomicCommandAuthenticationCandidateV2,
    assets: AssetLaneCustodyStateV2,
    margin: PerpsMarginStateV2,
    global_pre: GlobalEconomicStateV2,
    request: PerpsMarginRequestV2,
    *,
    guest_role_binding: PerpsMarginGuestRoleBindingV2,
    expected_guest_role_binding_root: str,
    receipt_executable_path: str,
    receipt_timeout_ms: int,
    signature_artifact_path: Path,
    signature_evidence_manifest: EconomicCommandSignatureVerifierEvidenceManifestV1,
    signature_timeout_ms: int,
    receipt_bytes: bytes,
) -> bytes | PerpsMarginGlobalRejectedV2:
    """Authenticate, prepare, and verify one isolated perps statement.

    All caller-owned values are copied before command-signature or receipt
    verifier I/O.  Economic rejection is returned immediately and therefore
    never causes receipt-artifact acquisition.
    """

    owned_candidate = snapshot_command_authentication_candidate_v2(candidate)
    owned_assets = snapshot_asset_lane_custody_state_v2(assets)
    if type(margin) is not PerpsMarginStateV2:
        raise TypeError("profiled perps margin must be exact")
    owned_margin = PerpsMarginStateV2(margin.economic_state, margin.active_claims)
    owned_global_pre = snapshot_global_economic_state_v2(global_pre)
    if type(request) is not PerpsMarginRequestV2:
        raise TypeError("profiled perps margin request must be exact")
    owned_request = PerpsMarginRequestV2(
        request.command,
        request.occurrence,
        request.oracle,
    )
    owned_signature_manifest = _snapshot_signature_verifier_manifest_v1(
        signature_evidence_manifest
    )
    owned_binding = require_perps_margin_guest_role_binding_v2(
        guest_role_binding,
        expected_guest_role_binding_root,
        owned_candidate.profile,
        owned_assets,
        owned_margin,
        owned_global_pre,
        owned_request,
    )

    if type(receipt_bytes) is not bytes:
        raise TypeError("profiled perps margin receipt must be exact bytes")
    if type(receipt_executable_path) is not str:
        raise TypeError("profiled perps margin receipt executable path must be exact str")
    if type(receipt_timeout_ms) is not int or not 1 <= receipt_timeout_ms <= 60_000:
        raise ValueError("profiled perps margin receipt timeout must be between 1 and 60000 ms")
    occurrence = owned_request.occurrence
    if owned_candidate.envelope.command_body_bytes != canonical_economic_command_body_bytes_v2(
        owned_request.command.command_kind,
        owned_request.command,
    ):
        raise ValueError("authenticated command body does not match the margin command")

    verify_isolated_economic_command_occurrence_v2(
        owned_candidate,
        occurrence,
        signature_artifact_path=signature_artifact_path,
        signature_evidence_manifest=owned_signature_manifest,
        signature_timeout_ms=signature_timeout_ms,
    )
    statement = prepare_perps_margin_statement_v2(
        owned_assets,
        owned_margin,
        owned_global_pre,
        owned_request,
    )
    if type(statement) is PerpsMarginGlobalRejectedV2:
        return statement
    if type(statement) is not bytes:
        raise TypeError("profiled perps margin producer returned an unsupported value")
    _verify_selected_custody_statement_v2(
        statement,
        receipt_bytes,
        owned_binding.evidence_manifest,
        receipt_executable_path,
        receipt_timeout_ms,
    )
    return statement


__all__ = ["verify_isolated_profiled_perps_margin_receipt_v2"]
