"""Pure isolated qualification binding for the V2 perps margin guest.

The binding selects the profile-governed perps route and its receipt evidence.
It does not authenticate a command, verify a receipt, authorize a state write,
or qualify a source or guest build for production.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .asset_lane_custody_profile_binding_v2 import (
    _require_global_predecessor_binding_v2,
)
from .asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from .economic_receipt_verifier_evidence_v1 import (
    EconomicReceiptVerifierEvidenceManifestV1,
    _snapshot_economic_receipt_verifier_manifest_v1,
    economic_receipt_verifier_backend_protocol_root_v1,
)
from .economic_receipt_verifier_registry_v1 import (
    REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v2 import _snapshot_occurrence_v2
from .global_economic_state_v2 import (
    GlobalEconomicStateV2,
    snapshot_global_economic_state_v2,
)
from .global_settlement_primitives_v2 import (
    _require_nonnegative_int_v2,
    _require_root_v2,
    hash_economic_command_body_v2,
    hash_global_v2,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ProfileStatusV1,
)
from .global_settlement_types_v2 import GLOBAL_SETTLEMENT_ABI_V2
from .perps_margin_state_v2 import PerpsMarginStateV2
from .perps_margin_types_v1 import (
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
)
from .perps_margin_wire_v2 import PerpsMarginRequestV2

PERPS_MARGIN_GLOBAL_V2: Final = "PERPS_MARGIN_GLOBAL_V2"
PERPS_MARGIN_GUEST_ROLE_PURPOSE_V2: Final = "ISOLATED_QUALIFICATION"
PERPS_MARGIN_GUEST_ROLE_BINDING_DOMAIN_V2: Final = (
    "perps-margin-global-guest-role-binding-v2"
)

# These descriptors are the normative V2 coordinates for the selected guest.
# Keep their fields and values in sync with the published successor contract;
# the roots below are deliberately derived rather than copied literals.
PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_DESCRIPTOR_V2: Final = {
    "schema": "zenodex/perps-margin-global-statement/v2",
    "fields": ("input_root", "refinement_root"),
}
PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2: Final = hash_global_v2(
    "perps-margin-global-journal-schema-v2",
    PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_DESCRIPTOR_V2,
)
PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_DESCRIPTOR_V2: Final = {
    "schema": "zenodex/perps-margin-global-receipt/v2",
    "proof_system": "risc0-succinct",
    "journal_schema_root": PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2,
}
PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_ROOT_V2: Final = hash_global_v2(
    "perps-margin-global-receipt-schema-v2",
    PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_DESCRIPTOR_V2,
)
PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_DESCRIPTOR_V2: Final = {
    "journal_schema_root": PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2,
    "receipt_schema_root": PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_ROOT_V2,
    "schema": "zenodex/perps-margin-global-qualification/v2",
    "abi": GLOBAL_SETTLEMENT_ABI_V2,
    "market_scope": "single-market",
    "publication_oracle": "absent",
}
PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_ROOT_V2: Final = hash_global_v2(
    "perps-margin-global-guest-specification-v2",
    PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_DESCRIPTOR_V2,
)

_SUPPORTED_MARGIN_COMMAND_KINDS_V2: Final = frozenset(
    {
        PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
        PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
    }
)
_PERPS_ROUTE_LANES_V2: Final = (LaneIdV1.ASSET_TRANSFER, LaneIdV1.PERPS_MARKET)


@dataclass(frozen=True, slots=True)
class PerpsMarginGuestRoleBindingV2:
    """Owned coordinates for isolated perps margin guest qualification."""

    profile_root: str
    authority_epoch: int
    evidence_manifest: EconomicReceiptVerifierEvidenceManifestV1

    def __post_init__(self) -> None:
        _require_root_v2(self.profile_root, name="perps margin guest profile root")
        _require_nonnegative_int_v2(
            self.authority_epoch,
            name="perps margin guest authority epoch",
        )
        if type(self.evidence_manifest) is not EconomicReceiptVerifierEvidenceManifestV1:
            raise TypeError("perps margin guest evidence manifest must be exactly typed")
        object.__setattr__(
            self,
            "evidence_manifest",
            _snapshot_economic_receipt_verifier_manifest_v1(self.evidence_manifest),
        )
        _require_manifest_coordinates_v2(self.evidence_manifest)

    @property
    def binding_root(self) -> str:
        owned = snapshot_perps_margin_guest_role_binding_v2(self)
        return hash_global_v2(
            PERPS_MARGIN_GUEST_ROLE_BINDING_DOMAIN_V2,
            owned.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V2,
            "role": PERPS_MARGIN_GLOBAL_V2,
            "purpose": PERPS_MARGIN_GUEST_ROLE_PURPOSE_V2,
            "profile_root": self.profile_root,
            "authority_epoch": self.authority_epoch,
            "evidence_manifest": self.evidence_manifest,
        }


def _require_manifest_coordinates_v2(
    manifest: EconomicReceiptVerifierEvidenceManifestV1,
) -> None:
    if manifest.proof_system != "risc0-succinct":
        raise ValueError("perps margin guest evidence proof system mismatch")
    coordinates = (
        (
            manifest.receipt_schema_root,
            PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_ROOT_V2,
            "receipt schema",
        ),
        (
            manifest.journal_schema_root,
            PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2,
            "journal schema",
        ),
        (
            manifest.specification_root,
            PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_ROOT_V2,
            "specification",
        ),
        (
            manifest.backend_protocol_root,
            economic_receipt_verifier_backend_protocol_root_v1(),
            "backend protocol",
        ),
    )
    for actual, expected, name in coordinates:
        if actual != expected:
            raise ValueError(f"perps margin guest evidence {name} root mismatch")
    statuses = {row.status for row in manifest.evidence_artifacts}
    if not REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1 <= statuses:
        raise ValueError("perps margin guest evidence lacks required shadow statuses")


def require_perps_margin_guest_role_binding_v2(
    binding: PerpsMarginGuestRoleBindingV2,
    expected_binding_root: str,
    profile: EconomicProfileSnapshotV1,
    assets: AssetLaneCustodyStateV2,
    margin: PerpsMarginStateV2,
    global_pre: GlobalEconomicStateV2,
    request: PerpsMarginRequestV2,
) -> PerpsMarginGuestRoleBindingV2:
    """Return owned role data when all route and predecessor coordinates agree."""

    _require_root_v2(
        expected_binding_root,
        name="expected perps margin guest binding root",
    )
    if type(request) is not PerpsMarginRequestV2:
        raise TypeError("perps margin guest request must be exact")
    owned_binding = snapshot_perps_margin_guest_role_binding_v2(binding)
    owned_profile = snapshot_economic_profile_v1(profile)
    owned_assets = snapshot_asset_lane_custody_state_v2(assets)
    if type(margin) is not PerpsMarginStateV2:
        raise TypeError("perps margin guest margin must be exact")
    owned_margin = PerpsMarginStateV2(margin.economic_state, margin.active_claims)
    owned_global_pre = snapshot_global_economic_state_v2(global_pre)
    owned_request = PerpsMarginRequestV2(
        request.command,
        request.occurrence,
        request.oracle,
    )

    if owned_binding.binding_root != expected_binding_root:
        raise ValueError("perps margin guest binding root mismatch")
    if owned_binding.profile_root != owned_profile.profile_id:
        raise ValueError("perps margin guest profile root mismatch")
    if owned_binding.authority_epoch != owned_profile.authority_epoch:
        raise ValueError("perps margin guest authority epoch mismatch")
    if owned_profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("perps margin guest requires an ACTIVE profile")

    # This is the common predecessor check used by the existing custody role;
    # it verifies every ABI V2 lane root against the selected profile release.
    _require_global_predecessor_binding_v2(owned_global_pre, owned_profile)

    if owned_request.oracle is not None:
        raise ValueError("perps margin guest does not accept an oracle candidate")
    command = owned_request.command
    occurrence = _snapshot_occurrence_v2(owned_request.occurrence)
    if command.command_kind not in _SUPPORTED_MARGIN_COMMAND_KINDS_V2:
        raise ValueError("perps margin guest command kind is unsupported")
    if occurrence.command_kind != command.command_kind:
        raise ValueError("perps margin guest occurrence command kind mismatch")
    if occurrence.command_body_hash != hash_economic_command_body_v2(
        command.command_kind,
        command,
    ):
        raise ValueError("perps margin guest occurrence command body mismatch")
    if occurrence.consumed_object_ids:
        raise ValueError("perps margin guest occurrence consumes unsupported objects")
    if (
        occurrence.chain_id,
        occurrence.deployment_root,
        occurrence.profile_root,
        occurrence.pre_state_root,
        occurrence.height,
    ) != (
        owned_global_pre.chain_id,
        owned_global_pre.deployment_root,
        owned_global_pre.profile_root,
        owned_global_pre.state_root,
        owned_global_pre.height + 1,
    ):
        raise ValueError("perps margin guest occurrence predecessor context mismatch")
    if occurrence.subject_id != command.owner:
        raise ValueError("perps margin guest occurrence subject mismatch")
    if command.market_id != owned_margin.economic_state.market_id:
        raise ValueError("perps margin guest market mismatch")
    if command.asset != owned_margin.economic_state.collateral_asset:
        raise ValueError("perps margin guest collateral asset mismatch")

    route = owned_profile.route_registry.route_for_command(
        command.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if route.ordered_lanes != _PERPS_ROUTE_LANES_V2:
        raise ValueError("perps margin guest route lane name mismatch")
    asset_release = owned_profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    margin_release = owned_profile.lane_registry.release_for(LaneIdV1.PERPS_MARKET)
    expected_releases = (asset_release.release_id, margin_release.release_id)
    if route.module_release_ids != expected_releases:
        raise ValueError("perps margin guest route release coordinates mismatch")
    if owned_assets.transfer_state.module_release_id != asset_release.release_id:
        raise ValueError("perps margin guest asset release mismatch")
    if owned_margin.economic_state.module_release_id != margin_release.release_id:
        raise ValueError("perps margin guest margin release mismatch")

    return owned_binding


def snapshot_perps_margin_guest_role_binding_v2(
    binding: PerpsMarginGuestRoleBindingV2,
) -> PerpsMarginGuestRoleBindingV2:
    """Defensively copy a role binding and all manifest artifact rows."""

    if type(binding) is not PerpsMarginGuestRoleBindingV2:
        raise TypeError("perps margin guest role binding must be exactly typed")
    return PerpsMarginGuestRoleBindingV2(
        profile_root=binding.profile_root,
        authority_epoch=binding.authority_epoch,
        evidence_manifest=binding.evidence_manifest,
    )


__all__ = [
    "PERPS_MARGIN_GLOBAL_V2",
    "PERPS_MARGIN_GUEST_ROLE_PURPOSE_V2",
    "PERPS_MARGIN_GUEST_ROLE_BINDING_DOMAIN_V2",
    "PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_DESCRIPTOR_V2",
    "PERPS_MARGIN_GLOBAL_JOURNAL_SCHEMA_ROOT_V2",
    "PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_DESCRIPTOR_V2",
    "PERPS_MARGIN_GLOBAL_RECEIPT_SCHEMA_ROOT_V2",
    "PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_DESCRIPTOR_V2",
    "PERPS_MARGIN_GLOBAL_GUEST_SPECIFICATION_ROOT_V2",
    "PerpsMarginGuestRoleBindingV2",
    "snapshot_perps_margin_guest_role_binding_v2",
    "require_perps_margin_guest_role_binding_v2",
]
