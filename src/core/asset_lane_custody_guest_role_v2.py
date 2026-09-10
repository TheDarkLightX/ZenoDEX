"""Pure, isolated qualification binding for the V2 custody guest role.

This value binds only coordinates needed to select the custody guest.  It does
not verify a receipt, activate a profile, or authorize publication.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .asset_lane_custody_profile_binding_v2 import (
    require_asset_lane_custody_profile_binding_v2,
)
from .asset_lane_state_v2 import (
    AssetLaneContextV2,
    _snapshot_asset_lane_context_v2,
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
from .global_economic_state_v2 import (
    GlobalEconomicStateV2,
    snapshot_global_economic_state_v2,
)
from .global_settlement_primitives_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    _require_nonnegative_int_v2,
    _require_root_v2,
    hash_global_v2,
)
from .global_settlement_types_v1 import EconomicProfileSnapshotV1

ASSET_LANE_CUSTODY_GLOBAL_V2: Final = "ASSET_LANE_CUSTODY_GLOBAL_V2"
ASSET_LANE_CUSTODY_GUEST_ROLE_PURPOSE_V2: Final = "ISOLATED_QUALIFICATION"
ASSET_LANE_CUSTODY_GUEST_ROLE_BINDING_DOMAIN_V2: Final = "asset-lane-custody-guest-role-binding-v2"

# These roots are source-bound coordinates from the normative role document.
ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2: Final = (
    "0x8c2cf1df8a3e4609753d679390a5b883b66a910caff2458047a06752a0034247"
)
ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2: Final = (
    "0x95bff77b384f00ed82be3b7219b80b4256548f04e3bd18afd7998659a4cbc392"
)
ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2: Final = (
    "0x4a9560fc265f7020bd059b116eb8a5f6b3718b2f91257471d49571cf5a63e825"
)
ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2: Final = (
    "0xe70a07652d48ab3b2d9a5dc2d578a6744dc81fb0bc877de898155c8d518c3f4e"
)


@dataclass(frozen=True, slots=True)
class AssetLaneCustodyGuestRoleBindingV2:
    """Owned coordinates for isolated custody guest qualification."""

    profile_root: str
    authority_epoch: int
    state_schema_root: str
    evidence_manifest: EconomicReceiptVerifierEvidenceManifestV1

    def __post_init__(self) -> None:
        _require_root_v2(self.profile_root, name="custody guest profile root")
        _require_nonnegative_int_v2(
            self.authority_epoch,
            name="custody guest authority epoch",
        )
        _require_root_v2(
            self.state_schema_root,
            name="custody guest state schema root",
        )
        if self.state_schema_root != ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2:
            raise ValueError("custody guest state schema root mismatch")
        if type(self.evidence_manifest) is not EconomicReceiptVerifierEvidenceManifestV1:
            raise TypeError("custody guest evidence manifest must be exactly typed")
        object.__setattr__(
            self,
            "evidence_manifest",
            _snapshot_economic_receipt_verifier_manifest_v1(self.evidence_manifest),
        )
        _require_manifest_coordinates_v2(self.evidence_manifest)

    @property
    def binding_root(self) -> str:
        owned = snapshot_asset_lane_custody_guest_role_binding_v2(self)
        return hash_global_v2(
            ASSET_LANE_CUSTODY_GUEST_ROLE_BINDING_DOMAIN_V2,
            owned.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V2,
            "role": ASSET_LANE_CUSTODY_GLOBAL_V2,
            "purpose": ASSET_LANE_CUSTODY_GUEST_ROLE_PURPOSE_V2,
            "profile_root": self.profile_root,
            "authority_epoch": self.authority_epoch,
            "state_schema_root": self.state_schema_root,
            "evidence_manifest": self.evidence_manifest,
        }


def _require_manifest_coordinates_v2(
    manifest: EconomicReceiptVerifierEvidenceManifestV1,
) -> None:
    if manifest.proof_system != "risc0-succinct":
        raise ValueError("custody guest evidence proof system mismatch")
    coordinates = (
        (manifest.receipt_schema_root, ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2, "receipt schema"),
        (manifest.journal_schema_root, ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2, "journal schema"),
        (
            manifest.specification_root,
            ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2,
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
            raise ValueError(f"custody guest evidence {name} root mismatch")
    statuses = {row.status for row in manifest.evidence_artifacts}
    if not REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1 <= statuses:
        raise ValueError("custody guest evidence lacks required shadow statuses")


def require_asset_lane_custody_guest_role_binding_v2(
    binding: AssetLaneCustodyGuestRoleBindingV2,
    expected_binding_root: str,
    profile: EconomicProfileSnapshotV1,
    context: AssetLaneContextV2,
    global_pre: GlobalEconomicStateV2,
) -> AssetLaneCustodyGuestRoleBindingV2:
    """Return owned role data when all independent selection coordinates agree."""

    _require_root_v2(expected_binding_root, name="expected custody guest binding root")
    owned_binding = snapshot_asset_lane_custody_guest_role_binding_v2(binding)
    owned_profile = snapshot_economic_profile_v1(profile)
    owned_context = _snapshot_asset_lane_context_v2(context)
    owned_global_pre = snapshot_global_economic_state_v2(global_pre)

    if (
        hash_global_v2(
            ASSET_LANE_CUSTODY_GUEST_ROLE_BINDING_DOMAIN_V2, owned_binding.to_canonical()
        )
        != expected_binding_root
    ):
        raise ValueError("custody guest binding root mismatch")
    if owned_binding.profile_root != owned_profile.profile_id:
        raise ValueError("custody guest profile root mismatch")
    if owned_binding.authority_epoch != owned_profile.authority_epoch:
        raise ValueError("custody guest authority epoch mismatch")

    require_asset_lane_custody_profile_binding_v2(
        owned_profile,
        owned_context,
        owned_global_pre,
    )
    if owned_context.global_pre_state_root != owned_global_pre.state_root:
        raise ValueError("custody guest context predecessor state root mismatch")
    occurrence = owned_context.occurrence
    if occurrence is None:
        raise ValueError("custody guest requires an occurrence")
    if occurrence.profile_root != owned_profile.profile_id:
        raise ValueError("custody guest occurrence profile root mismatch")
    if occurrence.pre_state_root != owned_global_pre.state_root:
        raise ValueError("custody guest occurrence predecessor state root mismatch")

    return owned_binding


def snapshot_asset_lane_custody_guest_role_binding_v2(
    binding: AssetLaneCustodyGuestRoleBindingV2,
) -> AssetLaneCustodyGuestRoleBindingV2:
    """Defensively copy a role binding and all manifest artifact rows."""

    if type(binding) is not AssetLaneCustodyGuestRoleBindingV2:
        raise TypeError("custody guest role binding must be exactly typed")
    return AssetLaneCustodyGuestRoleBindingV2(
        profile_root=binding.profile_root,
        authority_epoch=binding.authority_epoch,
        state_schema_root=binding.state_schema_root,
        evidence_manifest=binding.evidence_manifest,
    )


__all__ = [
    "ASSET_LANE_CUSTODY_GLOBAL_V2",
    "ASSET_LANE_CUSTODY_GUEST_ROLE_PURPOSE_V2",
    "ASSET_LANE_CUSTODY_GUEST_ROLE_BINDING_DOMAIN_V2",
    "ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2",
    "ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2",
    "ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2",
    "ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2",
    "AssetLaneCustodyGuestRoleBindingV2",
    "snapshot_asset_lane_custody_guest_role_binding_v2",
    "require_asset_lane_custody_guest_role_binding_v2",
]
