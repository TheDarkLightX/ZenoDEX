"""Release-image-bound receipt verification for accepted lane modules.

The deterministic core recomputes the structural release-route binding, selects
the expected guest image from the active lane release, and supplies the exact
canonical module journal bytes to a cryptographic verifier port. Only that path
can construct :class:`VerifiedLaneModuleTransitionV1`.

This module does not select or authenticate the verifier implementation, prove
the guest, coordinate lanes, compose routes, or publish ledger state.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    _recompute_asset_transfer_lane_module_accepted_v1,
    _snapshot_asset_transfer_lane_module_accepted_v1,
    _snapshot_asset_transfer_lane_module_input_v1,
)
from .economic_command_authentication_v1 import AuthenticatedEconomicCommandV1
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import (
    LaneModuleTransitionJournalV1,
    ReceiptKindV1,
    SuccinctReceiptVerifierV1,
)
from .global_oracle_price_occurrence_v1 import VerifiedGlobalOraclePriceV1
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    ReleaseStatusV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .lane_module_release_route_binding_v1 import (
    PerpsMarginReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
    bind_asset_transfer_lane_output_to_release_route_v1,
    bind_managed_asset_lifecycle_lane_output_to_release_route_v1,
    bind_perps_margin_lane_output_to_release_route_v1,
)
from .m6_capability_profile_binding_v1 import snapshot_economic_policy_registry_v1
from .managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    _recompute_managed_asset_lifecycle_lane_module_accepted_v1,
    _snapshot_managed_asset_lifecycle_lane_module_accepted_v1,
    _snapshot_managed_asset_lifecycle_lane_module_input_v1,
)
from .perps_margin_lane_module_v1 import (
    PerpsMarginLaneModuleInputV1,
    _recompute_perps_margin_accepted_v1,
    _snapshot_perps_margin_lane_module_input_v1,
)
from .perps_margin_types_v1 import PerpsMarginAcceptedV1
from .perps_market_policy_v1 import (
    PerpsMarketPolicyV1,
    snapshot_perps_market_policy_v1,
)

VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1: Final = (
    "zenodex/verified-lane-module-transition/v1"
)
_VERIFIED_LANE_MODULE_TRANSITION_TOKEN = object()


@dataclass(frozen=True, slots=True)
class LaneModuleReceiptEnvelopeV1:
    receipt_kind: ReceiptKindV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.receipt_kind, ReceiptKindV1):
            raise TypeError("lane module receipt kind is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("lane module receipt bytes must be exact bytes")


@dataclass(frozen=True, slots=True)
class AssetTransferLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    authenticated_command: AuthenticatedEconomicCommandV1
    module_input: AssetTransferLaneModuleInputV1
    accepted: AssetTransferLaneModuleAcceptedV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    receipt: LaneModuleReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (
                self.authenticated_command,
                AuthenticatedEconomicCommandV1,
                "authenticated economic command",
            ),
            (self.module_input, AssetTransferLaneModuleInputV1, "asset transfer input"),
            (self.accepted, AssetTransferLaneModuleAcceptedV1, "asset transfer output"),
            (
                self.release_route_binding,
                ReleaseRouteBoundLaneTransitionV1,
                "release-route binding",
            ),
            (self.receipt, LaneModuleReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"lane module {label} must be typed")


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    authenticated_command: AuthenticatedEconomicCommandV1
    module_input: ManagedAssetLifecycleLaneModuleInputV1
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    receipt: LaneModuleReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (
                self.authenticated_command,
                AuthenticatedEconomicCommandV1,
                "authenticated economic command",
            ),
            (
                self.module_input,
                ManagedAssetLifecycleLaneModuleInputV1,
                "managed lifecycle input",
            ),
            (
                self.accepted,
                ManagedAssetLifecycleLaneModuleAcceptedV1,
                "managed lifecycle output",
            ),
            (
                self.release_route_binding,
                ReleaseRouteBoundLaneTransitionV1,
                "release-route binding",
            ),
            (self.receipt, LaneModuleReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"lane module {label} must be typed")


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    market_policy: PerpsMarketPolicyV1
    authenticated_command: AuthenticatedEconomicCommandV1
    module_input: PerpsMarginLaneModuleInputV1
    accepted: PerpsMarginAcceptedV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    verified_price: VerifiedGlobalOraclePriceV1 | None
    receipt: LaneModuleReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.policy_registry, EconomicPolicyRegistryV1, "economic policy registry"),
            (self.market_policy, PerpsMarketPolicyV1, "perps market policy"),
            (
                self.authenticated_command,
                AuthenticatedEconomicCommandV1,
                "authenticated economic command",
            ),
            (self.module_input, PerpsMarginLaneModuleInputV1, "perps margin input"),
            (self.accepted, PerpsMarginAcceptedV1, "perps margin output"),
            (
                self.release_route_binding,
                ReleaseRouteBoundLaneTransitionV1,
                "release-route binding",
            ),
            (self.receipt, LaneModuleReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"lane module {label} must be typed")
        if self.verified_price is not None and (
            type(self.verified_price) is not VerifiedGlobalOraclePriceV1
        ):
            raise TypeError("lane module verified Oracle price must be exact typed data")


@dataclass(frozen=True, slots=True)
class _VerifiedLaneModuleTransitionFieldsV1:
    authenticated_command_binding_root: str
    release_route_binding_root: str
    expected_image_id: str
    module_journal_root: str
    module_journal_digest: str
    statement_root: str
    command_occurrence_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1


class VerifiedLaneModuleTransitionV1:
    """Opaque module-proof authority produced only after receipt verification."""

    _fields: _VerifiedLaneModuleTransitionFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _VerifiedLaneModuleTransitionFieldsV1,
    ) -> None:
        if token is not _VERIFIED_LANE_MODULE_TRANSITION_TOKEN:
            raise TypeError("VerifiedLaneModuleTransitionV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedLaneModuleTransitionV1 is immutable")

    @property
    def authenticated_command_binding_root(self) -> str:
        return self._fields.authenticated_command_binding_root

    @property
    def release_route_binding_root(self) -> str:
        return self._fields.release_route_binding_root

    @property
    def expected_image_id(self) -> str:
        return self._fields.expected_image_id

    @property
    def module_journal_root(self) -> str:
        return self._fields.module_journal_root

    @property
    def module_journal_digest(self) -> str:
        return self._fields.module_journal_digest

    @property
    def statement_root(self) -> str:
        return self._fields.statement_root

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def receipt_digest(self) -> str:
        return self._fields.receipt_digest

    @property
    def receipt_kind(self) -> ReceiptKindV1:
        return self._fields.receipt_kind

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-lane-module-transition-v1",
            {
                "schema": VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1,
                "authenticated_command_binding_root": (
                    self.authenticated_command_binding_root
                ),
                "release_route_binding_root": self.release_route_binding_root,
                "expected_image_id": self.expected_image_id,
                "module_journal_root": self.module_journal_root,
                "module_journal_digest": self.module_journal_digest,
                "statement_root": self.statement_root,
                "command_occurrence_id": self.command_occurrence_id,
                "receipt_digest": self.receipt_digest,
                "receipt_kind": self.receipt_kind,
            },
        )


def _sha256_root_v1(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


@dataclass(frozen=True, slots=True)
class _ReboundLaneModuleReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    authenticated_command_binding_root: str
    module_journal: LaneModuleTransitionJournalV1
    release_route_binding: ReleaseRouteBoundLaneTransitionV1
    rebound: ReleaseRouteBoundLaneTransitionV1
    receipt: LaneModuleReceiptEnvelopeV1


def _verify_rebound_module_receipt_v1(
    candidate: _ReboundLaneModuleReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    if candidate.release_route_binding.binding_root != candidate.rebound.binding_root:
        raise ValueError("lane module structural binding mismatch")
    if candidate.receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("lane module verification requires a succinct receipt")
    if not candidate.receipt.receipt_bytes:
        raise ValueError("lane module receipt bytes must be non-empty bytes")

    release = candidate.profile.lane_registry.release_for(candidate.rebound.lane_id)
    if release.release_id != candidate.rebound.module_release_id:
        raise ValueError("lane module verified release mismatch")
    if release.status is not ReleaseStatusV1.ACTIVE_NEW or not release.accepts_new_objects:
        raise ValueError("lane module release is not ACTIVE_NEW")

    journal_bytes = canonical_global_bytes_v1(candidate.module_journal)
    if len(journal_bytes) > release.max_journal_bytes:
        raise ValueError("lane module canonical journal exceeds its release byte ceiling")
    module_journal_digest = _sha256_root_v1(journal_bytes)
    receipt_digest = _sha256_root_v1(candidate.receipt.receipt_bytes)
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt.receipt_bytes,
        expected_image_id=release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedLaneModuleTransitionV1(
        _VERIFIED_LANE_MODULE_TRANSITION_TOKEN,
        _VerifiedLaneModuleTransitionFieldsV1(
            candidate.authenticated_command_binding_root,
            candidate.rebound.binding_root,
            release.guest_image_id,
            candidate.rebound.module_journal_root,
            module_journal_digest,
            candidate.rebound.statement_root,
            candidate.rebound.command_occurrence_id,
            receipt_digest,
            candidate.receipt.receipt_kind,
        ),
    )


def verify_asset_transfer_lane_module_receipt_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Verify one transfer receipt under its active release image and journal."""

    owned = _snapshot_asset_transfer_receipt_candidate_v1(candidate)
    occurrence = owned.authenticated_command.occurrence
    rebound = bind_asset_transfer_lane_output_to_release_route_v1(
        owned.profile,
        occurrence,
        owned.module_input,
        owned.accepted,
    )
    _, expected = _recompute_asset_transfer_lane_module_accepted_v1(
        owned.module_input,
        owned.accepted,
    )
    return _verify_rebound_module_receipt_v1(
        _ReboundLaneModuleReceiptCandidateV1(
            owned.profile,
            owned.authenticated_command.binding_root,
            expected.module_journal,
            owned.release_route_binding,
            rebound,
            owned.receipt,
        ),
        receipt_verifier,
    )


def verify_managed_asset_lifecycle_lane_module_receipt_v1(
    candidate: ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Verify one ordinary-token issue or burn receipt under its release image."""

    owned = _snapshot_managed_lifecycle_receipt_candidate_v1(candidate)
    occurrence = owned.authenticated_command.occurrence
    rebound = bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
        owned.profile,
        occurrence,
        owned.module_input,
        owned.accepted,
    )
    _, expected = _recompute_managed_asset_lifecycle_lane_module_accepted_v1(
        owned.module_input,
        owned.accepted,
    )
    return _verify_rebound_module_receipt_v1(
        _ReboundLaneModuleReceiptCandidateV1(
            owned.profile,
            owned.authenticated_command.binding_root,
            expected.module_journal,
            owned.release_route_binding,
            rebound,
            owned.receipt,
        ),
        receipt_verifier,
    )


def verify_perps_margin_lane_module_receipt_v1(
    candidate: PerpsMarginLaneModuleReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Verify one perps-margin receipt under command and Oracle authority."""

    owned = _snapshot_perps_margin_receipt_candidate_v1(candidate)
    occurrence = owned.authenticated_command.occurrence
    rebound = bind_perps_margin_lane_output_to_release_route_v1(
        PerpsMarginReleaseRouteBindingCandidateV1(
            owned.profile,
            owned.policy_registry,
            owned.market_policy,
            occurrence,
            owned.module_input,
            owned.accepted,
            owned.verified_price,
        )
    )
    _, expected = _recompute_perps_margin_accepted_v1(
        owned.module_input,
        owned.accepted,
    )
    return _verify_rebound_module_receipt_v1(
        _ReboundLaneModuleReceiptCandidateV1(
            owned.profile,
            owned.authenticated_command.binding_root,
            expected.module_journal,
            owned.release_route_binding,
            rebound,
            owned.receipt,
        ),
        receipt_verifier,
    )


def _snapshot_asset_transfer_receipt_candidate_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1,
) -> AssetTransferLaneModuleReceiptCandidateV1:
    if type(candidate) is not AssetTransferLaneModuleReceiptCandidateV1:
        raise TypeError("asset transfer receipt candidate must have the exact type")
    return AssetTransferLaneModuleReceiptCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        authenticated_command=candidate.authenticated_command,
        module_input=_snapshot_asset_transfer_lane_module_input_v1(
            candidate.module_input
        ),
        accepted=_snapshot_asset_transfer_lane_module_accepted_v1(candidate.accepted),
        release_route_binding=candidate.release_route_binding,
        receipt=_snapshot_lane_module_receipt_envelope_v1(candidate.receipt),
    )


def _snapshot_managed_lifecycle_receipt_candidate_v1(
    candidate: ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
) -> ManagedAssetLifecycleLaneModuleReceiptCandidateV1:
    if type(candidate) is not ManagedAssetLifecycleLaneModuleReceiptCandidateV1:
        raise TypeError("managed lifecycle receipt candidate must have the exact type")
    return ManagedAssetLifecycleLaneModuleReceiptCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        authenticated_command=candidate.authenticated_command,
        module_input=_snapshot_managed_asset_lifecycle_lane_module_input_v1(
            candidate.module_input
        ),
        accepted=_snapshot_managed_asset_lifecycle_lane_module_accepted_v1(
            candidate.accepted
        ),
        release_route_binding=candidate.release_route_binding,
        receipt=_snapshot_lane_module_receipt_envelope_v1(candidate.receipt),
    )


def _snapshot_perps_margin_receipt_candidate_v1(
    candidate: PerpsMarginLaneModuleReceiptCandidateV1,
) -> PerpsMarginLaneModuleReceiptCandidateV1:
    if type(candidate) is not PerpsMarginLaneModuleReceiptCandidateV1:
        raise TypeError("perps margin receipt candidate must have the exact type")
    _, accepted = _recompute_perps_margin_accepted_v1(
        candidate.module_input,
        candidate.accepted,
    )
    return PerpsMarginLaneModuleReceiptCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=snapshot_economic_policy_registry_v1(
            candidate.policy_registry
        ),
        market_policy=snapshot_perps_market_policy_v1(candidate.market_policy),
        authenticated_command=candidate.authenticated_command,
        module_input=_snapshot_perps_margin_lane_module_input_v1(
            candidate.module_input
        ),
        accepted=accepted,
        release_route_binding=candidate.release_route_binding,
        verified_price=candidate.verified_price,
        receipt=_snapshot_lane_module_receipt_envelope_v1(candidate.receipt),
    )


def _snapshot_lane_module_receipt_envelope_v1(
    receipt: LaneModuleReceiptEnvelopeV1,
) -> LaneModuleReceiptEnvelopeV1:
    if type(receipt) is not LaneModuleReceiptEnvelopeV1:
        raise TypeError("lane module receipt envelope must have the exact type")
    return LaneModuleReceiptEnvelopeV1(receipt.receipt_kind, receipt.receipt_bytes)


__all__ = [
    "AssetTransferLaneModuleReceiptCandidateV1",
    "LaneModuleReceiptEnvelopeV1",
    "ManagedAssetLifecycleLaneModuleReceiptCandidateV1",
    "PerpsMarginLaneModuleReceiptCandidateV1",
    "VERIFIED_LANE_MODULE_TRANSITION_SCHEMA_V1",
    "VerifiedLaneModuleTransitionV1",
    "verify_asset_transfer_lane_module_receipt_v1",
    "verify_managed_asset_lifecycle_lane_module_receipt_v1",
    "verify_perps_margin_lane_module_receipt_v1",
]
