"""Shadow receipt admission for the complete ZDEX tokenomics burn lane.

This boundary selects the coordinator image from an exact governed profile,
recomputes the deterministic lane composition, and verifies the exact public
journal before producing an opaque process-local witness. It has no settlement
or publication authority and does not close the purchase-and-burn route.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from typing import Final

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    VerifiedZDEXBurnV1,
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXLaneSuccinctReceiptVerifierV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)
from .zdex_tokenomics_lane_coordinator_v1 import (
    ZDEXTokenomicsBurnLaneCandidateV1,
    compose_zdex_tokenomics_burn_lane_v1,
)
from .zdex_tokenomics_lane_v1 import ZDEXTokenomicsLaneCompositionAcceptedV1

VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1: Final = (
    "zenodex/verified-zdex-tokenomics-lane/v1"
)
_GOVERNED_TOKENOMICS_PROFILE_TOKEN = object()
_VERIFIED_TOKENOMICS_LANE_TOKEN = object()


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsLaneReceiptCandidateV1:
    occurrence: EconomicCommandOccurrenceV1
    lane_candidate: ZDEXTokenomicsBurnLaneCandidateV1
    verified_burn: VerifiedZDEXBurnV1
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected = (
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (
                self.lane_candidate,
                ZDEXTokenomicsBurnLaneCandidateV1,
                "lane candidate",
            ),
            (self.verified_burn, VerifiedZDEXBurnV1, "verified burn"),
            (self.receipt, ZDEXLaneReceiptEnvelopeV1, "receipt"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(
                    f"ZDEX tokenomics lane receipt {label} must be exact typed data"
                )


@dataclass(frozen=True, slots=True)
class _GovernedZDEXTokenomicsProfileFieldsV1:
    profile: EconomicProfileSnapshotV1
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    coordinator_release: LaneCoordinatorReleaseV1


class GovernedZDEXTokenomicsProfileV1:
    """Verifier-selected SHADOW releases for tokenomics lane admission."""

    __slots__ = ("_fields",)
    _fields: _GovernedZDEXTokenomicsProfileFieldsV1

    def __init__(
        self,
        token: object,
        fields: _GovernedZDEXTokenomicsProfileFieldsV1,
    ) -> None:
        if token is not _GOVERNED_TOKENOMICS_PROFILE_TOKEN:
            raise TypeError("governed ZDEX tokenomics profile is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("governed ZDEX tokenomics profile is immutable")


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXTokenomicsLaneFieldsV1:
    profile_root: str
    route_release_id: str
    module_release_id: str
    coordinator_release_id: str
    command_occurrence_id: str
    writer_epoch: int
    module_journal_root: str
    lane_journal_root: str
    lane_journal_digest: str
    pre_lane_root: str
    post_lane_root: str
    effect_plan_root: str
    module_image_id: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1


class VerifiedZDEXTokenomicsLaneV1:
    """Non-authoritative process-local marker for shadow receipt admission."""

    __slots__ = ("_fields",)
    _fields: _VerifiedZDEXTokenomicsLaneFieldsV1

    def __init__(
        self,
        token: object,
        fields: _VerifiedZDEXTokenomicsLaneFieldsV1,
    ) -> None:
        if token is not _VERIFIED_TOKENOMICS_LANE_TOKEN:
            raise TypeError("VerifiedZDEXTokenomicsLaneV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedZDEXTokenomicsLaneV1 is immutable")

    @property
    def profile_root(self) -> str:
        return self._fields.profile_root

    @property
    def route_release_id(self) -> str:
        return self._fields.route_release_id

    @property
    def module_release_id(self) -> str:
        return self._fields.module_release_id

    @property
    def coordinator_release_id(self) -> str:
        return self._fields.coordinator_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def writer_epoch(self) -> int:
        return self._fields.writer_epoch

    @property
    def module_journal_root(self) -> str:
        return self._fields.module_journal_root

    @property
    def lane_journal_root(self) -> str:
        return self._fields.lane_journal_root

    @property
    def lane_journal_digest(self) -> str:
        return self._fields.lane_journal_digest

    @property
    def pre_lane_root(self) -> str:
        return self._fields.pre_lane_root

    @property
    def post_lane_root(self) -> str:
        return self._fields.post_lane_root

    @property
    def effect_plan_root(self) -> str:
        return self._fields.effect_plan_root

    @property
    def module_image_id(self) -> str:
        return self._fields.module_image_id

    @property
    def expected_image_id(self) -> str:
        return self._fields.expected_image_id

    @property
    def receipt_digest(self) -> str:
        return self._fields.receipt_digest

    @property
    def receipt_kind(self) -> ReceiptKindV1:
        return self._fields.receipt_kind

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-zdex-tokenomics-lane-v1",
            {
                "schema": VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1,
                "profile_root": self.profile_root,
                "route_release_id": self.route_release_id,
                "module_release_id": self.module_release_id,
                "coordinator_release_id": self.coordinator_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "writer_epoch": self.writer_epoch,
                "module_journal_root": self.module_journal_root,
                "lane_journal_root": self.lane_journal_root,
                "lane_journal_digest": self.lane_journal_digest,
                "pre_lane_root": self.pre_lane_root,
                "post_lane_root": self.post_lane_root,
                "effect_plan_root": self.effect_plan_root,
                "module_image_id": self.module_image_id,
                "expected_image_id": self.expected_image_id,
                "receipt_digest": self.receipt_digest,
                "receipt_kind": self.receipt_kind,
            },
        )


def _registered_buyback_route(
    profile: EconomicProfileSnapshotV1,
) -> RouteReleaseV1:
    for route in profile.route_registry.routes:
        if route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1:
            return route
    raise ValueError("ZDEX tokenomics governed buyback route is absent")


def _require_release_shapes(
    fields: _GovernedZDEXTokenomicsProfileFieldsV1,
) -> None:
    route = fields.route_release
    module = fields.module_release
    coordinator = fields.coordinator_release
    if route.status is not ReleaseStatusV1.SHADOW or route.accepts_new_objects:
        raise ValueError("ZDEX tokenomics route must remain SHADOW")
    if (
        route.ordered_lanes
        != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
        or route.module_release_ids[1] != module.release_id
        or route.dependency_roles
        != (AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1)
        or route.port_schema_roots
        != (
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        )
    ):
        raise ValueError("ZDEX tokenomics route shape mismatch")
    if (
        module.status is not ReleaseStatusV1.SHADOW
        or module.accepts_new_objects
        or module.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
        or PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1 not in module.command_variants
    ):
        raise ValueError("ZDEX tokenomics module release mismatch")
    if (
        coordinator.status is not ReleaseStatusV1.SHADOW
        or coordinator.accepts_new_objects
        or coordinator.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
    ):
        raise ValueError("ZDEX tokenomics coordinator release mismatch")


def _revalidate_governed_profile(
    fields: _GovernedZDEXTokenomicsProfileFieldsV1,
) -> None:
    """Re-run content-derived constructors and exact registry selection."""

    replace(fields.module_release)
    replace(fields.coordinator_release)
    replace(fields.route_release)
    replace(fields.profile)
    if (
        _registered_buyback_route(fields.profile) != fields.route_release
        or fields.profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS)
        != fields.module_release
        or fields.profile.lane_coordinator_registry.release_for(
            LaneIdV1.ZDEX_TOKENOMICS
        )
        != fields.coordinator_release
    ):
        raise ValueError("ZDEX tokenomics governed release selection changed")
    _require_release_shapes(fields)


def bind_zdex_tokenomics_shadow_profile_v1(
    *,
    expected_profile_id: str,
    expected_authority_epoch: int,
    profile: EconomicProfileSnapshotV1,
) -> GovernedZDEXTokenomicsProfileV1:
    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("ZDEX tokenomics profile must be exact typed data")
    if type(expected_profile_id) is not str or expected_profile_id != profile.profile_id:
        raise ValueError("ZDEX tokenomics expected profile mismatch")
    if (
        type(expected_authority_epoch) is not int
        or expected_authority_epoch != profile.authority_epoch
    ):
        raise ValueError("ZDEX tokenomics expected authority epoch mismatch")
    if profile.status is not ProfileStatusV1.SHADOW:
        raise ValueError("ZDEX tokenomics profile must remain SHADOW")
    fields = _GovernedZDEXTokenomicsProfileFieldsV1(
        profile,
        _registered_buyback_route(profile),
        profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        profile.lane_coordinator_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
    )
    _revalidate_governed_profile(fields)
    return GovernedZDEXTokenomicsProfileV1(
        _GOVERNED_TOKENOMICS_PROFILE_TOKEN,
        fields,
    )


def _require_candidate_bindings(
    candidate: ZDEXTokenomicsLaneReceiptCandidateV1,
    fields: _GovernedZDEXTokenomicsProfileFieldsV1,
) -> None:
    occurrence = candidate.occurrence
    lane = candidate.lane_candidate
    context = lane.context
    occurrence_id = occurrence.occurrence_id
    burn = lane.burn_journal
    burn_bytes = canonical_global_bytes_v1(burn)
    verified_burn = candidate.verified_burn
    if (
        occurrence.profile_root != fields.profile.profile_id
        or occurrence.command_kind != fields.route_release.command_kind
        or occurrence.route_release_id != fields.route_release.route_release_id
        or occurrence.pre_state_root != lane.pre_state.state_root
        or context.chain_id != occurrence.chain_id
        or context.deployment_root != occurrence.deployment_root
        or context.profile_root != fields.profile.profile_id
        or context.writer_epoch != fields.profile.authority_epoch
        or context.coordinator_release_id
        != fields.coordinator_release.coordinator_release_id
        or context.route_release_id != fields.route_release.route_release_id
        or context.tokenomics_module_release_id != fields.module_release.release_id
        or context.command_occurrence_id != occurrence_id
        or context.issue_burn_policy_root
        != fields.route_release.issue_burn_policy_root
        or verified_burn.route_release_id != fields.route_release.route_release_id
        or verified_burn.module_release_id != fields.module_release.release_id
        or verified_burn.command_occurrence_id != occurrence_id
        or verified_burn.profile_root != fields.profile.profile_id
        or verified_burn.writer_epoch != fields.profile.authority_epoch
        or verified_burn.journal_root != burn.journal_root
        or verified_burn.journal_digest
        != "0x" + hashlib.sha256(burn_bytes).hexdigest()
        or verified_burn.effect_plan_root != lane.module_effects.effect_plan_root
        or verified_burn.expected_image_id != fields.module_release.guest_image_id
        or verified_burn.receipt_kind is not ReceiptKindV1.SUCCINCT
    ):
        raise ValueError("ZDEX tokenomics governed candidate binding mismatch")


def _verify_coordinator_receipt(
    receipt: ZDEXLaneReceiptEnvelopeV1,
    journal: object,
    fields: _GovernedZDEXTokenomicsProfileFieldsV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> tuple[str, str]:
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("ZDEX tokenomics lane verification requires a succinct receipt")
    if not receipt.receipt_bytes:
        raise ValueError("ZDEX tokenomics lane receipt bytes must be nonempty")
    journal_bytes = canonical_global_bytes_v1(journal)
    if len(journal_bytes) > min(
        fields.route_release.max_journal_bytes,
        fields.coordinator_release.max_journal_bytes,
    ):
        raise ValueError("ZDEX tokenomics lane journal exceeds release byte ceiling")
    receipt_verifier.verify_succinct_receipt(
        receipt.receipt_bytes,
        expected_image_id=fields.coordinator_release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return (
        "0x" + hashlib.sha256(journal_bytes).hexdigest(),
        "0x" + hashlib.sha256(receipt.receipt_bytes).hexdigest(),
    )


def verify_zdex_tokenomics_lane_receipt_v1(
    candidate: ZDEXTokenomicsLaneReceiptCandidateV1,
    governed: GovernedZDEXTokenomicsProfileV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsLaneV1:
    """Reference admission through a supplied verifier; output has no authority."""

    if type(candidate) is not ZDEXTokenomicsLaneReceiptCandidateV1:
        raise TypeError("ZDEX tokenomics lane receipt candidate must be exact")
    if type(governed) is not GovernedZDEXTokenomicsProfileV1:
        raise TypeError("ZDEX tokenomics governed profile must be verifier-constructed")
    fields = governed._fields
    _revalidate_governed_profile(fields)
    _require_candidate_bindings(candidate, fields)
    recomputed = compose_zdex_tokenomics_burn_lane_v1(candidate.lane_candidate)
    if type(recomputed) is not ZDEXTokenomicsLaneCompositionAcceptedV1:
        raise ValueError("ZDEX tokenomics lane composition rejected")
    receipt = candidate.receipt
    journal = recomputed.lane_journal
    journal_digest, receipt_digest = _verify_coordinator_receipt(
        receipt,
        journal,
        fields,
        receipt_verifier,
    )
    return VerifiedZDEXTokenomicsLaneV1(
        _VERIFIED_TOKENOMICS_LANE_TOKEN,
        _VerifiedZDEXTokenomicsLaneFieldsV1(
            fields.profile.profile_id,
            fields.route_release.route_release_id,
            fields.module_release.release_id,
            fields.coordinator_release.coordinator_release_id,
            candidate.occurrence.occurrence_id,
            fields.profile.authority_epoch,
            candidate.lane_candidate.module_journal.journal_root,
            journal.journal_root,
            journal_digest,
            journal.pre_lane_root,
            journal.post_lane_root,
            recomputed.effects.effect_plan_root,
            fields.module_release.guest_image_id,
            fields.coordinator_release.guest_image_id,
            receipt_digest,
            receipt.receipt_kind,
        ),
    )


__all__ = [
    "GovernedZDEXTokenomicsProfileV1",
    "VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1",
    "VerifiedZDEXTokenomicsLaneV1",
    "ZDEXTokenomicsLaneReceiptCandidateV1",
    "bind_zdex_tokenomics_shadow_profile_v1",
    "verify_zdex_tokenomics_lane_receipt_v1",
]
