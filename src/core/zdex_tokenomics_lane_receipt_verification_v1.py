"""Shadow receipt admission for the complete ZDEX tokenomics burn lane.

This boundary selects the coordinator image from an exact governed profile,
recomputes the deterministic lane composition, and verifies the exact public
journal before producing an opaque process-local witness. It has no settlement
or publication authority and does not close the purchase-and-burn route.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

from .global_economic_profile_snapshot_v1 import (
    _snapshot_coordinator_release_v1,
    _snapshot_lane_release_v1,
    _snapshot_route_release_v1,
    snapshot_economic_profile_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    VerifiedZDEXBurnV1,
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXLaneSuccinctReceiptVerifierV1,
    _VerifiedZDEXLaneFieldsV1,
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
    _snapshot_zdex_tokenomics_burn_lane_candidate_v1,
    compose_zdex_tokenomics_burn_lane_v1,
)
from .zdex_tokenomics_lane_receipt_common_v1 import (
    VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1,
    VerifiedZDEXTokenomicsLaneV1,
    _verify_and_build_zdex_tokenomics_lane_v1,
    _ZDEXTokenomicsCoordinatorReceiptExpectationV1,
    _ZDEXTokenomicsLaneBindingV1,
)
from .zdex_tokenomics_lane_v1 import ZDEXTokenomicsLaneCompositionAcceptedV1

_GOVERNED_TOKENOMICS_PROFILE_TOKEN = object()


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

    __slots__ = ("_fields", "_trusted_profile_id", "_trusted_authority_epoch")
    _fields: _GovernedZDEXTokenomicsProfileFieldsV1
    _trusted_profile_id: str
    _trusted_authority_epoch: int

    def __init__(
        self,
        token: object,
        fields: _GovernedZDEXTokenomicsProfileFieldsV1,
        trusted_profile_id: str,
        trusted_authority_epoch: int,
    ) -> None:
        if token is not _GOVERNED_TOKENOMICS_PROFILE_TOKEN:
            raise TypeError("governed ZDEX tokenomics profile is verifier-constructed")
        if type(trusted_profile_id) is not str or type(trusted_authority_epoch) is not int:
            raise TypeError(
                "governed ZDEX tokenomics trusted profile anchor "
                "must be exact typed data"
            )
        object.__setattr__(self, "_fields", fields)
        object.__setattr__(self, "_trusted_profile_id", trusted_profile_id)
        object.__setattr__(self, "_trusted_authority_epoch", trusted_authority_epoch)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("governed ZDEX tokenomics profile is immutable")


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


def _trusted_tokenomics_profile_anchor_v1(
    governed: GovernedZDEXTokenomicsProfileV1,
) -> tuple[str, int]:
    if type(governed) is not GovernedZDEXTokenomicsProfileV1:
        raise TypeError("ZDEX tokenomics governed profile must be verifier-constructed")
    profile_id = governed._trusted_profile_id
    authority_epoch = governed._trusted_authority_epoch
    if type(profile_id) is not str or type(authority_epoch) is not int:
        raise TypeError("ZDEX tokenomics trusted profile anchor must be exact typed data")
    return profile_id, authority_epoch


def _snapshot_governed_profile_v1(
    governed: GovernedZDEXTokenomicsProfileV1,
) -> GovernedZDEXTokenomicsProfileV1:
    trusted_profile_id, trusted_authority_epoch = (
        _trusted_tokenomics_profile_anchor_v1(governed)
    )
    fields = governed._fields
    if type(fields) is not _GovernedZDEXTokenomicsProfileFieldsV1:
        raise TypeError("ZDEX tokenomics governed fields must be exact typed data")
    if type(fields.profile) is not EconomicProfileSnapshotV1:
        raise TypeError("ZDEX tokenomics governed profile must be exact typed data")
    owned_profile = snapshot_economic_profile_v1(fields.profile)
    if (
        owned_profile.profile_id != trusted_profile_id
        or owned_profile.authority_epoch != trusted_authority_epoch
    ):
        raise ValueError("ZDEX tokenomics trusted profile anchor changed")
    owned = bind_zdex_tokenomics_shadow_profile_v1(
        expected_profile_id=trusted_profile_id,
        expected_authority_epoch=trusted_authority_epoch,
        profile=owned_profile,
    )
    owned_fields = owned._fields
    if (
        _snapshot_route_release_v1(fields.route_release)
        != owned_fields.route_release
        or _snapshot_lane_release_v1(fields.module_release)
        != owned_fields.module_release
        or _snapshot_coordinator_release_v1(fields.coordinator_release)
        != owned_fields.coordinator_release
    ):
        raise ValueError("ZDEX tokenomics governed release selection changed")
    return owned


def bind_zdex_tokenomics_shadow_profile_v1(
    *,
    expected_profile_id: str,
    expected_authority_epoch: int,
    profile: EconomicProfileSnapshotV1,
) -> GovernedZDEXTokenomicsProfileV1:
    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("ZDEX tokenomics profile must be exact typed data")
    if type(expected_profile_id) is not str:
        raise ValueError("ZDEX tokenomics expected profile mismatch")
    if type(expected_authority_epoch) is not int:
        raise ValueError("ZDEX tokenomics expected authority epoch mismatch")
    owned_profile = snapshot_economic_profile_v1(profile)
    if expected_profile_id != owned_profile.profile_id:
        raise ValueError("ZDEX tokenomics expected profile mismatch")
    if expected_authority_epoch != owned_profile.authority_epoch:
        raise ValueError("ZDEX tokenomics expected authority epoch mismatch")
    if owned_profile.status is not ProfileStatusV1.SHADOW:
        raise ValueError("ZDEX tokenomics profile must remain SHADOW")
    fields = _GovernedZDEXTokenomicsProfileFieldsV1(
        owned_profile,
        _registered_buyback_route(owned_profile),
        owned_profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        owned_profile.lane_coordinator_registry.release_for(
            LaneIdV1.ZDEX_TOKENOMICS
        ),
    )
    _revalidate_governed_profile(fields)
    return GovernedZDEXTokenomicsProfileV1(
        _GOVERNED_TOKENOMICS_PROFILE_TOKEN,
        fields,
        expected_profile_id,
        expected_authority_epoch,
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
    # Route admission owns the occurrence's global pre-root. The exact
    # coordinator receipt binds this lane's pre/post roots.
    if (
        occurrence.profile_root != fields.profile.profile_id
        or occurrence.command_kind != fields.route_release.command_kind
        or occurrence.route_release_id != fields.route_release.route_release_id
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


def verify_zdex_tokenomics_lane_receipt_v1(
    candidate: ZDEXTokenomicsLaneReceiptCandidateV1,
    governed: GovernedZDEXTokenomicsProfileV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsLaneV1:
    """Reference admission through a supplied verifier; output has no authority."""

    if type(candidate) is not ZDEXTokenomicsLaneReceiptCandidateV1:
        raise TypeError("ZDEX tokenomics lane receipt candidate must be exact")
    candidate.__post_init__()
    owned_governed = _snapshot_governed_profile_v1(governed)
    fields = owned_governed._fields
    witness_fields = candidate.verified_burn._fields
    if type(witness_fields) is not _VerifiedZDEXLaneFieldsV1:
        raise TypeError("ZDEX tokenomics burn witness fields must be exact typed data")
    _require_exact_dataclass_scalars_v1(
        witness_fields,
        name="ZDEX tokenomics burn witness",
    )
    owned_candidate = replace(
        candidate,
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        lane_candidate=_snapshot_zdex_tokenomics_burn_lane_candidate_v1(
            candidate.lane_candidate
        ),
    )
    _require_candidate_bindings(owned_candidate, fields)
    recomputed = compose_zdex_tokenomics_burn_lane_v1(owned_candidate.lane_candidate)
    if type(recomputed) is not ZDEXTokenomicsLaneCompositionAcceptedV1:
        raise ValueError("ZDEX tokenomics lane composition rejected")
    receipt = owned_candidate.receipt
    journal = recomputed.lane_journal
    return _verify_and_build_zdex_tokenomics_lane_v1(
        receipt,
        journal,
        _ZDEXTokenomicsCoordinatorReceiptExpectationV1(
            fields.route_release,
            fields.coordinator_release,
        ),
        _ZDEXTokenomicsLaneBindingV1(
            fields.profile.profile_id,
            fields.route_release.route_release_id,
            fields.module_release.release_id,
            owned_candidate.occurrence.occurrence_id,
            fields.profile.authority_epoch,
            owned_candidate.lane_candidate.module_journal.journal_root,
            fields.module_release.guest_image_id,
        ),
        receipt_verifier,
    )


__all__ = [
    "GovernedZDEXTokenomicsProfileV1",
    "VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1",
    "VerifiedZDEXTokenomicsLaneV1",
    "ZDEXTokenomicsLaneReceiptCandidateV1",
    "bind_zdex_tokenomics_shadow_profile_v1",
    "verify_zdex_tokenomics_lane_receipt_v1",
]
