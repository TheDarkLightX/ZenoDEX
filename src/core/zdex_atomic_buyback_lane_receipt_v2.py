"""Profile-selected receipt admission for ZDEX buyback lane coordinators.

Successful admission produces a process-local opaque handle.  It binds one
coordinator journal, its normalized effects, the authenticated leaf assumption,
the current SHADOW authority snapshot, and one succinct receipt.  Durable
publication still requires the writer-side authority-head CAS.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from threading import Lock
from weakref import WeakKeyDictionary

from .economic_receipt_verifier_deployment_v1 import BoundEconomicReceiptVerifierV1
from .global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _snapshot_effect_plan_v1,
    _snapshot_lane_journal_v1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ReleaseStatusV1,
    _require_root,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_atomic_buyback_lane_coordinator_v2 import (
    ZDEXBuybackLaneCompositionAcceptedV2,
)
from .zdex_purchase_burn_receipt_verification_v1 import ZDEXLaneReceiptEnvelopeV1


@dataclass(frozen=True, slots=True)
class ZDEXBuybackLaneCoordinatorReceiptCandidateV2:
    profile: EconomicProfileSnapshotV1
    composition: ZDEXBuybackLaneCompositionAcceptedV2
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        if (
            type(self.profile) is not EconomicProfileSnapshotV1
            or type(self.composition) is not ZDEXBuybackLaneCompositionAcceptedV2
            or type(self.receipt) is not ZDEXLaneReceiptEnvelopeV1
        ):
            raise TypeError("ZDEX buyback coordinator receipt candidate is not closed")


def _snapshot_composition_v2(
    composition: ZDEXBuybackLaneCompositionAcceptedV2,
) -> ZDEXBuybackLaneCompositionAcceptedV2:
    if type(composition) is not ZDEXBuybackLaneCompositionAcceptedV2:
        raise TypeError("ZDEX buyback lane composition must be exact typed data")
    composition.__post_init__()
    owned = ZDEXBuybackLaneCompositionAcceptedV2(
        _snapshot_effect_plan_v1(composition.effects),
        _snapshot_lane_journal_v1(composition.lane_journal),
        composition.leaf_assumption_root,
        composition.leaf_binding_root,
        tuple(composition.outstanding_terminal_obligations),
        tuple(composition.discharged_terminal_obligations),
    )
    composition.__post_init__()
    return owned


@dataclass(frozen=True, slots=True)
class _VerifiedCoordinatorFieldsV2:
    composition: ZDEXBuybackLaneCompositionAcceptedV2
    coordinator_release_id: str
    expected_image_id: str
    journal_digest: str
    receipt_digest: str
    authority_head_root: str
    verifier_binding_root: str


_VERIFIED_COORDINATOR_TOKEN_V2 = object()
_VERIFIED_COORDINATOR_LOCK_V2 = Lock()
_VERIFIED_COORDINATOR_FIELDS_V2: WeakKeyDictionary[
    VerifiedZDEXBuybackLaneCompositionV2,
    _VerifiedCoordinatorFieldsV2,
] = WeakKeyDictionary()


class VerifiedZDEXBuybackLaneCompositionV2:
    """Data-slot-free coordinator witness registered after receipt admission."""

    __slots__ = ("__weakref__",)

    def __init__(self, token: object, fields: _VerifiedCoordinatorFieldsV2) -> None:
        if token is not _VERIFIED_COORDINATOR_TOKEN_V2:
            raise TypeError("verified ZDEX buyback coordinator is verifier-constructed")
        if type(fields) is not _VerifiedCoordinatorFieldsV2:
            raise TypeError("verified ZDEX buyback coordinator fields are not closed")
        _register_verified_coordinator_v2(self, fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("verified ZDEX buyback coordinator is immutable")

    @property
    def lane_id(self) -> LaneIdV1:
        return _verified_coordinator_fields_v2(self).composition.lane_journal.lane_id

    @property
    def route_occurrence_id(self) -> str:
        return _verified_coordinator_fields_v2(
            self
        ).composition.lane_journal.command_occurrence_id

    @property
    def profile_root(self) -> str:
        return _verified_coordinator_fields_v2(self).composition.lane_journal.profile_root

    @property
    def writer_epoch(self) -> int:
        return _verified_coordinator_fields_v2(self).composition.lane_journal.writer_epoch

    @property
    def journal_root(self) -> str:
        return _verified_coordinator_fields_v2(self).composition.lane_journal.journal_root

    @property
    def authority_head_root(self) -> str:
        return _verified_coordinator_fields_v2(self).authority_head_root

    @property
    def verifier_binding_root(self) -> str:
        return _verified_coordinator_fields_v2(self).verifier_binding_root

    @property
    def assumption_root(self) -> str:
        fields = _verified_coordinator_fields_v2(self)
        composition = fields.composition
        return hash_global_v1(
            "verified-zdex-buyback-lane-coordinator-assumption-v2",
            {
                "lane_journal_root": composition.lane_journal.journal_root,
                "effect_plan_root": composition.effects.effect_plan_root,
                "leaf_assumption_root": composition.leaf_assumption_root,
                "coordinator_release_id": fields.coordinator_release_id,
                "expected_image_id": fields.expected_image_id,
            },
        )

    @property
    def binding_root(self) -> str:
        fields = _verified_coordinator_fields_v2(self)
        return hash_global_v1(
            "verified-zdex-buyback-lane-coordinator-v2",
            {
                "assumption_root": self.assumption_root,
                "leaf_binding_root": fields.composition.leaf_binding_root,
                "journal_digest": fields.journal_digest,
                "receipt_digest": fields.receipt_digest,
                "authority_head_root": fields.authority_head_root,
                "verifier_binding_root": fields.verifier_binding_root,
            },
        )


def _register_verified_coordinator_v2(
    handle: VerifiedZDEXBuybackLaneCompositionV2,
    fields: _VerifiedCoordinatorFieldsV2,
) -> None:
    fields.composition.__post_init__()
    for name in (
        "coordinator_release_id",
        "expected_image_id",
        "journal_digest",
        "receipt_digest",
        "authority_head_root",
        "verifier_binding_root",
    ):
        value = object.__getattribute__(fields, name)
        if type(value) is not str:
            raise TypeError(f"verified ZDEX buyback coordinator {name} must be exact str")
        _require_root(value, name=f"verified ZDEX buyback coordinator {name}")
    with _VERIFIED_COORDINATOR_LOCK_V2:
        if handle in _VERIFIED_COORDINATOR_FIELDS_V2:
            raise TypeError("verified ZDEX buyback coordinator is already registered")
        _VERIFIED_COORDINATOR_FIELDS_V2[handle] = fields


def _verified_coordinator_fields_v2(
    handle: VerifiedZDEXBuybackLaneCompositionV2,
) -> _VerifiedCoordinatorFieldsV2:
    if type(handle) is not VerifiedZDEXBuybackLaneCompositionV2:
        raise TypeError("verified ZDEX buyback coordinator must have an exact type")
    with _VERIFIED_COORDINATOR_LOCK_V2:
        fields = _VERIFIED_COORDINATOR_FIELDS_V2.get(handle)
    if fields is None:
        raise TypeError("verified ZDEX buyback coordinator is not registered")
    return fields


def snapshot_verified_zdex_buyback_lane_composition_v2(
    verified: VerifiedZDEXBuybackLaneCompositionV2,
) -> ZDEXBuybackLaneCompositionAcceptedV2:
    return _snapshot_composition_v2(_verified_coordinator_fields_v2(verified).composition)


def verify_zdex_buyback_lane_coordinator_receipt_shadow_v2(
    candidate: ZDEXBuybackLaneCoordinatorReceiptCandidateV2,
    *,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXBuybackLaneCompositionV2:
    """Admit one coordinator receipt under the current SHADOW profile."""

    if type(candidate) is not ZDEXBuybackLaneCoordinatorReceiptCandidateV2:
        raise TypeError("ZDEX buyback coordinator candidate must be exact typed data")
    candidate.__post_init__()
    profile = snapshot_economic_profile_v1(candidate.profile)
    composition = _snapshot_composition_v2(candidate.composition)
    receipt = ZDEXLaneReceiptEnvelopeV1(
        candidate.receipt.receipt_kind,
        candidate.receipt.receipt_bytes,
    )
    if type(authority_head) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("ZDEX buyback coordinator authority head is not closed")
    head = replace(authority_head)
    lane_journal = composition.lane_journal
    coordinator = profile.lane_coordinator_registry.release_for(lane_journal.lane_id)
    if (
        head.status is not GlobalEconomicAuthorityStatusV1.ACTIVE
        or head.chain_id != lane_journal.chain_id
        or head.deployment_root != lane_journal.deployment_root
        or head.profile_root != profile.profile_id
        or head.profile_root != lane_journal.profile_root
        or head.writer_epoch != profile.authority_epoch
        or head.writer_epoch != lane_journal.writer_epoch
        or head.verifier_registry_root != profile.verifier_registry_root
        or head.verifier_release_id != receipt_verifier.release_id
        or head.verifier_binding_root != receipt_verifier.binding_root
        or head.root_image_id != profile.root_image_id
        or coordinator.coordinator_release_id != lane_journal.coordinator_release_id
        or coordinator.status is not ReleaseStatusV1.SHADOW
        or coordinator.accepts_new_objects
    ):
        raise ValueError("ZDEX buyback coordinator authority binding mismatch")
    receipt_verifier.require_binding(
        verifier_registry_root=profile.verifier_registry_root,
        deployment_root=head.deployment_root,
        profile_root=profile.profile_id,
        root_image_id=profile.root_image_id,
        selection_purpose=receipt_verifier.selection_purpose,
    )
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("ZDEX buyback coordinator requires a succinct receipt")
    if not receipt.receipt_bytes:
        raise ValueError("ZDEX buyback coordinator receipt bytes must be nonempty")
    journal_bytes = canonical_global_bytes_v1(lane_journal)
    if len(journal_bytes) > coordinator.max_journal_bytes:
        raise ValueError("ZDEX buyback coordinator journal exceeds its release ceiling")
    receipt_verifier.verify_profile_lane_coordinator_receipt(
        receipt.receipt_bytes,
        profile=profile,
        lane_id=lane_journal.lane_id,
        expected_coordinator_release_id=coordinator.coordinator_release_id,
        expected_image_id=coordinator.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXBuybackLaneCompositionV2(
        _VERIFIED_COORDINATOR_TOKEN_V2,
        _VerifiedCoordinatorFieldsV2(
            composition,
            coordinator.coordinator_release_id,
            coordinator.guest_image_id,
            "0x" + hashlib.sha256(journal_bytes).hexdigest(),
            "0x" + hashlib.sha256(receipt.receipt_bytes).hexdigest(),
            head.authority_root,
            receipt_verifier.binding_root,
        ),
    )


__all__ = [
    "VerifiedZDEXBuybackLaneCompositionV2",
    "ZDEXBuybackLaneCoordinatorReceiptCandidateV2",
    "snapshot_verified_zdex_buyback_lane_composition_v2",
    "verify_zdex_buyback_lane_coordinator_receipt_shadow_v2",
]
