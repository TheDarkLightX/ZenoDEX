"""Profile-selected receipt admission for the SHADOW ZDEX buyback route."""

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
from .global_economic_proof_v1 import ReceiptKindV1, RouteCompositionJournalV1
from .global_economic_refinement_snapshot_v1 import (
    _snapshot_effect_plan_v1,
    _snapshot_route_journal_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    ReleaseStatusV1,
    _require_root,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_atomic_buyback_route_contract_v2 import (
    ZDEXAtomicBuybackRouteAcceptedV2,
)
from .zdex_purchase_burn_receipt_verification_v1 import ZDEXLaneReceiptEnvelopeV1


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackRouteReceiptCandidateV2:
    profile: EconomicProfileSnapshotV1
    composition: ZDEXAtomicBuybackRouteAcceptedV2
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        if (
            type(self.profile) is not EconomicProfileSnapshotV1
            or type(self.composition) is not ZDEXAtomicBuybackRouteAcceptedV2
            or type(self.receipt) is not ZDEXLaneReceiptEnvelopeV1
        ):
            raise TypeError("ZDEX buyback route receipt candidate is not closed")


@dataclass(frozen=True, slots=True)
class _ZDEXAtomicBuybackRouteStatementV2:
    schema: str
    route_journal: RouteCompositionJournalV1
    ordered_leaf_binding_roots: tuple[str, str]
    ordered_lane_assumption_roots: tuple[str, str]
    ordered_lane_binding_roots: tuple[str, str]
    state_delta_root: str
    fee_disposition_root: str

    def __post_init__(self) -> None:
        if type(self.schema) is not str or type(self.route_journal) is not RouteCompositionJournalV1:
            raise TypeError("ZDEX buyback route statement is not closed")
        self.route_journal.__post_init__()
        for root in (
            *self.ordered_leaf_binding_roots,
            *self.ordered_lane_assumption_roots,
            *self.ordered_lane_binding_roots,
            self.state_delta_root,
            self.fee_disposition_root,
        ):
            _require_root(root, name="ZDEX buyback route statement root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "route_journal": self.route_journal,
            "ordered_leaf_binding_roots": self.ordered_leaf_binding_roots,
            "ordered_lane_assumption_roots": self.ordered_lane_assumption_roots,
            "ordered_lane_binding_roots": self.ordered_lane_binding_roots,
            "state_delta_root": self.state_delta_root,
            "fee_disposition_root": self.fee_disposition_root,
        }


def _route_statement_v2(
    composition: ZDEXAtomicBuybackRouteAcceptedV2,
) -> _ZDEXAtomicBuybackRouteStatementV2:
    statement = _ZDEXAtomicBuybackRouteStatementV2(
        "zenodex/zdex-atomic-buyback-route-statement/v2",
        composition.route_journal,
        composition.ordered_leaf_binding_roots,
        composition.ordered_lane_assumption_roots,
        composition.ordered_lane_binding_roots,
        composition.state_delta_root,
        composition.fee_disposition_root,
    )
    statement.__post_init__()
    return statement


def _snapshot_route_composition_v2(
    composition: ZDEXAtomicBuybackRouteAcceptedV2,
) -> ZDEXAtomicBuybackRouteAcceptedV2:
    if type(composition) is not ZDEXAtomicBuybackRouteAcceptedV2:
        raise TypeError("ZDEX buyback route composition must be exact typed data")
    composition.__post_init__()
    owned = ZDEXAtomicBuybackRouteAcceptedV2(
        _snapshot_state_v1(composition.post_state),
        _snapshot_effect_plan_v1(composition.effects),
        _snapshot_route_journal_v1(composition.route_journal),
        composition.ordered_leaf_binding_roots,
        composition.ordered_lane_assumption_roots,
        composition.ordered_lane_binding_roots,
        composition.state_delta_root,
        composition.fee_disposition_root,
    )
    composition.__post_init__()
    return owned


@dataclass(frozen=True, slots=True)
class _VerifiedRouteFieldsV2:
    composition: ZDEXAtomicBuybackRouteAcceptedV2
    expected_image_id: str
    journal_digest: str
    receipt_digest: str
    authority_head_root: str
    verifier_binding_root: str


_VERIFIED_ROUTE_TOKEN_V2 = object()
_VERIFIED_ROUTE_LOCK_V2 = Lock()
_VERIFIED_ROUTE_FIELDS_V2: WeakKeyDictionary[
    VerifiedZDEXAtomicBuybackRouteV2,
    _VerifiedRouteFieldsV2,
] = WeakKeyDictionary()


class VerifiedZDEXAtomicBuybackRouteV2:
    """Data-slot-free route witness registered after receipt admission."""

    __slots__ = ("__weakref__",)

    def __init__(self, token: object, fields: _VerifiedRouteFieldsV2) -> None:
        if token is not _VERIFIED_ROUTE_TOKEN_V2:
            raise TypeError("verified ZDEX buyback route is verifier-constructed")
        if type(fields) is not _VerifiedRouteFieldsV2:
            raise TypeError("verified ZDEX buyback route fields are not closed")
        _register_verified_route_v2(self, fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("verified ZDEX buyback route is immutable")

    @property
    def profile_root(self) -> str:
        return _verified_route_fields_v2(self).composition.route_journal.profile_root

    @property
    def writer_epoch(self) -> int:
        return _verified_route_fields_v2(self).composition.route_journal.writer_epoch

    @property
    def route_release_id(self) -> str:
        return _verified_route_fields_v2(
            self
        ).composition.route_journal.route_release_id

    @property
    def command_occurrence_id(self) -> str:
        return _verified_route_fields_v2(
            self
        ).composition.route_journal.command_occurrence_id

    @property
    def pre_state_root(self) -> str:
        return _verified_route_fields_v2(self).composition.route_journal.pre_state_root

    @property
    def post_state_root(self) -> str:
        return _verified_route_fields_v2(self).composition.route_journal.post_state_root

    @property
    def journal_root(self) -> str:
        return _verified_route_fields_v2(self).composition.route_journal.journal_root

    @property
    def authority_head_root(self) -> str:
        return _verified_route_fields_v2(self).authority_head_root

    @property
    def verifier_binding_root(self) -> str:
        return _verified_route_fields_v2(self).verifier_binding_root

    @property
    def assumption_root(self) -> str:
        fields = _verified_route_fields_v2(self)
        composition = fields.composition
        return hash_global_v1(
            "verified-zdex-atomic-buyback-route-assumption-v2",
            {
                "route_journal_root": composition.route_journal.journal_root,
                "effect_plan_root": composition.effects.effect_plan_root,
                "ordered_lane_assumption_roots": (
                    composition.ordered_lane_assumption_roots
                ),
                "state_delta_root": composition.state_delta_root,
                "fee_disposition_root": composition.fee_disposition_root,
                "expected_image_id": fields.expected_image_id,
            },
        )

    @property
    def binding_root(self) -> str:
        fields = _verified_route_fields_v2(self)
        return hash_global_v1(
            "verified-zdex-atomic-buyback-route-v2",
            {
                "assumption_root": self.assumption_root,
                "ordered_leaf_binding_roots": (
                    fields.composition.ordered_leaf_binding_roots
                ),
                "ordered_lane_binding_roots": (
                    fields.composition.ordered_lane_binding_roots
                ),
                "journal_digest": fields.journal_digest,
                "receipt_digest": fields.receipt_digest,
                "authority_head_root": fields.authority_head_root,
                "verifier_binding_root": fields.verifier_binding_root,
            },
        )


def _register_verified_route_v2(
    handle: VerifiedZDEXAtomicBuybackRouteV2,
    fields: _VerifiedRouteFieldsV2,
) -> None:
    fields.composition.__post_init__()
    for name in (
        "expected_image_id",
        "journal_digest",
        "receipt_digest",
        "authority_head_root",
        "verifier_binding_root",
    ):
        value = object.__getattribute__(fields, name)
        if type(value) is not str:
            raise TypeError(f"verified ZDEX buyback route {name} must be exact str")
        _require_root(value, name=f"verified ZDEX buyback route {name}")
    with _VERIFIED_ROUTE_LOCK_V2:
        if handle in _VERIFIED_ROUTE_FIELDS_V2:
            raise TypeError("verified ZDEX buyback route is already registered")
        _VERIFIED_ROUTE_FIELDS_V2[handle] = fields


def _verified_route_fields_v2(
    handle: VerifiedZDEXAtomicBuybackRouteV2,
) -> _VerifiedRouteFieldsV2:
    if type(handle) is not VerifiedZDEXAtomicBuybackRouteV2:
        raise TypeError("verified ZDEX buyback route must have an exact type")
    with _VERIFIED_ROUTE_LOCK_V2:
        fields = _VERIFIED_ROUTE_FIELDS_V2.get(handle)
    if fields is None:
        raise TypeError("verified ZDEX buyback route is not registered")
    return fields


def snapshot_verified_zdex_atomic_buyback_route_v2(
    verified: VerifiedZDEXAtomicBuybackRouteV2,
) -> ZDEXAtomicBuybackRouteAcceptedV2:
    return _snapshot_route_composition_v2(_verified_route_fields_v2(verified).composition)


def verify_zdex_atomic_buyback_route_receipt_shadow_v2(
    candidate: ZDEXAtomicBuybackRouteReceiptCandidateV2,
    *,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXAtomicBuybackRouteV2:
    """Admit the exact route journal under its current SHADOW release."""

    if type(candidate) is not ZDEXAtomicBuybackRouteReceiptCandidateV2:
        raise TypeError("ZDEX buyback route candidate must be exact typed data")
    candidate.__post_init__()
    profile = snapshot_economic_profile_v1(candidate.profile)
    composition = _snapshot_route_composition_v2(candidate.composition)
    receipt = ZDEXLaneReceiptEnvelopeV1(
        candidate.receipt.receipt_kind,
        candidate.receipt.receipt_bytes,
    )
    if type(authority_head) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("ZDEX buyback route authority head is not closed")
    head = replace(authority_head)
    journal = composition.route_journal
    selected = tuple(
        route
        for route in profile.route_registry.routes
        if route.route_release_id == journal.route_release_id
    )
    if len(selected) != 1:
        raise ValueError("ZDEX buyback route release is outside the profile")
    route = selected[0]
    if (
        head.status is not GlobalEconomicAuthorityStatusV1.ACTIVE
        or head.chain_id != journal.chain_id
        or head.deployment_root != journal.deployment_root
        or head.profile_root != profile.profile_id
        or head.profile_root != journal.profile_root
        or head.writer_epoch != profile.authority_epoch
        or head.writer_epoch != journal.writer_epoch
        or head.verifier_registry_root != profile.verifier_registry_root
        or head.verifier_release_id != receipt_verifier.release_id
        or head.verifier_binding_root != receipt_verifier.binding_root
        or head.root_image_id != profile.root_image_id
        or route.status is not ReleaseStatusV1.SHADOW
        or route.accepts_new_objects
    ):
        raise ValueError("ZDEX buyback route authority binding mismatch")
    receipt_verifier.require_binding(
        verifier_registry_root=profile.verifier_registry_root,
        deployment_root=head.deployment_root,
        profile_root=profile.profile_id,
        root_image_id=profile.root_image_id,
        selection_purpose=receipt_verifier.selection_purpose,
    )
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("ZDEX buyback route requires a succinct receipt")
    if not receipt.receipt_bytes:
        raise ValueError("ZDEX buyback route receipt bytes must be nonempty")
    journal_bytes = canonical_global_bytes_v1(_route_statement_v2(composition))
    if len(journal_bytes) > route.max_journal_bytes:
        raise ValueError("ZDEX buyback route journal exceeds its release ceiling")
    receipt_verifier.verify_profile_route_receipt(
        receipt.receipt_bytes,
        profile=profile,
        expected_route_release_id=route.route_release_id,
        expected_image_id=route.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXAtomicBuybackRouteV2(
        _VERIFIED_ROUTE_TOKEN_V2,
        _VerifiedRouteFieldsV2(
            composition,
            route.guest_image_id,
            "0x" + hashlib.sha256(journal_bytes).hexdigest(),
            "0x" + hashlib.sha256(receipt.receipt_bytes).hexdigest(),
            head.authority_root,
            receipt_verifier.binding_root,
        ),
    )


__all__ = [
    "VerifiedZDEXAtomicBuybackRouteV2",
    "ZDEXAtomicBuybackRouteReceiptCandidateV2",
    "snapshot_verified_zdex_atomic_buyback_route_v2",
    "verify_zdex_atomic_buyback_route_receipt_shadow_v2",
]
