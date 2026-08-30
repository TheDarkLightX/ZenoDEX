"""Profile-selected receipt admission for the ZDEX buyback successor leaves.

The boundary owns validated journal/effect snapshots before invoking the bound
receipt verifier.  Successful verification creates process-local opaque leaf
handles used by the later route composer.  This SHADOW path grants no commit,
settlement, epoch, migration, or production authority.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from threading import Lock
from typing import Final
from weakref import WeakKeyDictionary

from .economic_receipt_verifier_deployment_v1 import BoundEconomicReceiptVerifierV1
from .global_economic_authority_head_v1 import GlobalEconomicAuthorityHeadV1
from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_profile_snapshot_v1 import (
    _snapshot_lane_release_v1,
    _snapshot_route_release_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    RouteReleaseV1,
    _require_nonnegative_int,
    _require_root,
    hash_global_v1,
)
from .zdex_atomic_buyback_route_types_v2 import (
    require_zdex_atomic_buyback_route_shape_v2,
)
from .zdex_buyback_leaf_snapshot_v2 import (
    ZDEXSpotBuybackLeafSnapshotV2,
    ZDEXTokenomicsBuybackLeafSnapshotV2,
    _snapshot_spot_journal_v2,
    _snapshot_tokenomics_journal_v2,
    snapshot_zdex_spot_buyback_leaf_v2,
    snapshot_zdex_tokenomics_buyback_leaf_v2,
)
from .zdex_buyback_price_safety_v1 import (
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
)
from .zdex_buyback_spend_v1 import ZDEX_BUYBACK_SPEND_POLICY_KIND_V1
from .zdex_fee_allocation_types_v1 import ZDEX_FEE_ALLOCATION_POLICY_KIND_V1
from .zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneReceiptEnvelopeV1,
    _require_current_shadow_authority_v1,
)
from .zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
)
from .zdex_spot_buyback_transition_v2 import ZDEXSpotBuybackAcceptedV2
from .zdex_tokenomics_buyback_transition_v1 import (
    ZDEXTokenomicsBuybackAuthorityContextV1,
    _context_root_v1,
)
from .zdex_tokenomics_buyback_transition_v2 import (
    ZDEXTokenomicsBuybackAcceptedV2,
    ZDEXTokenomicsBuybackInputV2,
)

VERIFIED_ZDEX_SPOT_BUYBACK_LEAF_SCHEMA_V2: Final = (
    "zenodex/verified-zdex-spot-buyback-leaf/v2"
)
VERIFIED_ZDEX_TOKENOMICS_BUYBACK_LEAF_SCHEMA_V2: Final = (
    "zenodex/verified-zdex-tokenomics-buyback-leaf/v2"
)


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackReceiptCandidateV2:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    accepted: ZDEXSpotBuybackAcceptedV2
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        _require_candidate_types_v2(
            self.route_release,
            self.module_release,
            self.occurrence,
            self.accepted,
            self.receipt,
            expected_accepted=ZDEXSpotBuybackAcceptedV2,
        )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackReceiptCandidateV2:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    accepted: ZDEXTokenomicsBuybackAcceptedV2
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        _require_candidate_types_v2(
            self.route_release,
            self.module_release,
            self.occurrence,
            self.accepted,
            self.receipt,
            expected_accepted=ZDEXTokenomicsBuybackAcceptedV2,
        )


def _require_candidate_types_v2(
    route_release: object,
    module_release: object,
    occurrence: object,
    accepted: object,
    receipt: object,
    *,
    expected_accepted: type[object],
) -> None:
    expected = (
        (route_release, RouteReleaseV1, "route release"),
        (module_release, LaneModuleReleaseV1, "module release"),
        (occurrence, EconomicCommandOccurrenceV1, "occurrence"),
        (accepted, expected_accepted, "accepted result"),
        (receipt, ZDEXLaneReceiptEnvelopeV1, "receipt"),
    )
    for value, expected_type, label in expected:
        if type(value) is not expected_type:
            raise TypeError(f"ZDEX buyback receipt {label} must be exact typed data")


@dataclass(frozen=True, slots=True)
class _OwnedSpotReceiptCandidateV2:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    leaf: ZDEXSpotBuybackLeafSnapshotV2
    receipt: ZDEXLaneReceiptEnvelopeV1


@dataclass(frozen=True, slots=True)
class _OwnedTokenomicsAuthorityV2:
    chain_id: str
    deployment_root: str
    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    writer_epoch: int
    current_height: int
    spot_module_release_id: str
    tokenomics_module_release_id: str
    execution_policy_root: str
    fee_policy_root: str
    spend_policy_root: str
    hyperdeflation_policy_root: str
    price_policy_root: str
    context_root: str


@dataclass(frozen=True, slots=True)
class _OwnedTokenomicsReceiptCandidateV2:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    leaf: ZDEXTokenomicsBuybackLeafSnapshotV2
    authority: _OwnedTokenomicsAuthorityV2
    receipt: ZDEXLaneReceiptEnvelopeV1


def _snapshot_receipt_v2(receipt: ZDEXLaneReceiptEnvelopeV1) -> ZDEXLaneReceiptEnvelopeV1:
    if type(receipt) is not ZDEXLaneReceiptEnvelopeV1:
        raise TypeError("ZDEX buyback receipt envelope must be exact typed data")
    return ZDEXLaneReceiptEnvelopeV1(receipt.receipt_kind, receipt.receipt_bytes)


def _snapshot_spot_candidate_v2(
    candidate: ZDEXSpotBuybackReceiptCandidateV2,
) -> _OwnedSpotReceiptCandidateV2:
    if type(candidate) is not ZDEXSpotBuybackReceiptCandidateV2:
        raise TypeError("Spot buyback receipt candidate must be exact typed data")
    candidate.__post_init__()
    return _OwnedSpotReceiptCandidateV2(
        _snapshot_route_release_v1(candidate.route_release),
        _snapshot_lane_release_v1(candidate.module_release),
        _snapshot_occurrence_v1(candidate.occurrence),
        snapshot_zdex_spot_buyback_leaf_v2(candidate.accepted),
        _snapshot_receipt_v2(candidate.receipt),
    )


def _snapshot_tokenomics_candidate_v2(
    candidate: ZDEXTokenomicsBuybackReceiptCandidateV2,
) -> _OwnedTokenomicsReceiptCandidateV2:
    if type(candidate) is not ZDEXTokenomicsBuybackReceiptCandidateV2:
        raise TypeError("Tokenomics buyback receipt candidate must be exact typed data")
    candidate.__post_init__()
    accepted = candidate.accepted
    accepted.validate()
    subject = object.__getattribute__(accepted, "_subject")
    if type(subject) is not ZDEXTokenomicsBuybackInputV2:
        raise TypeError("Tokenomics buyback accepted subject is not closed")
    intent_input = subject.intent_input
    authority = object.__getattribute__(intent_input, "authority")
    if type(authority) is not ZDEXTokenomicsBuybackAuthorityContextV1:
        raise TypeError("Tokenomics buyback accepted authority is not closed")
    context_root = _context_root_v1(authority, intent_input.safe_limit_port)
    owned_authority = _OwnedTokenomicsAuthorityV2(
        authority.chain_id,
        authority.deployment_root,
        authority.profile_root,
        authority.route_release_id,
        authority.command_occurrence_id,
        authority.global_pre_state_root,
        authority.writer_epoch,
        authority.current_height,
        authority.spot_module_release_id,
        authority.tokenomics_module_release_id,
        authority.execution_policy.policy_root,
        authority.fee_policy.policy_root,
        authority.spend_policy.policy_root,
        authority.hyperdeflation_policy.policy_root,
        authority.price_policy_root,
        context_root,
    )
    leaf = snapshot_zdex_tokenomics_buyback_leaf_v2(accepted)
    if leaf.journal.context_root != context_root:
        raise ValueError("Tokenomics buyback context preimage does not match its journal")
    accepted.validate()
    return _OwnedTokenomicsReceiptCandidateV2(
        _snapshot_route_release_v1(candidate.route_release),
        _snapshot_lane_release_v1(candidate.module_release),
        _snapshot_occurrence_v1(candidate.occurrence),
        leaf,
        owned_authority,
        _snapshot_receipt_v2(candidate.receipt),
    )


def _require_release_v2(
    route: RouteReleaseV1,
    release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    lane_id: LaneIdV1,
    route_index: int,
) -> None:
    require_zdex_atomic_buyback_route_shape_v2(route)
    if release.lane_id is not lane_id:
        raise ValueError("ZDEX buyback module release lane mismatch")
    if route.module_release_ids[route_index] != release.release_id:
        raise ValueError("ZDEX buyback route module release mismatch")
    if PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1 not in release.command_variants:
        raise ValueError("ZDEX buyback module release lacks the command")
    if (
        occurrence.command_kind != route.command_kind
        or occurrence.route_release_id != route.route_release_id
    ):
        raise ValueError("ZDEX buyback occurrence route mismatch")


def _require_policy_root_v2(
    registry: EconomicPolicyRegistryV1,
    *,
    policy_kind: str,
    expected_root: str,
) -> None:
    binding = registry.require_binding(
        policy_kind=policy_kind,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )
    if binding.policy_root != expected_root:
        raise ValueError(f"ZDEX buyback {policy_kind} binding mismatch")


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXBuybackLeafFieldsV2:
    lane_id: LaneIdV1
    route_release_id: str
    module_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    journal_root: str
    journal_digest: str
    effect_plan_root: str
    snapshot_root: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1
    authority_head_root: str
    verifier_binding_root: str
    policy_registry_root: str
    execution_policy_root: str
    price_policy_root: str
    issue_burn_policy_root: str
    snapshot: ZDEXSpotBuybackLeafSnapshotV2 | ZDEXTokenomicsBuybackLeafSnapshotV2


_VERIFIED_SPOT_TOKEN_V2 = object()
_VERIFIED_TOKENOMICS_TOKEN_V2 = object()
_VERIFIED_LEAF_LOCK_V2 = Lock()
_VERIFIED_LEAF_FIELDS_V2: WeakKeyDictionary[
    _VerifiedZDEXBuybackLeafV2,
    _VerifiedZDEXBuybackLeafFieldsV2,
] = WeakKeyDictionary()


class _VerifiedZDEXBuybackLeafV2:
    __slots__ = ("__weakref__",)
    _token: object
    _schema: str
    _domain: str
    _lane_id: LaneIdV1

    def __init__(self, token: object, fields: _VerifiedZDEXBuybackLeafFieldsV2) -> None:
        if token is not self._token:
            raise TypeError(f"{type(self).__name__} is verifier-constructed")
        if type(fields) is not _VerifiedZDEXBuybackLeafFieldsV2:
            raise TypeError("verified ZDEX buyback leaf fields are not closed")
        if fields.lane_id is not self._lane_id:
            raise TypeError("verified ZDEX buyback leaf lane is inconsistent")
        _register_verified_leaf_v2(self, fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError(f"{type(self).__name__} is immutable")

    @property
    def route_release_id(self) -> str:
        return _verified_leaf_fields_v2(self).route_release_id

    @property
    def module_release_id(self) -> str:
        return _verified_leaf_fields_v2(self).module_release_id

    @property
    def command_occurrence_id(self) -> str:
        return _verified_leaf_fields_v2(self).command_occurrence_id

    @property
    def profile_root(self) -> str:
        return _verified_leaf_fields_v2(self).profile_root

    @property
    def writer_epoch(self) -> int:
        return _verified_leaf_fields_v2(self).writer_epoch

    @property
    def journal_root(self) -> str:
        return _verified_leaf_fields_v2(self).journal_root

    @property
    def effect_plan_root(self) -> str:
        return _verified_leaf_fields_v2(self).effect_plan_root

    @property
    def snapshot_root(self) -> str:
        return _verified_leaf_fields_v2(self).snapshot_root

    @property
    def authority_head_root(self) -> str:
        return _verified_leaf_fields_v2(self).authority_head_root

    @property
    def verifier_binding_root(self) -> str:
        return _verified_leaf_fields_v2(self).verifier_binding_root

    @property
    def policy_registry_root(self) -> str:
        return _verified_leaf_fields_v2(self).policy_registry_root

    @property
    def execution_policy_root(self) -> str:
        return _verified_leaf_fields_v2(self).execution_policy_root

    @property
    def price_policy_root(self) -> str:
        return _verified_leaf_fields_v2(self).price_policy_root

    @property
    def issue_burn_policy_root(self) -> str:
        return _verified_leaf_fields_v2(self).issue_burn_policy_root

    def _claim_body(self) -> dict[str, object]:
        fields = _verified_leaf_fields_v2(self)
        return {
            "schema": self._schema,
            "lane_id": fields.lane_id,
            "route_release_id": fields.route_release_id,
            "module_release_id": fields.module_release_id,
            "command_occurrence_id": fields.command_occurrence_id,
            "profile_root": fields.profile_root,
            "writer_epoch": fields.writer_epoch,
            "journal_root": fields.journal_root,
            "journal_digest": fields.journal_digest,
            "effect_plan_root": fields.effect_plan_root,
            "snapshot_root": fields.snapshot_root,
            "expected_image_id": fields.expected_image_id,
        }

    @property
    def assumption_root(self) -> str:
        return hash_global_v1(self._domain + "-assumption", self._claim_body())

    @property
    def binding_root(self) -> str:
        fields = _verified_leaf_fields_v2(self)
        return hash_global_v1(
            self._domain,
            {
                **self._claim_body(),
                "receipt_digest": fields.receipt_digest,
                "receipt_kind": fields.receipt_kind,
                "authority_head_root": fields.authority_head_root,
                "verifier_binding_root": fields.verifier_binding_root,
                "policy_registry_root": fields.policy_registry_root,
                "execution_policy_root": fields.execution_policy_root,
                "price_policy_root": fields.price_policy_root,
                "issue_burn_policy_root": fields.issue_burn_policy_root,
            },
        )


class VerifiedZDEXSpotBuybackLeafV2(_VerifiedZDEXBuybackLeafV2):
    _token = _VERIFIED_SPOT_TOKEN_V2
    _schema = VERIFIED_ZDEX_SPOT_BUYBACK_LEAF_SCHEMA_V2
    _domain = "verified-zdex-spot-buyback-leaf-v2"
    _lane_id = LaneIdV1.SPOT_LIQUIDITY


class VerifiedZDEXTokenomicsBuybackLeafV2(_VerifiedZDEXBuybackLeafV2):
    _token = _VERIFIED_TOKENOMICS_TOKEN_V2
    _schema = VERIFIED_ZDEX_TOKENOMICS_BUYBACK_LEAF_SCHEMA_V2
    _domain = "verified-zdex-tokenomics-buyback-leaf-v2"
    _lane_id = LaneIdV1.ZDEX_TOKENOMICS


def _register_verified_leaf_v2(
    handle: _VerifiedZDEXBuybackLeafV2,
    fields: _VerifiedZDEXBuybackLeafFieldsV2,
) -> None:
    if type(fields.lane_id) is not LaneIdV1:
        raise TypeError("verified ZDEX buyback leaf lane is not closed")
    for name in (
        "route_release_id",
        "module_release_id",
        "command_occurrence_id",
        "profile_root",
        "journal_root",
        "journal_digest",
        "effect_plan_root",
        "snapshot_root",
        "expected_image_id",
        "receipt_digest",
        "authority_head_root",
        "verifier_binding_root",
        "policy_registry_root",
        "execution_policy_root",
        "price_policy_root",
        "issue_burn_policy_root",
    ):
        value = object.__getattribute__(fields, name)
        if type(value) is not str:
            raise TypeError(f"verified ZDEX buyback leaf {name} must be exact str")
        _require_root(value, name=f"verified ZDEX buyback leaf {name}")
    _require_nonnegative_int(
        fields.writer_epoch,
        name="verified ZDEX buyback leaf writer epoch",
    )
    if type(fields.receipt_kind) is not ReceiptKindV1:
        raise TypeError("verified ZDEX buyback leaf receipt kind is not closed")
    expected_snapshot = (
        ZDEXSpotBuybackLeafSnapshotV2
        if fields.lane_id is LaneIdV1.SPOT_LIQUIDITY
        else ZDEXTokenomicsBuybackLeafSnapshotV2
    )
    if type(fields.snapshot) is not expected_snapshot:
        raise TypeError("verified ZDEX buyback leaf snapshot lane is inconsistent")
    fields.snapshot.validate()
    if (
        fields.journal_root != fields.snapshot.journal_root
        or fields.effect_plan_root != fields.snapshot.effect_plan_root
        or fields.snapshot_root != fields.snapshot.snapshot_root
    ):
        raise ValueError("verified ZDEX buyback leaf snapshot binding mismatch")
    with _VERIFIED_LEAF_LOCK_V2:
        if handle in _VERIFIED_LEAF_FIELDS_V2:
            raise TypeError("verified ZDEX buyback leaf is already registered")
        _VERIFIED_LEAF_FIELDS_V2[handle] = fields


def _verified_leaf_fields_v2(
    handle: _VerifiedZDEXBuybackLeafV2,
) -> _VerifiedZDEXBuybackLeafFieldsV2:
    if type(handle) not in {
        VerifiedZDEXSpotBuybackLeafV2,
        VerifiedZDEXTokenomicsBuybackLeafV2,
    }:
        raise TypeError("verified ZDEX buyback leaf must have an exact type")
    with _VERIFIED_LEAF_LOCK_V2:
        fields = _VERIFIED_LEAF_FIELDS_V2.get(handle)
    if fields is None:
        raise TypeError("verified ZDEX buyback leaf is not registered")
    return fields


def snapshot_verified_zdex_spot_buyback_leaf_v2(
    verified: VerifiedZDEXSpotBuybackLeafV2,
) -> ZDEXSpotBuybackLeafSnapshotV2:
    fields = _verified_leaf_fields_v2(verified)
    snapshot = fields.snapshot
    if type(snapshot) is not ZDEXSpotBuybackLeafSnapshotV2:
        raise TypeError("verified Spot buyback leaf snapshot is not closed")
    return ZDEXSpotBuybackLeafSnapshotV2(
        _snapshot_spot_journal_v2(snapshot.journal),
        _snapshot_effect_plan_v1(snapshot.effects),
    )


def snapshot_verified_zdex_tokenomics_buyback_leaf_v2(
    verified: VerifiedZDEXTokenomicsBuybackLeafV2,
) -> ZDEXTokenomicsBuybackLeafSnapshotV2:
    fields = _verified_leaf_fields_v2(verified)
    snapshot = fields.snapshot
    if type(snapshot) is not ZDEXTokenomicsBuybackLeafSnapshotV2:
        raise TypeError("verified Tokenomics buyback leaf snapshot is not closed")
    return ZDEXTokenomicsBuybackLeafSnapshotV2(
        _snapshot_tokenomics_journal_v2(snapshot.journal),
        _snapshot_effect_plan_v1(snapshot.effects),
    )


def _receipt_roots_v2(
    receipt: ZDEXLaneReceiptEnvelopeV1,
    journal_bytes: bytes,
) -> tuple[str, str]:
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("ZDEX buyback leaf verification requires a succinct receipt")
    if not receipt.receipt_bytes:
        raise ValueError("ZDEX buyback leaf receipt bytes must be nonempty")
    return (
        "0x" + hashlib.sha256(journal_bytes).hexdigest(),
        "0x" + hashlib.sha256(receipt.receipt_bytes).hexdigest(),
    )


def _verify_receipt_v2(
    *,
    profile: EconomicProfileSnapshotV1,
    release: LaneModuleReleaseV1,
    lane_id: LaneIdV1,
    journal_bytes: bytes,
    receipt: ZDEXLaneReceiptEnvelopeV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> tuple[str, str]:
    journal_digest, receipt_digest = _receipt_roots_v2(receipt, journal_bytes)
    if len(journal_bytes) > release.max_journal_bytes:
        raise ValueError("ZDEX buyback leaf journal exceeds its release byte ceiling")
    receipt_verifier.verify_profile_lane_receipt(
        receipt.receipt_bytes,
        profile=profile,
        lane_id=lane_id,
        expected_module_release_id=release.release_id,
        expected_image_id=release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return journal_digest, receipt_digest


def _verified_fields_v2(
    *,
    lane_id: LaneIdV1,
    route: RouteReleaseV1,
    release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    leaf: ZDEXSpotBuybackLeafSnapshotV2 | ZDEXTokenomicsBuybackLeafSnapshotV2,
    journal_digest: str,
    receipt_digest: str,
    receipt: ZDEXLaneReceiptEnvelopeV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
    policy_registry: EconomicPolicyRegistryV1,
    execution_policy_root: str,
) -> _VerifiedZDEXBuybackLeafFieldsV2:
    return _VerifiedZDEXBuybackLeafFieldsV2(
        lane_id=lane_id,
        route_release_id=route.route_release_id,
        module_release_id=release.release_id,
        command_occurrence_id=occurrence.occurrence_id,
        profile_root=occurrence.profile_root,
        writer_epoch=authority_head.writer_epoch,
        journal_root=leaf.journal_root,
        journal_digest=journal_digest,
        effect_plan_root=leaf.effect_plan_root,
        snapshot_root=leaf.snapshot_root,
        expected_image_id=release.guest_image_id,
        receipt_digest=receipt_digest,
        receipt_kind=receipt.receipt_kind,
        authority_head_root=authority_head.authority_root,
        verifier_binding_root=receipt_verifier.binding_root,
        policy_registry_root=policy_registry.registry_root,
        execution_policy_root=execution_policy_root,
        price_policy_root=route.oracle_policy_root,
        issue_burn_policy_root=route.issue_burn_policy_root,
        snapshot=leaf,
    )


def verify_governed_zdex_spot_buyback_receipt_shadow_v2(
    candidate: ZDEXSpotBuybackReceiptCandidateV2,
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXSpotBuybackLeafV2:
    """Authenticate one Spot successor journal under current SHADOW authority."""

    owned = _snapshot_spot_candidate_v2(candidate)
    _require_release_v2(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        route_index=0,
    )
    owned_head = replace(authority_head)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        authority_head=owned_head,
        receipt_verifier=receipt_verifier,
    )
    owned_registry = snapshot_economic_policy_registry_v1(policy_registry)
    if owned_registry.registry_root != owned_profile.policy_registry_root:
        raise ValueError("ZDEX Spot buyback policy registry mismatch")
    journal = owned.leaf.journal
    context = journal.context
    coordinates = context.coordinates
    bindings = (
        (context.chain_id, owned.occurrence.chain_id),
        (context.deployment_root, owned.occurrence.deployment_root),
        (coordinates.profile_root, owned.occurrence.profile_root),
        (coordinates.route_release_id, owned.route_release.route_release_id),
        (coordinates.command_occurrence_id, owned.occurrence.occurrence_id),
        (coordinates.global_pre_state_root, owned.occurrence.pre_state_root),
        (context.writer_epoch, owned_profile.authority_epoch),
        (context.current_height, owned.occurrence.height),
        (context.spot_module_release_id, owned.module_release.release_id),
        (context.tokenomics_module_release_id, owned.route_release.module_release_ids[1]),
        (context.price_policy_root, owned.route_release.oracle_policy_root),
    )
    if any(actual != expected for actual, expected in bindings):
        raise ValueError("ZDEX Spot buyback occurrence or release binding mismatch")
    _require_policy_root_v2(
        owned_registry,
        policy_kind=ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
        expected_root=context.execution_policy_root,
    )
    _require_policy_root_v2(
        owned_registry,
        policy_kind=ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
        expected_root=context.price_policy_root,
    )
    journal_digest, receipt_digest = _verify_receipt_v2(
        profile=owned_profile,
        release=owned.module_release,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        journal_bytes=owned.leaf.journal_bytes,
        receipt=owned.receipt,
        receipt_verifier=receipt_verifier,
    )
    return VerifiedZDEXSpotBuybackLeafV2(
        _VERIFIED_SPOT_TOKEN_V2,
        _verified_fields_v2(
            lane_id=LaneIdV1.SPOT_LIQUIDITY,
            route=owned.route_release,
            release=owned.module_release,
            occurrence=owned.occurrence,
            leaf=owned.leaf,
            journal_digest=journal_digest,
            receipt_digest=receipt_digest,
            receipt=owned.receipt,
            authority_head=owned_head,
            receipt_verifier=receipt_verifier,
            policy_registry=owned_registry,
            execution_policy_root=context.execution_policy_root,
        ),
    )


def verify_governed_zdex_tokenomics_buyback_receipt_shadow_v2(
    candidate: ZDEXTokenomicsBuybackReceiptCandidateV2,
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsBuybackLeafV2:
    """Authenticate one Tokenomics successor journal under current authority."""

    owned = _snapshot_tokenomics_candidate_v2(candidate)
    _require_release_v2(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        route_index=1,
    )
    owned_head = replace(authority_head)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        authority_head=owned_head,
        receipt_verifier=receipt_verifier,
    )
    owned_registry = snapshot_economic_policy_registry_v1(policy_registry)
    if owned_registry.registry_root != owned_profile.policy_registry_root:
        raise ValueError("ZDEX Tokenomics buyback policy registry mismatch")
    authority = owned.authority
    bindings = (
        (authority.chain_id, owned.occurrence.chain_id),
        (authority.deployment_root, owned.occurrence.deployment_root),
        (authority.profile_root, owned.occurrence.profile_root),
        (authority.route_release_id, owned.route_release.route_release_id),
        (authority.command_occurrence_id, owned.occurrence.occurrence_id),
        (authority.global_pre_state_root, owned.occurrence.pre_state_root),
        (authority.writer_epoch, owned_profile.authority_epoch),
        (authority.current_height, owned.occurrence.height),
        (authority.spot_module_release_id, owned.route_release.module_release_ids[0]),
        (authority.tokenomics_module_release_id, owned.module_release.release_id),
        (authority.price_policy_root, owned.route_release.oracle_policy_root),
        (authority.hyperdeflation_policy_root, owned.route_release.issue_burn_policy_root),
        (authority.context_root, owned.leaf.journal.context_root),
        (
            owned.leaf.effects.occurrence_consumptions,
            (owned.occurrence.occurrence_id,),
        ),
    )
    if any(actual != expected for actual, expected in bindings):
        raise ValueError("ZDEX Tokenomics buyback occurrence or release binding mismatch")
    for policy_kind, expected_root in (
        (ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1, authority.execution_policy_root),
        (ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1, authority.price_policy_root),
        (ZDEX_FEE_ALLOCATION_POLICY_KIND_V1, authority.fee_policy_root),
        (ZDEX_BUYBACK_SPEND_POLICY_KIND_V1, authority.spend_policy_root),
    ):
        _require_policy_root_v2(
            owned_registry,
            policy_kind=policy_kind,
            expected_root=expected_root,
        )
    journal_digest, receipt_digest = _verify_receipt_v2(
        profile=owned_profile,
        release=owned.module_release,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        journal_bytes=owned.leaf.journal_bytes,
        receipt=owned.receipt,
        receipt_verifier=receipt_verifier,
    )
    return VerifiedZDEXTokenomicsBuybackLeafV2(
        _VERIFIED_TOKENOMICS_TOKEN_V2,
        _verified_fields_v2(
            lane_id=LaneIdV1.ZDEX_TOKENOMICS,
            route=owned.route_release,
            release=owned.module_release,
            occurrence=owned.occurrence,
            leaf=owned.leaf,
            journal_digest=journal_digest,
            receipt_digest=receipt_digest,
            receipt=owned.receipt,
            authority_head=owned_head,
            receipt_verifier=receipt_verifier,
            policy_registry=owned_registry,
            execution_policy_root=authority.execution_policy_root,
        ),
    )


__all__ = [
    "VERIFIED_ZDEX_SPOT_BUYBACK_LEAF_SCHEMA_V2",
    "VERIFIED_ZDEX_TOKENOMICS_BUYBACK_LEAF_SCHEMA_V2",
    "VerifiedZDEXSpotBuybackLeafV2",
    "VerifiedZDEXTokenomicsBuybackLeafV2",
    "ZDEXSpotBuybackReceiptCandidateV2",
    "ZDEXTokenomicsBuybackReceiptCandidateV2",
    "snapshot_verified_zdex_spot_buyback_leaf_v2",
    "snapshot_verified_zdex_tokenomics_buyback_leaf_v2",
    "verify_governed_zdex_spot_buyback_receipt_shadow_v2",
    "verify_governed_zdex_tokenomics_buyback_receipt_shadow_v2",
]
