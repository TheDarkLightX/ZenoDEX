"""Receipt preparation for one governed ZDEX fee-allocation output.

The pure core snapshots the candidate and governed profile, checks every
binding, recomputes the deterministic allocation and fixes the exact module
receipt request (receipt bytes, module image, canonical journal) plus the
exact marker fields as one prepared subject.  It performs no verifier call.
``src.integration.zdex_fee_allocation_receipt_verification_v1`` executes the
prepared subject on the caller-supplied reference verifier and mints
:class:`VerifiedZDEXFeeAllocationV1` from the executed copy only.

This module remains a shadow boundary because no production RISC0 image is
mounted here.  Neither the prepared subject nor the marker carries publication
or settlement authority.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from typing import Final

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    ReleaseStatusV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_fee_allocation_profile_binding_v1 import (
    GovernedZDEXFeeAllocationProfileV1,
    _revalidate_governed_fee_profile,
    bind_zdex_fee_allocation_shadow_profile_v1,
)
from .zdex_fee_allocation_types_v1 import (
    PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeShareV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
)
from .zdex_fee_allocation_v1 import transition_zdex_fee_allocation_v1
from .zdex_purchase_burn_receipt_verification_v1 import ZDEXLaneReceiptEnvelopeV1

VERIFIED_ZDEX_FEE_ALLOCATION_SCHEMA_V1: Final = (
    "zenodex/verified-zdex-fee-allocation/v1"
)
_VERIFIED_FEE_ALLOCATION_TOKEN = object()


@dataclass(frozen=True, slots=True)
class ZDEXFeeAllocationReceiptCandidateV1:
    occurrence: EconomicCommandOccurrenceV1
    policy: ZDEXFeeAllocationPolicyV1
    pre_state: ZDEXFeeStateV1
    post_state: ZDEXFeeStateV1
    journal: ZDEXFeeAllocationOccurrenceV1
    effects: GlobalEconomicEffectPlanV1
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected = (
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (self.policy, ZDEXFeeAllocationPolicyV1, "policy"),
            (self.pre_state, ZDEXFeeStateV1, "pre-state"),
            (self.post_state, ZDEXFeeStateV1, "post-state"),
            (self.journal, ZDEXFeeAllocationOccurrenceV1, "journal"),
            (self.effects, GlobalEconomicEffectPlanV1, "effects"),
            (self.receipt, ZDEXLaneReceiptEnvelopeV1, "receipt"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(
                    f"ZDEX fee-allocation receipt {label} must be exact typed data"
                )


def _snapshot_fee_destination_amounts_v1(
    values: object,
    *,
    name: str,
) -> tuple[ZDEXFeeDestinationAmountV1, ...]:
    if type(values) is not tuple or any(
        type(value) is not ZDEXFeeDestinationAmountV1 for value in values
    ):
        raise TypeError(f"ZDEX fee-allocation {name} must be exact typed tuple data")
    snapshots = []
    for value in values:
        if (
            type(value.destination) is not ZDEXFeeDestinationV1
            or type(value.allocation_atoms) is not int
        ):
            raise TypeError(
                f"ZDEX fee-allocation {name} must contain exact scalar data"
            )
        snapshots.append(replace(value))
    return tuple(snapshots)


def _snapshot_fee_policy_v1(
    policy: ZDEXFeeAllocationPolicyV1,
) -> ZDEXFeeAllocationPolicyV1:
    if type(policy) is not ZDEXFeeAllocationPolicyV1:
        raise TypeError("ZDEX fee-allocation policy must be exact typed data")
    _require_exact_dataclass_scalars_v1(
        policy,
        name="ZDEX fee-allocation policy",
        tuple_fields=frozenset({"shares"}),
    )
    if type(policy.shares) is not tuple or any(
        type(share) is not ZDEXFeeShareV1 for share in policy.shares
    ):
        raise TypeError("ZDEX fee-allocation shares must be exact typed data")
    shares = []
    for share in policy.shares:
        if (
            type(share.destination) is not ZDEXFeeDestinationV1
            or type(share.share_bps) is not int
        ):
            raise TypeError("ZDEX fee-allocation shares must contain exact scalar data")
        shares.append(replace(share))
    return replace(policy, shares=tuple(shares))


def _snapshot_fee_state_v1(state: ZDEXFeeStateV1) -> ZDEXFeeStateV1:
    if type(state) is not ZDEXFeeStateV1:
        raise TypeError("ZDEX fee-allocation state must be exact typed data")
    _require_exact_dataclass_scalars_v1(
        state,
        name="ZDEX fee-allocation state",
        tuple_fields=frozenset({"destination_balances"}),
    )
    return replace(
        state,
        destination_balances=_snapshot_fee_destination_amounts_v1(
            state.destination_balances,
            name="state destination balances",
        ),
    )


def _snapshot_fee_journal_v1(
    journal: ZDEXFeeAllocationOccurrenceV1,
) -> ZDEXFeeAllocationOccurrenceV1:
    if type(journal) is not ZDEXFeeAllocationOccurrenceV1:
        raise TypeError("ZDEX fee-allocation journal must be exact typed data")
    _require_exact_dataclass_scalars_v1(
        journal,
        name="ZDEX fee-allocation journal",
        tuple_fields=frozenset({"allocations"}),
    )
    return replace(
        journal,
        allocations=_snapshot_fee_destination_amounts_v1(
            journal.allocations,
            name="journal allocations",
        ),
    )


def _snapshot_fee_receipt_candidate_v1(
    candidate: ZDEXFeeAllocationReceiptCandidateV1,
) -> ZDEXFeeAllocationReceiptCandidateV1:
    """Own and exact-check every candidate value before the callback."""

    if type(candidate) is not ZDEXFeeAllocationReceiptCandidateV1:
        raise TypeError("ZDEX fee-allocation receipt candidate must be exact typed data")
    candidate.__post_init__()
    return ZDEXFeeAllocationReceiptCandidateV1(
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        policy=_snapshot_fee_policy_v1(candidate.policy),
        pre_state=_snapshot_fee_state_v1(candidate.pre_state),
        post_state=_snapshot_fee_state_v1(candidate.post_state),
        journal=_snapshot_fee_journal_v1(candidate.journal),
        effects=_snapshot_effect_plan_v1(candidate.effects),
        receipt=ZDEXLaneReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


def _snapshot_governed_fee_profile_v1(
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> GovernedZDEXFeeAllocationProfileV1:
    """Own the profile graph and its selected releases before the callback."""

    return _revalidate_governed_fee_profile(governed)


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXFeeAllocationFieldsV1:
    allocation_route_release_id: str
    authorized_buyback_route_release_id: str
    module_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    journal_root: str
    journal_digest: str
    effect_plan_root: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1
    policy_root: str
    fee_asset_id: str
    fee_ingress_atoms: int
    buyback_quote_atoms: int
    pre_lane_root: str
    post_lane_root: str


class VerifiedZDEXFeeAllocationV1:
    """Immutable marker for the shell's shadow admission result.

    Python module internals are inspectable, so this value never carries
    publication authority. Consumers must independently recompute semantics.
    """

    __slots__ = ("_fields",)
    _fields: _VerifiedZDEXFeeAllocationFieldsV1

    def __init__(
        self,
        token: object,
        fields: _VerifiedZDEXFeeAllocationFieldsV1,
    ) -> None:
        if token is not _VERIFIED_FEE_ALLOCATION_TOKEN:
            raise TypeError("VerifiedZDEXFeeAllocationV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedZDEXFeeAllocationV1 is immutable")

    @property
    def allocation_route_release_id(self) -> str:
        return self._fields.allocation_route_release_id

    @property
    def authorized_buyback_route_release_id(self) -> str:
        return self._fields.authorized_buyback_route_release_id

    @property
    def module_release_id(self) -> str:
        return self._fields.module_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def profile_root(self) -> str:
        return self._fields.profile_root

    @property
    def writer_epoch(self) -> int:
        return self._fields.writer_epoch

    @property
    def journal_root(self) -> str:
        return self._fields.journal_root

    @property
    def journal_digest(self) -> str:
        return self._fields.journal_digest

    @property
    def effect_plan_root(self) -> str:
        return self._fields.effect_plan_root

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
    def policy_root(self) -> str:
        return self._fields.policy_root

    @property
    def fee_asset_id(self) -> str:
        return self._fields.fee_asset_id

    @property
    def fee_ingress_atoms(self) -> int:
        return self._fields.fee_ingress_atoms

    @property
    def buyback_quote_atoms(self) -> int:
        return self._fields.buyback_quote_atoms

    @property
    def pre_lane_root(self) -> str:
        return self._fields.pre_lane_root

    @property
    def post_lane_root(self) -> str:
        return self._fields.post_lane_root

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-zdex-fee-allocation-v1",
            {
                "schema": VERIFIED_ZDEX_FEE_ALLOCATION_SCHEMA_V1,
                "allocation_route_release_id": self.allocation_route_release_id,
                "authorized_buyback_route_release_id": (
                    self.authorized_buyback_route_release_id
                ),
                "module_release_id": self.module_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "profile_root": self.profile_root,
                "writer_epoch": self.writer_epoch,
                "journal_root": self.journal_root,
                "journal_digest": self.journal_digest,
                "effect_plan_root": self.effect_plan_root,
                "expected_image_id": self.expected_image_id,
                "receipt_digest": self.receipt_digest,
                "receipt_kind": self.receipt_kind,
                "policy_root": self.policy_root,
                "fee_asset_id": self.fee_asset_id,
                "fee_ingress_atoms": self.fee_ingress_atoms,
                "buyback_quote_atoms": self.buyback_quote_atoms,
                "pre_lane_root": self.pre_lane_root,
                "post_lane_root": self.post_lane_root,
            },
        )


def _require_candidate_profile_binding(
    candidate: ZDEXFeeAllocationReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> None:
    fields = governed._fields
    if (
        candidate.occurrence.profile_root != fields.profile.profile_id
        or candidate.journal.profile_root != fields.profile.profile_id
        or candidate.journal.writer_epoch != fields.profile.authority_epoch
        or candidate.policy.policy_root != fields.policy_binding.policy_root
    ):
        raise ValueError("ZDEX fee-allocation governed profile binding mismatch")


def _require_release_and_occurrence(
    candidate: ZDEXFeeAllocationReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> None:
    fields = governed._fields
    release = fields.module_release
    occurrence = candidate.occurrence
    # The occurrence pre-root is the route/global pre-state root. The fee
    # substate is bound independently by the recomputed allocation journal.
    if release.status is not ReleaseStatusV1.SHADOW:
        raise ValueError("ZDEX fee-allocation module release must remain SHADOW")
    if (
        release.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
        or PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1 not in release.command_variants
    ):
        raise ValueError("ZDEX fee-allocation module release mismatch")
    if (
        occurrence.command_kind != PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
        or occurrence.route_release_id
        != fields.allocation_route.route_release_id
    ):
        raise ValueError("ZDEX fee-allocation occurrence mismatch")
    if candidate.policy != candidate_zdex_fee_allocation_policy_v1():
        raise ValueError("ZDEX fee-allocation policy is outside this shadow release")


def _recompute(
    candidate: ZDEXFeeAllocationReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> None:
    fields = governed._fields
    journal = candidate.journal
    occurrence = candidate.occurrence
    context = ZDEXFeeAllocationContextV1(
        chain_id=occurrence.chain_id,
        deployment_root=occurrence.deployment_root,
        profile_root=occurrence.profile_root,
        writer_epoch=journal.writer_epoch,
        allocation_route_release_id=fields.allocation_route.route_release_id,
        authorized_buyback_route_release_id=(
            fields.buyback_route.route_release_id
        ),
        tokenomics_module_release_id=fields.module_release.release_id,
        command_occurrence_id=occurrence.occurrence_id,
        policy_root=candidate.policy.policy_root,
    )
    recomputed = transition_zdex_fee_allocation_v1(
        context,
        candidate.pre_state,
        candidate.policy,
        ZDEXFeeAllocationCommandV1(journal.fee_charged_atoms),
    )
    if type(recomputed) is not ZDEXFeeAllocationAcceptedV1:
        raise ValueError("ZDEX fee-allocation transition rejected")
    if (
        recomputed.post_state != candidate.post_state
        or recomputed.occurrence != journal
        or recomputed.effects != candidate.effects
    ):
        raise ValueError("ZDEX fee-allocation journal or effects mismatch")


@dataclass(frozen=True, slots=True)
class PreparedZDEXFeeAllocationReceiptV1:
    """Complete pure execution subject: exact marker fields plus request bytes.

    Data only.  Holding this record is not evidence that any verifier ran; the
    shell executes it and mints the marker from its own detached snapshot.  The
    expected image is the marker's own ``expected_image_id`` (the module
    release image), so no duplicated request field can disagree with the
    minted marker.
    """

    verified_fields: _VerifiedZDEXFeeAllocationFieldsV1
    receipt_bytes: bytes
    expected_journal_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.verified_fields) is not _VerifiedZDEXFeeAllocationFieldsV1:
            raise TypeError("prepared ZDEX fee-allocation fields must be exact typed data")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("prepared ZDEX fee-allocation receipt bytes must be exact bytes")
        if type(self.expected_journal_bytes) is not bytes:
            raise TypeError("prepared ZDEX fee-allocation journal bytes must be exact bytes")

    @property
    def expected_image_id(self) -> str:
        return self.verified_fields.expected_image_id


def _sha256_root_v1(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _copy_verified_zdex_fee_allocation_fields_v1(
    fields: _VerifiedZDEXFeeAllocationFieldsV1,
) -> _VerifiedZDEXFeeAllocationFieldsV1:
    return _VerifiedZDEXFeeAllocationFieldsV1(
        fields.allocation_route_release_id,
        fields.authorized_buyback_route_release_id,
        fields.module_release_id,
        fields.command_occurrence_id,
        fields.profile_root,
        fields.writer_epoch,
        fields.journal_root,
        fields.journal_digest,
        fields.effect_plan_root,
        fields.expected_image_id,
        fields.receipt_digest,
        fields.receipt_kind,
        fields.policy_root,
        fields.fee_asset_id,
        fields.fee_ingress_atoms,
        fields.buyback_quote_atoms,
        fields.pre_lane_root,
        fields.post_lane_root,
    )


def _require_prepared_zdex_fee_allocation_digests_v1(
    prepared: PreparedZDEXFeeAllocationReceiptV1,
) -> None:
    """Bind the digest fields to the exact request bytes that will be executed."""

    fields = prepared.verified_fields
    if fields.receipt_digest != _sha256_root_v1(prepared.receipt_bytes):
        raise ValueError("prepared ZDEX fee-allocation receipt digest mismatch")
    if fields.journal_digest != _sha256_root_v1(prepared.expected_journal_bytes):
        raise ValueError("prepared ZDEX fee-allocation journal digest mismatch")


def snapshot_prepared_zdex_fee_allocation_receipt_v1(
    prepared: PreparedZDEXFeeAllocationReceiptV1,
) -> PreparedZDEXFeeAllocationReceiptV1:
    """Return a validated detached copy of one prepared subject.

    Exact record, scalar and byte types plus digest-to-bytes binding are
    rechecked.  No further release restriction is added: the preparation
    entry point's own upstream validators fix the acceptance domain, exactly
    as before the extraction.
    """

    if type(prepared) is not PreparedZDEXFeeAllocationReceiptV1:
        raise TypeError("prepared ZDEX fee-allocation receipt must be exact typed data")
    fields = prepared.verified_fields
    if type(fields) is not _VerifiedZDEXFeeAllocationFieldsV1:
        raise TypeError("prepared ZDEX fee-allocation fields must be exact typed data")
    _require_exact_dataclass_scalars_v1(fields, name="prepared ZDEX fee-allocation")
    if type(fields.receipt_kind) is not ReceiptKindV1:
        raise TypeError("prepared ZDEX fee-allocation receipt kind is not closed")
    if type(prepared.receipt_bytes) is not bytes:
        raise TypeError("prepared ZDEX fee-allocation receipt bytes must be exact bytes")
    if type(prepared.expected_journal_bytes) is not bytes:
        raise TypeError("prepared ZDEX fee-allocation journal bytes must be exact bytes")
    _require_prepared_zdex_fee_allocation_digests_v1(prepared)
    return PreparedZDEXFeeAllocationReceiptV1(
        _copy_verified_zdex_fee_allocation_fields_v1(fields),
        prepared.receipt_bytes,
        prepared.expected_journal_bytes,
    )


def _build_verified_zdex_fee_allocation_v1(
    prepared: PreparedZDEXFeeAllocationReceiptV1,
) -> VerifiedZDEXFeeAllocationV1:
    """Mint the existing marker from one validated prepared subject.

    Deterministic data construction only.  Post-callback sequencing belongs to
    the shell, which calls this with the detached snapshot it executed.  The
    marker carries no authority and this factory is not a verifier.
    """

    owned = snapshot_prepared_zdex_fee_allocation_receipt_v1(prepared)
    return VerifiedZDEXFeeAllocationV1(
        _VERIFIED_FEE_ALLOCATION_TOKEN,
        owned.verified_fields,
    )


def prepare_zdex_fee_allocation_receipt_v1(
    candidate: ZDEXFeeAllocationReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> PreparedZDEXFeeAllocationReceiptV1:
    """Fix one exact allocation's module receipt request with no verifier call.

    Reject precedence is unchanged from the former effectful entry point:
    candidate snapshot, governed snapshot, profile binding, release and
    occurrence checks, exact transition recomputation, succinct receipt kind,
    nonempty receipt bytes, then the canonical journal byte ceiling
    ``min(module_release.max_journal_bytes, allocation_route.max_journal_bytes)``.
    The expected image is the module release image, never the coordinator.
    """

    owned_candidate = _snapshot_fee_receipt_candidate_v1(candidate)
    owned_governed = _snapshot_governed_fee_profile_v1(governed)
    fields = owned_governed._fields
    _require_candidate_profile_binding(owned_candidate, owned_governed)
    _require_release_and_occurrence(owned_candidate, owned_governed)
    _recompute(owned_candidate, owned_governed)
    receipt = owned_candidate.receipt
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("ZDEX fee-allocation verification requires a succinct receipt")
    if not receipt.receipt_bytes:
        raise ValueError("ZDEX fee-allocation receipt bytes must be nonempty")
    journal_bytes = canonical_global_bytes_v1(owned_candidate.journal)
    if len(journal_bytes) > min(
        fields.module_release.max_journal_bytes,
        fields.allocation_route.max_journal_bytes,
    ):
        raise ValueError("ZDEX fee-allocation journal exceeds release byte ceiling")
    journal = owned_candidate.journal
    verified_fields = _VerifiedZDEXFeeAllocationFieldsV1(
        fields.allocation_route.route_release_id,
        fields.buyback_route.route_release_id,
        fields.module_release.release_id,
        owned_candidate.occurrence.occurrence_id,
        owned_candidate.occurrence.profile_root,
        journal.writer_epoch,
        journal.occurrence_root,
        _sha256_root_v1(journal_bytes),
        owned_candidate.effects.effect_plan_root,
        fields.module_release.guest_image_id,
        _sha256_root_v1(receipt.receipt_bytes),
        receipt.receipt_kind,
        owned_candidate.policy.policy_root,
        journal.fee_asset_id,
        owned_candidate.pre_state.fee_ingress_atoms,
        journal.buyback_quote_atoms,
        journal.pre_lane_root,
        journal.post_lane_root,
    )
    return PreparedZDEXFeeAllocationReceiptV1(
        verified_fields,
        receipt.receipt_bytes,
        journal_bytes,
    )


__all__ = [
    "GovernedZDEXFeeAllocationProfileV1",
    "PreparedZDEXFeeAllocationReceiptV1",
    "VERIFIED_ZDEX_FEE_ALLOCATION_SCHEMA_V1",
    "VerifiedZDEXFeeAllocationV1",
    "ZDEXFeeAllocationReceiptCandidateV1",
    "bind_zdex_fee_allocation_shadow_profile_v1",
    "prepare_zdex_fee_allocation_receipt_v1",
    "snapshot_prepared_zdex_fee_allocation_receipt_v1",
]
