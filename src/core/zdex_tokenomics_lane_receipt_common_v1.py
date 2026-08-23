"""Common immutable marker and receipt checks for ZDEX tokenomics lanes."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from .global_economic_profile_snapshot_v1 import (
    _snapshot_coordinator_release_v1,
    _snapshot_route_release_v1,
)
from .global_economic_proof_v1 import LaneCompositionJournalV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_lane_journal_v1,
)
from .global_settlement_types_v1 import (
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXLaneSuccinctReceiptVerifierV1,
)

VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1: Final = (
    "zenodex/verified-zdex-tokenomics-lane/v1"
)
_VERIFIED_TOKENOMICS_LANE_TOKEN = object()


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


@dataclass(frozen=True, slots=True)
class _ZDEXTokenomicsCoordinatorReceiptExpectationV1:
    route_release: RouteReleaseV1
    coordinator_release: LaneCoordinatorReleaseV1


@dataclass(frozen=True, slots=True)
class _ZDEXTokenomicsLaneBindingV1:
    profile_root: str
    route_release_id: str
    module_release_id: str
    command_occurrence_id: str
    writer_epoch: int
    module_journal_root: str
    module_image_id: str


def _verify_and_build_zdex_tokenomics_lane_v1(
    receipt: ZDEXLaneReceiptEnvelopeV1,
    journal: LaneCompositionJournalV1,
    expectation: _ZDEXTokenomicsCoordinatorReceiptExpectationV1,
    binding: _ZDEXTokenomicsLaneBindingV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsLaneV1:
    if type(receipt) is not ZDEXLaneReceiptEnvelopeV1:
        raise TypeError("ZDEX tokenomics lane receipt must be exact typed data")
    if type(journal) is not LaneCompositionJournalV1:
        raise TypeError("ZDEX tokenomics lane journal must be exact typed data")
    if type(expectation) is not _ZDEXTokenomicsCoordinatorReceiptExpectationV1:
        raise TypeError("ZDEX tokenomics lane expectation must be exact typed data")
    if type(binding) is not _ZDEXTokenomicsLaneBindingV1:
        raise TypeError("ZDEX tokenomics lane binding must be exact typed data")
    _require_exact_dataclass_scalars_v1(
        binding,
        name="ZDEX tokenomics lane binding",
    )
    owned_receipt = ZDEXLaneReceiptEnvelopeV1(
        receipt.receipt_kind,
        receipt.receipt_bytes,
    )
    owned_journal = _snapshot_lane_journal_v1(journal)
    owned_expectation = _ZDEXTokenomicsCoordinatorReceiptExpectationV1(
        _snapshot_route_release_v1(expectation.route_release),
        _snapshot_coordinator_release_v1(expectation.coordinator_release),
    )
    owned_binding = _ZDEXTokenomicsLaneBindingV1(
        binding.profile_root,
        binding.route_release_id,
        binding.module_release_id,
        binding.command_occurrence_id,
        binding.writer_epoch,
        binding.module_journal_root,
        binding.module_image_id,
    )
    if (
        owned_journal.profile_root != owned_binding.profile_root
        or owned_journal.writer_epoch != owned_binding.writer_epoch
        or owned_journal.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
        or owned_journal.coordinator_release_id
        != owned_expectation.coordinator_release.coordinator_release_id
        or owned_journal.command_occurrence_id != owned_binding.command_occurrence_id
        or owned_journal.ordered_module_journal_roots
        != (owned_binding.module_journal_root,)
        or owned_expectation.route_release.route_release_id
        != owned_binding.route_release_id
    ):
        raise ValueError("ZDEX tokenomics verified-lane binding mismatch")
    if owned_receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("ZDEX tokenomics lane verification requires a succinct receipt")
    if not owned_receipt.receipt_bytes:
        raise ValueError("ZDEX tokenomics lane receipt bytes must be nonempty")
    journal_bytes = canonical_global_bytes_v1(owned_journal)
    if len(journal_bytes) > min(
        owned_expectation.route_release.max_journal_bytes,
        owned_expectation.coordinator_release.max_journal_bytes,
    ):
        raise ValueError("ZDEX tokenomics lane journal exceeds release byte ceiling")
    verified_fields = _VerifiedZDEXTokenomicsLaneFieldsV1(
        owned_binding.profile_root,
        owned_binding.route_release_id,
        owned_binding.module_release_id,
        owned_expectation.coordinator_release.coordinator_release_id,
        owned_binding.command_occurrence_id,
        owned_binding.writer_epoch,
        owned_binding.module_journal_root,
        owned_journal.journal_root,
        "0x" + hashlib.sha256(journal_bytes).hexdigest(),
        owned_journal.pre_lane_root,
        owned_journal.post_lane_root,
        owned_journal.effect_plan_root,
        owned_binding.module_image_id,
        owned_expectation.coordinator_release.guest_image_id,
        "0x" + hashlib.sha256(owned_receipt.receipt_bytes).hexdigest(),
        owned_receipt.receipt_kind,
    )
    receipt_verifier.verify_succinct_receipt(
        owned_receipt.receipt_bytes,
        expected_image_id=owned_expectation.coordinator_release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXTokenomicsLaneV1(
        _VERIFIED_TOKENOMICS_LANE_TOKEN,
        verified_fields,
    )


__all__ = [
    "VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1",
    "VerifiedZDEXTokenomicsLaneV1",
]
