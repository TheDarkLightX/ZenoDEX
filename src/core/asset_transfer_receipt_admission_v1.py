"""Receipt admission for the ASSET_TRANSFER allocation fragment (C9a).

``verify_asset_transfer_fragment_receipt_v1`` takes the receipt-verified
module witness (``VerifiedLaneModuleTransitionV1``, mintable only by
``verify_asset_transfer_lane_module_receipt_v1`` after a succinct-receipt
check against the recomputed module journal under an ACTIVE_NEW release
image), binds the caller's accepted value to that witness root for root,
re-runs the wave-B fragment producer, and mints the opaque
``VerifiedLaneAllocationFragmentV1`` witness. The certificate registry still
keeps ASSET_TRANSFER at NO_PRODUCER: nothing consumes this witness on an
acceptance path until C9b lands the registry flip behind a type gate.

Research-only evidence. It grants no writer, verifier, release, or
publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .asset_transfer_lane_module_v1 import AssetTransferLaneModuleAcceptedV1
from .global_accounting_allocation_certificate_v1 import (
    ClaimantEntitlementRowV1,
    LaneAllocationFragmentV1,
)
from .global_accounting_lane_producers_v1 import (
    ReceiptBackedProducerRejectedV1,
    produce_asset_transfer_fragment_v1,
)
from .global_settlement_types_v1 import LaneIdV1, LaneStateRootV1, _require_root
from .lane_module_receipt_verification_v1 import (
    ReceiptKindV1,
    VerifiedLaneModuleTransitionV1,
)

RECEIPT_ADMISSION_SCHEMA_V1: Final = "zenodex/asset-transfer-receipt-admission/v1"

_VERIFIED_FRAGMENT_TOKEN: Final = object()


class ReceiptWitnessRejectCodeV1(str, Enum):
    """Closed witness-binding rejects, checked before the producer runs."""

    WITNESS_KIND_DRIFT = "WITNESS_KIND_DRIFT"
    WITNESS_JOURNAL_ROOT_DRIFT = "WITNESS_JOURNAL_ROOT_DRIFT"
    WITNESS_STATEMENT_ROOT_DRIFT = "WITNESS_STATEMENT_ROOT_DRIFT"
    WITNESS_OCCURRENCE_DRIFT = "WITNESS_OCCURRENCE_DRIFT"
    WITNESS_BINDING_ROOT_DRIFT = "WITNESS_BINDING_ROOT_DRIFT"


@dataclass(frozen=True, slots=True)
class ReceiptWitnessRejectedV1:
    """A witness-binding refusal: nothing is minted, every input left unchanged."""

    code: ReceiptWitnessRejectCodeV1
    lane_id: LaneIdV1
    committed_lane_root: str
    detail: str

    def __post_init__(self) -> None:
        if type(self.code) is not ReceiptWitnessRejectCodeV1:
            raise TypeError("receipt witness reject code is not closed")
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("receipt witness lane id is not closed")
        _require_root(
            self.committed_lane_root,
            name="receipt witness committed lane root",
            allow_zero=True,
        )
        if not isinstance(self.detail, str) or not self.detail or len(self.detail) > 200:
            raise ValueError("receipt witness detail must be a short non-empty string")


@dataclass(frozen=True, slots=True)
class _VerifiedFragmentFieldsV1:
    fragment: LaneAllocationFragmentV1
    module_journal_root: str
    receipt_digest: str
    expected_image_id: str


class VerifiedLaneAllocationFragmentV1:
    """Opaque receipt-admitted fragment, produced only by this verifier."""

    _fields: _VerifiedFragmentFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _VerifiedFragmentFieldsV1) -> None:
        if token is not _VERIFIED_FRAGMENT_TOKEN:
            raise TypeError("VerifiedLaneAllocationFragmentV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedLaneAllocationFragmentV1 is immutable")

    @property
    def fragment(self) -> LaneAllocationFragmentV1:
        return self._fields.fragment

    @property
    def module_journal_root(self) -> str:
        return self._fields.module_journal_root

    @property
    def receipt_digest(self) -> str:
        return self._fields.receipt_digest

    @property
    def expected_image_id(self) -> str:
        return self._fields.expected_image_id


def verify_asset_transfer_fragment_receipt_v1(
    witness: VerifiedLaneModuleTransitionV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
    lane_root: LaneStateRootV1,
    prior_fragment: LaneAllocationFragmentV1,
    claimant_entitlements: tuple[ClaimantEntitlementRowV1, ...],
) -> (
    VerifiedLaneAllocationFragmentV1
    | ReceiptWitnessRejectedV1
    | ReceiptBackedProducerRejectedV1
):
    """Admit one fragment only through the receipt-verified module witness.

    Check order: (1) the witness carries a succinct receipt (defensive; the
    mint point enforces it); (2) the receipt-verified module journal root
    equals ``accepted.module_journal.journal_root`` -- one equality binds the
    caller's value to the proof; (3) the statement root and command occurrence
    agree (defensive double-binding; both derive from the journal); then the
    wave-B producer re-runs with its full check family, and (4) the produced
    fragment's ``binding_root`` must equal the witness-bound receipt root.
    Every reject is a value; no input is mutated.
    """

    if type(witness) is not VerifiedLaneModuleTransitionV1:
        raise TypeError("fragment admission requires the module receipt witness")
    committed = lane_root.state_root
    if witness.receipt_kind is not ReceiptKindV1.SUCCINCT:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_KIND_DRIFT,
            lane_root.lane_id,
            committed,
            "witness kind",
        )
    if witness.module_journal_root != accepted.module_journal.journal_root:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_JOURNAL_ROOT_DRIFT,
            lane_root.lane_id,
            committed,
            "journal root",
        )
    if witness.statement_root != accepted.statement_root:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_STATEMENT_ROOT_DRIFT,
            lane_root.lane_id,
            committed,
            "statement root",
        )
    if witness.command_occurrence_id != accepted.module_journal.command_occurrence_id:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_OCCURRENCE_DRIFT,
            lane_root.lane_id,
            committed,
            "command occurrence",
        )
    produced = produce_asset_transfer_fragment_v1(
        accepted, lane_root, prior_fragment, claimant_entitlements
    )
    if isinstance(produced, ReceiptBackedProducerRejectedV1):
        return produced
    if produced.binding_root != accepted.module_journal.receipt_root:
        return ReceiptWitnessRejectedV1(
            ReceiptWitnessRejectCodeV1.WITNESS_BINDING_ROOT_DRIFT,
            lane_root.lane_id,
            committed,
            "binding root",
        )
    return VerifiedLaneAllocationFragmentV1(
        _VERIFIED_FRAGMENT_TOKEN,
        _VerifiedFragmentFieldsV1(
            fragment=produced,
            module_journal_root=witness.module_journal_root,
            receipt_digest=witness.receipt_digest,
            expected_image_id=witness.expected_image_id,
        ),
    )


__all__ = [
    "RECEIPT_ADMISSION_SCHEMA_V1",
    "ReceiptWitnessRejectCodeV1",
    "ReceiptWitnessRejectedV1",
    "VerifiedLaneAllocationFragmentV1",
    "verify_asset_transfer_fragment_receipt_v1",
]
