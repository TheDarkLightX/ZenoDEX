"""Lane fragment producers: registered-empty (wave A) and receipt-backed (wave B).

Wave A (EXTERNAL_CUSTODY, PROOF_REWARDS): a registered-empty lane has exactly
one representable typed state, the empty one, and its committed lane root must
be that state's root; the producer is a pure function of the committed
``LaneStateRootV1`` and returns the exact-empty fragment or a closed reject.

Wave B (ASSET_TRANSFER): ``produce_asset_transfer_fragment_v1`` folds one
accepted lane-module transition into a receipt-bound fragment or rejects with
a closed code; it emits ``producer_kind=RECEIPT_BACKED`` fragments. The producer
trusts its caller for ``accepted``; receipt admission lives one layer up in
``asset_transfer_receipt_admission_v1`` (C9a), which takes the module witness
minted by ``lane_module_receipt_verification_v1``, rebuilds the accepted value
through the exact-typed snapshot, and re-runs this producer on it. The
certificate registry keeps ASSET_TRANSFER at NO_PRODUCER, so no acceptance path
uses these fragments until C9b.

Research-only evidence. It grants no writer, verifier, release, or
publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .asset_transfer_lane_module_v1 import AssetTransferLaneModuleAcceptedV1
from .global_accounting_allocation_certificate_v1 import (
    LANE_ALLOCATION_PRODUCER_REGISTRY_V1,
    MAX_ATOMS_U128_V1,
    MAX_FRAGMENT_ROWS_V1,
    REGISTERED_EMPTY_LANE_ROOTS_V1,
    ClaimantEntitlementRowV1,
    ControlledLocationRowV1,
    LaneAllocationFragmentV1,
    LaneProducerKindV1,
)
from .global_settlement_types_v1 import ZERO_ROOT_V1, LaneIdV1, LaneStateRootV1, _require_root

REGISTERED_EMPTY_PRODUCER_LANES_V1: Final[tuple[LaneIdV1, ...]] = tuple(
    lane
    for lane in LaneIdV1
    if LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane][0]
    in (LaneProducerKindV1.REGISTERED_EMPTY_DISABLED, LaneProducerKindV1.REGISTERED_EMPTY_BLOCKED)
)


class LaneProducerRejectCodeV1(str, Enum):
    """Closed reject codes of the registered-empty producers, in check precedence."""

    LANE_NOT_REGISTERED_EMPTY = "LANE_NOT_REGISTERED_EMPTY"
    LANE_ENABLED = "LANE_ENABLED"
    REGISTERED_EMPTY_ROOT_DRIFT = "REGISTERED_EMPTY_ROOT_DRIFT"


LANE_PRODUCER_REJECT_MESSAGE_BY_CODE_V1: Final[dict[LaneProducerRejectCodeV1, str]] = {
    LaneProducerRejectCodeV1.LANE_NOT_REGISTERED_EMPTY: "lane has no registered-empty producer",
    LaneProducerRejectCodeV1.LANE_ENABLED: "registered-empty lane is enabled",
    LaneProducerRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT: "committed lane root is not the empty lane state root",
}


@dataclass(frozen=True, slots=True)
class LaneProducerRejectedV1:
    """A producer refusal: nothing is produced and the committed lane root is echoed unchanged."""

    code: LaneProducerRejectCodeV1
    lane_id: LaneIdV1
    committed_lane_root: str

    def __post_init__(self) -> None:
        if type(self.code) is not LaneProducerRejectCodeV1:
            raise TypeError("lane producer reject code is not closed")
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane producer lane id is not closed")
        _require_root(self.committed_lane_root, name="lane producer committed lane root", allow_zero=True)

    @property
    def message(self) -> str:
        return LANE_PRODUCER_REJECT_MESSAGE_BY_CODE_V1[self.code]

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "lane_id": self.lane_id,
            "message": self.message,
            "committed_lane_root": self.committed_lane_root,
        }


def produce_registered_empty_fragment_v1(
    lane_root: LaneStateRootV1,
) -> LaneAllocationFragmentV1 | LaneProducerRejectedV1:
    """Produce the exact-empty fragment of a registered-empty lane from its committed root."""

    if type(lane_root) is not LaneStateRootV1:
        raise TypeError("lane producer input must be the exact LaneStateRootV1")
    registered_kind, _ = LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane_root.lane_id]
    empty_root = REGISTERED_EMPTY_LANE_ROOTS_V1.get(lane_root.lane_id)
    if lane_root.lane_id not in REGISTERED_EMPTY_PRODUCER_LANES_V1 or empty_root is None:
        return LaneProducerRejectedV1(LaneProducerRejectCodeV1.LANE_NOT_REGISTERED_EMPTY, lane_root.lane_id, lane_root.state_root)
    if lane_root.enabled:
        return LaneProducerRejectedV1(LaneProducerRejectCodeV1.LANE_ENABLED, lane_root.lane_id, lane_root.state_root)
    if lane_root.state_root != empty_root:
        return LaneProducerRejectedV1(LaneProducerRejectCodeV1.REGISTERED_EMPTY_ROOT_DRIFT, lane_root.lane_id, lane_root.state_root)
    return LaneAllocationFragmentV1(
        lane_id=lane_root.lane_id,
        module_release_id=lane_root.module_release_id,
        enabled=False,
        lane_state_root=lane_root.state_root,
        producer_kind=registered_kind,
        binding_root=lane_root.state_root,
    )


class ReceiptBackedProducerRejectCodeV1(str, Enum):
    """Closed reject codes of the receipt-backed fragment producers, in check precedence."""

    ACCEPTED_INVALID = "ACCEPTED_INVALID"
    JOURNAL_LANE_DRIFT = "JOURNAL_LANE_DRIFT"
    LANE_DISABLED = "LANE_DISABLED"
    MODULE_RELEASE_DRIFT = "MODULE_RELEASE_DRIFT"
    JOURNAL_ROOT_DRIFT = "JOURNAL_ROOT_DRIFT"
    STALE_JOURNAL = "STALE_JOURNAL"
    TERMINAL_ROOT_NOT_EMPTY = "TERMINAL_ROOT_NOT_EMPTY"
    ENTITLEMENT_ROWS_NOT_CANONICAL = "ENTITLEMENT_ROWS_NOT_CANONICAL"
    CONTROLLED_FOLD_OVERFLOW = "CONTROLLED_FOLD_OVERFLOW"
    ENTITLEMENT_COVERAGE_DRIFT = "ENTITLEMENT_COVERAGE_DRIFT"
    FRAGMENT_INVALID = "FRAGMENT_INVALID"


RECEIPT_BACKED_PRODUCER_REJECT_MESSAGE_BY_CODE_V1: Final[dict[ReceiptBackedProducerRejectCodeV1, str]] = {
    ReceiptBackedProducerRejectCodeV1.ACCEPTED_INVALID: "accepted transition value fails its own validation",
    ReceiptBackedProducerRejectCodeV1.JOURNAL_LANE_DRIFT: "journal and committed root name different lanes",
    ReceiptBackedProducerRejectCodeV1.LANE_DISABLED: "receipt-backed production requires an enabled lane",
    ReceiptBackedProducerRejectCodeV1.MODULE_RELEASE_DRIFT: "journal module release differs from the committed lane release",
    ReceiptBackedProducerRejectCodeV1.JOURNAL_ROOT_DRIFT: "journal post root differs from the committed lane root",
    ReceiptBackedProducerRejectCodeV1.STALE_JOURNAL: "journal pre root does not continue the prior fragment",
    ReceiptBackedProducerRejectCodeV1.TERMINAL_ROOT_NOT_EMPTY: "asset transfer journal must commit no terminal obligations",
    ReceiptBackedProducerRejectCodeV1.ENTITLEMENT_ROWS_NOT_CANONICAL: "entitlement rows are not canonically ordered, unique, and nonzero",
    ReceiptBackedProducerRejectCodeV1.CONTROLLED_FOLD_OVERFLOW: "controlled or entitlement fold exceeds the u128 ceiling",
    ReceiptBackedProducerRejectCodeV1.ENTITLEMENT_COVERAGE_DRIFT: "entitlement rows do not cover the controlled atoms exactly",
    ReceiptBackedProducerRejectCodeV1.FRAGMENT_INVALID: "the assembled fragment fails its own validation",
}


@dataclass(frozen=True, slots=True)
class ReceiptBackedProducerRejectedV1:
    """A receipt-backed producer refusal: nothing is produced, every input left unchanged."""

    code: ReceiptBackedProducerRejectCodeV1
    lane_id: LaneIdV1
    committed_lane_root: str
    detail: str

    def __post_init__(self) -> None:
        if type(self.code) is not ReceiptBackedProducerRejectCodeV1:
            raise TypeError("receipt-backed producer reject code is not closed")
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("receipt-backed producer lane id is not closed")
        _require_root(self.committed_lane_root, name="receipt-backed producer committed lane root", allow_zero=True)
        if type(self.detail) is not str or not self.detail or len(self.detail) > 200:
            raise ValueError("receipt-backed producer detail must be a short non-empty string")

    @property
    def message(self) -> str:
        return RECEIPT_BACKED_PRODUCER_REJECT_MESSAGE_BY_CODE_V1[self.code]

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "detail": self.detail,
            "lane_id": self.lane_id,
            "message": self.message,
            "committed_lane_root": self.committed_lane_root,
        }


def _reject_receipt_backed(
    code: ReceiptBackedProducerRejectCodeV1, lane_id: LaneIdV1, committed_lane_root: str, detail: str
) -> ReceiptBackedProducerRejectedV1:
    return ReceiptBackedProducerRejectedV1(code, lane_id, committed_lane_root, detail)


def produce_asset_transfer_fragment_v1(
    accepted: AssetTransferLaneModuleAcceptedV1,
    lane_root: LaneStateRootV1,
    prior_fragment: LaneAllocationFragmentV1,
    claimant_entitlements: tuple[ClaimantEntitlementRowV1, ...],
) -> LaneAllocationFragmentV1 | ReceiptBackedProducerRejectedV1:
    """Fold one accepted asset-transfer transition into a receipt-bound lane fragment (wave B).

    Checks in precedence order; every reject is a no-op value naming its cause:
    0. the accepted value validates                          -> ACCEPTED_INVALID
       (unreachable through construction here: the exact-type gate admits only
       AssetTransferLaneModuleAcceptedV1 and every construction validates via
       __post_init__ -- only object.__new__ forgery bypasses it; the Rust
       twin's plain struct makes this check genuinely reachable there)
    1. journal lane == ASSET_TRANSFER == committed lane      -> JOURNAL_LANE_DRIFT
    2. committed lane enabled                                -> LANE_DISABLED
    3. journal release == committed release                  -> MODULE_RELEASE_DRIFT
    4. journal post root == committed state root             -> JOURNAL_ROOT_DRIFT
    5. the prior fragment continues THIS lane's chain: prior lane is
       ASSET_TRANSFER, prior release equals the committed release, and the
       journal pre root equals the prior committed root      -> STALE_JOURNAL
       (details "prior lane" / "prior release" / "pre root")
    6. journal terminal root is the zero root                -> TERMINAL_ROOT_NOT_EMPTY
    7. entitlement rows are canonically ordered, unique by
       (asset, claimant, control_domain), and nonzero        -> ENTITLEMENT_ROWS_NOT_CANONICAL
    8. the folds stay under the u128 ceiling                 -> CONTROLLED_FOLD_OVERFLOW
       (unreachable on the controlled side for well-formed accepted inputs,
       whose supply-conservation invariant bounds custody totals -- the
       reachable path is the caller-provided entitlement rows)
    9. entitlements cover the post custody exactly per
       (asset, control_domain)                               -> ENTITLEMENT_COVERAGE_DRIFT
    10. the assembled fragment validates (defensive totality: the module input's
        custody key (asset, owner, domain) already equals the fragment's
        controlled key, the producer re-sorts anyway, and the row ceilings are
        pre-checked)                                         -> FRAGMENT_INVALID

    The fragment's controlled locations are the accepted transition's post custody
    projection (owner -> controlling principal, custody_domain -> control domain);
    the asset-transfer module emits no reserves, external obligations, or terminal
    obligations, so those row families are empty. ``binding_root`` is the journal's
    receipt root. NONCLAIM (scoped): this producer trusts its caller for
    ``accepted`` and its coverage fold is keyed on (asset, control_domain) only,
    so claimant identity and the split across claimants are caller-chosen at
    THIS layer and not proved by the receipt; they are bound at the certificate
    layer by ENTITLEMENT_ROWS_DRIFT (derived rows must equal the V1 liabilities
    partition of GlobalEconomicStateV1 exactly), into which no acceptance path
    carries this producer's rows while ASSET_TRANSFER stays at NO_PRODUCER.
    Receipt admission
    (``asset_transfer_receipt_admission_v1``, C9a) takes the module witness
    minted by ``lane_module_receipt_verification_v1`` and re-runs this producer
    on the exact-typed snapshot of ``accepted``; the registry flip is C9b.
    Research-only evidence; authority NONE.
    """

    if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
        raise TypeError("receipt-backed producer input must be the exact AssetTransferLaneModuleAcceptedV1")
    if type(lane_root) is not LaneStateRootV1:
        raise TypeError("receipt-backed producer input must be the exact LaneStateRootV1")
    if type(prior_fragment) is not LaneAllocationFragmentV1:
        raise TypeError("receipt-backed producer prior fragment must be the exact LaneAllocationFragmentV1")
    if type(claimant_entitlements) is not tuple or any(
        type(row) is not ClaimantEntitlementRowV1 for row in claimant_entitlements
    ):
        raise TypeError("receipt-backed producer entitlements must be exact ClaimantEntitlementRowV1 rows")
    journal = accepted.module_journal
    committed = lane_root.state_root
    if journal.lane_id is not LaneIdV1.ASSET_TRANSFER or lane_root.lane_id is not LaneIdV1.ASSET_TRANSFER:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.JOURNAL_LANE_DRIFT,
            lane_root.lane_id,
            committed,
            f"journal {journal.lane_id.value} vs committed {lane_root.lane_id.value}",
        )
    if not lane_root.enabled:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.LANE_DISABLED, lane_root.lane_id, committed, "lane disabled"
        )
    if journal.module_release_id != lane_root.module_release_id:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.MODULE_RELEASE_DRIFT, lane_root.lane_id, committed, "module release"
        )
    if journal.post_lane_root != committed:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.JOURNAL_ROOT_DRIFT, lane_root.lane_id, committed, "post root"
        )
    if prior_fragment.lane_id is not LaneIdV1.ASSET_TRANSFER:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.STALE_JOURNAL, lane_root.lane_id, committed, "prior lane"
        )
    if prior_fragment.producer_kind is not LaneProducerKindV1.RECEIPT_BACKED:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.STALE_JOURNAL, lane_root.lane_id, committed, "prior kind"
        )
    if not prior_fragment.enabled:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.STALE_JOURNAL, lane_root.lane_id, committed, "prior disabled"
        )
    if prior_fragment.module_release_id != lane_root.module_release_id:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.STALE_JOURNAL, lane_root.lane_id, committed, "prior release"
        )
    if journal.pre_lane_root != prior_fragment.lane_state_root:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.STALE_JOURNAL, lane_root.lane_id, committed, "pre root"
        )
    if journal.terminal_obligations_root != ZERO_ROOT_V1:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.TERMINAL_ROOT_NOT_EMPTY, lane_root.lane_id, committed, "terminal root"
        )
    if len(claimant_entitlements) > MAX_FRAGMENT_ROWS_V1:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.ENTITLEMENT_ROWS_NOT_CANONICAL,
            lane_root.lane_id,
            committed,
            "row ceiling",
        )
    entitlement_keys = tuple((row.asset, row.claimant, row.control_domain) for row in claimant_entitlements)
    if entitlement_keys != tuple(sorted(set(entitlement_keys))):
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.ENTITLEMENT_ROWS_NOT_CANONICAL,
            lane_root.lane_id,
            committed,
            "entitlement ordering",
        )
    if any(row.amount_atoms == 0 for row in claimant_entitlements):
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.ENTITLEMENT_ROWS_NOT_CANONICAL,
            lane_root.lane_id,
            committed,
            "zero amount",
        )
    controlled: dict[tuple[str, str], int] = {}
    for row in accepted.private_port.post_state.custody:
        key = (row.asset, row.custody_domain)
        total = controlled.get(key, 0) + row.amount_atoms
        if total > MAX_ATOMS_U128_V1:
            return _reject_receipt_backed(
                ReceiptBackedProducerRejectCodeV1.CONTROLLED_FOLD_OVERFLOW, lane_root.lane_id, committed, "controlled"
            )
        controlled[key] = total
    assigned: dict[tuple[str, str], int] = {}
    for entitlement in claimant_entitlements:
        key = (entitlement.asset, entitlement.control_domain)
        total = assigned.get(key, 0) + entitlement.amount_atoms
        if total > MAX_ATOMS_U128_V1:
            return _reject_receipt_backed(
                ReceiptBackedProducerRejectCodeV1.CONTROLLED_FOLD_OVERFLOW, lane_root.lane_id, committed, "entitlements"
            )
        assigned[key] = total
    if controlled != assigned:
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.ENTITLEMENT_COVERAGE_DRIFT,
            lane_root.lane_id,
            committed,
            "coverage",
        )
    controlled_rows = tuple(
        sorted(
            (
                ControlledLocationRowV1(row.asset, row.owner, row.custody_domain, row.amount_atoms)
                for row in accepted.private_port.post_state.custody
            ),
            key=lambda row: row.key,
        )
    )
    try:
        return LaneAllocationFragmentV1(
            lane_id=lane_root.lane_id,
            module_release_id=lane_root.module_release_id,
            enabled=True,
            lane_state_root=committed,
            producer_kind=LaneProducerKindV1.RECEIPT_BACKED,
            binding_root=journal.receipt_root,
            controlled_locations=controlled_rows,
            claimant_entitlements=claimant_entitlements,
        )
    except (TypeError, ValueError):
        # Defensive totality (Opus P18 P2-D): the ceilings and canonical checks above make
        # this unreachable in intent; if any residual constructor invariant fires, the
        # caller still receives a closed reject, never an exception.
        return _reject_receipt_backed(
            ReceiptBackedProducerRejectCodeV1.FRAGMENT_INVALID,
            lane_root.lane_id,
            committed,
            "fragment validation",
        )


__all__ = [
    "LANE_PRODUCER_REJECT_MESSAGE_BY_CODE_V1",
    "RECEIPT_BACKED_PRODUCER_REJECT_MESSAGE_BY_CODE_V1",
    "REGISTERED_EMPTY_PRODUCER_LANES_V1",
    "LaneProducerRejectCodeV1",
    "LaneProducerRejectedV1",
    "ReceiptBackedProducerRejectCodeV1",
    "ReceiptBackedProducerRejectedV1",
    "produce_asset_transfer_fragment_v1",
    "produce_registered_empty_fragment_v1",
]
