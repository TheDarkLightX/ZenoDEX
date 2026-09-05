"""Pure restricted ASSET allocation checks over explicit epoch disclosures.

The shell owns committed-source acquisition and the cryptographic origin of
module witnesses. Only the initial predecessor is committed; later states are
prospective. These ordinary diagnostic values grant no publication authority.
The standalone W04 relation currently refuses the second ordinary command of
an epoch because intermediate epoch heights do not increment per command.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias

from .asset_transfer_global_allocation_v1 import (
    AssetTransferGlobalAllocationCandidateV1,
    GlobalAllocationBindingRejectedV1,
)
from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    _snapshot_asset_transfer_lane_module_accepted_v1,
)
from .asset_transfer_receipt_admission_v1 import (
    ReceiptWitnessRejectedV1,
    verify_asset_transfer_global_fragment_receipt_v1,
)
from .global_accounting_allocation_certificate_v1 import (
    AllocationCertificateAcceptedV1,
    AllocationCertificateRejectedV1,
    VerifiedLaneAllocationFragmentV1,
    check_global_accounting_allocation_certificate_v1,
)
from .global_accounting_allocation_projection_v1 import (
    AllocationProjectionRejectedV1,
    project_allocation_certificate_v1,
)
from .global_accounting_lane_producers_v1 import ReceiptBackedProducerRejectedV1
from .global_economic_proof_v1 import (
    MAX_EPOCH_COMMANDS_V1,
    EconomicEpochReceiptCandidateV1,
    _snapshot_economic_epoch_candidate_v1,
    _validate_command_occurrences,
)
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import ALL_LANE_IDS_V1, GlobalEconomicStateV1, LaneIdV1
from .lane_module_receipt_verification_v1 import (
    VerifiedLaneModuleTransitionV1,
    require_verified_lane_module_transition_scalars_v1,
)

AssetTransferModuleEvidenceV1: TypeAlias = tuple[
    AssetTransferLaneModuleAcceptedV1, VerifiedLaneModuleTransitionV1
]
AllocationCauseV1: TypeAlias = (
    GlobalAllocationBindingRejectedV1
    | ReceiptWitnessRejectedV1
    | ReceiptBackedProducerRejectedV1
    | AllocationProjectionRejectedV1
    | AllocationCertificateRejectedV1
)


class AssetTransferEpochAllocationRejectCodeV1(str, Enum):
    INPUT_SHAPE = "INPUT_SHAPE"
    EVIDENCE_SHAPE = "EVIDENCE_SHAPE"
    EPOCH_CARDINALITY = "EPOCH_CARDINALITY"
    MALFORMED_INPUT = "MALFORMED_INPUT"
    SOURCE_MISMATCH = "SOURCE_MISMATCH"
    OCCURRENCE_MISMATCH = "OCCURRENCE_MISMATCH"
    MODULE_MEMBERSHIP_MISMATCH = "MODULE_MEMBERSHIP_MISMATCH"
    ROUTE_MEMBERSHIP_MISMATCH = "ROUTE_MEMBERSHIP_MISMATCH"
    GLOBAL_FRAGMENT_REJECTED = "GLOBAL_FRAGMENT_REJECTED"
    PROJECTION_REJECTED = "PROJECTION_REJECTED"
    CERTIFICATE_REJECTED = "CERTIFICATE_REJECTED"
    FINAL_STATE_MISMATCH = "FINAL_STATE_MISMATCH"


@dataclass(frozen=True, slots=True)
class AssetTransferEpochAllocationRejectedV1:
    code: AssetTransferEpochAllocationRejectCodeV1
    occurrence_index: int | None = None
    cause: AllocationCauseV1 | None = None


@dataclass(frozen=True, slots=True)
class AssetTransferEpochAllocationAcceptedV1:
    """Ordinary checker results; construction grants no source or writer authority."""

    source_state_root: str
    post_state_root: str
    checks: tuple[AllocationCertificateAcceptedV1, ...]


def _shape_rejection_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    predecessor: GlobalEconomicStateV1,
    evidence: tuple[AssetTransferModuleEvidenceV1, ...],
) -> AssetTransferEpochAllocationRejectCodeV1 | None:
    code = AssetTransferEpochAllocationRejectCodeV1
    if (
        type(candidate) is not EconomicEpochReceiptCandidateV1
        or type(predecessor) is not GlobalEconomicStateV1
    ):
        return code.INPUT_SHAPE
    if type(evidence) is not tuple:
        return code.EVIDENCE_SHAPE
    sequences = (
        candidate.command_occurrences,
        candidate.route_journals,
        candidate.route_state_disclosures,
        candidate.verified_routes,
        candidate.route_effect_plans,
        candidate.ordered_command_body_hashes,
    )
    if any(type(rows) is not tuple for rows in sequences):
        return code.INPUT_SHAPE
    count = len(candidate.command_occurrences)
    if not 1 <= count <= MAX_EPOCH_COMMANDS_V1 or any(
        len(rows) != count for rows in (*sequences, evidence)
    ):
        return code.EPOCH_CARDINALITY
    if any(
        type(pair) is not tuple
        or len(pair) != 2
        or type(pair[0]) is not AssetTransferLaneModuleAcceptedV1
        or type(pair[1]) is not VerifiedLaneModuleTransitionV1
        for pair in evidence
    ):
        return code.EVIDENCE_SHAPE
    return None


def _snapshot_evidence_v1(
    evidence: tuple[AssetTransferModuleEvidenceV1, ...],
) -> tuple[AssetTransferModuleEvidenceV1, ...]:
    owned = []
    for accepted, witness in evidence:
        require_verified_lane_module_transition_scalars_v1(witness)
        owned.append((_snapshot_asset_transfer_lane_module_accepted_v1(accepted), witness))
    return tuple(owned)


def _membership_rejection_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    index: int,
    evidence: AssetTransferModuleEvidenceV1,
) -> AssetTransferEpochAllocationRejectCodeV1 | None:
    code = AssetTransferEpochAllocationRejectCodeV1
    accepted, witness = evidence
    occurrence = candidate.command_occurrences[index]
    disclosure = candidate.route_state_disclosures[index]
    journal, route = candidate.route_journals[index], candidate.verified_routes[index]
    if (
        accepted.module_journal.command_occurrence_id != occurrence.occurrence_id
        or witness.command_occurrence_id != occurrence.occurrence_id
    ):
        return code.OCCURRENCE_MISMATCH
    if len(disclosure.lane_journals) != 1:
        return code.MODULE_MEMBERSHIP_MISMATCH
    lane = disclosure.lane_journals[0]
    if lane.lane_id is not LaneIdV1.ASSET_TRANSFER or lane.ordered_module_journal_roots != (
        accepted.module_journal.journal_root,
    ):
        return code.MODULE_MEMBERSHIP_MISMATCH
    expected_context = (
        occurrence.chain_id,
        occurrence.deployment_root,
        occurrence.profile_root,
        candidate.pre_state.writer_epoch,
        occurrence.occurrence_id,
    )
    if any(
        (
            row.chain_id,
            row.deployment_root,
            row.profile_root,
            row.writer_epoch,
            row.command_occurrence_id,
        )
        != expected_context
        for row in (lane, journal)
    ):
        return code.OCCURRENCE_MISMATCH
    if (
        journal.ordered_lane_journal_roots != (lane.journal_root,)
        or route.ordered_lane_ids != (LaneIdV1.ASSET_TRANSFER,)
        or route.ordered_lane_journal_roots != (lane.journal_root,)
        or route.route_journal_root != journal.journal_root
        or route.command_occurrence_id != occurrence.occurrence_id
        or route.profile_id != candidate.profile.profile_id
        or route.writer_epoch != candidate.pre_state.writer_epoch
        or route.route_release_id != occurrence.route_release_id
        or journal.route_release_id != occurrence.route_release_id
    ):
        return code.ROUTE_MEMBERSHIP_MISMATCH
    return None


def _check_fragment_v1(
    fragment: VerifiedLaneAllocationFragmentV1,
    current: GlobalEconomicStateV1,
    index: int,
) -> AllocationCertificateAcceptedV1 | AssetTransferEpochAllocationRejectedV1:
    code = AssetTransferEpochAllocationRejectCodeV1
    slots = (fragment, *(None for _ in ALL_LANE_IDS_V1[1:]))
    # Admission defines the fragment binding as the module journal receipt root;
    # a module-journal hash or coordinator state root is a different identity.
    roots = ((LaneIdV1.ASSET_TRANSFER, fragment.fragment.binding_root),)
    projected = project_allocation_certificate_v1(current, roots, slots)
    if isinstance(projected, AllocationProjectionRejectedV1):
        return AssetTransferEpochAllocationRejectedV1(code.PROJECTION_REJECTED, index, projected)
    checked = check_global_accounting_allocation_certificate_v1(projected, current, slots)
    if isinstance(checked, AllocationCertificateRejectedV1):
        return AssetTransferEpochAllocationRejectedV1(code.CERTIFICATE_REJECTED, index, checked)
    if type(checked) is not AllocationCertificateAcceptedV1:
        raise TypeError("allocation checker returned an unregistered outcome")
    return checked


def _check_occurrence_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    predecessor: GlobalEconomicStateV1,
    evidence: AssetTransferModuleEvidenceV1,
    index: int,
) -> AllocationCertificateAcceptedV1 | AssetTransferEpochAllocationRejectedV1:
    code = _membership_rejection_v1(candidate, index, evidence)
    if code is not None:
        return AssetTransferEpochAllocationRejectedV1(code, index)
    accepted, witness = evidence
    current = candidate.route_state_disclosures[index].post_state
    fragment = verify_asset_transfer_global_fragment_receipt_v1(
        witness,
        AssetTransferGlobalAllocationCandidateV1(
            accepted,
            candidate.command_occurrences[index],
            predecessor,
            current,
        ),
    )
    if not isinstance(fragment, VerifiedLaneAllocationFragmentV1):
        return AssetTransferEpochAllocationRejectedV1(
            AssetTransferEpochAllocationRejectCodeV1.GLOBAL_FRAGMENT_REJECTED,
            index,
            fragment,
        )
    return _check_fragment_v1(fragment, current, index)


def check_asset_transfer_epoch_allocation_v1(
    *,
    candidate: EconomicEpochReceiptCandidateV1,
    predecessor: GlobalEconomicStateV1,
    module_evidence: tuple[AssetTransferModuleEvidenceV1, ...],
) -> AssetTransferEpochAllocationAcceptedV1 | AssetTransferEpochAllocationRejectedV1:
    """Check bounded shape, owned source, order, membership and every allocation.

    Expected malformed inputs and existing semantic rejects return closed values.
    Errors after owned validation are not broadly swallowed. Inputs remain
    unchanged, and rejection exposes no successor or partially accepted checks.
    This supplements epoch verification; it does not verify receipts, select
    policy, authorize initial ownership, acquire storage or commit publication.
    """
    code = AssetTransferEpochAllocationRejectCodeV1
    shape = _shape_rejection_v1(candidate, predecessor, module_evidence)
    if shape is not None:
        return AssetTransferEpochAllocationRejectedV1(shape)
    try:
        owned = _snapshot_economic_epoch_candidate_v1(candidate)
        source = _snapshot_state_v1(predecessor)
        evidence = _snapshot_evidence_v1(module_evidence)
    except (TypeError, ValueError, OverflowError):
        return AssetTransferEpochAllocationRejectedV1(code.MALFORMED_INPUT)
    if (
        source != owned.pre_state
        or source.profile_root != owned.profile.profile_id
        or source.writer_epoch != owned.profile.authority_epoch
    ):
        return AssetTransferEpochAllocationRejectedV1(code.SOURCE_MISMATCH)
    try:
        _validate_command_occurrences(
            owned.certificate, owned.command_occurrences, owned.ordered_command_body_hashes
        )
    except (TypeError, ValueError):
        return AssetTransferEpochAllocationRejectedV1(code.OCCURRENCE_MISMATCH)
    current = source
    checks = []
    for index, pair in enumerate(evidence):
        checked = _check_occurrence_v1(owned, current, pair, index)
        if isinstance(checked, AssetTransferEpochAllocationRejectedV1):
            return checked
        checks.append(checked)
        current = owned.route_state_disclosures[index].post_state
    if current != owned.post_state:
        return AssetTransferEpochAllocationRejectedV1(code.FINAL_STATE_MISMATCH)
    return AssetTransferEpochAllocationAcceptedV1(
        source.state_root, current.state_root, tuple(checks)
    )


__all__ = [
    "AssetTransferModuleEvidenceV1",
    "AssetTransferEpochAllocationRejectCodeV1",
    "AssetTransferEpochAllocationRejectedV1",
    "AssetTransferEpochAllocationAcceptedV1",
    "check_asset_transfer_epoch_allocation_v1",
]
