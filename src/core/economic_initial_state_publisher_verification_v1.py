"""Verifier-owned genesis and migration witnesses for the publisher shell."""

from __future__ import annotations

from .economic_initial_state_atom_coverage_v1 import EconomicInitialStateKindV1
from .economic_initial_state_v1 import (
    EconomicInitialStateAdmissionV1,
    _OwnedEconomicInitialStateAdmissionV1,
    _snapshot_economic_initial_state_admission_v1,
    _validate_owned_economic_initial_state_admission_v1,
    _VerifiedEconomicInitialStateV1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import SuccinctReceiptVerifierV1
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import (
    GlobalEconomicStateV1,
    canonical_global_bytes_v1,
)


def _verify_economic_initial_state_for_publisher_v1(
    admission: EconomicInitialStateAdmissionV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> _VerifiedEconomicInitialStateV1:
    """Verify genesis before constructing a publisher-owned head."""

    owned = _snapshot_economic_initial_state_admission_v1(admission)
    if owned.certificate.kind is not EconomicInitialStateKindV1.GENESIS:
        raise ValueError("commit port construction requires a genesis admission")
    return _verify_owned_economic_initial_state_for_publisher_v1(
        owned,
        receipt_verifier,
    )


def _verify_economic_migration_for_publisher_v1(
    admission: EconomicInitialStateAdmissionV1,
    expected_predecessor_state: GlobalEconomicStateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> _VerifiedEconomicInitialStateV1:
    """Verify migration against the exact publisher-owned predecessor."""

    if type(expected_predecessor_state) is not GlobalEconomicStateV1:
        raise TypeError("migration expected predecessor state type is not closed")
    owned = _snapshot_economic_initial_state_admission_v1(admission)
    if owned.certificate.kind is not EconomicInitialStateKindV1.MIGRATION:
        raise ValueError("migration activation requires a migration admission")
    expected_predecessor = _snapshot_state_v1(expected_predecessor_state)
    if owned.predecessor_state is None:
        raise ValueError("migration initial state requires a predecessor state")
    if canonical_global_bytes_v1(
        owned.predecessor_state
    ) != canonical_global_bytes_v1(expected_predecessor):
        raise ValueError(
            "migration predecessor does not match the publisher-owned source head"
        )
    return _verify_owned_economic_initial_state_for_publisher_v1(
        owned,
        receipt_verifier,
    )


def _verify_owned_economic_initial_state_for_publisher_v1(
    owned: _OwnedEconomicInitialStateAdmissionV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> _VerifiedEconomicInitialStateV1:
    """Complete receipt verification over an already-owned admission."""

    journal_bytes = _validate_owned_economic_initial_state_admission_v1(owned)
    receipt_verifier.verify_succinct_receipt(
        owned.receipt_bytes,
        expected_image_id=owned.profile.root_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return _VerifiedEconomicInitialStateV1(
        profile=snapshot_economic_profile_v1(owned.profile),
        state=_snapshot_state_v1(owned.state),
        certificate_root=owned.certificate.certificate_root,
    )
