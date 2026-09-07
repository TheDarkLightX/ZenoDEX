"""Receipt execution shell for prepared genesis and migration subjects.

Core (``src.core.economic_initial_state_publisher_verification_v1``) owns every
admission, snapshot, kind, predecessor and journal decision.  This shell
executes exactly the prepared receipt, image and canonical journal on the
publisher's selected verifier and finishes only that subject.  The generic
port's return value is ignored, as before this extraction;
``BoundEconomicReceiptVerifierV1`` enforces its own exact success contract.
No publication capability is added here.
"""

from __future__ import annotations

from ..core.economic_initial_state_publisher_verification_v1 import (
    _finish_prepared_economic_initial_state_v1,
    _prepare_economic_initial_state_for_publisher_v1,
    _prepare_economic_migration_for_publisher_v1,
    _PreparedEconomicInitialStateV1,
    _require_prepared_economic_initial_state_v1,
    _snapshot_prepared_economic_initial_state_v1,
)
from ..core.economic_initial_state_v1 import (
    EconomicInitialStateAdmissionV1,
    _VerifiedEconomicInitialStateV1,
)
from ..core.global_settlement_types_v1 import GlobalEconomicStateV1
from .global_economic_epoch_verification_v1 import SuccinctReceiptVerifierV1


def _verify_economic_initial_state_for_publisher_v1(
    admission: EconomicInitialStateAdmissionV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> _VerifiedEconomicInitialStateV1:
    """Verify genesis before constructing a publisher-owned head."""

    prepared = _prepare_economic_initial_state_for_publisher_v1(admission)
    return _execute_prepared_economic_initial_state_v1(prepared, receipt_verifier)


def _verify_economic_migration_for_publisher_v1(
    admission: EconomicInitialStateAdmissionV1,
    expected_predecessor_state: GlobalEconomicStateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> _VerifiedEconomicInitialStateV1:
    """Verify migration against the exact publisher-owned predecessor."""

    prepared = _prepare_economic_migration_for_publisher_v1(
        admission,
        expected_predecessor_state,
    )
    return _execute_prepared_economic_initial_state_v1(prepared, receipt_verifier)


def _execute_prepared_economic_initial_state_v1(
    prepared: _PreparedEconomicInitialStateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> _VerifiedEconomicInitialStateV1:
    """Execute exactly one prepared subject and finish only that subject.

    Subclasses, forged instances and substituted field records are refused
    before any call; the executed receipt, image and journal come from the
    retained complete owned admission.
    """

    owned_prepared = _snapshot_prepared_economic_initial_state_v1(prepared)
    fields = _require_prepared_economic_initial_state_v1(owned_prepared)
    receipt_verifier.verify_succinct_receipt(
        fields.owned.receipt_bytes,
        expected_image_id=fields.owned.profile.root_image_id,
        expected_journal_bytes=fields.expected_journal_bytes,
    )
    return _finish_prepared_economic_initial_state_v1(owned_prepared)
