"""Locked decision and typed-result construction for atomic settlement."""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass

from src.core._zrpf_settlement_commit_authority import _AuthenticatedSettlementCommitV1
from src.core.recursive_stark_admission import RecursiveStarkAdmissionRejectReason
from src.integration._recursive_stark_admission_store_engine import _receipt_from_row
from src.integration._zrpf_atomic_settlement_store_engine import (
    _read_settlement_cursor,
    _read_settlement_plan_row,
    _settlement_overlap_reason,
    _settlement_receipt_from_row,
)
from src.integration._zrpf_atomic_settlement_store_history import (
    _validate_coupled_admission_settlement_history,
)
from src.integration.recursive_stark_admission_store import _read_locked_evaluation
from src.integration.recursive_stark_admission_store_types import (
    DurableRecursiveStarkAdmissionCursor,
    _hash_bytes,
)
from src.integration.zrpf_atomic_settlement_store_types import (
    DurableZrpfAtomicSettlementResultV1,
    DurableZrpfSettlementCursorV1,
    ZrpfAtomicSettlementDispositionV1,
    ZrpfAtomicSettlementRejectReasonV1,
)


@dataclass(frozen=True, slots=True)
class _AtomicSettlementEvaluationV1:
    admission_head: DurableRecursiveStarkAdmissionCursor
    settlement_head: DurableZrpfSettlementCursorV1
    existing_admission: sqlite3.Row | None
    existing_settlement: sqlite3.Row | None
    admission_facts_digest: bytes
    admission_outcome_key: bytes
    recursive_reject_reason: RecursiveStarkAdmissionRejectReason | None
    idempotent_replay: bool


@dataclass(frozen=True, slots=True)
class _AtomicSettlementExpectedCursorsV1:
    admission: DurableRecursiveStarkAdmissionCursor
    settlement: DurableZrpfSettlementCursorV1


@dataclass(frozen=True, slots=True)
class _AtomicSettlementAcceptedRowsV1:
    admission_head: DurableRecursiveStarkAdmissionCursor
    settlement_head: DurableZrpfSettlementCursorV1
    admission_row: sqlite3.Row
    settlement_row: sqlite3.Row


def _evaluate_atomic_settlement_locked(
    connection: sqlite3.Connection,
    authenticated: _AuthenticatedSettlementCommitV1,
) -> _AtomicSettlementEvaluationV1:
    _validate_coupled_admission_settlement_history(connection)
    root_evaluation = _read_locked_evaluation(connection, authenticated.authenticated_root)
    existing_settlement = _read_settlement_plan_row(
        connection,
        root_journal_hash=authenticated.authenticated_root.facts.root_journal_hash,
    )
    exact_idempotent = (
        root_evaluation.idempotent_replay
        and existing_settlement is not None
        and bytes(existing_settlement["plan_commitment"])
        == _hash_bytes(authenticated.plan.commitment, name="plan commitment")
    )
    recursive_reject = root_evaluation.plan_reject_reason
    if root_evaluation.idempotent_replay and not exact_idempotent:
        recursive_reject = RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL
    return _AtomicSettlementEvaluationV1(
        admission_head=root_evaluation.actual_cursor,
        settlement_head=_read_settlement_cursor(connection),
        existing_admission=root_evaluation.existing,
        existing_settlement=existing_settlement,
        admission_facts_digest=root_evaluation.facts_digest,
        admission_outcome_key=root_evaluation.outcome_key,
        recursive_reject_reason=recursive_reject,
        idempotent_replay=exact_idempotent,
    )


def _resolve_atomic_settlement_no_commit(
    connection: sqlite3.Connection,
    evaluation: _AtomicSettlementEvaluationV1,
    expected: _AtomicSettlementExpectedCursorsV1,
    authenticated: _AuthenticatedSettlementCommitV1,
) -> DurableZrpfAtomicSettlementResultV1 | None:
    if evaluation.idempotent_replay:
        return _idempotent_result(evaluation)
    if evaluation.recursive_reject_reason is not None:
        return _recursive_rejected_result(evaluation, evaluation.recursive_reject_reason)
    if evaluation.admission_head != expected.admission:
        return _settlement_rejected_result(
            evaluation,
            ZrpfAtomicSettlementRejectReasonV1.ADMISSION_CURSOR_MISMATCH,
        )
    if evaluation.settlement_head != expected.settlement:
        return _settlement_rejected_result(
            evaluation,
            ZrpfAtomicSettlementRejectReasonV1.SETTLEMENT_CURSOR_MISMATCH,
        )
    if authenticated.plan.pre_state_root != evaluation.settlement_head.state_root:
        return _settlement_rejected_result(
            evaluation,
            ZrpfAtomicSettlementRejectReasonV1.PRE_STATE_ROOT_MISMATCH,
        )
    overlap = _settlement_overlap_reason(connection, authenticated.plan)
    if overlap is not None:
        return _settlement_rejected_result(evaluation, overlap)
    return None


def _idempotent_result(
    evaluation: _AtomicSettlementEvaluationV1,
) -> DurableZrpfAtomicSettlementResultV1:
    if evaluation.existing_admission is None or evaluation.existing_settlement is None:
        raise ValueError("idempotent atomic settlement rows are missing")
    rows = _AtomicSettlementAcceptedRowsV1(
        admission_head=evaluation.admission_head,
        settlement_head=evaluation.settlement_head,
        admission_row=evaluation.existing_admission,
        settlement_row=evaluation.existing_settlement,
    )
    return _accepted_atomic_settlement_result(
        ZrpfAtomicSettlementDispositionV1.IDEMPOTENT_REPLAY,
        rows,
    )


def _accepted_atomic_settlement_result(
    disposition: ZrpfAtomicSettlementDispositionV1,
    rows: _AtomicSettlementAcceptedRowsV1,
) -> DurableZrpfAtomicSettlementResultV1:
    return DurableZrpfAtomicSettlementResultV1(
        disposition=disposition,
        admission_head=rows.admission_head,
        settlement_head=rows.settlement_head,
        admission_receipt=_receipt_from_row(rows.admission_row),
        settlement_receipt=_settlement_receipt_from_row(rows.settlement_row),
        recursive_reject_reason=None,
        settlement_reject_reason=None,
    )


def _recursive_rejected_result(
    evaluation: _AtomicSettlementEvaluationV1,
    reason: RecursiveStarkAdmissionRejectReason,
) -> DurableZrpfAtomicSettlementResultV1:
    return DurableZrpfAtomicSettlementResultV1(
        disposition=ZrpfAtomicSettlementDispositionV1.REJECTED,
        admission_head=evaluation.admission_head,
        settlement_head=evaluation.settlement_head,
        admission_receipt=None,
        settlement_receipt=None,
        recursive_reject_reason=reason,
        settlement_reject_reason=None,
    )


def _settlement_rejected_result(
    evaluation: _AtomicSettlementEvaluationV1,
    reason: ZrpfAtomicSettlementRejectReasonV1,
) -> DurableZrpfAtomicSettlementResultV1:
    return DurableZrpfAtomicSettlementResultV1(
        disposition=ZrpfAtomicSettlementDispositionV1.REJECTED,
        admission_head=evaluation.admission_head,
        settlement_head=evaluation.settlement_head,
        admission_receipt=None,
        settlement_receipt=None,
        recursive_reject_reason=None,
        settlement_reject_reason=reason,
    )
