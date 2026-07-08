from __future__ import annotations

import pytest

from src.core.cross_shard_ledger_posting import (
    CrossShardLedgerPostingBuildResult,
    CrossShardLedgerPostingSummaryV1,
    build_cross_shard_ledger_posting_summary,
)
from src.core.cross_shard_settlement_admission import CrossShardSettlementAdmissionResult

_SETTLEMENT_CERT_HASH = "0x" + "a" * 64


def _accepted_admission(
    applied_amounts: tuple[tuple[str, int], ...],
    *,
    committed_count: int,
    rejected_count: int = 0,
    pending_count: int = 0,
) -> CrossShardSettlementAdmissionResult:
    return CrossShardSettlementAdmissionResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
        shard_count=2,
        cross_shard_transfer_count=committed_count + rejected_count + pending_count,
        decision_certificate_count=committed_count + rejected_count + pending_count,
        committed_transfer_count=committed_count,
        rejected_transfer_count=rejected_count,
        pending_transfer_count=pending_count,
        applied_cross_shard_transfer_count=committed_count,
        applied_cross_shard_amounts_by_asset=applied_amounts,
        user_statuses=tuple("global_cross_shard_commit_accepted" for _ in range(committed_count)),
    )


def test_cross_shard_posting_summary_uses_committed_applied_amounts() -> None:
    admission = _accepted_admission((("quote", 1_000),), committed_count=1)

    result = build_cross_shard_ledger_posting_summary(admission)

    assert result.ok is True
    assert result.error is None
    assert result.postings == (
        CrossShardLedgerPostingSummaryV1(
            asset_id="quote",
            committed_debit_atoms=1_000,
            committed_credit_atoms=1_000,
        ),
    )
    assert result.sharded_settlement_certificate_hash == _SETTLEMENT_CERT_HASH
    assert result.total_committed_debit_atoms == 1_000
    assert result.total_committed_credit_atoms == 1_000


def test_cross_shard_posting_summary_ignores_rejected_and_pending_amounts() -> None:
    admission = _accepted_admission(
        (("base", 250), ("quote", 1_000)),
        committed_count=2,
        rejected_count=1,
        pending_count=1,
    )

    result = build_cross_shard_ledger_posting_summary(admission)

    assert result.ok is True
    assert [posting.to_payload() for posting in result.postings] == [
        {
            "asset_id": "base",
            "committed_debit_atoms": 250,
            "committed_credit_atoms": 250,
        },
        {
            "asset_id": "quote",
            "committed_debit_atoms": 1_000,
            "committed_credit_atoms": 1_000,
        },
    ]
    assert result.total_committed_debit_atoms == 1_250
    assert result.total_committed_credit_atoms == 1_250


def test_cross_shard_posting_summary_is_empty_without_commits() -> None:
    admission = _accepted_admission((), committed_count=0, rejected_count=1, pending_count=1)

    result = build_cross_shard_ledger_posting_summary(admission)

    assert result == CrossShardLedgerPostingBuildResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
        postings=(),
        total_committed_debit_atoms=0,
        total_committed_credit_atoms=0,
    )


def test_cross_shard_posting_summary_rejects_failed_admission() -> None:
    admission = CrossShardSettlementAdmissionResult(ok=False, error="missing decision")

    result = build_cross_shard_ledger_posting_summary(admission)

    assert result == CrossShardLedgerPostingBuildResult(
        ok=False,
        error="cross-shard admission result is rejected",
    )


def test_cross_shard_posting_summary_rejects_wrong_input_type() -> None:
    result = build_cross_shard_ledger_posting_summary("not-admission")  # type: ignore[arg-type]

    assert result == CrossShardLedgerPostingBuildResult(
        ok=False,
        error="admission_result must be CrossShardSettlementAdmissionResult",
    )


def test_cross_shard_posting_summary_constructor_rejects_unbalanced_row() -> None:
    with pytest.raises(
        ValueError,
        match="cross-shard ledger posting summary must balance debit and credit",
    ):
        CrossShardLedgerPostingSummaryV1(
            asset_id="quote",
            committed_debit_atoms=1_000,
            committed_credit_atoms=999,
        )


def test_cross_shard_posting_result_constructor_rejects_unbalanced_totals() -> None:
    with pytest.raises(
        ValueError,
        match="cross-shard ledger posting totals must balance",
    ):
        CrossShardLedgerPostingBuildResult(
            ok=True,
            error=None,
            sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
            postings=(),
            total_committed_debit_atoms=1,
            total_committed_credit_atoms=0,
        )
