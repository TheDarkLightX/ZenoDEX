from __future__ import annotations

import pytest

from src.core.cross_shard_ledger_effects import (
    CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1,
    CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1,
    CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1,
    CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1,
    CrossShardLedgerEffectsBuildResult,
    CrossShardLedgerEffectV1,
    build_cross_shard_ledger_effects_from_posting_result,
)
from src.core.cross_shard_ledger_posting import (
    CrossShardLedgerPostingBuildResult,
    CrossShardLedgerPostingSummaryV1,
)

_SETTLEMENT_CERT_HASH = "0x" + "e" * 64


def _accepted_posting_result() -> CrossShardLedgerPostingBuildResult:
    return CrossShardLedgerPostingBuildResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
        postings=(
            CrossShardLedgerPostingSummaryV1(
                asset_id="base",
                committed_debit_atoms=250,
                committed_credit_atoms=250,
            ),
            CrossShardLedgerPostingSummaryV1(
                asset_id="quote",
                committed_debit_atoms=1_000,
                committed_credit_atoms=1_000,
            ),
        ),
        total_committed_debit_atoms=1_250,
        total_committed_credit_atoms=1_250,
    )


def test_cross_shard_ledger_effects_are_derived_from_posting_rows() -> None:
    result = build_cross_shard_ledger_effects_from_posting_result(
        _accepted_posting_result()
    )

    assert result.ok is True
    assert result.error is None
    assert result.total_debit_atoms == 1_250
    assert result.total_credit_atoms == 1_250
    assert [effect.to_payload() for effect in result.effects] == [
        {
            "schema": CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1,
            "asset_id": "base",
            "account_id": CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1,
            "delta_atoms": -250,
            "source": CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1,
        },
        {
            "schema": CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1,
            "asset_id": "base",
            "account_id": CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1,
            "delta_atoms": 250,
            "source": CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1,
        },
        {
            "schema": CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1,
            "asset_id": "quote",
            "account_id": CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1,
            "delta_atoms": -1_000,
            "source": CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1,
        },
        {
            "schema": CROSS_SHARD_LEDGER_EFFECT_SCHEMA_V1,
            "asset_id": "quote",
            "account_id": CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1,
            "delta_atoms": 1_000,
            "source": CROSS_SHARD_LEDGER_EFFECT_SOURCE_V1,
        },
    ]


def test_cross_shard_ledger_effects_allow_empty_accepted_summary() -> None:
    result = build_cross_shard_ledger_effects_from_posting_result(
        CrossShardLedgerPostingBuildResult(
            ok=True,
            error=None,
            sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
            postings=(),
            total_committed_debit_atoms=0,
            total_committed_credit_atoms=0,
        )
    )

    assert result == CrossShardLedgerEffectsBuildResult(
        ok=True,
        error=None,
        effects=(),
        total_debit_atoms=0,
        total_credit_atoms=0,
    )


def test_cross_shard_ledger_effects_reject_failed_posting_result() -> None:
    result = build_cross_shard_ledger_effects_from_posting_result(
        CrossShardLedgerPostingBuildResult(
            ok=False,
            error="missing decision",
        )
    )

    assert result == CrossShardLedgerEffectsBuildResult(
        ok=False,
        error="cross-shard posting result is rejected",
    )


def test_cross_shard_ledger_effects_reject_raw_candidate_like_input() -> None:
    result = build_cross_shard_ledger_effects_from_posting_result(
        {"candidate_legs": [{"asset_id": "quote", "amount_atoms": 1_000}]}  # type: ignore[arg-type]
    )

    assert result == CrossShardLedgerEffectsBuildResult(
        ok=False,
        error="posting_result must be CrossShardLedgerPostingBuildResult",
    )


def test_cross_shard_ledger_effect_constructor_rejects_source_override() -> None:
    with pytest.raises(ValueError, match="cross-shard ledger effect source mismatch"):
        CrossShardLedgerEffectV1(
            asset_id="quote",
            account_id=CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1,
            delta_atoms=1_000,
            source="raw_candidate_leg",
        )


def test_cross_shard_ledger_effect_result_rejects_unbalanced_totals() -> None:
    with pytest.raises(ValueError, match="cross-shard ledger effects totals must balance"):
        CrossShardLedgerEffectsBuildResult(
            ok=True,
            error=None,
            effects=(
                CrossShardLedgerEffectV1(
                    asset_id="quote",
                    account_id=CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1,
                    delta_atoms=-1_000,
                ),
            ),
            total_debit_atoms=1_000,
            total_credit_atoms=0,
        )
