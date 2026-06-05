from __future__ import annotations

import pytest

from src.core.zusd_multi_oracle_commit_mcr import (
    E8,
    ZUSDMultiOracleCommitMCROutcome,
    check_multi_oracle_commit_mcr,
)


def test_multi_oracle_commit_mcr_accepts_when_both_vaults_are_safe() -> None:
    outcome = check_multi_oracle_commit_mcr(
        price_pending_e8=100 * E8,
        mcr_bps=11_000,
        vault_a_collateral_e8=2 * E8,
        vault_a_debt_e8=150 * E8,
        vault_b_collateral_e8=2 * E8,
        vault_b_debt_e8=100 * E8,
    )

    assert outcome.vault_a_mcr_ok is True
    assert outcome.vault_b_mcr_ok is True
    assert outcome.mcr_ok_at_pending is True


def test_multi_oracle_commit_mcr_rejects_when_one_vault_falls_below_mcr() -> None:
    outcome = check_multi_oracle_commit_mcr(
        price_pending_e8=50 * E8,
        mcr_bps=11_000,
        vault_a_collateral_e8=2 * E8,
        vault_a_debt_e8=150 * E8,
        vault_b_collateral_e8=2 * E8,
        vault_b_debt_e8=80 * E8,
    )

    assert outcome.vault_a_mcr_ok is False
    assert outcome.vault_b_mcr_ok is True
    assert outcome.mcr_ok_at_pending is False


def test_multi_oracle_commit_mcr_treats_zero_debt_vaults_as_safe_even_at_zero_pending() -> None:
    outcome = check_multi_oracle_commit_mcr(
        price_pending_e8=0,
        mcr_bps=11_000,
        vault_a_collateral_e8=0,
        vault_a_debt_e8=0,
        vault_b_collateral_e8=5 * E8,
        vault_b_debt_e8=0,
    )

    assert outcome.vault_a_mcr_ok is True
    assert outcome.vault_b_mcr_ok is True
    assert outcome.mcr_ok_at_pending is True


def test_multi_oracle_commit_mcr_rejects_bool_numeric_inputs() -> None:
    # REVIEW [B -> A-]: the running helper already rejected bool-as-int on some
    # paths; pin all public numeric inputs because these fields feed oracle/MCR
    # policy bits consumed by zUSD mint/commit gates.
    valid = {
        "price_pending_e8": 100 * E8,
        "mcr_bps": 11_000,
        "vault_a_collateral_e8": 2 * E8,
        "vault_a_debt_e8": 100 * E8,
        "vault_b_collateral_e8": 2 * E8,
        "vault_b_debt_e8": 100 * E8,
    }
    for field in valid:
        bad = dict(valid)
        bad[field] = True
        with pytest.raises(ValueError, match=field):
            check_multi_oracle_commit_mcr(**bad)


def test_multi_oracle_commit_mcr_outcome_rejects_forged_witness_fields() -> None:
    # REVIEW [B -> A-]: direct outcome construction is part of the evidence
    # surface. It must reject truthy non-bools and aggregate flags that do not
    # match the per-vault facts.
    with pytest.raises(ValueError, match="price_pending_e8"):
        ZUSDMultiOracleCommitMCROutcome(
            price_pending_e8=True,  # type: ignore[arg-type]
            mcr_bps=11_000,
            vault_a_mcr_ok=True,
            vault_b_mcr_ok=True,
            mcr_ok_at_pending=True,
        )

    with pytest.raises(TypeError, match="vault_a_mcr_ok"):
        ZUSDMultiOracleCommitMCROutcome(
            price_pending_e8=100 * E8,
            mcr_bps=11_000,
            vault_a_mcr_ok="yes",  # type: ignore[arg-type]
            vault_b_mcr_ok=True,
            mcr_ok_at_pending=True,
        )

    with pytest.raises(ValueError, match="mcr_ok_at_pending"):
        ZUSDMultiOracleCommitMCROutcome(
            price_pending_e8=100 * E8,
            mcr_bps=11_000,
            vault_a_mcr_ok=True,
            vault_b_mcr_ok=False,
            mcr_ok_at_pending=True,
        )
