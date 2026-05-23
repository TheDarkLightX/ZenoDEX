from __future__ import annotations

from src.core.zusd_multi_oracle_commit_mcr import E8, check_multi_oracle_commit_mcr


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
