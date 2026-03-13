from __future__ import annotations

import pytest

from src.core.zusd_multi_oracle_commit_mcr import check_multi_oracle_commit_mcr


def test_multi_oracle_commit_mcr_accepts_both_vaults_when_safe() -> None:
    outcome = check_multi_oracle_commit_mcr(
        price_pending_e8=200_00000000,
        mcr_bps=11_000,
        vault_a_collateral_e8=2_00000000,
        vault_a_debt_e8=300_00000000,
        vault_b_collateral_e8=3_00000000,
        vault_b_debt_e8=400_00000000,
    )
    assert outcome.vault_a_mcr_ok is True
    assert outcome.vault_b_mcr_ok is True
    assert outcome.mcr_ok_at_pending is True


def test_multi_oracle_commit_mcr_rejects_when_any_vault_fails() -> None:
    outcome = check_multi_oracle_commit_mcr(
        price_pending_e8=100_00000000,
        mcr_bps=15_000,
        vault_a_collateral_e8=1_00000000,
        vault_a_debt_e8=100_00000000,
        vault_b_collateral_e8=1_00000000,
        vault_b_debt_e8=100_00000000,
    )
    assert outcome.mcr_ok_at_pending is False
    assert (outcome.vault_a_mcr_ok, outcome.vault_b_mcr_ok) == (False, False)


def test_multi_oracle_commit_mcr_validates_inputs() -> None:
    with pytest.raises(ValueError, match="price_pending_e8 must be a non-negative int"):
        check_multi_oracle_commit_mcr(
            price_pending_e8=-1,
            mcr_bps=11_000,
            vault_a_collateral_e8=1,
            vault_a_debt_e8=1,
            vault_b_collateral_e8=1,
            vault_b_debt_e8=1,
        )
