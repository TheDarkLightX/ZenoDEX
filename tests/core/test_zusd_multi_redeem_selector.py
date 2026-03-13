from __future__ import annotations

import pytest

from src.core.zusd_multi_redeem_selector import select_multi_redeem_vault


def test_multi_redeem_selector_chooses_smaller_headroom_vault_when_both_safe() -> None:
    outcome = select_multi_redeem_vault(
        amount_e8=100_00000000,
        price_e8=200_00000000,
        mcr_bps=11_000,
        vault_a_collateral_e8=1_50000000,
        vault_a_debt_e8=200_00000000,
        vault_b_collateral_e8=3_00000000,
        vault_b_debt_e8=200_00000000,
    )
    assert outcome.candidate_a_ok is True
    assert outcome.candidate_b_ok is True
    assert outcome.selected_vault == "a"


def test_multi_redeem_selector_returns_none_when_neither_vault_is_safe() -> None:
    outcome = select_multi_redeem_vault(
        amount_e8=100_00000000,
        price_e8=100_00000000,
        mcr_bps=15_000,
        vault_a_collateral_e8=1_00000000,
        vault_a_debt_e8=150_00000000,
        vault_b_collateral_e8=1_00000000,
        vault_b_debt_e8=150_00000000,
    )
    assert outcome.selected_vault is None


def test_multi_redeem_selector_validates_positive_price_and_amount() -> None:
    with pytest.raises(ValueError, match="amount_e8 must be a positive int"):
        select_multi_redeem_vault(
            amount_e8=0,
            price_e8=100_00000000,
            mcr_bps=11_000,
            vault_a_collateral_e8=1,
            vault_a_debt_e8=1,
            vault_b_collateral_e8=1,
            vault_b_debt_e8=1,
        )
