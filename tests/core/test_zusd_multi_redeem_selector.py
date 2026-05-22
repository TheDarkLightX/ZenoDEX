from __future__ import annotations

import pytest

from src.core.zusd_multi_redeem_selector import E8, select_multi_redeem_vault


def test_selector_chooses_vault_closest_to_mcr() -> None:
    outcome = select_multi_redeem_vault(
        amount_e8=50 * E8,
        price_e8=100 * E8,
        mcr_bps=11_000,
        vault_a_collateral_e8=5 * E8,
        vault_a_debt_e8=200 * E8,
        vault_b_collateral_e8=5 * E8,
        vault_b_debt_e8=300 * E8,
    )

    assert outcome.candidate_a_ok is True
    assert outcome.candidate_b_ok is True
    assert outcome.selected_vault == "b"
    assert outcome.selected_post_debt_e8 == 250 * E8


def test_selector_tie_breaks_to_vault_a() -> None:
    outcome = select_multi_redeem_vault(
        amount_e8=50 * E8,
        price_e8=100 * E8,
        mcr_bps=11_000,
        vault_a_collateral_e8=4 * E8,
        vault_a_debt_e8=200 * E8,
        vault_b_collateral_e8=4 * E8,
        vault_b_debt_e8=200 * E8,
    )

    assert outcome.candidate_a_ok is True
    assert outcome.candidate_b_ok is True
    assert outcome.selected_vault == "a"


def test_selector_returns_none_when_no_candidate_satisfies_policy() -> None:
    outcome = select_multi_redeem_vault(
        amount_e8=150 * E8,
        price_e8=100 * E8,
        mcr_bps=11_000,
        vault_a_collateral_e8=1 * E8,
        vault_a_debt_e8=200 * E8,
        vault_b_collateral_e8=3 * E8,
        vault_b_debt_e8=10 * E8,
    )

    assert outcome.candidate_a_ok is False
    assert outcome.candidate_b_ok is False
    assert outcome.selected_vault is None


def test_selector_rejects_tiny_gross_collateral_case() -> None:
    with pytest.raises(ValueError, match="amount too small"):
        select_multi_redeem_vault(
            amount_e8=1,
            price_e8=10**30,
            mcr_bps=11_000,
            vault_a_collateral_e8=10,
            vault_a_debt_e8=10,
            vault_b_collateral_e8=10,
            vault_b_debt_e8=10,
        )


def test_selector_exact_defense_boundary_flips_selection() -> None:
    below = select_multi_redeem_vault(
        amount_e8=50 * E8,
        price_e8=100 * E8,
        mcr_bps=11_000,
        vault_a_collateral_e8=390_000_000,
        vault_a_debt_e8=200 * E8,
        vault_b_collateral_e8=5 * E8,
        vault_b_debt_e8=300 * E8,
    )
    at = select_multi_redeem_vault(
        amount_e8=50 * E8,
        price_e8=100 * E8,
        mcr_bps=11_000,
        vault_a_collateral_e8=390_000_001,
        vault_a_debt_e8=200 * E8,
        vault_b_collateral_e8=5 * E8,
        vault_b_debt_e8=300 * E8,
    )

    assert below.candidate_a_ok is True
    assert below.candidate_b_ok is True
    assert below.selected_vault == "a"
    assert at.candidate_a_ok is True
    assert at.candidate_b_ok is True
    assert at.selected_vault == "b"
