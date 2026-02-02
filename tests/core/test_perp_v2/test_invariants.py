"""Tests for src/core/perp_v2/invariants.py — 16 invariant checkers."""

from dataclasses import replace

from src.core.perp_v2.invariants import INVARIANT_REGISTRY, check_all
from src.core.perp_v2.state import initial_state


class TestAllInvariantsOnInitialState:
    def test_initial_state_passes_all(self):
        s = initial_state()
        violations = check_all(s)
        assert violations == []

    def test_registry_has_16_invariants(self):
        assert len(INVARIANT_REGISTRY) == 16


class TestClearingNotFromFuture:
    def test_pass(self):
        s = replace(initial_state(), now_epoch=10, clearing_price_epoch=5)
        assert "inv_clearing_not_from_future" not in check_all(s)

    def test_fail(self):
        s = replace(initial_state(), now_epoch=5, clearing_price_epoch=10)
        assert "inv_clearing_not_from_future" in check_all(s)


class TestClearingSeenZeroed:
    def test_pass_seen(self):
        s = replace(initial_state(), clearing_price_seen=True, clearing_price_epoch=5, clearing_price_e8=100)
        # When seen=True, invariant holds regardless
        assert "inv_clearing_seen_zeroed" not in check_all(s)

    def test_pass_not_seen_zeroed(self):
        s = replace(initial_state(), clearing_price_seen=False, clearing_price_epoch=0, clearing_price_e8=0)
        assert "inv_clearing_seen_zeroed" not in check_all(s)

    def test_fail_not_seen_nonzero(self):
        s = replace(initial_state(), clearing_price_seen=False, clearing_price_epoch=5)
        assert "inv_clearing_seen_zeroed" in check_all(s)


class TestOracleNotFromFuture:
    def test_pass(self):
        s = replace(initial_state(), now_epoch=10, oracle_last_update_epoch=5)
        assert "inv_oracle_not_from_future" not in check_all(s)

    def test_fail(self):
        s = replace(initial_state(), now_epoch=5, oracle_last_update_epoch=10)
        assert "inv_oracle_not_from_future" in check_all(s)


class TestOracleSeenZeroed:
    def test_fail_not_seen_nonzero(self):
        s = replace(initial_state(), oracle_seen=False, index_price_e8=100)
        assert "inv_oracle_seen_zeroed" in check_all(s)


class TestBreakerNotFromFuture:
    def test_fail(self):
        s = replace(initial_state(), now_epoch=5, breaker_last_trigger_epoch=10, breaker_active=True)
        assert "inv_breaker_not_from_future" in check_all(s)


class TestBreakerInactiveZeroed:
    def test_fail(self):
        s = replace(initial_state(), breaker_active=False, breaker_last_trigger_epoch=5)
        assert "inv_breaker_inactive_zeroed" in check_all(s)


class TestMarginParamsOrdered:
    def test_pass(self):
        # eff_maint = 500+100=600, initial=1000 → 600 <= 1000 ✓
        # max_move=500 → 500 <= 600 ✓
        s = initial_state()
        assert "inv_margin_params_ordered" not in check_all(s)

    def test_fail_maint_exceeds_initial(self):
        s = replace(initial_state(), maintenance_margin_bps=900, depeg_buffer_bps=200, initial_margin_bps=1000)
        # eff_maint = 1100 > initial 1000
        assert "inv_margin_params_ordered" in check_all(s)


class TestEntryZeroWhenFlat:
    def test_fail(self):
        s = replace(initial_state(), position_base=0, entry_price_e8=100)
        assert "inv_entry_zero_when_flat" in check_all(s)


class TestEntryMatchesPriceWhenOpen:
    def test_fail(self):
        s = replace(
            initial_state(),
            position_base=100,
            entry_price_e8=200_000_000,
            index_price_e8=100_000_000,
            oracle_seen=True,
            oracle_last_update_epoch=0,
            collateral_quote=1_000_000,  # enough margin
        )
        assert "inv_entry_matches_price_when_open" in check_all(s)


class TestMaintMarginOk:
    def test_fail_undercollateralized(self):
        s = replace(
            initial_state(),
            position_base=1000,
            entry_price_e8=100_000_000,
            index_price_e8=100_000_000,
            oracle_seen=True,
            collateral_quote=0,
        )
        assert "inv_maint_margin_ok" in check_all(s)


class TestFundingBounded:
    def test_pass(self):
        s = replace(initial_state(), funding_rate_bps=50, funding_cap_bps=100)
        assert "inv_funding_bounded" not in check_all(s)

    def test_fail(self):
        s = replace(initial_state(), funding_rate_bps=200, funding_cap_bps=100)
        assert "inv_funding_bounded" in check_all(s)


class TestInsuranceNonneg:
    def test_pass(self):
        assert "inv_insurance_nonneg" not in check_all(initial_state())


class TestInsuranceConservation:
    def test_pass(self):
        assert "inv_insurance_conservation" not in check_all(initial_state())

    def test_fail(self):
        s = replace(initial_state(), insurance_balance=999, initial_insurance=0, fee_income=0, claims_paid=0)
        assert "inv_insurance_conservation" in check_all(s)


class TestLiquidationIcGuard:
    def test_pass(self):
        assert "inv_liquidation_ic_guard" not in check_all(initial_state())

    def test_fail(self):
        # liq_penalty=600 >= eff_maint=600
        s = replace(initial_state(), liquidation_penalty_bps=600)
        assert "inv_liquidation_ic_guard" in check_all(s)


class TestFundingEpochGated:
    def test_fail(self):
        s = replace(initial_state(), funding_last_applied_epoch=5, now_epoch=3)
        assert "inv_funding_epoch_gated" in check_all(s)


class TestFeePoolEqFeeIncome:
    def test_fail(self):
        s = replace(initial_state(), fee_pool_quote=100, fee_income=0)
        assert "inv_fee_pool_eq_fee_income" in check_all(s)
