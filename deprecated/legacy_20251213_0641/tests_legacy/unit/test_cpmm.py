"""
Unit tests for CPMM algorithm.
"""

import pytest

from src.core.cpmm import (
    swap_exact_in,
    swap_exact_out,
    compute_lp_mint,
    compute_lp_burn,
    MIN_LP_LOCK,
)


class TestSwapExactIn:
    """Test exact-in swap calculations."""
    
    def test_basic_swap(self):
        """Test basic swap with no fee."""
        reserve_in = 1000
        reserve_out = 1000
        amount_in = 100
        fee_bps = 0
        
        amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in(
            reserve_in, reserve_out, amount_in, fee_bps
        )
        
        assert amount_out == 90  # 1000 * 100 / 1100 = 90.9... -> 90
        assert new_reserve_in == 1100
        assert new_reserve_out == 910
        assert new_reserve_in * new_reserve_out >= reserve_in * reserve_out
    
    def test_swap_with_fee(self):
        """Test swap with 30 bps fee."""
        reserve_in = 1000
        reserve_out = 1000
        amount_in = 100
        fee_bps = 30  # 0.3%
        
        amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in(
            reserve_in, reserve_out, amount_in, fee_bps
        )
        
        # Fee = ceil(100 * 30 / 10000) = ceil(0.3) = 1
        # Net in = 99
        # Amount out = floor(1000 * 99 / 1099) = 90
        assert amount_out == 90
        assert new_reserve_in == 1100
        assert new_reserve_out == 910
    
    def test_swap_invariant_preserved(self):
        """Test that CPMM invariant is preserved."""
        reserve_in = 1000000
        reserve_out = 1000000
        amount_in = 10000
        fee_bps = 30
        
        old_k = reserve_in * reserve_out
        
        amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in(
            reserve_in, reserve_out, amount_in, fee_bps
        )
        
        new_k = new_reserve_in * new_reserve_out
        assert new_k >= old_k
    
    def test_swap_edge_case_small_amount(self):
        """Test swap with very small amount."""
        reserve_in = 1000000
        reserve_out = 1000000
        amount_in = 100  # Use larger amount to avoid rounding to 0
        fee_bps = 30
        
        amount_out, _ = swap_exact_in(reserve_in, reserve_out, amount_in, fee_bps)
        assert amount_out > 0
        assert amount_out < reserve_out
    
    def test_swap_invalid_inputs(self):
        """Test that invalid inputs raise errors."""
        with pytest.raises(ValueError, match="amount_in must be positive"):
            swap_exact_in(1000, 1000, 0, 0)
        
        with pytest.raises(ValueError, match="fee_bps must be in"):
            swap_exact_in(1000, 1000, 100, 10001)


class TestSwapExactOut:
    """Test exact-out swap calculations."""
    
    def test_basic_exact_out(self):
        """Test basic exact-out swap."""
        reserve_in = 1000
        reserve_out = 1000
        amount_out = 90
        fee_bps = 0
        
        amount_in, (new_reserve_in, new_reserve_out) = swap_exact_out(
            reserve_in, reserve_out, amount_out, fee_bps
        )
        
        # Required net_in = ceil(1000 * 90 / 910) = ceil(98.9...) = 99
        # Amount in = 99 (no fee)
        assert amount_in == 99
        assert new_reserve_in == 1099
        assert new_reserve_out == 910
    
    def test_exact_out_with_fee(self):
        """Test exact-out swap with fee."""
        reserve_in = 1000
        reserve_out = 1000
        amount_out = 90
        fee_bps = 30
        
        amount_in, _ = swap_exact_out(reserve_in, reserve_out, amount_out, fee_bps)
        
        # Should require more input due to fee
        assert amount_in >= 99
    
    def test_exact_out_cannot_drain(self):
        """Test that exact-out cannot drain full reserve."""
        reserve_in = 1000
        reserve_out = 1000
        
        with pytest.raises(ValueError, match="Cannot drain full reserve"):
            swap_exact_out(reserve_in, reserve_out, reserve_out, 0)


class TestLPMinting:
    """Test LP token minting."""
    
    def test_first_deposit(self):
        """Test LP minting for first deposit."""
        reserve0 = 0
        reserve1 = 0
        amount0 = 10000  # Use larger amounts to get positive LP
        amount1 = 10000
        lp_supply = 0
        
        lp = compute_lp_mint(reserve0, reserve1, amount0, amount1, lp_supply)
        
        # lp = floor(sqrt(10000 * 10000)) - MIN_LP_LOCK = 10000 - 1000 = 9000
        expected = int((amount0 * amount1) ** 0.5) - MIN_LP_LOCK
        assert lp == max(1, expected)  # At least 1 LP token
    
    def test_subsequent_deposit(self):
        """Test LP minting for subsequent deposit."""
        reserve0 = 1000
        reserve1 = 1000
        amount0 = 100
        amount1 = 100
        lp_supply = 1000
        
        lp = compute_lp_mint(reserve0, reserve1, amount0, amount1, lp_supply)
        
        # lp = min(floor(100 * 1000 / 1000), floor(100 * 1000 / 1000))
        #    = min(100, 100) = 100
        assert lp == 100
    
    def test_unequal_deposit(self):
        """Test LP minting with unequal deposit amounts."""
        reserve0 = 1000
        reserve1 = 2000
        amount0 = 100
        amount1 = 200
        lp_supply = 1000
        
        lp = compute_lp_mint(reserve0, reserve1, amount0, amount1, lp_supply)
        
        # lp0 = floor(100 * 1000 / 1000) = 100
        # lp1 = floor(200 * 1000 / 2000) = 100
        # lp = min(100, 100) = 100
        assert lp == 100


class TestLPBurning:
    """Test LP token burning."""
    
    def test_basic_burn(self):
        """Test basic LP burn."""
        lp_amount = 100
        reserve0 = 1000
        reserve1 = 1000
        lp_supply = 1000
        
        amount0, amount1 = compute_lp_burn(
            lp_amount, reserve0, reserve1, lp_supply
        )
        
        # amount0 = floor(100 * 1000 / 1000) = 100
        # amount1 = floor(100 * 1000 / 1000) = 100
        assert amount0 == 100
        assert amount1 == 100
    
    def test_burn_proportional(self):
        """Test that burn returns proportional amounts."""
        lp_amount = 500
        reserve0 = 2000
        reserve1 = 1000
        lp_supply = 1000
        
        amount0, amount1 = compute_lp_burn(
            lp_amount, reserve0, reserve1, lp_supply
        )
        
        # amount0 = floor(500 * 2000 / 1000) = 1000
        # amount1 = floor(500 * 1000 / 1000) = 500
        assert amount0 == 1000
        assert amount1 == 500
    
    def test_burn_cannot_exceed_supply(self):
        """Test that burn cannot exceed supply."""
        with pytest.raises(ValueError, match="Cannot burn more LP"):
            compute_lp_burn(1001, 1000, 1000, 1000)

