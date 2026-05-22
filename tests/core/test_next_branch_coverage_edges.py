from __future__ import annotations

from fractions import Fraction

import pytest

from src.core.cpmm_u256_safety import (
    analyze_cpmm_exact_in_u256_overflows,
    fee_total_ceil_bigint,
    fee_total_ceil_decomposed,
    mul_div_floor_gcd_reduced_u256,
)
from src.core.epoch_oracle_commitment import (
    EpochOracleCommitment,
    OracleRegistry,
    estimate_cross_module_arbitrage_bps,
)
from src.core.mobius_cpmm import Mobius, cpmm_pool_mobius, cpmm_two_hop_collapsed_floor_fee0
from src.core.price_impact_preview import compute_isolated_output, compute_price_impact_bps
from src.core.fixed_width import U256_MAX


def test_mobius_helpers_reject_zero_denominator_and_bad_inputs() -> None:
    zero_den = Mobius(a=1, b=0, c=0, d=0)
    with pytest.raises(ZeroDivisionError, match="Mobius denominator is zero"):
        zero_den.eval_fraction(Fraction(1, 1))
    with pytest.raises(ZeroDivisionError, match="Mobius denominator is zero"):
        zero_den.eval_floor_int(1)

    with pytest.raises(TypeError, match="reserve_in must be an int"):
        cpmm_pool_mobius(reserve_in=True, reserve_out=10)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="x1 must be an int"):
        cpmm_two_hop_collapsed_floor_fee0(x1=True, y1=1, x2=1, y2=1, dx=1)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="x1,y1,x2,y2,dx must be positive"):
        cpmm_two_hop_collapsed_floor_fee0(x1=0, y1=1, x2=1, y2=1, dx=1)


def test_price_impact_helpers_cover_reserve_and_zero_output_edges() -> None:
    with pytest.raises(ValueError, match="Reserves must be positive"):
        compute_isolated_output(0, 1_000, 1, 0)

    assert compute_price_impact_bps(1_000_000, 1_000_000, 1, 10_000) == 10_000


def test_epoch_oracle_commitment_rejects_invalid_fields_and_stale_registry_reads() -> None:
    with pytest.raises(ValueError, match="epoch must be non-negative"):
        EpochOracleCommitment(epoch=-1, price_e8=100, timestamp=1, source_hash="src")
    with pytest.raises(ValueError, match="price_e8 must be positive"):
        EpochOracleCommitment(epoch=1, price_e8=0, timestamp=1, source_hash="src")
    with pytest.raises(ValueError, match="timestamp must be non-negative"):
        EpochOracleCommitment(epoch=1, price_e8=100, timestamp=-1, source_hash="src")
    with pytest.raises(ValueError, match="source_hash must be non-empty"):
        EpochOracleCommitment(epoch=1, price_e8=100, timestamp=1, source_hash="")

    reg = OracleRegistry()
    reg.commit(EpochOracleCommitment(epoch=2, price_e8=101_000_000, timestamp=2, source_hash="h2"))
    assert reg.get_price_e8(2) == 101_000_000
    with pytest.raises(ValueError, match="not strictly after latest epoch"):
        reg.commit(EpochOracleCommitment(epoch=1, price_e8=100_000_000, timestamp=1, source_hash="h1"))
    with pytest.raises(KeyError, match="No oracle commitment for epoch 3"):
        reg.get_price_e8(3)

    with pytest.raises(ValueError, match="Prices must be positive"):
        estimate_cross_module_arbitrage_bps(0, 100_000_000, 1)
    assert estimate_cross_module_arbitrage_bps(100_000_000, 101_000_000, 0) == 0


def test_cpmm_u256_safety_rejects_bounds_and_reports_intractable_muldiv() -> None:
    with pytest.raises(ValueError, match="gross_in must be non-negative"):
        fee_total_ceil_bigint(-1, 0)
    with pytest.raises(ValueError, match="fee_bps out of range"):
        fee_total_ceil_bigint(1, 10_001)
    with pytest.raises(ValueError, match="gross_in must be non-negative"):
        fee_total_ceil_decomposed(-1, 0)
    with pytest.raises(ValueError, match="fee_bps out of range"):
        fee_total_ceil_decomposed(1, 10_001)

    with pytest.raises(ValueError, match="a,b must be non-negative and c must be positive"):
        mul_div_floor_gcd_reduced_u256(a=-1, b=1, c=1)
    with pytest.raises(ValueError, match="inputs must fit in u256"):
        mul_div_floor_gcd_reduced_u256(a=U256_MAX + 1, b=1, c=1)
    assert mul_div_floor_gcd_reduced_u256(a=U256_MAX, b=U256_MAX, c=1) is None

    with pytest.raises(TypeError, match="reserve_in must be an int"):
        analyze_cpmm_exact_in_u256_overflows(
            reserve_in=True,  # type: ignore[arg-type]
            reserve_out=1,
            amount_in=1,
            fee_bps=0,
        )
    with pytest.raises(ValueError, match="inputs must fit in u256"):
        analyze_cpmm_exact_in_u256_overflows(
            reserve_in=U256_MAX + 1,
            reserve_out=1,
            amount_in=1,
            fee_bps=0,
        )
