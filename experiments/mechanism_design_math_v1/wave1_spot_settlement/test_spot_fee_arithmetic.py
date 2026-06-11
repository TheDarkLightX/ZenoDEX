"""Wave 1 spot-settlement arithmetic evidence.

These tests cover the local integer fee obligations in
`docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md`:

- H-MD-SS-002 / O-SS-02: splitting an exact-in order cannot reduce the total
  ceil-rounded fee in the bounded model below.
- H-MD-SS-008 / O-SS-07: fee routing with dust carry conserves value at every
  split and leaves strictly less than three fee units as three-way dust.

They are research evidence only. They do not change settlement behavior.
"""

from __future__ import annotations

from itertools import product

from src.core.cpmm import compute_fee_total
from src.core.fees import (
    BPS_DENOM,
    FeeAccumulatorState,
    FeeSplitParams,
    split_fee_with_dust_carry,
)


def _ceil_fee_formula(gross: int, fee_bps: int) -> int:
    return (gross * fee_bps + BPS_DENOM - 1) // BPS_DENOM


def test_h_md_ss_002_ceil_fee_superadditivity_bounded() -> None:
    """Every two-way split in this bounded grid pays at least the one-shot fee."""

    # Exhaustive over all fee rates and all two-part partitions up to 64 units:
    # 10_001 * sum_{g=0..64}(g+1) = 21,127,111 integer partition checks.
    for fee_bps in range(BPS_DENOM + 1):
        for gross in range(65):
            whole = _ceil_fee_formula(gross, fee_bps)
            for first in range(gross + 1):
                second = gross - first
                split_total = _ceil_fee_formula(first, fee_bps) + _ceil_fee_formula(
                    second, fee_bps
                )
                assert split_total >= whole

    # Bind the formula to the consensus helper on a broader representative grid.
    gross_cases = (0, 1, 2, 3, 7, 10, 31, 64, 65, 99, 127, 255, 1_000, 65_535)
    fee_cases = (0, 1, 2, 3, 7, 30, 99, 333, 999, 2_500, 5_000, 9_999, 10_000)
    for gross, fee_bps in product(gross_cases, fee_cases):
        assert compute_fee_total(gross, fee_bps) == _ceil_fee_formula(gross, fee_bps)


def test_h_md_ss_008_dust_conservation_and_tight_bound() -> None:
    """Three-way floor split conserves each step and always carries dust < 3."""

    param_cases = (
        FeeSplitParams(0, 0, BPS_DENOM),
        FeeSplitParams(BPS_DENOM, 0, 0),
        FeeSplitParams(0, BPS_DENOM, 0),
        FeeSplitParams(3_333, 3_333, 3_334),
        FeeSplitParams(1, 9_999, 0),
        FeeSplitParams(9_998, 1, 1),
        FeeSplitParams(2_500, 2_500, 5_000),
        FeeSplitParams(1_111, 2_222, 6_667),
    )
    fee_cases = (0, 1, 2, 3, 7, 10, 31, 99, 127, 255, 1_000, 10_001, 65_535)
    dust_cases = (0, 1, 2, 3, 7, 99, 10_000, 65_535)

    for params, fee, dust in product(param_cases, fee_cases, dust_cases):
        result, next_state = split_fee_with_dust_carry(
            fee,
            params,
            state=FeeAccumulatorState(dust=dust),
        )
        distributed = (
            result.buyback_amount + result.treasury_amount + result.rewards_amount
        )
        assert distributed + result.dust_carried == fee + dust
        assert next_state.dust == result.dust_carried
        assert 0 <= result.dust_carried < 3


def test_h_md_ss_008_dust_conservation_over_sequences() -> None:
    """Across repeated splits, total distributed plus final dust equals total input."""

    params = FeeSplitParams(3_333, 3_333, 3_334)
    fees = (1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233)
    state = FeeAccumulatorState(dust=0)
    distributed_total = 0

    for fee in fees:
        result, state = split_fee_with_dust_carry(fee, params, state=state)
        distributed_total += (
            result.buyback_amount + result.treasury_amount + result.rewards_amount
        )
        assert result.dust_carried < 3

    assert distributed_total + state.dust == sum(fees)
