# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.cpmm import swap_exact_in, swap_exact_out
from src.integration.tau_runner import split_u32
from src.integration.tau_witness import build_swap_exact_in_v1_step, build_swap_exact_out_v1_step


def test_build_swap_exact_in_v1_step_matches_split_u32() -> None:
    reserve_in = 2_000_000
    reserve_out = 2_000_000
    amount_in = 1000
    fee_bps = 30
    min_amount_out = 1

    amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )

    step = build_swap_exact_in_v1_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        min_amount_out=min_amount_out,
        amount_out=amount_out,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )

    assert (step["i1"], step["i2"]) == split_u32(reserve_in)
    assert (step["i3"], step["i4"]) == split_u32(reserve_out)
    assert (step["i5"], step["i6"]) == split_u32(amount_in)
    assert (step["i8"], step["i9"]) == split_u32(min_amount_out)
    assert (step["i10"], step["i11"]) == split_u32(amount_out)
    assert (step["i12"], step["i13"]) == split_u32(new_reserve_in)
    assert (step["i14"], step["i15"]) == split_u32(new_reserve_out)


def test_build_swap_exact_out_v1_step_matches_split_u32() -> None:
    reserve_in = 2_000_000
    reserve_out = 2_000_000
    amount_out = 1000
    fee_bps = 30
    max_amount_in = 10_000_000

    amount_in, (new_reserve_in, new_reserve_out) = swap_exact_out(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
    )

    step = build_swap_exact_out_v1_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_amount_in=max_amount_in,
        amount_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )

    assert (step["i1"], step["i2"]) == split_u32(reserve_in)
    assert (step["i3"], step["i4"]) == split_u32(reserve_out)
    assert (step["i5"], step["i6"]) == split_u32(amount_out)
    assert (step["i8"], step["i9"]) == split_u32(max_amount_in)
    assert (step["i10"], step["i11"]) == split_u32(amount_in)
    assert (step["i12"], step["i13"]) == split_u32(new_reserve_in)
    assert (step["i14"], step["i15"]) == split_u32(new_reserve_out)


def test_build_witness_rejects_out_of_u32_range() -> None:
    with pytest.raises(ValueError):
        build_swap_exact_in_v1_step(
            reserve_in=0x1_0000_0000,  # > u32 max
            reserve_out=1,
            amount_in=1,
            fee_bps=0,
            min_amount_out=0,
            amount_out=1,
            new_reserve_in=1,
            new_reserve_out=1,
        )
