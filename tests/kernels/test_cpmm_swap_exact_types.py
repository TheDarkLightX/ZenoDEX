from __future__ import annotations

import pytest

from src.kernels.python import cpmm_swap_v8, cpmm_swap_v9


class _ExecutableInt(int):
    """An integer-shaped object whose multiplication changes fee arithmetic."""

    def __mul__(self, _other: object) -> int:
        return 0


@pytest.mark.parametrize("kernel", [cpmm_swap_v8, cpmm_swap_v9])
def test_exact_in_rejects_executable_int_subclass_before_arithmetic(kernel: object) -> None:
    swap_exact_in = kernel.swap_exact_in
    normal = swap_exact_in(
        reserve_in=1_000,
        reserve_out=1_000,
        amount_in=201,
        fee_bps=50,
        protocol_fee_share_bps=5_000,
    )
    assert (normal.fee_total, normal.protocol_fee, normal.amount_out) == (2, 1, 165)

    with pytest.raises(TypeError, match="amount_in must be an int"):
        swap_exact_in(
            reserve_in=1_000,
            reserve_out=1_000,
            amount_in=_ExecutableInt(201),
            fee_bps=50,
            protocol_fee_share_bps=5_000,
        )


@pytest.mark.parametrize("kernel", [cpmm_swap_v8, cpmm_swap_v9])
def test_exact_out_rejects_executable_int_subclass_before_arithmetic(kernel: object) -> None:
    swap_exact_out = kernel.swap_exact_out

    with pytest.raises(TypeError, match="amount_out must be an int"):
        swap_exact_out(
            reserve_in=1_000,
            reserve_out=1_000,
            amount_out=_ExecutableInt(100),
            fee_bps=50,
        )


def test_fee_helpers_reject_executable_int_subclasses() -> None:
    with pytest.raises(TypeError, match="gross_in must be an int"):
        cpmm_swap_v8.compute_fee_total(gross_in=_ExecutableInt(201), fee_bps=50)
    with pytest.raises(TypeError, match="fee_total must be an int"):
        cpmm_swap_v9.compute_protocol_fee(
            fee_total=_ExecutableInt(2),
            protocol_fee_share_bps=5_000,
        )
