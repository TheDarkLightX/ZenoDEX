# [TESTER] v1

from __future__ import annotations

import pytest

from src.kernels.python.lp_math_v7 import mint_liquidity


def test_mint_liquidity_rejects_inconsistent_initial_state() -> None:
    with pytest.raises(ValueError, match="initial liquidity"):
        mint_liquidity(
            reserve0=1,
            reserve1=1,
            total_supply=0,
            amount0_desired=10,
            amount1_desired=10,
        )

