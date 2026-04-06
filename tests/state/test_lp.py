from __future__ import annotations

import pytest

from src.state.lp import LPTable

PK = "0x" + "11" * 48
POOL_ID = "pool-1"


def test_lp_table_defaults_and_zero_removal() -> None:
    lp = LPTable()

    assert lp.get(PK, POOL_ID) == 0

    lp.set(PK, POOL_ID, 13)
    assert lp.get(PK, POOL_ID) == 13

    lp.set(PK, POOL_ID, 0)
    assert lp.get(PK, POOL_ID) == 0
    assert lp.get_all_balances() == {}


def test_lp_table_add_subtract_and_verify_non_negative() -> None:
    lp = LPTable()

    lp.add(PK, POOL_ID, 9)
    lp.subtract(PK, POOL_ID, 4)

    assert lp.get(PK, POOL_ID) == 5
    assert lp.verify_non_negative() is True


@pytest.mark.parametrize("delta", [-1, -3])
def test_lp_table_rejects_negative_or_overdrawn_updates(delta: int) -> None:
    lp = LPTable()

    with pytest.raises(ValueError):
        lp.set(PK, POOL_ID, delta)

    with pytest.raises(ValueError):
        lp.subtract(PK, POOL_ID, delta)

    with pytest.raises(ValueError):
        lp.add(PK, POOL_ID, delta)
