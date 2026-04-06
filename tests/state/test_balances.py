from __future__ import annotations

import pytest

from src.state.balances import NATIVE_ASSET, BalanceTable

PK = "0x" + "11" * 48
ASSET = "0x" + "22" * 32


def test_balance_table_defaults_and_zero_removal() -> None:
    balances = BalanceTable()

    assert balances.get(PK, ASSET) == 0

    balances.set(PK, ASSET, 7)
    assert balances.get(PK, ASSET) == 7

    balances.set(PK, ASSET, 0)
    assert balances.get(PK, ASSET) == 0
    assert balances.get_all_balances() == {}


def test_balance_table_add_subtract_and_asset_view() -> None:
    balances = BalanceTable()

    balances.add(PK, NATIVE_ASSET, 9)
    balances.subtract(PK, NATIVE_ASSET, 4)

    assert balances.get(PK, NATIVE_ASSET) == 5
    assert balances.get_balances_for_asset(NATIVE_ASSET) == {PK: 5}
    assert balances.verify_non_negative() is True


@pytest.mark.parametrize("amount", [-1, -5])
def test_balance_table_rejects_negative_updates(amount: int) -> None:
    balances = BalanceTable()

    with pytest.raises(ValueError):
        balances.set(PK, ASSET, amount)

    with pytest.raises(ValueError):
        balances.subtract(PK, ASSET, amount)

    with pytest.raises(ValueError):
        balances.add(PK, ASSET, amount)
