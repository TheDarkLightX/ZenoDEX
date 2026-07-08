from __future__ import annotations

import pytest

from src.state.balances import BalanceTable


def test_balance_table_set_get_and_sparse_zero_removal() -> None:
    table = BalanceTable()

    assert table.get("alice", "A") == 0
    table.set("alice", "A", 7)
    assert table.get("alice", "A") == 7

    table.set("alice", "A", 0)
    assert table.get("alice", "A") == 0
    assert table.get_all_balances() == {}


def test_balance_table_rejects_negative_set() -> None:
    table = BalanceTable()

    with pytest.raises(ValueError, match="cannot be negative"):
        table.set("alice", "A", -1)


def test_balance_table_add_and_subtract_enforce_non_negative() -> None:
    table = BalanceTable()
    table.set("alice", "A", 5)

    table.add("alice", "A", 3)
    assert table.get("alice", "A") == 8

    table.subtract("alice", "A", 8)
    assert table.get("alice", "A") == 0

    with pytest.raises(ValueError, match="Delta must be non-negative"):
        table.subtract("alice", "A", -1)

    with pytest.raises(ValueError, match="Insufficient balance"):
        table.add("alice", "A", -1)


def test_balance_table_asset_view_and_repr() -> None:
    table = BalanceTable()
    table.set("alice", "A", 5)
    table.set("bob", "A", 9)
    table.set("carol", "B", 4)

    assert table.get_balances_for_asset("A") == {"alice": 5, "bob": 9}
    assert table.get_balances_for_asset("missing") == {}
    assert repr(table) == "BalanceTable(3 entries)"


def test_balance_table_verify_non_negative_detects_corruption() -> None:
    table = BalanceTable()
    table.set("alice", "A", 1)
    assert table.verify_non_negative() is True

    table._balances[("alice", "A")] = -1
    assert table.verify_non_negative() is False
