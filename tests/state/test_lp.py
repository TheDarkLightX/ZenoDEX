from __future__ import annotations

import pytest

from src.state.lp import LPTable


def test_lp_table_set_get_and_sparse_zero_removal() -> None:
    table = LPTable()

    assert table.get("alice", "pool") == 0
    table.set("alice", "pool", 7)
    assert table.get("alice", "pool") == 7

    table.set("alice", "pool", 0)
    assert table.get("alice", "pool") == 0
    assert table.get_all_balances() == {}


def test_lp_table_rejects_negative_set() -> None:
    table = LPTable()

    with pytest.raises(ValueError, match="cannot be negative"):
        table.set("alice", "pool", -1)


def test_lp_table_add_and_subtract_enforce_non_negative() -> None:
    table = LPTable()
    table.set("alice", "pool", 5)

    table.add("alice", "pool", 3)
    assert table.get("alice", "pool") == 8

    table.subtract("alice", "pool", 8)
    assert table.get("alice", "pool") == 0

    with pytest.raises(ValueError, match="Delta must be non-negative"):
        table.subtract("alice", "pool", -1)

    with pytest.raises(ValueError, match="Insufficient LP balance"):
        table.add("alice", "pool", -1)


def test_lp_table_verify_non_negative_and_repr() -> None:
    table = LPTable()
    table.set("alice", "pool-a", 5)
    table.set("bob", "pool-b", 9)

    assert table.verify_non_negative() is True
    assert repr(table) == "LPTable(2 entries)"

    table._balances[("alice", "pool-a")] = -1
    assert table.verify_non_negative() is False
