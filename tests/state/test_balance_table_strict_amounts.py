import pytest

from src.state.balances import BalanceTable


def test_balance_table_rejects_bool_amounts_before_state_mutation() -> None:
    table = BalanceTable()

    with pytest.raises(TypeError, match="amount must be an int"):
        table.set("alice", "A", True)

    assert table.get("alice", "A") == 0


def test_balance_table_rejects_bool_deltas_before_state_mutation() -> None:
    table = BalanceTable()
    table.set("alice", "A", 10)

    with pytest.raises(TypeError, match="delta must be an int"):
        table.add("alice", "A", True)
    with pytest.raises(TypeError, match="delta must be an int"):
        table.subtract("alice", "A", False)

    assert table.get("alice", "A") == 10


def test_balance_table_rejects_non_int_amounts_and_deltas() -> None:
    table = BalanceTable()

    with pytest.raises(TypeError, match="amount must be an int"):
        table.set("alice", "A", "1")  # type: ignore[arg-type]

    table.set("alice", "A", 3)
    with pytest.raises(TypeError, match="delta must be an int"):
        table.add("alice", "A", "1")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="delta must be an int"):
        table.subtract("alice", "A", "1")  # type: ignore[arg-type]

    assert table.get("alice", "A") == 3
