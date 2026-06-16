import pytest

from src.state.lp import LPTable


def test_lp_table_rejects_bool_amounts_before_state_mutation() -> None:
    table = LPTable()

    with pytest.raises(TypeError, match="amount must be an int"):
        table.set("pk", "pool", True)

    assert table.get("pk", "pool") == 0


def test_lp_table_rejects_bool_deltas_before_state_mutation() -> None:
    table = LPTable()
    table.set("pk", "pool", 10)

    with pytest.raises(TypeError, match="delta must be an int"):
        table.add("pk", "pool", True)
    with pytest.raises(TypeError, match="delta must be an int"):
        table.subtract("pk", "pool", False)

    assert table.get("pk", "pool") == 10


def test_lp_table_rejects_non_int_amounts_and_deltas() -> None:
    table = LPTable()

    with pytest.raises(TypeError, match="amount must be an int"):
        table.set("pk", "pool", "1")  # type: ignore[arg-type]

    table.set("pk", "pool", 3)
    with pytest.raises(TypeError, match="delta must be an int"):
        table.add("pk", "pool", "1")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="delta must be an int"):
        table.subtract("pk", "pool", "1")  # type: ignore[arg-type]

    assert table.get("pk", "pool") == 3
