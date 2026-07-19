from __future__ import annotations

from src.core.zusd import (
    E8,
    ZUSDCommand,
    init_state,
    step,
)


def test_zusd_oracle_auth_rejects_string_bool() -> None:
    result = step(
        init_state(),
        ZUSDCommand(tag="bootstrap_oracle", args={"price_e8": 100 * E8, "auth_ok": "yes"}),
    )

    assert result.ok is False
    assert result.state is None
    assert result.error == "bootstrap_oracle requires auth_ok=true"
