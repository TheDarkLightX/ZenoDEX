from __future__ import annotations

from tools.zenodex_oracle_cli import _step_ok


def test_oracle_cli_step_ok_rejects_truthy_string() -> None:
    assert _step_ok({"ok": True}) is True
    assert _step_ok({"ok": "true"}) is False
    assert _step_ok({"ok": 1}) is False
