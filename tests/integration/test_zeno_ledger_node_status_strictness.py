from __future__ import annotations

import pytest

from tools.zeno_ledger_node import _strict_status_response_v0


@pytest.mark.parametrize("truthy_non_bool", ["true", "ok", 1, ["accepted"]])
def test_strict_status_response_rejects_truthy_non_bool_ok(truthy_non_bool: object) -> None:
    report = _strict_status_response_v0({"ok": truthy_non_bool, "detail": "candidate"})

    assert report["ok"] is False
    assert report["status"]["ok"] == truthy_non_bool


def test_strict_status_response_accepts_literal_true_only() -> None:
    assert _strict_status_response_v0({"ok": True})["ok"] is True
    assert _strict_status_response_v0({"ok": False})["ok"] is False
