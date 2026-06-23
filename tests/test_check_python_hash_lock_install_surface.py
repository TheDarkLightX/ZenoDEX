from __future__ import annotations

from tools.check_python_hash_lock_install_surface import run_check


def test_python_hash_lock_install_surface_accepts() -> None:
    result = run_check()

    assert result["schema"] == "zenodex.python_hash_lock_install_surface_check.v1"
    assert result["ok"] is True
    assert result["errors"] == []
    assert result["lock_files"] == [
        "requirements-core.lock.txt",
        "requirements-agents.lock.txt",
        "requirements-dev.lock.txt",
    ]
