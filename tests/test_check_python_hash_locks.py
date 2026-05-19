from __future__ import annotations

from pathlib import Path

from tools.check_python_hash_locks import run_check


def test_python_hash_locks_accept_current_lockfiles() -> None:
    result = run_check()

    assert result["schema"] == "zenodex.python_hash_locks_check.v1"
    assert result["ok"] is True
    assert result["errors"] == []
    assert result["lock_files"]["requirements-core.lock.txt"]["package_count"] == 13
    assert result["lock_files"]["requirements-agents.lock.txt"]["package_count"] == 40
    assert result["lock_files"]["requirements-dev.lock.txt"]["package_count"] == 90
    assert result["lock_files"]["requirements-core.lock.txt"]["hash_count"] == 387
    assert result["lock_files"]["requirements-agents.lock.txt"]["hash_count"] == 668
    assert result["lock_files"]["requirements-dev.lock.txt"]["hash_count"] == 1370


def test_python_hash_locks_reject_missing_file(tmp_path: Path) -> None:
    result = run_check((str(tmp_path / "missing.lock.txt"),))

    assert result["ok"] is False
    assert any(error.startswith("missing_lock_file:") for error in result["errors"])


def test_python_hash_locks_reject_non_exact_requirement(tmp_path: Path) -> None:
    lock_path = tmp_path / "bad.lock.txt"
    lock_path.write_text(
        "# pip-compile --generate-hashes\n"
        "example>=1.0 \\\n"
        "    --hash=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
        encoding="utf-8",
    )

    result = run_check((str(lock_path),))

    assert result["ok"] is False
    assert any("non_exact_requirement" in error for error in result["errors"])


def test_python_hash_locks_reject_missing_hashes(tmp_path: Path) -> None:
    lock_path = tmp_path / "bad.lock.txt"
    lock_path.write_text("# pip-compile --generate-hashes\nexample==1.0\n", encoding="utf-8")

    result = run_check((str(lock_path),))

    assert result["ok"] is False
    assert any("missing_hashes:example" in error for error in result["errors"])


def test_python_hash_locks_reject_missing_generate_hashes_header(tmp_path: Path) -> None:
    lock_path = tmp_path / "bad.lock.txt"
    lock_path.write_text(
        "example==1.0 \\\n"
        "    --hash=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n",
        encoding="utf-8",
    )

    result = run_check((str(lock_path),))

    assert result["ok"] is False
    assert any("missing_generate_hashes_header" in error for error in result["errors"])
