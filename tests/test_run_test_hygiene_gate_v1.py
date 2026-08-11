from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from tools.run_test_hygiene_gate_v1 import run_declared_pytest_nodes


def test_runner_executes_exact_nodes_without_shell(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange
    calls: list[tuple[list[str], Path, bool]] = []

    def fake_run(
        command: list[str], *, cwd: Path, check: bool
    ) -> subprocess.CompletedProcess[str]:
        calls.append((command, cwd, check))
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(subprocess, "run", fake_run)
    nodes = ["tests/core/test_example.py::test_reject_is_noop"]

    # Act
    run_declared_pytest_nodes(
        nodes,
        repo_root=tmp_path,
        python_executable="/verified/python",
    )

    # Assert
    assert calls == [
        (
            ["/verified/python", "-m", "pytest", "-q", nodes[0]],
            tmp_path,
            True,
        )
    ]


def test_runner_skips_process_when_diff_has_no_critical_nodes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange
    def unexpected_run(*args: object, **kwargs: object) -> None:
        raise AssertionError((args, kwargs))

    monkeypatch.setattr(subprocess, "run", unexpected_run)

    # Act / Assert
    run_declared_pytest_nodes([], repo_root=tmp_path)


def test_runner_propagates_pytest_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange
    def failing_run(
        command: list[str], *, cwd: Path, check: bool
    ) -> subprocess.CompletedProcess[str]:
        raise subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(subprocess, "run", failing_run)

    # Act / Assert
    with pytest.raises(subprocess.CalledProcessError):
        run_declared_pytest_nodes(
            ["tests/core/test_example.py::test_failure"],
            repo_root=tmp_path,
        )
