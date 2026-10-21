from __future__ import annotations

import subprocess

import pytest

import tools.run_test_quality_gate_v2 as runner


def test_runner_executes_only_nodes_selected_by_quality_checker(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[list[str]] = []
    report = {
        "critical_path_count": 1,
        "pytest_node_ids": ["tests/test_example.py::test_exact_obligation"],
    }
    monkeypatch.setattr(runner, "check_test_quality_repository", lambda **_kwargs: report)
    monkeypatch.setattr(
        runner,
        "run_declared_pytest_nodes",
        lambda nodes, **_kwargs: calls.append(list(nodes)),
    )

    exit_code = runner.main(["--changed-file", "M:tools/example.py"])

    assert exit_code == 0
    assert calls == [["tests/test_example.py::test_exact_obligation"]]


def test_runner_propagates_declared_test_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = {
        "critical_path_count": 1,
        "pytest_node_ids": ["tests/test_example.py::test_failure"],
    }
    monkeypatch.setattr(runner, "check_test_quality_repository", lambda **_kwargs: report)

    def fail(_nodes: object, **_kwargs: object) -> None:
        raise subprocess.CalledProcessError(7, ["pytest"])

    monkeypatch.setattr(runner, "run_declared_pytest_nodes", fail)

    exit_code = runner.main(["--changed-file", "M:tools/example.py"])

    assert exit_code == 7
