from __future__ import annotations

from pathlib import Path

import pytest

import tools.run_release_pytest_groups as pytest_groups
from tools.run_release_pytest_groups import discover_pytest_groups, run_pytest_groups

ROOT = Path(__file__).resolve().parents[1]


def _write(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")


def test_discover_pytest_groups_covers_root_and_first_level_dirs(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    _write(tests_root / "core" / "test_core.py")
    _write(tests_root / "core" / "nested" / "test_nested.py")
    (tests_root / "fixtures").mkdir(parents=True)

    groups = discover_pytest_groups(tests_root)

    assert [group.group_id for group in groups] == ["root_test_files", "dir_core"]
    covered = {path.name for group in groups for path in group.test_files}
    assert covered == {"test_root.py", "test_core.py", "test_nested.py"}


def test_discover_pytest_groups_chunks_large_groups(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_a.py")
    _write(tests_root / "test_b.py")
    _write(tests_root / "core" / "test_c.py")
    _write(tests_root / "core" / "test_d.py")

    groups = discover_pytest_groups(tests_root, max_files_per_group=1)

    assert [group.group_id for group in groups] == [
        "root_test_files_001",
        "root_test_files_002",
        "dir_core_001",
        "dir_core_002",
    ]
    assert all(len(group.test_files) == 1 for group in groups)


def test_discover_pytest_groups_isolates_formal_tests_by_default(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "formal" / "test_a.py")
    _write(tests_root / "formal" / "test_b.py")
    _write(tests_root / "core" / "test_c.py")
    _write(tests_root / "core" / "test_d.py")

    groups = discover_pytest_groups(tests_root)

    formal_groups = [group for group in groups if group.group_id.startswith("dir_formal")]
    core_groups = [group for group in groups if group.group_id.startswith("dir_core")]
    assert [group.group_id for group in formal_groups] == ["dir_formal_001", "dir_formal_002"]
    assert all(len(group.test_files) == 1 for group in formal_groups)
    assert [group.group_id for group in core_groups] == ["dir_core"]
    assert len(core_groups[0].test_files) == 2


def test_discover_pytest_groups_splits_slow_marked_files_by_nodeid(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "integration" / "test_fast.py")
    slow_file = tests_root / "integration" / "test_slow.py"
    slow_file.parent.mkdir(parents=True, exist_ok=True)
    slow_file.write_text(
        "\n".join(
            [
                "import pytest",
                "",
                "@pytest.mark.slow",
                "def test_slow_a():",
                "    assert True",
                "",
                "def test_slow_b():",
                "    assert True",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    groups = discover_pytest_groups(tests_root)

    assert [group.group_id for group in groups] == [
        "dir_integration",
        "dir_integration_test_slow_slow_001",
        "dir_integration_test_slow_slow_002",
    ]
    assert groups[0].targets == (str((tests_root / "integration" / "test_fast.py").resolve()),)
    assert groups[1].targets == (f"{slow_file.resolve()}::test_slow_a",)
    assert groups[2].targets == (f"{slow_file.resolve()}::test_slow_b",)
    assert groups[1].test_files == (slow_file.resolve(),)
    assert groups[2].test_files == (slow_file.resolve(),)

    def runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        stdout_path.write_text("passed\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 0, False

    report = run_pytest_groups(
        report_path=tmp_path / "pytest_groups.json",
        tests_root=tests_root,
        runner=runner,
    )
    assert report["all_test_file_count"] == 2


def test_run_pytest_groups_accepts_only_when_every_group_passes(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    _write(tests_root / "integration" / "test_integration.py")
    report_path = tmp_path / "pytest_groups.json"
    calls: list[list[str]] = []

    def runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        calls.append(argv)
        stdout_path.write_text("passed\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        assert timeout_sec == 11
        return 0, False

    report = run_pytest_groups(
        report_path=report_path,
        tests_root=tests_root,
        timeout_sec_per_group=11,
        runner=runner,
    )

    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert report["group_count"] == 2
    assert len(report["groups"]) == 2
    assert len(calls) == 2


def test_run_pytest_groups_stops_at_first_failed_group(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    _write(tests_root / "integration" / "test_integration.py")
    report_path = tmp_path / "pytest_groups.json"

    def runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        stdout_path.write_text("failed\n", encoding="utf-8")
        stderr_path.write_text("boom\n", encoding="utf-8")
        return 7, False

    report = run_pytest_groups(report_path=report_path, tests_root=tests_root, runner=runner)

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["incomplete_reasons"] == ["pytest_group_failed:root_test_files"]
    assert len(report["groups"]) == 1
    assert report["groups"][0]["returncode"] == 7


def test_run_pytest_groups_stops_at_first_timed_out_group(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    _write(tests_root / "integration" / "test_integration.py")
    report_path = tmp_path / "pytest_groups.json"

    def runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        stdout_path.write_text("still running\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        assert timeout_sec == 3
        return None, True

    report = run_pytest_groups(
        report_path=report_path,
        tests_root=tests_root,
        timeout_sec_per_group=3,
        runner=runner,
    )

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["incomplete_reasons"] == ["pytest_group_failed:root_test_files"]
    assert len(report["groups"]) == 1
    assert report["groups"][0]["returncode"] is None
    assert report["groups"][0]["timed_out"] is True


def test_run_pytest_groups_accepts_skip_only_optional_tool_group(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "formal" / "test_optional_tool.py")
    report_path = tmp_path / "pytest_groups.json"

    def runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        stdout_path.write_text("1 skipped, 1 warning in 0.26s\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 5, False

    report = run_pytest_groups(report_path=report_path, tests_root=tests_root, runner=runner)

    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert report["groups"][0]["ok"] is True
    assert report["groups"][0]["skip_only"] is True
    assert report["groups"][0]["status"] == "accepted"


def test_run_pytest_groups_rejects_empty_no_tests_collected_group(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_empty.py")
    report_path = tmp_path / "pytest_groups.json"

    def runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        stdout_path.write_text("no tests ran in 0.01s\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 5, False

    report = run_pytest_groups(report_path=report_path, tests_root=tests_root, runner=runner)

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["groups"][0]["ok"] is False
    assert report["groups"][0]["skip_only"] is False


def test_run_pytest_groups_clears_stale_log_dir(tmp_path: Path) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    report_path = tmp_path / "pytest_groups.json"
    log_dir = report_path.with_suffix("")
    log_dir.mkdir()
    (log_dir / "stale.stdout.log").write_text("old\n", encoding="utf-8")

    def runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        stdout_path.write_text("passed\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 0, False

    report = run_pytest_groups(report_path=report_path, tests_root=tests_root, runner=runner)

    assert report["ok"] is True
    assert not (log_dir / "stale.stdout.log").exists()
    assert (log_dir / "root_test_files.stdout.log").exists()


def test_run_pytest_groups_resumes_accepted_current_commit_prefix(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    _write(tests_root / "integration" / "test_integration.py")
    report_path = tmp_path / "pytest_groups.json"
    first_run_calls = 0

    monkeypatch.setattr(pytest_groups, "_git_head", lambda: "commit-a")
    monkeypatch.setattr(pytest_groups, "_git_dirty", lambda: False)

    def interrupted_runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        nonlocal first_run_calls
        first_run_calls += 1
        if first_run_calls == 1:
            stdout_path.write_text("passed\n", encoding="utf-8")
            stderr_path.write_text("", encoding="utf-8")
            return 0, False
        raise KeyboardInterrupt

    with pytest.raises(KeyboardInterrupt):
        run_pytest_groups(report_path=report_path, tests_root=tests_root, runner=interrupted_runner)

    resumed_calls: list[list[str]] = []

    def resumed_runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        resumed_calls.append(argv)
        stdout_path.write_text("passed\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 0, False

    report = run_pytest_groups(
        report_path=report_path,
        tests_root=tests_root,
        resume=True,
        runner=resumed_runner,
    )

    assert report["ok"] is True
    assert report["resumed_group_count"] == 1
    assert report["resume_rejected_reasons"] == []
    assert len(resumed_calls) == 1
    assert report["groups"][0]["group_id"] == "root_test_files"
    assert report["groups"][0]["resumed_from_previous_report"] is True
    assert report["groups"][1]["group_id"] == "dir_integration"
    assert report["groups"][1]["resumed_from_previous_report"] is False


def test_run_pytest_groups_resumes_prefix_from_rejected_timeout_report(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    _write(tests_root / "integration" / "test_integration.py")
    report_path = tmp_path / "pytest_groups.json"
    first_run_calls = 0

    monkeypatch.setattr(pytest_groups, "_git_head", lambda: "commit-a")
    monkeypatch.setattr(pytest_groups, "_git_dirty", lambda: False)

    def first_runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        nonlocal first_run_calls
        first_run_calls += 1
        if first_run_calls == 1:
            stdout_path.write_text("passed\n", encoding="utf-8")
            stderr_path.write_text("", encoding="utf-8")
            return 0, False
        stdout_path.write_text("still running\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return None, True

    first_report = run_pytest_groups(
        report_path=report_path,
        tests_root=tests_root,
        runner=first_runner,
    )

    assert first_report["ok"] is False
    assert first_report["status"] == "rejected"
    assert len(first_report["groups"]) == 2
    assert first_report["groups"][0]["status"] == "accepted"
    assert first_report["groups"][1]["timed_out"] is True

    resumed_calls: list[list[str]] = []

    def resumed_runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        resumed_calls.append(argv)
        stdout_path.write_text("passed\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 0, False

    report = run_pytest_groups(
        report_path=report_path,
        tests_root=tests_root,
        resume=True,
        runner=resumed_runner,
    )

    assert report["ok"] is True
    assert report["resumed_group_count"] == 1
    assert report["resume_rejected_reasons"] == []
    assert len(resumed_calls) == 1
    assert report["groups"][0]["resumed_from_previous_report"] is True
    assert report["groups"][1]["resumed_from_previous_report"] is False


def test_run_pytest_groups_rejects_stale_commit_resume(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    tests_root = tmp_path / "tests"
    _write(tests_root / "test_root.py")
    _write(tests_root / "integration" / "test_integration.py")
    report_path = tmp_path / "pytest_groups.json"

    monkeypatch.setattr(pytest_groups, "_git_head", lambda: "commit-a")
    monkeypatch.setattr(pytest_groups, "_git_dirty", lambda: False)

    def first_runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        stdout_path.write_text("passed\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 0, False

    first_report = run_pytest_groups(
        report_path=report_path,
        tests_root=tests_root,
        runner=first_runner,
    )
    assert first_report["ok"] is True

    monkeypatch.setattr(pytest_groups, "_git_head", lambda: "commit-b")
    fresh_calls: list[list[str]] = []

    def fresh_runner(
        argv: list[str],
        stdout_path: Path,
        stderr_path: Path,
        timeout_sec: int | None,
    ) -> tuple[int | None, bool]:
        fresh_calls.append(argv)
        stdout_path.write_text("passed\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return 0, False

    report = run_pytest_groups(
        report_path=report_path,
        tests_root=tests_root,
        resume=True,
        runner=fresh_runner,
    )

    assert report["ok"] is True
    assert report["commit_sha"] == "commit-b"
    assert report["resumed_group_count"] == 0
    assert report["resume_rejected_reasons"] == ["resume_commit_mismatch"]
    assert len(fresh_calls) == 2
    assert all(group["resumed_from_previous_report"] is False for group in report["groups"])


def test_prod_gate_uses_grouped_pytest_artifact() -> None:
    gate = (ROOT / "tools" / "prod_gate.sh").read_text(encoding="utf-8")

    assert "tools/run_release_pytest_groups.py" in gate
    assert "PYTEST_GROUP_TIMEOUT_SEC" in gate
    assert "--timeout-sec-per-group \"$PYTEST_GROUP_TIMEOUT_SEC\"" in gate
    assert "--resume" in gate
    assert "pytest -q\n" not in gate
