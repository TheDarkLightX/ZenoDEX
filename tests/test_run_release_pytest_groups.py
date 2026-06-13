from __future__ import annotations

from pathlib import Path

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


def test_prod_gate_uses_grouped_pytest_artifact() -> None:
    gate = (ROOT / "tools" / "prod_gate.sh").read_text(encoding="utf-8")

    assert "tools/run_release_pytest_groups.py" in gate
    assert "pytest -q\n" not in gate
