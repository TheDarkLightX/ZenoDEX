from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import cast

import pytest

from tests.test_thv1_mutation_ledger_v1 import (
    _MOD_TEST,
    _commit_packet,
    _git,
    _killed_row,
    _narrative_row,
    _packet,
    _subject,
    _write,
)
from tools import run_test_hygiene_gate_v1 as gate
from tools.check_test_hygiene_v1 import ChangedPathV1, TestHygieneError
from tools.run_test_hygiene_gate_v1 import run_declared_pytest_nodes

_SOURCE_PATH = "src/core/mod.py"
_DEPENDENCY_PATH = "src/core/dependency.py"
_DEPENDENCY_SOURCE = "POSITIVE_GUARD = True\n"
_SUBJECT_MOD_SOURCE = (
    "from src.core.dependency import POSITIVE_GUARD\n\n"
    "def guard(value: int) -> bool:\n"
    "    if value < 0:\n"
    "        return False\n"
    "    return POSITIVE_GUARD\n"
)


def _mechanical_row(path: str = _SOURCE_PATH) -> dict[str, object]:
    row = _killed_row()
    cast(dict[str, object], row["mutant"])["path"] = path
    return row


def _replay_subject(
    tmp_path: Path,
    *,
    test_text: str = _MOD_TEST,
    rows: list[dict[str, object]] | None = None,
    families: list[str] | None = None,
) -> tuple[Path, str]:
    repo = _subject(tmp_path)
    _write(repo / "src/__init__.py", "")
    _write(repo / "src/core/__init__.py", "")
    _write(repo / _DEPENDENCY_PATH, _DEPENDENCY_SOURCE)
    _write(repo / _SOURCE_PATH, _SUBJECT_MOD_SOURCE)
    _write(repo / "tests/test_mod.py", test_text.replace("from pkg.mod", "from src.core.mod"))
    packet = _packet(
        repo,
        rows=[_mechanical_row()] if rows is None else rows,
        source_paths=(_SOURCE_PATH, _DEPENDENCY_PATH),
    )
    if families is not None:
        packet["evidence_families"] = families
    _commit_packet(repo, packet)
    return repo, str(packet["evidence_id"])


def _run_replay(repo: Path, *, replay_mutations: bool = True) -> dict[str, object]:
    return gate._run_gate(
        repo_root=repo,
        contract_path=repo / "tools/test_hygiene_contract_v1.json",
        evidence_dir=repo / "tests/evidence/test_hygiene",
        changed_paths=(ChangedPathV1("M", _SOURCE_PATH),),
        replay_mutations=replay_mutations,
        python_executable=sys.executable,
    )


def test_runner_executes_exact_nodes_without_shell(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange
    calls: list[tuple[list[str], Path, bool, object]] = []

    def fake_run(
        command: list[str], *, cwd: Path, check: bool, stdout: object
    ) -> subprocess.CompletedProcess[str]:
        calls.append((command, cwd, check, stdout))
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
            sys.stderr,
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


def test_runner_propagates_pytest_failure(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    # Arrange
    def failing_run(
        command: list[str], *, cwd: Path, check: bool, stdout: object
    ) -> subprocess.CompletedProcess[str]:
        raise subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(subprocess, "run", failing_run)

    # Act / Assert
    with pytest.raises(subprocess.CalledProcessError):
        run_declared_pytest_nodes(
            ["tests/core/test_example.py::test_failure"],
            repo_root=tmp_path,
        )


def test_replay_executes_a_committed_mechanical_killer_and_cleans_scratch(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    repo, _ = _replay_subject(tmp_path)
    unrelated_dirty = repo / "notes/local.txt"
    _write(unrelated_dirty, "preserve this worktree file\n")
    scratch = tmp_path / "replay-scratch"

    class RecordingTemporaryDirectory:
        def __init__(self, **_: object) -> None:
            self.path = scratch

        def __enter__(self) -> str:
            self.path.mkdir()
            return str(self.path)

        def __exit__(self, *args: object) -> None:
            shutil.rmtree(self.path)

    monkeypatch.setattr(gate.tempfile, "TemporaryDirectory", RecordingTemporaryDirectory)

    report = _run_replay(repo)

    replay = cast(dict[str, object], report["mutation_replay"])
    assert {
        key: replay[key]
        for key in ("mechanical", "killed", "narrative", "legacy", "survived", "errors")
    } == {
        "mechanical": 1,
        "killed": 1,
        "narrative": 0,
        "legacy": 0,
        "survived": 0,
        "errors": 0,
    }
    assert replay["subject_commit"] == _git(repo, "rev-parse", "HEAD")
    assert replay["ok"] is True and report["ok"] is True
    assert unrelated_dirty.read_text(encoding="utf-8") == "preserve this worktree file\n"
    assert not scratch.exists()


@pytest.mark.parametrize(
    ("test_text", "survived", "errors"),
    (
        (
            _MOD_TEST.replace("assert guard(-1) is False", "assert True"),
            1,
            0,
        ),
        (
            "import pytest\n\n"
            + _MOD_TEST.replace(
                "def test_negative_is_refused() -> None:",
                "@pytest.mark.skip\ndef test_negative_is_refused() -> None:",
            ),
            0,
            1,
        ),
    ),
)
def test_replay_rejects_a_coedited_or_skipped_killer(
    tmp_path: Path,
    test_text: str,
    survived: int,
    errors: int,
) -> None:
    repo, _ = _replay_subject(tmp_path, test_text=test_text)

    report = _run_replay(repo)

    replay = cast(dict[str, object], report["mutation_replay"])
    assert (replay["survived"], replay["errors"], replay["ledger_nonzero"]) == (
        survived,
        errors,
        1,
    )
    assert replay["ok"] is False and report["ok"] is False


@pytest.mark.parametrize(
    ("path", "label"),
    (
        ("tools/test_hygiene_contract_v1.json", "contract"),
        ("tests/evidence/test_hygiene/THV1-20260903-ledger-subject-v1.json", "packet"),
        (_SOURCE_PATH, "source"),
        (_DEPENDENCY_PATH, "source"),
        ("tests/test_mod.py", "test"),
    ),
)
def test_replay_preflight_rejects_stale_worktree_metadata_or_pins(
    tmp_path: Path,
    path: str,
    label: str,
) -> None:
    repo, evidence_id = _replay_subject(tmp_path)
    commit = _git(repo, "rev-parse", "HEAD")
    target = repo / path
    target.write_bytes(target.read_bytes() + b"\n# stale worktree bytes\n")

    with pytest.raises(
        TestHygieneError,
        match=rf"^mutation replay worktree {label} differs from commit {commit}: {path}$",
    ):
        gate._load_replay_packets(
            repo_root=repo,
            commit=commit,
            evidence_ids=(evidence_id,),
        )


def test_replay_preflight_rejects_a_pin_stale_at_the_committed_subject(tmp_path: Path) -> None:
    repo, evidence_id = _replay_subject(tmp_path)
    _write(repo / _SOURCE_PATH, _SUBJECT_MOD_SOURCE + "\n# committed drift\n")
    _git(repo, "add", _SOURCE_PATH)
    _git(repo, "commit", "-q", "-m", "stale pin")
    commit = _git(repo, "rev-parse", "HEAD")

    with pytest.raises(
        TestHygieneError,
        match=rf"^{evidence_id}: committed source sha256 drift for {_SOURCE_PATH}$",
    ):
        gate._load_replay_packets(
            repo_root=repo,
            commit=commit,
            evidence_ids=(evidence_id,),
        )


def test_replay_resolves_head_once_and_reuses_the_exact_commit(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    repo, evidence_id = _replay_subject(tmp_path)
    commit = _git(repo, "rev-parse", "HEAD")
    packet = gate._load_replay_packets(
        repo_root=repo,
        commit=commit,
        evidence_ids=(evidence_id,),
    )[0]
    resolutions: list[Path] = []
    options_seen: list[gate.LedgerOptionsV1] = []

    def resolve_head(repo_root: Path) -> str:
        resolutions.append(repo_root)
        return commit

    def fake_ledger(options: gate.LedgerOptionsV1) -> dict[str, object]:
        options_seen.append(options)
        return {
            "mechanical": 1,
            "killed": 1,
            "narrative": 0,
            "legacy": 0,
            "survived": 0,
            "errors": 0,
        }

    monkeypatch.setattr(gate, "_resolve_head_commit", resolve_head)
    monkeypatch.setattr(gate, "_load_replay_packets", lambda **_: (packet, packet))
    monkeypatch.setattr(gate, "run_declared_pytest_nodes", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(gate, "run_ledger_v1", fake_ledger)

    report = _run_replay(repo)

    assert resolutions == [repo]
    assert [(item.rev, item.packet_file, item.filters, item.keep) for item in options_seen] == [
        (commit, None, (), False),
        (commit, None, (), False),
    ]
    assert cast(dict[str, object], report["mutation_replay"])["killed"] == 2


def test_strict_replay_rejects_a_selected_narrative_only_mutation_packet(
    tmp_path: Path,
) -> None:
    repo, _ = _replay_subject(tmp_path, rows=[_narrative_row()])

    static_report = _run_replay(repo, replay_mutations=False)
    static_rows = cast(dict[str, int], static_report["mutation_rows"])
    assert (static_rows["mechanical"], static_rows["narrative"], static_rows["legacy"]) == (
        0,
        1,
        0,
    )

    with pytest.raises(
        TestHygieneError,
        match=r"^THV1-20260903-ledger-subject-v1: mutation evidence requires a mechanical row$",
    ):
        _run_replay(repo)


def test_strict_replay_keeps_nonmutation_packets_and_no_selection_explicit(tmp_path: Path) -> None:
    repo, _ = _replay_subject(
        tmp_path,
        rows=[_narrative_row()],
        families=["negative_regression", "boundary", "property"],
    )

    report = _run_replay(repo)
    replay = cast(dict[str, object], report["mutation_replay"])
    assert (replay["mechanical"], replay["killed"], replay["narrative"], replay["legacy"]) == (
        0,
        0,
        1,
        0,
    )
    assert replay["ok"] is True and report["ok"] is True

    no_selection = gate._run_gate(
        repo_root=repo,
        contract_path=repo / "tools/test_hygiene_contract_v1.json",
        evidence_dir=repo / "tests/evidence/test_hygiene",
        changed_paths=(),
        replay_mutations=True,
    )
    no_selection_replay = cast(dict[str, object], no_selection["mutation_replay"])
    assert (no_selection_replay["mechanical"], no_selection_replay["narrative"]) == (0, 0)
    assert no_selection_replay["ok"] is True


def test_default_gate_does_not_resolve_or_replay_mutations(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    repo, _ = _replay_subject(tmp_path)
    monkeypatch.setattr(
        gate,
        "_resolve_head_commit",
        lambda *_: (_ for _ in ()).throw(AssertionError("default gate resolved HEAD")),
    )
    monkeypatch.setattr(
        gate,
        "run_ledger_v1",
        lambda *_: (_ for _ in ()).throw(AssertionError("default gate replayed mutations")),
    )
    monkeypatch.setattr(gate, "run_declared_pytest_nodes", lambda *_args, **_kwargs: None)

    report = _run_replay(repo, replay_mutations=False)

    assert "mutation_replay" not in report


def test_replay_refuses_nonstandard_contract_or_evidence_paths(tmp_path: Path) -> None:
    repo, _ = _replay_subject(tmp_path)

    with pytest.raises(
        TestHygieneError,
        match=r"^--replay-mutations requires the standard contract and evidence paths$",
    ):
        gate._run_gate(
            repo_root=repo,
            contract_path=tmp_path / "other-contract.json",
            evidence_dir=repo / "tests/evidence/test_hygiene",
            changed_paths=(ChangedPathV1("M", _SOURCE_PATH),),
            replay_mutations=True,
        )


def test_cli_replay_failure_is_one_json_document_or_a_failed_human_summary(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    report: dict[str, object] = {
        "ok": False,
        "critical_path_count": 1,
        "pytest_node_ids": [],
        "mutation_replay": {
            "mechanical": 1,
            "killed": 0,
            "narrative": 0,
            "legacy": 0,
            "subject_commit": "a" * 40,
            "ok": False,
        },
    }
    monkeypatch.setattr(gate, "_resolve_head_commit", lambda _: "a" * 40)
    monkeypatch.setattr(gate, "_run_gate", lambda **_: report)

    assert gate.main(["--replay-mutations", "--json"]) == 1
    captured = capsys.readouterr()
    assert json.loads(captured.out) == report
    assert captured.err == ""

    assert gate.main(["--replay-mutations"]) == 1
    captured = capsys.readouterr()
    assert "test-hygiene-v1: mutation replay failed" in captured.out
    assert "evidence passed" not in captured.out


def test_strict_cli_uses_one_resolved_subject_for_diff_and_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    commit = "b" * 40
    resolutions: list[Path] = []
    diff_heads: list[str] = []
    gate_commits: list[str | None] = []

    def resolve(repo_root: Path) -> str:
        resolutions.append(repo_root)
        return commit

    def collect(repo_root: Path, base_ref: str, *, head_ref: str) -> tuple[ChangedPathV1, ...]:
        assert base_ref == "base"
        diff_heads.append(head_ref)
        return ()

    def run_gate(**kwargs: object) -> dict[str, object]:
        gate_commits.append(cast(str | None, kwargs["subject_commit"]))
        return {
            "ok": True,
            "critical_path_count": 0,
            "pytest_node_ids": [],
            "mutation_replay": {
                "mechanical": 0,
                "killed": 0,
                "narrative": 0,
                "legacy": 0,
                "subject_commit": commit,
                "ok": True,
            },
        }

    monkeypatch.setattr(gate, "_resolve_head_commit", resolve)
    monkeypatch.setattr(gate, "collect_git_changed_paths", collect)
    monkeypatch.setattr(gate, "_run_gate", run_gate)

    assert gate.main(["--replay-mutations", "--base-ref", "base"]) == 0
    assert len(resolutions) == 1
    assert diff_heads == [commit]
    assert gate_commits == [commit]


def test_strict_cli_json_keeps_real_pytest_output_on_stderr(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capfd: pytest.CaptureFixture[str],
) -> None:
    repo, _ = _replay_subject(tmp_path)
    monkeypatch.setattr(gate, "REPO_ROOT", repo)
    monkeypatch.setattr(gate, "DEFAULT_CONTRACT", repo / "tools/test_hygiene_contract_v1.json")
    monkeypatch.setattr(
        gate,
        "DEFAULT_EVIDENCE_DIR",
        repo / "tests/evidence/test_hygiene",
    )

    assert gate.main(["--replay-mutations", "--changed-file", f"M:{_SOURCE_PATH}", "--json"]) == 0
    stdout, stderr = capfd.readouterr()
    report = json.loads(stdout)
    assert report["ok"] is True
    assert "2 passed" in stderr
