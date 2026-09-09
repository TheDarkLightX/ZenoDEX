"""Subprocess evidence for the signed ZenoLacuna project CLI boundary."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from typing import cast

from src.zenolacuna.codec import decode_candidate, encode
from src.zenolacuna.model import Candidate, Profile, SourceRef
from src.zenolacuna.project_types import RuntimeSpec, Task, decode_task, task_value
from tests.zenolacuna_project_helpers import OWNER_SECRET, public_key, scope

_ROOT = Path(__file__).resolve().parents[1]
_SCRIPT = _ROOT / "tools" / "zenolacuna.py"
_PYTHON = _ROOT / ".venv" / "bin" / "python"
if not _PYTHON.is_file():
    _PYTHON = Path(sys.executable)


def _run(*arguments: str) -> tuple[subprocess.CompletedProcess[str], dict[str, object]]:
    result = subprocess.run(
        [str(_PYTHON), str(_SCRIPT), *arguments],
        cwd=_ROOT,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        text=True,
        capture_output=True,
        check=False,
    )
    lines = [line for line in result.stdout.splitlines() if line]
    assert lines, result.stderr
    return result, json.loads(lines[-1])


def _task(path: Path, *, profile: Profile = Profile.REAL_OWNER) -> None:
    value = Task(
        scope=scope() if profile is Profile.REAL_OWNER else replace(scope(), profile=profile),
        runtime=RuntimeSpec("RELATION", (), ()),
        delegates=(),
        tau_sha256=None,
        esso_sha256=None,
    )
    path.write_bytes(encode(task_value(value)))


def _key(path: Path, raw: bytes = OWNER_SECRET) -> None:
    path.write_bytes(raw)
    path.chmod(0o600)


def _prepare_and_sign(tmp_path: Path, task_path: Path) -> tuple[Path, Path, Path]:
    request = tmp_path / "init.request"
    signed = tmp_path / "init.signed"
    key = tmp_path / "owner.seed"
    _key(key)
    result, report = _run(
        "project", "prepare-init", "--task", str(task_path), "--project-id", "cli-project",
        "--out", str(request),
    )
    assert result.returncode == 0, report
    assert report["artifact"] == "UNSIGNED_REQUEST"
    result, report = _run(
        "project", "sign", "--request", str(request), "--key-file", str(key), "--out", str(signed),
    )
    assert result.returncode == 0, report
    assert OWNER_SECRET.hex() not in result.stdout
    return request, signed, key


def test_given_prepared_request_when_signed_and_applied_then_restart_status_is_stable(tmp_path: Path) -> None:
    task_path = tmp_path / "task.json"
    _task(task_path)
    _request, signed, _key_path = _prepare_and_sign(tmp_path, task_path)
    run_path = tmp_path / "project.sqlite"

    result, applied = _run(
        "project", "apply", "--run", str(run_path), "--owner-key", public_key(),
        "--command", str(signed),
    )
    assert result.returncode == 0, applied
    assert applied["project_id"] == "cli-project"
    result, status = _run(
        "project", "status", "--run", str(run_path), "--owner-key", public_key(),
    )
    assert result.returncode == 0, status
    assert status["revision"] == applied["revision"]
    assert status["approval"] == "OWNER_PIN_VERIFIED"
    assert status["execution_context"] == "FRESH_SOURCE_PROCESS"
    result, proposal = _run(
        "project", "propose", "--run", str(run_path), "--owner-key", public_key(),
    )
    assert result.returncode == 0, proposal
    assert isinstance(proposal["analysis"], dict)
    assert "witness" in proposal["analysis"]
    assert proposal["admitted_survivors"] == status["survivors"]


def test_given_current_revision_when_prepare_answer_then_signed_revision_can_be_applied(tmp_path: Path) -> None:
    task_path = tmp_path / "task.json"
    _task(task_path)
    _request, signed, key_path = _prepare_and_sign(tmp_path, task_path)
    run_path = tmp_path / "project.sqlite"
    _run("project", "apply", "--run", str(run_path), "--owner-key", public_key(), "--command", str(signed))

    request = tmp_path / "answer.request"
    signed_answer = tmp_path / "answer.signed"
    result, report = _run(
        "project", "prepare", "--run", str(run_path), "--owner-key", public_key(),
        "--action", "answer", "--answer", "yes", "--out", str(request),
    )
    assert result.returncode == 0, report
    result, report = _run(
        "project", "sign", "--request", str(request), "--key-file", str(key_path),
        "--out", str(signed_answer),
    )
    assert result.returncode == 0, report
    result, report = _run(
        "project", "apply", "--run", str(run_path), "--owner-key", public_key(),
        "--command", str(signed_answer),
    )
    assert result.returncode == 0, report
    assert report["code"] != "IDEMPOTENT_DUPLICATE"


def test_given_simulated_task_when_init_applies_then_profile_cannot_be_lowered_implicitly(tmp_path: Path) -> None:
    task_path = tmp_path / "simulated-task.json"
    _task(task_path, profile=Profile.SIMULATED)
    _request, signed, _key_path = _prepare_and_sign(tmp_path, task_path)
    result, report = _run(
        "project", "apply", "--run", str(tmp_path / "project.sqlite"), "--owner-key", public_key(),
        "--command", str(signed),
    )
    assert result.returncode != 0
    assert report == {"code": "AUTHORIZATION_PROFILE_MISMATCH", "status": "REJECTED"}


def test_given_existing_output_or_weak_key_file_then_artifact_write_rejects_without_echoing_secret(tmp_path: Path) -> None:
    task_path = tmp_path / "task.json"
    _task(task_path)
    request = tmp_path / "init.request"
    result, report = _run(
        "project", "prepare-init", "--task", str(task_path), "--project-id", "cli-project",
        "--out", str(request),
    )
    assert result.returncode == 0, report
    result, report = _run(
        "project", "prepare-init", "--task", str(task_path), "--project-id", "cli-project",
        "--out", str(request),
    )
    assert result.returncode != 0
    assert report == {"code": "OUTPUT_EXISTS", "status": "REJECTED"}

    weak_key = tmp_path / "weak.seed"
    weak_key.write_bytes(OWNER_SECRET)
    weak_key.chmod(0o644)
    result, report = _run(
        "project", "sign", "--request", str(request), "--key-file", str(weak_key),
        "--out", str(tmp_path / "signed"),
    )
    assert result.returncode != 0
    assert report == {"code": "KEY_PERMISSIONS", "status": "REJECTED"}
    assert OWNER_SECRET.hex() not in result.stdout


def test_given_legacy_command_when_project_dispatch_is_absent_then_legacy_cli_remains_unchanged() -> None:
    result, report = _run("describe")
    assert result.returncode == 0
    commands = cast(list[object], report["commands"])
    assert "analyze" in commands
    assert "project" not in commands
    workflow = cast(dict[str, object], report["project_workflow"])
    assert workflow == {
        "authority": "REAL_OWNER_SIGNED_ED25519",
        "command": "zenolacuna project",
        "evidence": "DURABLE_SQLITE_SIGNED_EVENT_HISTORY",
        "execution": "FRESH_SOURCE_PROCESS",
    }


def test_candidate_command_writes_the_allowlisted_migration_candidate(tmp_path: Path) -> None:
    output = tmp_path / "guarded.candidate.json"
    result, report = _run(
        "project", "candidate", "--mode", "guarded", "--out", str(output),
    )
    assert result.returncode == 0, report
    candidate = decode_candidate(output.read_bytes())
    assert candidate.name == "real-signal-migration-guarded"
    assert report["mode"] == "GUARDED"
    assert report["artifact"] == "CANDIDATE"


def test_task_factory_pins_explicit_native_tools_into_the_task(tmp_path: Path) -> None:
    tau_binary = tmp_path / "tau"
    tau_binary.write_text("#!/bin/sh\nexit 0\n")
    tau_binary.chmod(0o700)
    task_input = tmp_path / "task.json"
    _task(task_input)
    task_output = tmp_path / "pinned-task.json"
    result, report = _run(
        "project", "task", "--input", str(task_input), "--tau-bin", str(tau_binary),
        "--out", str(task_output),
    )
    assert result.returncode == 0, report
    pinned = decode_task(json.loads(task_output.read_text()))
    assert pinned.tau_sha256 == hashlib.sha256(tau_binary.read_bytes()).hexdigest()


def test_signal_task_factory_pins_explicit_esso_package(tmp_path: Path) -> None:
    esso_root = tmp_path / "esso-root"
    package = esso_root / "ESSO"
    package.mkdir(parents=True)
    (package / "__init__.py").write_text("# test-only package\n")
    task_output = tmp_path / "signal-task.json"
    result, report = _run(
        "project", "task", "--adapter", "signal-migration", "--esso-root", str(esso_root),
        "--out", str(task_output),
    )
    assert result.returncode == 0, report
    pinned = decode_task(json.loads(task_output.read_text()))
    assert pinned.esso_sha256 is not None


def test_observe_returns_bounded_membership_receipt_for_assessed_candidate(tmp_path: Path) -> None:
    task_path = tmp_path / "task.json"
    _task(task_path)
    _request, init_signed, key_path = _prepare_and_sign(tmp_path, task_path)
    run_path = tmp_path / "project.sqlite"
    _run("project", "apply", "--run", str(run_path), "--owner-key", public_key(),
         "--command", str(init_signed))

    answer_request = tmp_path / "answer.request"
    answer_signed = tmp_path / "answer.signed"
    result, report = _run(
        "project", "prepare", "--run", str(run_path), "--owner-key", public_key(),
        "--action", "answer", "--answer", "yes", "--out", str(answer_request),
    )
    assert result.returncode == 0, report
    _run("project", "sign", "--request", str(answer_request), "--key-file", str(key_path),
         "--out", str(answer_signed))
    _run("project", "apply", "--run", str(run_path), "--owner-key", public_key(),
         "--command", str(answer_signed))

    candidate_path = tmp_path / "candidate.json"
    candidate = Candidate("observed", ((0,), (0,)), (0, 1))
    candidate_path.write_bytes(encode(candidate))
    assess_request = tmp_path / "assess.request"
    assess_signed = tmp_path / "assess.signed"
    result, report = _run(
        "project", "prepare", "--run", str(run_path), "--owner-key", public_key(),
        "--action", "assess", "--candidate", str(candidate_path), "--out", str(assess_request),
    )
    assert result.returncode == 0, report
    _run("project", "sign", "--request", str(assess_request), "--key-file", str(key_path),
         "--out", str(assess_signed))
    result, report = _run(
        "project", "apply", "--run", str(run_path), "--owner-key", public_key(),
        "--command", str(assess_signed),
    )
    assert result.returncode == 0, report

    result, receipt = _run(
        "project", "observe", "--run", str(run_path), "--owner-key", public_key(),
        "--context", "positive", "--kind", "ACCEPT", "--observation", "allow",
    )
    assert result.returncode == 0, receipt
    assert receipt["code"] == "OBSERVATION_ALLOWED"
    assert receipt["claim"] == "FINITE_MODEL_MEMBERSHIP"


def test_prepare_revise_uses_archived_revision_after_source_drift(tmp_path: Path) -> None:
    source_root = tmp_path / "sources"
    source_root.mkdir()
    source_path = source_root / "input.txt"
    original = b"original\n"
    source_path.write_bytes(original)
    initial_scope = replace(
        scope(), sources=(SourceRef("input.txt", hashlib.sha256(original).hexdigest()),),
    )
    task_path = tmp_path / "task.json"
    task_path.write_bytes(encode(task_value(Task(
        scope=initial_scope, runtime=RuntimeSpec("RELATION", (), ()), delegates=(),
        tau_sha256=None, esso_sha256=None,
    ))))
    request = tmp_path / "init.request"
    signed = tmp_path / "init.signed"
    key_path = tmp_path / "owner.seed"
    _key(key_path)
    result, report = _run(
        "project", "prepare-init", "--source-root", str(source_root), "--task", str(task_path),
        "--project-id", "drift-project", "--out", str(request),
    )
    assert result.returncode == 0, report
    _run("project", "sign", "--request", str(request), "--key-file", str(key_path),
         "--out", str(signed))
    run_path = tmp_path / "project.sqlite"
    result, report = _run(
        "project", "apply", "--source-root", str(source_root), "--run", str(run_path),
        "--owner-key", public_key(), "--command", str(signed),
    )
    assert result.returncode == 0, report

    changed = b"edited\n"
    source_path.write_bytes(changed)
    result, report = _run(
        "project", "status", "--source-root", str(source_root), "--run", str(run_path),
        "--owner-key", public_key(),
    )
    assert result.returncode != 0
    assert report == {"code": "SOURCE_DRIFT", "status": "REJECTED"}

    successor_scope = replace(
        initial_scope, sources=(SourceRef("input.txt", hashlib.sha256(changed).hexdigest()),),
    )
    successor_task = tmp_path / "successor-task.json"
    successor_task.write_bytes(encode(task_value(Task(
        scope=successor_scope, runtime=RuntimeSpec("RELATION", (), ()), delegates=(),
        tau_sha256=None, esso_sha256=None,
    ))))
    revise_request = tmp_path / "revise.request"
    result, report = _run(
        "project", "prepare", "--source-root", str(source_root), "--run", str(run_path),
        "--owner-key", public_key(), "--action", "revise", "--task", str(successor_task),
        "--reason", "refresh archived source", "--out", str(revise_request),
    )
    assert result.returncode == 0, report
