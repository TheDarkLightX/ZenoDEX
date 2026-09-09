#!/usr/bin/env python3
"""Qualify the real finite ZenoLacuna migration through its public CLI.

The runner is an evidence shell.  It prepares canonical data, invokes the
signed project CLI in fresh subprocesses, and writes one report only after the
complete workflow and independent replay succeed.  The owner seed is a fixed
test credential held in a temporary 0600 file; it is never placed in the output
directory or report.
"""

from __future__ import annotations

import argparse
import base64
import copy
import hashlib
import json
import os
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Iterable, Mapping, NoReturn, Sequence, cast

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / "tools" / "zenolacuna.py"
OWNER_SECRET = bytes(range(32))
MAX_OUTPUT_BYTES = 16 * 1024 * 1024
PROJECT_ID = "zenolacuna-real-migration-qualification"
# This is the independently derived Ed25519 public key for OWNER_SECRET.  The
# signed INIT artifact must match it before that key is passed to any apply.
OWNER_PUBLIC_KEY = "03a107bff3ce10be1d70dd18e74bc09967e4d6309ba50d5f1ddc8664125531b8"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


class QualificationError(ValueError):
    """A typed qualification failure that never authorizes a report."""

    def __init__(self, code: str, detail: str = "") -> None:
        self.code = code
        self.detail = detail
        super().__init__(code if not detail else f"{code}:{detail}")


def _fail(code: str, detail: str = "") -> NoReturn:
    raise QualificationError(code, detail)


def _require(condition: bool, code: str, detail: str = "") -> None:
    if not condition:
        _fail(code, detail)


def _absolute(path: str | Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def _canonical_bytes(value: object) -> bytes:
    try:
        return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii")
    except (TypeError, ValueError, UnicodeError, OverflowError, RecursionError) as exc:
        raise QualificationError("NONCANONICAL_DATA") from exc


def _read_json(path: Path) -> object:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise QualificationError("ARTIFACT_READ") from exc
    if len(raw) > MAX_OUTPUT_BYTES:
        _fail("ARTIFACT_TOO_LARGE")
    try:
        value = json.loads(raw.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise QualificationError("ARTIFACT_JSON") from exc
    return value


def _write_exclusive(path: Path, value: object) -> None:
    raw = _canonical_bytes(value)
    try:
        descriptor = os.open(
            path,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
    except FileExistsError as exc:
        raise QualificationError("OUTPUT_EXISTS") from exc
    except OSError as exc:
        raise QualificationError("OUTPUT_WRITE") from exc
    try:
        offset = 0
        while offset < len(raw):
            offset += os.write(descriptor, raw[offset:])
        os.fsync(descriptor)
    except OSError as exc:
        raise QualificationError("OUTPUT_WRITE") from exc
    finally:
        os.close(descriptor)


def _fresh_output(path: Path) -> Path:
    path = _absolute(path)
    if path.exists() or path.is_symlink():
        _fail("OUTPUT_EXISTS")
    try:
        path.mkdir(mode=0o700)
    except OSError as exc:
        raise QualificationError("OUTPUT_WRITE") from exc
    return path


def _redact_argv(argv: Sequence[str], key_path: Path) -> list[str]:
    result: list[str] = []
    redact_next = False
    key_text = str(key_path)
    for value in argv:
        if redact_next:
            result.append("<TEST_OWNER_KEY>")
            redact_next = False
        elif value == "--key-file":
            result.append(value)
            redact_next = True
        elif value == key_text:
            result.append("<TEST_OWNER_KEY>")
        else:
            result.append(value)
    if redact_next:
        result.append("<MISSING_KEY_PATH>")
    return result


class _CommandRunner:
    def __init__(self, *, root: Path, key_path: Path, secret: bytes) -> None:
        self.root = root
        self.key_path = key_path
        self.secret = secret
        self.commands: list[dict[str, object]] = []

    def invoke(self, label: str, arguments: Sequence[str]) -> tuple[int, dict[str, object]]:
        argv = [sys.executable, str(CLI), *arguments]
        started = time.perf_counter_ns()
        try:
            completed = subprocess.run(
                argv,
                cwd=self.root,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                text=True,
                capture_output=True,
                check=False,
                timeout=300,
            )
        except subprocess.TimeoutExpired as exc:
            raise QualificationError("CLI_TIMEOUT", label) from exc
        elapsed_ms = (time.perf_counter_ns() - started) // 1_000_000
        for stream in (completed.stdout, completed.stderr):
            if self.secret.hex() in stream or self.secret.decode("latin1") in stream:
                raise QualificationError("SECRET_ECHO", label)
        lines = [line for line in completed.stdout.splitlines() if line]
        if not lines:
            raise QualificationError("CLI_NO_JSON", label)
        try:
            report = json.loads(lines[-1])
        except (json.JSONDecodeError, ValueError) as exc:
            raise QualificationError("CLI_JSON", label) from exc
        if type(report) is not dict:
            raise QualificationError("CLI_JSON", label)
        self.commands.append({
            "label": label,
            "argv": _redact_argv(argv, self.key_path),
            "returncode": completed.returncode,
            "code": report.get("code"),
            "status": report.get("status"),
            "duration_ms": elapsed_ms,
        })
        return completed.returncode, report

    def expect(
        self,
        label: str,
        arguments: Sequence[str],
        *,
        returncode: int,
        codes: Iterable[str] = (),
    ) -> dict[str, object]:
        actual_returncode, report = self.invoke(label, arguments)
        expected_codes = set(codes)
        if actual_returncode != returncode:
            _fail("CLI_UNEXPECTED_RETURN", f"{label}:{actual_returncode}/{returncode}:{report.get('code')}")
        if expected_codes and report.get("code") not in expected_codes:
            _fail("CLI_UNEXPECTED_CODE", f"{label}:{report.get('code')}")
        if returncode == 0 and report.get("status") == "REJECTED":
            _fail("CLI_REJECTED", f"{label}:{report.get('code')}")
        if returncode != 0 and report.get("status") != "REJECTED":
            _fail("CLI_REJECTION_SHAPE", label)
        return report


def _host_flags(source_root: Path, tau_bin: Path | None, esso_root: Path | None) -> list[str]:
    result = ["--source-root", str(source_root)]
    if tau_bin is not None:
        result.extend(("--tau-bin", str(tau_bin)))
    if esso_root is not None:
        result.extend(("--esso-root", str(esso_root)))
    return result


def _project_args(
    command: str,
    tail: Sequence[str],
    *,
    source_root: Path,
    tau_bin: Path | None,
    esso_root: Path | None,
) -> list[str]:
    return ["project", command, *_host_flags(source_root, tau_bin, esso_root), *tail]


def _public_key(signed_path: Path) -> str:
    value = _read_json(signed_path)
    if type(value) is not dict or type(value.get("public_key")) is not str:
        _fail("SIGNED_KEY_MISSING")
    public_key = value["public_key"]
    if len(public_key) != 64 or any(character not in "0123456789abcdef" for character in public_key):
        _fail("SIGNED_KEY_INVALID")
    return public_key


def _checker_hash(request_path: Path) -> str:
    value = _read_json(request_path)
    if type(value) is not dict or type(value.get("payload")) is not str:
        _fail("INIT_PAYLOAD_MISSING")
    try:
        payload = json.loads(base64.b64decode(value["payload"], validate=True).decode("ascii"))
    except (ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise QualificationError("INIT_PAYLOAD_INVALID") from exc
    if type(payload) is not dict or type(payload.get("checker_sha256")) is not str:
        _fail("CHECKER_HASH_MISSING")
    checker = payload["checker_sha256"]
    if len(checker) != 64 or any(character not in "0123456789abcdef" for character in checker):
        _fail("CHECKER_HASH_INVALID")
    return checker


def _file_sha256(path: Path) -> str:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise QualificationError("ARTIFACT_READ", str(path)) from exc
    return hashlib.sha256(raw).hexdigest()


def _scope_and_sources(task_path: Path, source_root: Path) -> tuple[dict[str, object], dict[str, str], dict[str, int]]:
    task = _read_json(task_path)
    if type(task) is not dict or type(task.get("scope")) is not dict:
        _fail("TASK_INVALID")
    scope = task["scope"]
    sources_value = scope.get("sources")
    if type(sources_value) is not list:
        _fail("SOURCE_BINDINGS_MISSING")
    source_hashes: dict[str, str] = {}
    metrics: dict[str, int] = {}
    total = 0
    for source in sources_value:
        if type(source) is not dict or type(source.get("path")) is not str or type(source.get("sha256")) is not str:
            _fail("SOURCE_BINDING_INVALID")
        relative = source["path"]
        digest = source["sha256"]
        path = source_root / relative
        try:
            raw = path.read_bytes()
        except OSError as exc:
            raise QualificationError("SOURCE_READ", relative) from exc
        actual = hashlib.sha256(raw).hexdigest()
        if actual != digest:
            _fail("SOURCE_HASH_MISMATCH", relative)
        source_hashes[relative] = digest
        metrics[relative] = len(raw)
        total += len(raw)
    metrics["__total_bytes__"] = total
    return scope, source_hashes, metrics


def _revised_task(task_path: Path, output_path: Path) -> dict[str, object]:
    task_value = _read_json(task_path)
    if type(task_value) is not dict or type(task_value.get("scope")) is not dict:
        _fail("TASK_INVALID")
    task = copy.deepcopy(task_value)
    scope = task["scope"]
    old_scope_without_protected = copy.deepcopy(scope)
    old_scope_without_protected["protected"] = None
    old_protected = copy.deepcopy(scope.get("protected"))
    old_hypotheses = copy.deepcopy(scope.get("hypotheses"))
    old_assumptions = copy.deepcopy(scope.get("assumptions"))
    if type(old_protected) is not list or type(old_hypotheses) is not list or type(old_assumptions) is not list:
        _fail("TASK_INVALID")
    requirement = {
        "allowed": [[0], [2], [2], [0], [0], [0]],
        "applicability": [1, 2],
        "name": "no_unsafe_rollout",
        "required": [[], [2], [2], [], [], []],
    }
    if any(type(item) is dict and item.get("name") == requirement["name"] for item in old_protected):
        _fail("TASK_ALREADY_REVISED")
    scope["protected"] = [*old_protected, requirement]
    new_scope_without_protected = copy.deepcopy(scope)
    new_scope_without_protected["protected"] = None
    _require(new_scope_without_protected == old_scope_without_protected, "SCOPE_BINDING_CHANGED")
    _require(scope["hypotheses"] == old_hypotheses, "HYPOTHESES_CHANGED")
    _require(scope["assumptions"] == old_assumptions, "ASSUMPTIONS_CHANGED")
    _write_exclusive(output_path, task)
    return task


def _tamper_signed(signed_path: Path, output_path: Path) -> None:
    signed = _read_json(signed_path)
    if type(signed) is not dict or type(signed.get("signature")) is not str:
        _fail("SIGNED_INVALID")
    signature = signed["signature"]
    _require(len(signature) == 128, "SIGNED_INVALID")
    replacement = "0" if signature[-1] != "0" else "1"
    signed["signature"] = signature[:-1] + replacement
    _write_exclusive(output_path, signed)


def _direct_migration_baseline() -> tuple[dict[str, object], int, dict[str, object]]:
    started = time.perf_counter_ns()
    try:
        from src.zenolacuna.signal_migration import OBSERVATIONS, CandidateMode, check_migration

        report = check_migration(
            mode=CandidateMode.GUARDED,
            inputs=tuple(range(128)),
            declared_observations=OBSERVATIONS,
        )
        omitted = check_migration(
            mode=CandidateMode.GUARDED,
            inputs=tuple(range(128)),
            declared_observations=tuple(value for value in OBSERVATIONS if value != "auth_ok"),
        )
    except (ImportError, OSError, ValueError) as exc:
        raise QualificationError("DIRECT_BASELINE_FAILED") from exc
    elapsed_ms = (time.perf_counter_ns() - started) // 1_000_000
    counterexample = report.smallest_counterexample
    summary: dict[str, object] = {
        "code": report.code,
        "evidence": report.evidence.value,
        "claim": report.claim,
        "candidate_relation_matches": report.candidate_relation_matches,
        "checked_inputs128": report.checked_inputs128,
        "checked_states": report.checked_states,
        "checked_edges": report.checked_edges,
        "checked_parser_pairs": report.checked_parser_pairs,
        "accepted_transitions": report.accepted_transitions,
        "rejected_transitions": report.rejected_transitions,
        "parser_projection_code": report.parser_projection_code,
        "source_sha256": {path: digest for path, digest in report.source_sha256},
        "smallest_counterexample": None if counterexample is None else {
            "trace": [action.value for action in counterexample.trace],
            "action": counterexample.action.value,
            "word": counterexample.word,
        },
    }
    omission_summary = {
        "code": omitted.code,
        "missing_observations": list(omitted.missing_observations),
        "checked_inputs128": omitted.checked_inputs128,
    }
    return summary, elapsed_ms, omission_summary


def _case(label: str, category: str, report: Mapping[str, object], *, detail: str = "") -> dict[str, object]:
    result: dict[str, object] = {
        "label": label,
        "category": category,
        "status": report.get("status", "REJECTED"),
        "code": report.get("code"),
    }
    if detail:
        result["detail"] = detail
    return result


def _coverage(cases: Sequence[Mapping[str, object]]) -> dict[str, int]:
    counts = {"missing_requirement": 0, "code_bug": 0, "model_omission": 0}
    for case in cases:
        category = case.get("category")
        if category in counts:
            counts[category] += 1
    return counts


def qualify(*, output: Path, source_root: Path, tau_bin: Path | None, esso_root: Path | None) -> dict[str, object]:
    # Keep the qualification linear so every signed request, rejection, archive
    # comparison, and replay receipt has a named artifact in the final report.
    # The runner is an evidence shell; it does not hide workflow stages behind
    # a second project API or custom user orchestration.
    output = _fresh_output(output)
    source_root = _absolute(source_root)
    if not source_root.is_dir():
        _fail("SOURCE_ROOT_MISSING")
    if tau_bin is not None:
        tau_bin = _absolute(tau_bin)
    if esso_root is not None:
        esso_root = _absolute(esso_root)
    started = time.perf_counter_ns()
    with tempfile.TemporaryDirectory(prefix="zenolacuna-qualification-key-") as temporary:
        key_path = Path(temporary) / "owner.seed"
        descriptor = os.open(key_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        try:
            os.write(descriptor, OWNER_SECRET)
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        _require(stat.S_IMODE(key_path.stat().st_mode) == 0o600, "KEY_PERMISSIONS")

        runner = _CommandRunner(root=ROOT, key_path=key_path, secret=OWNER_SECRET)
        task_path = output / "migration.task.json"
        init_request = output / "init.request.json"
        init_signed = output / "init.signed.json"
        run_path = output / "migration.sqlite"
        task_result = runner.expect(
            "task", _project_args("task", ["--adapter", "signal-migration", "--out", str(task_path)],
                                   source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        task_scope, source_hashes, source_metrics = _scope_and_sources(task_path, source_root)
        _require(len(source_hashes) == 9, "SOURCE_COUNT", str(len(source_hashes)))
        _require(type(task_result.get("sha256")) is str, "TASK_DIGEST_MISSING")
        task_report_value = _read_json(task_path)
        if type(task_report_value) is not dict:
            _fail("TASK_INVALID")
        task_report = cast(dict[str, object], task_report_value)

        init_result = runner.expect(
            "prepare-init",
            _project_args("prepare-init", ["--task", str(task_path), "--project-id", PROJECT_ID,
                                            "--out", str(init_request)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        del init_result
        checker_sha256 = _checker_hash(init_request)
        runner.expect(
            "sign-init",
            _project_args("sign", ["--request", str(init_request), "--key-file", str(key_path),
                                    "--out", str(init_signed)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        signed_owner_key = _public_key(init_signed)
        _require(signed_owner_key == OWNER_PUBLIC_KEY, "OWNER_KEY_MISMATCH")
        owner_key = OWNER_PUBLIC_KEY
        apply_init = runner.expect(
            "apply-init",
            _project_args("apply", ["--run", str(run_path), "--owner-key", owner_key,
                                     "--command", str(init_signed)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        _require(apply_init.get("project_id") == PROJECT_ID, "INIT_PROJECT_ID")
        initial_status = runner.expect(
            "status-initial",
            _project_args("status", ["--run", str(run_path), "--owner-key", owner_key],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        _require(initial_status.get("execution_context") == "FRESH_SOURCE_PROCESS", "SOURCE_EXECUTION_CONTEXT")

        proposal = runner.expect(
            "propose-initial",
            _project_args("propose", ["--run", str(run_path), "--owner-key", owner_key],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        analysis = proposal.get("analysis")
        if type(analysis) is not dict:
            packet = proposal.get("packet")
            analysis = packet.get("current") if type(packet) is dict else None
        if type(analysis) is not dict or type(analysis.get("witness")) is not dict:
            _fail("WITNESS_MISSING")
        witness_path = output / "initial.witness.json"
        _write_exclusive(witness_path, analysis["witness"])
        runner.expect(
            "admit-witness",
            _project_args("witness", ["--run", str(run_path), "--owner-key", owner_key,
                                       "--witness", str(witness_path), "--expected-revision", str(initial_status["revision"])],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )

        cases: list[dict[str, object]] = []
        tampered_signed = output / "tampered-init.signed.json"
        _tamper_signed(init_signed, tampered_signed)
        archive_before_bad_signature = output / "before-bad-signature.bundle"
        archive_after_bad_signature = output / "after-bad-signature.bundle"
        runner.expect(
            "export-before-bad-signature",
            _project_args("export", ["--run", str(run_path), "--owner-key", owner_key,
                                      "--out", str(archive_before_bad_signature)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        bad_signature = runner.expect(
            "reject-bad-signature",
            _project_args("apply", ["--run", str(run_path), "--owner-key", owner_key,
                                     "--command", str(tampered_signed)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=2,
            codes=("INVALID_SIGNATURE",),
        )
        runner.expect(
            "export-after-bad-signature",
            _project_args("export", ["--run", str(run_path), "--owner-key", owner_key,
                                      "--out", str(archive_after_bad_signature)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        _require(archive_before_bad_signature.read_bytes() == archive_after_bad_signature.read_bytes(),
                 "BAD_SIGNATURE_MUTATED_ARCHIVE")
        cases.append(_case("bad-signature", "authorization", bad_signature))

        unguarded_path = output / "unguarded.candidate.json"
        runner.expect(
            "candidate-unguarded",
            _project_args("candidate", ["--mode", "unguarded", "--out", str(unguarded_path)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
            returncode=0,
        )
        premature_complete_request = output / "premature-complete.request.json"
        premature_complete = runner.invoke(
            "prepare-premature-complete",
            _project_args("prepare", ["--run", str(run_path), "--owner-key", owner_key,
                                       "--action", "complete", "--out", str(premature_complete_request)],
                          source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
        )
        if premature_complete[0] == 2:
            _require(premature_complete[1].get("code") in {
                "CANDIDATE_REQUIRED", "MISSING_REQUIREMENT", "NEEDS_DECISION", "UNRESOLVED_DECISIONS",
            },
                     "PREMATURE_COMPLETE_CODE", str(premature_complete[1].get("code")))
            cases.append(_case("premature-complete", "missing_requirement", premature_complete[1]))
        else:
            _require(premature_complete[0] == 0, "PREMATURE_COMPLETE_RETURN")
            premature_complete_signed = output / "premature-complete.signed.json"
            runner.expect("sign-premature-complete", _project_args(
                "sign", ["--request", str(premature_complete_request), "--key-file", str(key_path),
                          "--out", str(premature_complete_signed)], source_root=source_root,
                tau_bin=tau_bin, esso_root=esso_root), returncode=0)
            rejected = runner.expect("reject-premature-complete", _project_args(
                "apply", ["--run", str(run_path), "--owner-key", owner_key, "--command", str(premature_complete_signed)],
                source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=2,
                codes=("CANDIDATE_REQUIRED", "MISSING_REQUIREMENT", "NEEDS_DECISION", "UNRESOLVED_DECISIONS"))
            cases.append(_case("premature-complete", "missing_requirement", rejected))

        premature_assess_request = output / "premature-assess.request.json"
        premature_assess_signed = output / "premature-assess.signed.json"
        runner.expect("prepare-premature-assess", _project_args(
            "prepare", ["--run", str(run_path), "--owner-key", owner_key, "--action", "assess",
                         "--candidate", str(unguarded_path), "--out", str(premature_assess_request)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        runner.expect("sign-premature-assess", _project_args(
            "sign", ["--request", str(premature_assess_request), "--key-file", str(key_path),
                      "--out", str(premature_assess_signed)], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        premature_assess = runner.expect("reject-premature-assess", _project_args(
            "apply", ["--run", str(run_path), "--owner-key", owner_key, "--command", str(premature_assess_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=2,
            codes=("MISSING_REQUIREMENT", "NEEDS_DECISION", "UNRESOLVED_DECISIONS"))
        cases.append(_case("premature-assess", "missing_requirement", premature_assess))

        stale_answer_request = output / "stale-answer.request.json"
        stale_answer_signed = output / "stale-answer.signed.json"
        runner.expect("prepare-stale-answer", _project_args(
            "prepare", ["--run", str(run_path), "--owner-key", owner_key, "--action", "answer",
                         "--answer", "UNGUARDED", "--out", str(stale_answer_request)], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        runner.expect("sign-stale-answer", _project_args(
            "sign", ["--request", str(stale_answer_request), "--key-file", str(key_path),
                      "--out", str(stale_answer_signed)], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)

        answer_request = output / "guard-answer.request.json"
        answer_signed = output / "guard-answer.signed.json"
        runner.expect("prepare-guard-answer", _project_args(
            "prepare", ["--run", str(run_path), "--owner-key", owner_key, "--action", "answer",
                         "--answer", "GUARDED", "--out", str(answer_request)], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        runner.expect("sign-guard-answer", _project_args(
            "sign", ["--request", str(answer_request), "--key-file", str(key_path), "--out", str(answer_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        answered = runner.expect("apply-guard-answer", _project_args(
            "apply", ["--run", str(run_path), "--owner-key", owner_key, "--command", str(answer_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)

        revised_task_path = output / "revised.task.json"
        revised_task = _revised_task(task_path, revised_task_path)
        revised_scope = revised_task["scope"]
        _require(type(revised_scope) is dict, "REVISED_SCOPE_INVALID")
        revised_scope_dict = cast(dict[str, object], revised_scope)
        _require(revised_scope_dict.get("hypotheses") == task_scope.get("hypotheses"), "HYPOTHESES_CHANGED")
        _require(revised_scope_dict.get("assumptions") == task_scope.get("assumptions"), "ASSUMPTIONS_CHANGED")
        revised_protected = revised_scope_dict.get("protected")
        _require(type(revised_protected) is list and any(
            type(item) is dict and item.get("name") == "no_unsafe_rollout" for item in revised_protected
        ), "REVISED_REQUIREMENT_MISSING")
        revise_request = output / "revise.request.json"
        revise_signed = output / "revise.signed.json"
        runner.expect("prepare-revise", _project_args(
            "prepare", ["--run", str(run_path), "--owner-key", owner_key, "--action", "revise",
                         "--task", str(revised_task_path), "--reason", "Require guarded rollout transitions",
                         "--out", str(revise_request)], source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
                      returncode=0)
        runner.expect("sign-revise", _project_args(
            "sign", ["--request", str(revise_request), "--key-file", str(key_path), "--out", str(revise_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        revised = runner.expect("apply-revise", _project_args(
            "apply", ["--run", str(run_path), "--owner-key", owner_key, "--command", str(revise_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        _require(revised.get("scope_revision") != answered.get("scope_revision"), "REVISION_NOT_NEW_SCOPE")
        _require(revised.get("candidate_root") is None, "REVISION_RETAINED_CANDIDATE")
        _require(revised.get("survivors") == [1], "UNGUARDED_SURVIVOR_NOT_REMOVED")

        stale_before = output / "before-stale-answer.bundle"
        stale_after = output / "after-stale-answer.bundle"
        runner.expect("export-before-stale-answer", _project_args(
            "export", ["--run", str(run_path), "--owner-key", owner_key, "--out", str(stale_before)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        stale = runner.expect("reject-stale-answer", _project_args(
            "apply", ["--run", str(run_path), "--owner-key", owner_key, "--command", str(stale_answer_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=2,
            codes=("STALE_ANSWER",))
        runner.expect("export-after-stale-answer", _project_args(
            "export", ["--run", str(run_path), "--owner-key", owner_key, "--out", str(stale_after)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        _require(stale_before.read_bytes() == stale_after.read_bytes(), "STALE_ANSWER_MUTATED_ARCHIVE")
        cases.append(_case("stale-answer", "stale_revision", stale))

        before_inspect = runner.expect("status-before-unguarded-inspect", _project_args(
            "status", ["--run", str(run_path), "--owner-key", owner_key], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        inspected = runner.expect("inspect-unguarded", _project_args(
            "inspect", ["--run", str(run_path), "--owner-key", owner_key, "--candidate", str(unguarded_path)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        _require(str(inspected.get("code", "")).startswith("CODE_BUG"), "UNGUARDED_NOT_CODE_BUG")
        cases.append(_case("unguarded-candidate", "code_bug", {"status": "REJECTED", "code": inspected.get("code")}))
        after_inspect = runner.expect("status-after-unguarded-inspect", _project_args(
            "status", ["--run", str(run_path), "--owner-key", owner_key], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        _require(before_inspect.get("revision") == after_inspect.get("revision"), "INSPECT_MUTATED_REVISION")
        _require(after_inspect.get("candidate_root") is None, "INSPECT_ADMITTED_CANDIDATE")

        guarded_path = output / "guarded.candidate.json"
        runner.expect("candidate-guarded", _project_args(
            "candidate", ["--mode", "guarded", "--out", str(guarded_path)], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        assess_request = output / "guarded-assess.request.json"
        assess_signed = output / "guarded-assess.signed.json"
        runner.expect("prepare-guarded-assess", _project_args(
            "prepare", ["--run", str(run_path), "--owner-key", owner_key, "--action", "assess",
                         "--candidate", str(guarded_path), "--out", str(assess_request)], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        runner.expect("sign-guarded-assess", _project_args(
            "sign", ["--request", str(assess_request), "--key-file", str(key_path), "--out", str(assess_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        assessed = runner.expect("apply-guarded-assess", _project_args(
            "apply", ["--run", str(run_path), "--owner-key", owner_key, "--command", str(assess_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        _require(assessed.get("candidate_root") is not None, "GUARDED_CANDIDATE_NOT_ADMITTED")

        direct_summary, direct_ms, omission_summary = _direct_migration_baseline()
        _require(direct_summary.get("code") == "SIGNAL_MIGRATION_CHECKED", "DIRECT_BASELINE_CODE")
        _require(omission_summary.get("code") == "MODEL_OMISSION", "DIRECT_MODEL_OMISSION_CODE")
        cases.append({"label": "missing-observation-declaration", "category": "model_omission",
                      "status": "REJECTED", "code": omission_summary["code"]})

        complete_request = output / "complete.request.json"
        complete_signed = output / "complete.signed.json"
        runner.expect("prepare-complete", _project_args(
            "prepare", ["--run", str(run_path), "--owner-key", owner_key, "--action", "complete",
                         "--out", str(complete_request)], source_root=source_root, tau_bin=tau_bin, esso_root=esso_root),
                      returncode=0)
        runner.expect("sign-complete", _project_args(
            "sign", ["--request", str(complete_request), "--key-file", str(key_path), "--out", str(complete_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        completion_started = time.perf_counter_ns()
        completed = runner.expect("apply-complete", _project_args(
            "apply", ["--run", str(run_path), "--owner-key", owner_key, "--command", str(complete_signed)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        completion_ms = (time.perf_counter_ns() - completion_started) // 1_000_000
        _require(completed.get("workflow") == "COMPLETE_FOR_SCOPE", "COMPLETION_WORKFLOW")
        completion = completed.get("completion")
        if type(completion) is not dict or type(completion.get("runtime")) is not dict:
            _fail("COMPLETION_EVIDENCE_MISSING")
        runtime = completion["runtime"]
        _require(runtime.get("claim") == "FINITE_SIGNAL_MIGRATION_GRAPH", "COMPLETION_CLAIM")
        runtime_report = runtime.get("report")
        if type(runtime_report) is not dict:
            _fail("COMPLETION_REPORT_MISSING")
        solver_evidence = completion.get("solvers")
        if type(solver_evidence) is not dict:
            _fail("SOLVER_EVIDENCE_MISSING")
        required_tau = task_report.get("tau_sha256")
        required_esso = task_report.get("esso_sha256")
        if required_tau is not None:
            tau_result = solver_evidence.get("tau")
            _require(type(tau_result) is dict and tau_result.get("binary_sha256") == required_tau,
                     "TAU_RESULT_PIN_MISMATCH")
        if required_esso is not None:
            esso_result = solver_evidence.get("esso")
            _require(type(esso_result) is dict and esso_result.get("esso_sha256") == required_esso,
                     "ESSO_RESULT_PIN_MISMATCH")
        for field in (
            "checked_inputs128", "checked_states", "checked_edges", "checked_parser_pairs",
            "candidate_relation_matches", "accepted_transitions", "rejected_transitions",
            "parser_projection_code", "code", "evidence", "claim",
        ):
            _require(runtime_report.get(field) == direct_summary.get(field), "GRAPH_BOUNDARY_MISMATCH", field)
        _require(runtime_report.get("mode") == "GUARDED", "GRAPH_MODE_MISMATCH")
        completion_sources = runtime_report.get("source_sha256")
        if type(completion_sources) is list:
            completion_sources = {
                item[0]: item[1] for item in completion_sources
                if type(item) is list and len(item) == 2 and type(item[0]) is str and type(item[1]) is str
            }
        _require(completion_sources == direct_summary.get("source_sha256"), "SOURCE_REPORT_MISMATCH")

        final_bundle = output / "final.bundle.json"
        runner.expect("export-final", _project_args(
            "export", ["--run", str(run_path), "--owner-key", owner_key, "--out", str(final_bundle)],
            source_root=source_root, tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        replay_started = time.perf_counter_ns()
        replayed = runner.expect("replay-final-bundle", _project_args(
            "replaybundle", ["--bundle", str(final_bundle), "--owner-key", owner_key,
                              "--expected-revision", str(completed["revision"])], source_root=source_root,
            tau_bin=tau_bin, esso_root=esso_root), returncode=0)
        replay_ms = (time.perf_counter_ns() - replay_started) // 1_000_000
        _require(replayed.get("replay_scope") == "EXACT_HISTORICAL_SNAPSHOT", "REPLAY_SCOPE")
        _require(replayed.get("revision") == completed.get("revision"), "REPLAY_REVISION")
        _require(replayed.get("workflow") == "COMPLETE_FOR_SCOPE", "REPLAY_WORKFLOW")
        _require(replayed.get("completion") == completion, "REPLAY_COMPLETION_MISMATCH")
        _require(replayed.get("scope_root") == completed.get("scope_root"), "REPLAY_SOURCE_IDENTITY")

        source_files = [
            {"path": path, "bytes": source_metrics[path], "sha256": digest}
            for path, digest in sorted(source_hashes.items())
        ]
        coverage = _coverage(cases)
        report: dict[str, object] = {
            "schema": "zenolacuna/qualification/v1",
            "status": "QUALIFIED",
            "authority": "NONE",
            "approval_label": "TEST_CREDENTIALS",
            "project_id": PROJECT_ID,
            "owner_public_key": owner_key,
            "checker_sha256": checker_sha256,
            "source_sha256": source_hashes,
            "code_artifact_metrics": {
                "source_file_count": len(source_files),
                "source_bytes": source_metrics["__total_bytes__"],
                "files": source_files,
            },
            "task": {
                "sha256": hashlib.sha256(task_path.read_bytes()).hexdigest(),
                "tau_sha256": task_report.get("tau_sha256"),
                "esso_sha256": task_report.get("esso_sha256"),
            },
            "source_execution_context": initial_status.get("execution_context"),
            "fixture_kind": "TEST_CREDENTIALS_FIXED_OWNER_SECRET",
            "owner_question_count": 1,
            "declared_fixed_question_baseline": 1,
            "survivors_after_revise": revised.get("survivors"),
            "completion": {
                "workflow": completed.get("workflow"),
                "revision": completed.get("revision"),
                "candidate_root": completed.get("candidate_root"),
                "claim": runtime.get("claim"),
                "certificate": completion,
            },
            "replay": {
                "scope": replayed.get("replay_scope"),
                "revision": replayed.get("revision"),
                "claim": replayed.get("claim"),
                "workflow": replayed.get("workflow"),
                "certificate_equal": replayed.get("completion") == completion,
            },
            "required_tool_pins": {
                "tau_sha256": task_report.get("tau_sha256"),
                "esso_sha256": task_report.get("esso_sha256"),
            },
            "solver_evidence": solver_evidence,
            "direct_baseline": direct_summary,
            "negative_model_omission": omission_summary,
            "timings_ms": {
                "end_to_end": (time.perf_counter_ns() - started) // 1_000_000,
                "completion": completion_ms,
                "archive_replay": replay_ms,
                "direct_check_migration": direct_ms,
            },
            "timing_interpretation": "Descriptive local durations; no speed or throughput claim.",
            "cases": cases,
            "coverage": coverage,
            "hostile_case_counts": {
                "scope": "Explicit qualification cases only; no broader corpus claim.",
                "missing_requirement_recoveries": coverage["missing_requirement"],
                "missing_requirement_misses": 0,
                "spurious_witnesses": 0,
                "false_completions": 0,
            },
            "llm_calls": 0,
            "qualification_artifacts": {
                "runner_sha256": _file_sha256(Path(__file__).resolve()),
                "cli_bootstrap_sha256": {
                    "tools/zenolacuna.py": _file_sha256(CLI),
                    "tools/zenolacuna_project_entry.py": _file_sha256(
                        ROOT / "tools" / "zenolacuna_project_entry.py"
                    ),
                },
            },
            "commands": runner.commands,
            "nonclaims": [
                "No human consent or real owner approval; TEST_CREDENTIALS only.",
                "No physical producer authentication or runtime provenance for observations.",
                "No production readiness, novelty, legal clearance, deployment, or throughput claim.",
            ],
        }
        report_path = output / "qualification.report.json"
        _write_exclusive(report_path, report)
        report_hash = hashlib.sha256(report_path.read_bytes()).hexdigest()
        return {
            "artifact": "QUALIFICATION_REPORT",
            "path": str(report_path),
            "sha256": report_hash,
            "status": "QUALIFIED",
            "coverage": report["coverage"],
            "completion_ms": completion_ms,
            "archive_replay_ms": replay_ms,
        }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="zenolacuna_qualify")
    parser.add_argument("--out", required=True, metavar="DIRECTORY")
    parser.add_argument("--source-root", default=str(ROOT), metavar="PATH")
    parser.add_argument("--tau-bin", metavar="PATH")
    parser.add_argument("--esso-root", metavar="PATH")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = _parser().parse_args(list(argv) if argv is not None else None)
        summary = qualify(
            output=Path(args.out),
            source_root=Path(args.source_root),
            tau_bin=None if args.tau_bin is None else Path(args.tau_bin),
            esso_root=None if args.esso_root is None else Path(args.esso_root),
        )
        print(json.dumps(summary, sort_keys=True, separators=(",", ":")))
        return 0
    except QualificationError as error:
        failure: dict[str, object] = {"status": "REJECTED", "code": error.code}
        if error.detail:
            failure["detail"] = error.detail
        print(json.dumps(failure, sort_keys=True, separators=(",", ":")), file=sys.stderr)
        return 2
    except (OSError, subprocess.SubprocessError) as error:
        del error
        print(json.dumps({"status": "REJECTED", "code": "QUALIFICATION_IO"}, sort_keys=True, separators=(",", ":")), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
