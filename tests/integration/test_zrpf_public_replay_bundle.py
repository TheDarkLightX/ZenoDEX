from __future__ import annotations

import copy
import json
import os
import platform
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, cast

import pytest

from src.integration import zrpf_public_replay_bundle as replay

REPO_ROOT = Path(__file__).resolve().parents[2]
BUNDLE = REPO_ROOT / replay.DEFAULT_BUNDLE_RELATIVE
REFERENCE = REPO_ROOT / replay.DEFAULT_REFERENCE_RELATIVE
NATIVE_REPLAY_ENV = "ZENODEX_RUN_NATIVE_ZRPF_REPLAY"


def _check(bundle: Path, reference: Path, *, execute: bool = False) -> dict[str, object]:
    return replay.check_bundle(
        bundle_directory=bundle,
        reference_path=reference,
        execute=execute,
    )


def _copy_bundle(tmp_path: Path) -> tuple[Path, Path]:
    bundle = tmp_path / "bundle"
    shutil.copytree(BUNDLE, bundle)
    reference = tmp_path / "reference.json"
    shutil.copy2(REFERENCE, reference)
    return bundle, reference


def _rewrite_reference(
    reference_path: Path,
    manifest_raw: bytes,
    *,
    verifier_sha256: str | None = None,
) -> None:
    reference = json.loads(reference_path.read_bytes())
    reference["manifest_sha256"] = replay.sha256_hex(manifest_raw)
    if verifier_sha256 is not None:
        reference["verifier_sha256"] = verifier_sha256
    reference_path.write_bytes(replay.canonical_json_bytes(reference))


def _trust_test_reference(
    monkeypatch: pytest.MonkeyPatch,
    reference_path: Path,
) -> None:
    monkeypatch.setattr(
        replay,
        "EXPECTED_REFERENCE_FILE_SHA256",
        replay.sha256_hex(reference_path.read_bytes()),
    )


def test_committed_public_replay_bundle_passes_static_validation() -> None:
    report = _check(BUNDLE, REFERENCE)
    assert report == {
        "checked_artifacts": 21,
        "errors": [],
        "execution_checked": False,
        "ok": True,
        "production_claim_allowed": False,
        "schema": replay.REPORT_SCHEMA,
        "scoped_public_replay_claim_allowed": False,
        "status": "static_bundle_accepted",
    }


def test_static_snapshot_modes_are_independent_of_caller_umask() -> None:
    previous_umask = os.umask(0o077)
    try:
        report = _check(BUNDLE, REFERENCE)
    finally:
        os.umask(previous_umask)

    assert report["ok"] is True
    assert report["status"] == "static_bundle_accepted"


def test_callable_boundary_rejects_non_boolean_execute_before_native_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def unexpected_execute(*args: object, **kwargs: object) -> None:
        raise AssertionError("native replay must not run")

    monkeypatch.setattr(replay, "_execute_and_compare", unexpected_execute)

    report = replay.check_bundle(
        bundle_directory=BUNDLE,
        reference_path=REFERENCE,
        execute=cast(Any, 1),
    )

    assert report == {
        "checked_artifacts": 0,
        "errors": ["execute flag must be boolean"],
        "execution_checked": False,
        "ok": False,
        "production_claim_allowed": False,
        "scoped_public_replay_claim_allowed": False,
        "schema": replay.REPORT_SCHEMA,
        "status": "rejected",
    }


@pytest.mark.skipif(
    os.environ.get(NATIVE_REPLAY_ENV) != "1"
    or sys.platform != "linux"
    or platform.machine().lower() not in {"amd64", "x86_64"},
    reason=(f"native replay requires Linux x86-64 and explicit {NATIVE_REPLAY_ENV}=1 opt-in"),
)
def test_committed_public_replay_executes_pinned_verifier() -> None:
    report = _check(BUNDLE, REFERENCE, execute=True)
    assert report["ok"] is True
    assert report["execution_checked"] is True
    assert report["scoped_public_replay_claim_allowed"] is True
    assert report["status"] == "executed_replay_accepted"


@pytest.mark.parametrize(
    ("tool", "expected"),
    [
        ("tools/check_zrpf_v3_public_replay_bundle.py", '"status":"static_bundle_accepted"'),
        ("tools/build_zrpf_v3_public_replay_bundle.py", "--proof-source-closure"),
    ],
)
def test_public_replay_clis_ignore_hostile_pythonpath(
    tmp_path: Path,
    tool: str,
    expected: str,
) -> None:
    fake = tmp_path / "evil/src/integration"
    fake.mkdir(parents=True)
    (fake.parent / "__init__.py").write_text("", encoding="utf-8")
    (fake / "__init__.py").write_text("", encoding="utf-8")
    (fake / "zrpf_public_replay_bundle.py").write_text(
        "raise SystemExit('hostile import executed')\n",
        encoding="utf-8",
    )
    command = [sys.executable, tool]
    if "build_" in tool:
        command.append("--help")
    env = os.environ.copy()
    env["PYTHONPATH"] = f"{tmp_path / 'evil'}:{REPO_ROOT}"

    completed = subprocess.run(
        command,
        cwd=REPO_ROOT,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0
    assert "hostile import executed" not in completed.stderr
    assert expected in completed.stdout


@pytest.mark.skipif(sys.platform != "linux", reason="POSIX resource limits are Linux-gated")
def test_native_process_output_has_a_kernel_file_size_limit(tmp_path: Path) -> None:
    returncode, stdout, stderr = replay._run_bounded_process(
        [
            sys.executable,
            "-c",
            f"import sys; sys.stdout.write('x' * {replay.MAX_TRANSCRIPT_BYTES * 2})",
        ],
        tmp_path,
    )

    assert returncode != 0
    assert len(stdout) <= replay.MAX_TRANSCRIPT_BYTES
    assert len(stderr) <= replay.MAX_TRANSCRIPT_BYTES


def test_reference_rejects_a_rebound_manifest_digest(tmp_path: Path) -> None:
    reference = json.loads(REFERENCE.read_bytes())
    reference["manifest_sha256"] = "0" * 64
    rebound = tmp_path / "reference.json"
    rebound.write_bytes(replay.canonical_json_bytes(reference))
    rebound.chmod(0o644)

    report = _check(BUNDLE, rebound)

    assert report["ok"] is False
    assert report["errors"] == ["reference does not match the reviewed trust anchor"]


def test_checker_rejects_a_coherently_reanchored_extra_seal_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    mutated_path = bundle / replay.MUTATED_RECEIPT
    mutated = json.loads(mutated_path.read_bytes())
    mutated["inner"]["Succinct"]["seal"][2] ^= 1
    mutated_raw = replay.compact_json_bytes(mutated)
    mutated_path.write_bytes(mutated_raw)

    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    row = next(
        artifact for artifact in manifest["artifacts"] if artifact["path"] == replay.MUTATED_RECEIPT
    )
    row["sha256"] = replay.sha256_hex(mutated_raw)
    row["size_bytes"] = len(mutated_raw)
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["mutated receipt does not change exactly seal word 1"]


def test_checker_rejects_duplicate_manifest_keys_even_when_reanchored(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    original = manifest_path.read_bytes()
    duplicated = original[:-1] + b',"schema":"duplicate"}'
    manifest_path.write_bytes(duplicated)
    _rewrite_reference(reference, duplicated)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert "duplicate JSON key: schema" in str(report["errors"])


def test_checker_rejects_unknown_files_and_symlinks(tmp_path: Path) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    (bundle / "unknown").write_bytes(b"unexpected")
    unknown_report = _check(bundle, reference)
    assert unknown_report["errors"] == ["bundle inventory mismatch"]

    (bundle / "unknown").unlink()
    (bundle / "link").symlink_to(bundle / "manifest.json")
    symlink_report = _check(bundle, reference)
    assert symlink_report["errors"] == ["bundle contains a symlink"]


def test_checker_rejects_a_coherently_reanchored_claim_expansion(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = copy.deepcopy(json.loads(manifest_path.read_bytes()))
    manifest["claims"]["production_authority"] = True
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["claims values mismatch"]


def test_checker_rejects_integer_substitution_for_boolean_claim(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["claims"]["public_artifact_replay"] = 1
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["claims values mismatch"]


def test_checker_rejects_integer_substitution_for_boolean_sanitization_fact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["sanitization"]["embedded_absolute_compiler_paths_present"] = 1
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["sanitization values mismatch"]


def test_checker_rejects_boolean_substitution_for_replay_exit_code(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["replay"]["positive"]["expected_exit_code"] = False
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["positive replay contract mismatch"]


def test_checker_rejects_a_self_anchored_fake_verifier(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    verifier_path = bundle / replay.VERIFIER
    fake = b"#!/bin/sh\nprintf '%s\\n' '{\"ok\":true}'\n"
    verifier_path.write_bytes(fake)
    verifier_path.chmod(0o755)

    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    row = next(
        artifact for artifact in manifest["artifacts"] if artifact["path"] == replay.VERIFIER
    )
    row["sha256"] = replay.sha256_hex(fake)
    row["size_bytes"] = len(fake)
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(
        reference,
        manifest_raw,
        verifier_sha256=replay.sha256_hex(fake),
    )
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference, execute=True)

    assert report["ok"] is False
    assert report["errors"] == ["verifier does not match the reviewed trust anchor"]


@pytest.mark.parametrize("malformed", [0, {"role": "receipt"}])
def test_checker_reports_malformed_artifact_rows_fail_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    malformed: object,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["artifacts"][0] = malformed
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["artifact fields mismatch"]


def test_checker_enforces_governed_executable_policy(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    (bundle / replay.VERIFIER).chmod(0o644)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    row = next(
        artifact for artifact in manifest["artifacts"] if artifact["path"] == replay.VERIFIER
    )
    row["executable"] = False
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["artifact path, role, or authority contract mismatch"]


def test_checker_rejects_group_or_world_writable_artifact_mode(tmp_path: Path) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    (bundle / replay.VERIFIER).chmod(0o777)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == [f"source artifact changed: {replay.VERIFIER}"]


@pytest.mark.parametrize(
    ("field", "value", "error"),
    [
        ("version", True, "bundle manifest schema or version mismatch"),
        ("evidence_date", "2026-99-99", "manifest evidence date is invalid"),
    ],
)
def test_checker_rejects_boolean_versions_and_impossible_dates(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    value: object,
    error: str,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest[field] = value
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == [error]


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("seal_word_index", True),
        ("xor_mask", True),
        ("seal_word_original", False),
        ("seal_word_mutated", True),
    ],
)
def test_checker_rejects_boolean_mutation_numbers(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    value: object,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["tree"]["seal_mutation"][field] = value
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["seal mutation facts mismatch"]


def test_checker_rejects_non_integer_source_file_count(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    closure_path = bundle / replay.VERIFIER_SOURCE_CLOSURE
    closure = json.loads(closure_path.read_bytes())
    closure["file_count"] = 37.0
    closure_raw = replay.canonical_json_bytes(closure)
    closure_path.write_bytes(closure_raw)

    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    row = next(
        artifact
        for artifact in manifest["artifacts"]
        if artifact["path"] == replay.VERIFIER_SOURCE_CLOSURE
    )
    row["sha256"] = replay.sha256_hex(closure_raw)
    row["size_bytes"] = len(closure_raw)
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["source closure file count mismatch"]


def test_checker_uses_private_snapshot_after_source_capture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    context_path = bundle / "inputs/v1-spot.proof.json"
    original_validate = replay._validate_artifact_files
    calls = 0

    def mutate_after_first_validation(
        checked_bundle: Path,
        artifacts: list[dict[str, Any]],
    ) -> None:
        nonlocal calls
        original_validate(checked_bundle, artifacts)
        calls += 1
        if calls == 1:
            context_path.write_bytes(context_path.read_bytes() + b" ")

    monkeypatch.setattr(replay, "_validate_artifact_files", mutate_after_first_validation)

    report = _check(bundle, reference)

    assert context_path.read_bytes().endswith(b" ")
    assert report["ok"] is True
    assert report["execution_checked"] is False
    assert report["status"] == "static_bundle_accepted"


def test_checker_cross_binds_build_record_to_source_closure(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["proof_generation_record"]["source_git_commit"] = "0" * 40
    manifest_raw = replay.canonical_json_bytes(manifest)
    manifest_path.write_bytes(manifest_raw)
    _rewrite_reference(reference, manifest_raw)
    _trust_test_reference(monkeypatch, reference)

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["proof source closure differs from manifest build record"]


def test_checker_rejects_unknown_empty_directories(tmp_path: Path) -> None:
    bundle, reference = _copy_bundle(tmp_path)
    (bundle / "empty").mkdir()

    report = _check(bundle, reference)

    assert report["ok"] is False
    assert report["errors"] == ["bundle directory inventory mismatch"]


def test_manifest_marks_context_artifacts_and_generation_nonclaims() -> None:
    manifest = json.loads((BUNDLE / "manifest.json").read_bytes())
    context_roles = {
        "guest_elf_context",
        "proof_source_closure_context",
        "source_proof_context",
        "toolchain_lock_context",
        "verifier_source_closure_context",
    }
    assert all(
        row["replay_authority"] is False
        for row in manifest["artifacts"]
        if row["role"] in context_roles
    )
    assert manifest["claims"]["fresh_proof_artifacts_from_source_frozen_run"] is False
    assert manifest["claims"]["proof_generation_provenance_machine_verified"] is False
    assert manifest["claims"]["verifier_build_provenance_machine_verified"] is False
    assert manifest["sanitization"] == {
        "embedded_absolute_compiler_paths_present": True,
        "publisher_private_name_review_recorded": True,
        "public_checker_validates_artifact_bytes_for_private_names": False,
        "source_path_remapping_complete": False,
    }
