from __future__ import annotations

import ast
import json
import subprocess
import sys
from pathlib import Path

from tests.test_zrpf_v3_firecracker_candidate_plan import build_intent_document
from tests.test_zrpf_v3_firecracker_runtime_manifest import build_manifest_document
from tools import check_zrpf_v3_firecracker_launch_preflight as preflight
from tools import zrpf_v3_firecracker_runtime_manifest as runtime


def test_preflight_compiles_non_executable_plan_without_artifacts(
    tmp_path: Path,
) -> None:
    manifest_path, manifest_sha, intent_path = _inputs(tmp_path)

    report = preflight.build_report(
        manifest_path=manifest_path,
        expected_manifest_sha256=manifest_sha,
        intent_path=intent_path,
        artifact_directory=None,
    )

    assert report["candidate_plan_compiled"] is True
    assert report["decision"] == "candidate_plan_compiled_artifacts_unavailable"
    assert report["artifact_bytes_status"] == "not_supplied"
    assert report["executable_prerequisites_satisfied"] is False
    assert report["root_launcher_ready"] is False
    assert report["microvm_replay_verified"] is False
    assert all(value is False for value in report["authority"].values())


def test_preflight_locally_binds_exact_artifact_bytes(tmp_path: Path) -> None:
    kernel = b"kernel"
    rootfs = b"rootfs"
    manifest_path, manifest_sha, intent_path = _inputs(
        tmp_path,
        kernel=kernel,
        rootfs=rootfs,
    )
    artifact_directory = tmp_path / "artifacts"
    artifact_directory.mkdir()
    document = build_manifest_document(kernel, rootfs)
    (artifact_directory / document["guest_kernel"]["artifact_name"]).write_bytes(kernel)
    (artifact_directory / document["input_image"]["artifact_name"]).write_bytes(b"input-image")
    (artifact_directory / document["rootfs"]["artifact_name"]).write_bytes(rootfs)

    report = preflight.build_report(
        manifest_path=manifest_path,
        expected_manifest_sha256=manifest_sha,
        intent_path=intent_path,
        artifact_directory=artifact_directory,
    )

    assert report["candidate_plan_compiled"] is True
    assert report["decision"] == ("candidate_plan_compiled_artifacts_locally_bound")
    assert report["artifact_bytes_status"] == "exact_match"
    assert report["root_launcher_ready"] is False


def test_require_executable_always_exits_one_with_canonical_report(
    tmp_path: Path,
    capfd,
) -> None:
    manifest_path, manifest_sha, intent_path = _inputs(tmp_path)

    exit_code = preflight.main(
        [
            "--manifest",
            str(manifest_path),
            "--expected-manifest-sha256",
            manifest_sha,
            "--intent",
            str(intent_path),
            "--require-executable",
        ]
    )
    captured = capfd.readouterr()
    report = json.loads(captured.out)

    assert exit_code == 1
    assert report["candidate_plan_compiled"] is True
    assert report["root_launcher_ready"] is False
    assert captured.out.encode("ascii") == runtime.canonical_document_bytes(report)
    assert captured.err == ""


def test_wrong_governed_manifest_hash_rejects_without_path_disclosure(
    tmp_path: Path,
) -> None:
    manifest_path, _manifest_sha, intent_path = _inputs(tmp_path)

    report = preflight.build_report(
        manifest_path=manifest_path,
        expected_manifest_sha256="ab" * 32,
        intent_path=intent_path,
        artifact_directory=None,
    )

    assert report["candidate_plan_compiled"] is False
    assert report["errors"] == ["runtime_manifest_governed_hash_mismatch"]
    assert report["decision"] == "candidate_plan_rejected"
    assert tmp_path.as_posix() not in json.dumps(report)
    assert all(value is False for value in report["authority"].values())


def test_intent_rejection_preserves_manifest_integrity_scope(tmp_path: Path) -> None:
    manifest_path, manifest_sha, intent_path = _inputs(tmp_path)
    intent_path.write_bytes(runtime.canonical_document_bytes({"schema": "wrong"}))

    report = preflight.build_report(
        manifest_path=manifest_path,
        expected_manifest_sha256=manifest_sha,
        intent_path=intent_path,
        artifact_directory=None,
    )

    assert report["candidate_plan_compiled"] is False
    assert report["errors"] == ["candidate_intent_fields_mismatch"]
    assert report["runtime_manifest_integrity_valid"] is True
    assert report["candidate_profile_binding_valid"] is True
    assert report["manifest_anchor_scope"] == "caller_supplied_preflight_only"
    assert report["root_launcher_ready"] is False


def test_isolated_cli_uses_only_sibling_modules(tmp_path: Path) -> None:
    manifest_path, manifest_sha, intent_path = _inputs(tmp_path)

    completed = subprocess.run(
        [
            sys.executable,
            "-I",
            preflight.__file__,
            "--manifest",
            str(manifest_path),
            "--expected-manifest-sha256",
            manifest_sha,
            "--intent",
            str(intent_path),
        ],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        env={"PATH": "/usr/bin:/bin", "PYTHONPATH": tmp_path.as_posix()},
        timeout=10,
    )

    assert completed.returncode == 0
    assert completed.stderr == b""
    report = json.loads(completed.stdout)
    assert report["candidate_plan_compiled"] is True
    assert report["root_launcher_ready"] is False


def test_contract_layer_contains_no_process_execution_primitive() -> None:
    modules = (
        preflight,
        preflight.artifact_set,
        preflight.candidate_plan,
        preflight.runtime_manifest,
    )
    forbidden_imports = {"subprocess", "socket"}
    forbidden_calls = {"execv", "execve", "fork", "posix_spawn", "system"}
    for module in modules:
        module_file = module.__file__
        assert isinstance(module_file, str)
        tree = ast.parse(Path(module_file).read_text(encoding="utf-8"))
        imported: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".", 1)[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".", 1)[0])
        called_attributes = {
            node.func.attr
            for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
        }
        assert forbidden_imports.isdisjoint(imported), module.__name__
        assert forbidden_calls.isdisjoint(called_attributes), module.__name__


def _inputs(
    root: Path,
    *,
    kernel: bytes = b"test-kernel",
    rootfs: bytes = b"test-rootfs",
) -> tuple[Path, str, Path]:
    manifest_document = build_manifest_document(kernel, rootfs)
    manifest_path = root / "manifest.json"
    manifest_path.write_bytes(runtime.canonical_document_bytes(manifest_document))
    intent_path = root / "intent.json"
    intent_path.write_bytes(runtime.canonical_document_bytes(build_intent_document()))
    return (
        manifest_path,
        runtime.canonical_sha256_hex(manifest_document),
        intent_path,
    )
