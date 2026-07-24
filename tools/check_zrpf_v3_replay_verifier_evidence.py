#!/usr/bin/env python3
"""Check or replay the exact retained ZRPF V3 receipt evidence lane."""

from __future__ import annotations

import argparse
import importlib
import json
import os
import stat
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_MODULE_PREFIX = "tools." if __package__ else ""
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")
live_controls = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_live_controls")
environment = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_environment")
source_snapshot = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_v3_replay_source_snapshot"
)
toolchain = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_toolchain")
record_writer = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_v3_replay_record_writer"
)
process_runner = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_process")
privacy = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_artifact_privacy")
sealed_executable = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_v3_replay_sealed_executable"
)

PACKAGE = "zenodex-zrpf-risc0-replay-verifier"
BINARY = "zenodex-zrpf-risc0-replay-verifier"
MAX_PROCESS_OUTPUT = 16 * 1024 * 1024
MAX_FAILURE_DIAGNOSTIC_BYTES = 2 * 1024
MAX_EVIDENCE_BYTES = 4 * 1024 * 1024
FORBIDDEN_GRAPH_TOKENS = (
    "bonsai-sdk",
    "risc0-build",
    "zenodex-zrpf-risc0-harness",
    "zenodex-zrpf-risc0-methods",
    "zenodex-zrpf-risc0-structural-aggregate",
    "zenodex-zrpf-risc0-v1-leaf-adapter",
)


@dataclass(frozen=True)
class LiveContext:
    repo_root: Path
    workspace: Path
    source_root: Path
    target_directory: Path
    cargo: str
    env: dict[str, str]
    toolchain_versions: dict[str, str]


@dataclass(frozen=True)
class LiveReplay:
    binary_sha256: str
    binary_size_bytes: int
    binary_transport: str
    dependency_graph: tuple[str, ...]
    negative_controls: list[dict[str, Any]]
    stdout: bytes


@dataclass(frozen=True)
class LoadedEvidence:
    document: dict[str, Any]
    raw: bytes


def load_evidence(path: Path) -> tuple[LoadedEvidence | None, list[str]]:
    try:
        raw = _read_bounded_regular_file(path, MAX_EVIDENCE_BYTES)
    except (OSError, ValueError):
        return None, ["evidence file read failed"]
    try:
        value = support.strict_json_loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        return None, [f"evidence JSON rejected: {exc}"]
    if not isinstance(value, dict):
        return None, ["evidence root must be an object"]
    return LoadedEvidence(value, raw), []


def _read_bounded_regular_file(path: Path, maximum: int) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NONBLOCK
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > maximum
        ):
            raise ValueError("evidence file is not a bounded regular file")
        output = bytearray()
        while True:
            chunk = os.read(descriptor, min(64 * 1024, maximum + 1 - len(output)))
            if not chunk:
                break
            output.extend(chunk)
            if len(output) > maximum:
                raise ValueError("evidence file is not a bounded regular file")
        after = os.fstat(descriptor)
        if _stat_identity(before) != _stat_identity(after) or len(output) != after.st_size:
            raise ValueError("evidence file changed while read")
        return bytes(output)
    finally:
        os.close(descriptor)


def _stat_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def validate_static(
    path: Path = support.EVIDENCE_PATH,
    repo_root: Path = support.REPO_ROOT,
) -> dict[str, Any]:
    loaded, errors = load_evidence(path)
    material = validate_materials(repo_root)
    errors.extend(material["errors"])
    privacy_ok = False
    recorded_identity: dict[str, Any] | None = None
    if loaded is not None:
        if support.sha256_bytes(loaded.raw) != support.EXPECTED_EVIDENCE_SHA256:
            errors.append("evidence SHA-256 differs from governed anchor")
        existing_scan = privacy.scan_artifacts(repo_root, privacy.PRE_RECORD_ARTIFACTS)
        candidate_scan = privacy.scan_candidate_bytes(
            privacy.EVIDENCE_ARTIFACT,
            loaded.raw,
        )
        privacy_ok = bool(existing_scan.get("ok") and candidate_scan.get("ok"))
        if not privacy_ok:
            errors.append("public artifact privacy scan failed")
    expected = None
    if loaded is not None:
        try:
            recorded_identity = _recorded_execution_identity(loaded.document)
            expected = support.expected_evidence(recorded_identity, repo_root)
        except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
            errors.append(f"static source or receipt validation failed: {exc}")
    if loaded is not None and expected is not None:
        evidence = loaded.document
        actual_keys = set(evidence)
        expected_keys = set(expected)
        if actual_keys != expected_keys:
            errors.append("evidence root field set mismatch")
        for key in sorted(actual_keys & expected_keys):
            if evidence[key] != expected[key]:
                errors.append(f"evidence field mismatch: {key}")
        if loaded.raw != support.canonical_evidence_bytes(expected):
            errors.append("evidence bytes are not canonical")
    return {
        "errors": errors,
        "facts": {
            "evidence_sha256": (
                support.sha256_bytes(loaded.raw) if loaded is not None else None
            ),
            "receipt_artifacts_checked": material["facts"][
                "receipt_artifacts_checked"
            ],
            "artifact_privacy_scan_passed": privacy_ok,
            "recorded_execution_identity": recorded_identity,
            "source_files_checked": material["facts"]["source_files_checked"],
            "static_evidence_valid": not errors,
        },
        "ok": not errors,
        "schema": "zenodex/zrpf_v3_replay_evidence_check/v1",
    }


def validate_materials(repo_root: Path = support.REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    source_files_checked = 0
    receipt_artifacts_checked = 0
    try:
        closure = support.anchored_source_closure(repo_root)
        receipts = support.retained_receipt_set(
            repo_root / support.RECEIPT_DIRECTORY.relative_to(support.REPO_ROOT)
        )
        source_files_checked = closure["file_count"]
        receipt_artifacts_checked = receipts["artifact_count"]
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        errors.append(f"static source or receipt validation failed: {exc}")
    if privacy.scan_artifacts(repo_root, privacy.PRE_RECORD_ARTIFACTS).get("ok") is not True:
        errors.append("public artifact privacy input scan failed")
    errors.extend(verify_source_anchor(repo_root))
    return {
        "errors": errors,
        "facts": {
            "receipt_artifacts_checked": receipt_artifacts_checked,
            "source_files_checked": source_files_checked,
        },
        "ok": not errors,
        "schema": "zenodex/zrpf_v3_replay_material_check/v1",
    }


def _recorded_execution_identity(document: dict[str, Any]) -> dict[str, Any]:
    build = document.get("recorded_build")
    execution = document.get("recorded_execution")
    if not isinstance(build, dict) or not isinstance(execution, dict):
        raise ValueError("recorded execution identity is absent")
    identity = support.exact_execution_identity(
        {
            "binary_sha256": execution.get("executing_binary_sha256"),
            "binary_size_bytes": execution.get("executing_binary_size_bytes"),
            "binary_transport": execution.get("binary_transport"),
            "dependency_graph_package_count": build.get(
                "dependency_graph_package_count"
            ),
            "dependency_graph_sha256": build.get("dependency_graph_sha256"),
        }
    )
    if any(
        (
            build.get("verifier_binary_sha256") != identity["binary_sha256"],
            build.get("verifier_binary_size_bytes") != identity["binary_size_bytes"],
        )
    ):
        raise ValueError("recorded build and execution identities differ")
    return identity


def verify_source_anchor(repo_root: Path) -> list[str]:
    errors: list[str] = []
    try:
        tagged_commit = _run(
            [
                "git",
                "rev-parse",
                "--verify",
                f"refs/tags/{support.SOURCE_TAG}^{{commit}}",
            ],
            cwd=repo_root,
            env=environment.clean_environment(),
            timeout=30,
            profile=process_runner.ProcessProfile.TOOL,
            phase="source_anchor_tag",
        )
        tree = _run(
            ["git", "show", "-s", "--format=%T", support.SOURCE_COMMIT],
            cwd=repo_root,
            env=environment.clean_environment(),
            timeout=30,
            profile=process_runner.ProcessProfile.TOOL,
            phase="source_anchor_tree",
        )
    except RuntimeError:
        return ["source anchor commit is unavailable"]
    if tagged_commit.stdout.decode("ascii", errors="replace").strip() != support.SOURCE_COMMIT:
        errors.append("source anchor tag target mismatch")
    if tree.stdout.decode("ascii", errors="replace").strip() != support.SOURCE_TREE:
        errors.append("source anchor tree mismatch")
    try:
        closure = support.anchored_source_closure(repo_root)
    except (OSError, RuntimeError, ValueError):
        errors.append("source anchor closure is unavailable")
        return errors
    if any(
        (
            closure["file_count"] != support.EXPECTED_SOURCE_CLOSURE_FILES,
            closure["total_bytes"] != support.EXPECTED_SOURCE_CLOSURE_BYTES,
            closure["sha256"] != support.EXPECTED_SOURCE_CLOSURE_SHA256,
        )
    ):
        errors.append("source anchor closure mismatch")
    return errors


def live_check(
    risc0_home: Path,
    target_directory: Path,
    evidence_path: Path = support.EVIDENCE_PATH,
) -> dict[str, Any]:
    static = validate_static(evidence_path)
    recorded_identity = static.get("facts", {}).get("recorded_execution_identity")
    return _live_check(risc0_home, target_directory, static, recorded_identity)


def live_create_check(risc0_home: Path, target_directory: Path) -> dict[str, Any]:
    return _live_check(risc0_home, target_directory, validate_materials(), None)


def _live_check(
    risc0_home: Path,
    target_directory: Path,
    static: dict[str, Any],
    recorded_identity: Any,
) -> dict[str, Any]:
    if not static["ok"]:
        return static | {"live": {"executed": False, "verified": False}}
    _require_unprivileged_execution_context()
    repo_root = support.REPO_ROOT.resolve()
    target_directory = _prepare_target_directory(target_directory, repo_root)
    with source_snapshot.SourceSnapshot(
        repo_root,
        target_directory,
        support.SOURCE_COMMIT,
        support.SOURCE_TREE,
    ) as source_root:
        context = _prepare_live_context(risc0_home, target_directory, source_root)
        graph = _selected_dependency_graph(context)
        replay = _build_and_replay(context, graph)
    return static | {"live": _live_facts(context, replay, recorded_identity)}


def _require_unprivileged_execution_context() -> None:
    if sys.platform != "linux" or os.geteuid() == 0:
        raise RuntimeError("live replay requires an unprivileged Linux execution context")
    try:
        status = Path("/proc/self/status").read_text(encoding="ascii")
    except (OSError, UnicodeDecodeError) as exc:
        raise RuntimeError("process privilege state is unavailable") from exc
    fields: dict[str, str] = {}
    for line in status.splitlines():
        if ":" not in line:
            continue
        name, value = line.split(":", 1)
        if name in {"Uid", "Gid", "CapInh", "CapPrm", "CapEff", "CapAmb"}:
            fields[name] = value.strip()
    if set(fields) != {"Uid", "Gid", "CapInh", "CapPrm", "CapEff", "CapAmb"}:
        raise RuntimeError("process privilege state is incomplete")
    try:
        uids = tuple(int(value) for value in fields["Uid"].split())
        gids = tuple(int(value) for value in fields["Gid"].split())
        capabilities = tuple(
            int(fields[name], 16)
            for name in ("CapInh", "CapPrm", "CapEff", "CapAmb")
        )
    except ValueError as exc:
        raise RuntimeError("process privilege state is malformed") from exc
    if (
        len(uids) != 4
        or len(gids) != 4
        or len(set(uids)) != 1
        or len(set(gids)) != 1
        or uids[0] == 0
        or gids[0] == 0
    ):
        raise RuntimeError("live replay requires one unprivileged UID and GID identity")
    if any(capabilities):
        raise RuntimeError("live replay requires zero inherited, permitted, effective, and ambient capabilities")


def _prepare_target_directory(target_directory: Path, repo_root: Path) -> Path:
    parent = target_directory.parent.resolve(strict=True)
    candidate = parent / target_directory.name
    if candidate == repo_root or candidate.is_relative_to(repo_root):
        raise RuntimeError("target directory must be outside the repository")
    return environment.create_private_target(candidate)


def _prepare_live_context(
    risc0_home: Path,
    target_directory: Path,
    source_root: Path,
) -> LiveContext:
    _require_snapshot_closure(source_root)
    paths, versions = toolchain.verify_toolchain(risc0_home.resolve(), source_root)
    toolchain.validate_manifest_features(source_root)
    workspace = source_root / "zk/zrpf_risc0"
    environment.validate_cargo_config_ancestors(workspace)
    env = environment.build_environment(paths, target_directory)
    return LiveContext(
        repo_root=support.REPO_ROOT.resolve(),
        workspace=workspace,
        source_root=source_root,
        target_directory=target_directory,
        cargo=str(paths["cargo"]),
        env=env,
        toolchain_versions=versions,
    )


def _selected_dependency_graph(context: LiveContext) -> tuple[str, ...]:
    graph = _run(
        [
            context.cargo,
            "tree",
            "--locked",
            "--offline",
            "--target",
            "x86_64-unknown-linux-gnu",
            "-p",
            PACKAGE,
            "--edges",
            "normal,build,no-proc-macro",
            "--prefix",
            "none",
            "--format",
            "{p}",
        ],
        cwd=context.workspace,
        env=context.env,
        timeout=120,
        profile=process_runner.ProcessProfile.BUILD,
        phase="selected_dependency_graph",
    ).stdout
    dependency_graph = _canonical_dependency_graph(graph, context.source_root)
    graph_text = "\n".join(dependency_graph)
    if any(token in graph_text for token in FORBIDDEN_GRAPH_TOKENS):
        raise RuntimeError("forbidden package is reachable in selected graph")
    return dependency_graph


def _canonical_dependency_graph(raw: bytes, source_root: Path) -> tuple[str, ...]:
    try:
        graph_text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise RuntimeError("selected dependency graph is not UTF-8") from exc
    source = str(source_root.resolve(strict=True))
    source_prefix = f" ({source}/"
    canonical_prefix = f" ({support.DEPENDENCY_GRAPH_CANONICAL_SOURCE_ROOT}/"
    lines: set[str] = set()
    for raw_line in graph_text.splitlines():
        if not raw_line:
            continue
        line = raw_line.replace(source_prefix, canonical_prefix)
        if source in line or (" (/" in line and canonical_prefix not in line):
            raise RuntimeError("selected dependency graph contains an unbound path")
        lines.add(line)
    if not lines:
        raise RuntimeError("selected dependency graph is empty")
    return tuple(sorted(lines))


def _build_and_replay(context: LiveContext, graph: tuple[str, ...]) -> LiveReplay:
    _run(
        [context.cargo, "build", "--frozen", "--release", "-p", PACKAGE],
        cwd=context.workspace,
        env=context.env,
        timeout=600,
        profile=process_runner.ProcessProfile.BUILD,
        phase="build_replay_verifier",
    )
    _require_snapshot_closure(context.source_root)
    binary = context.target_directory / "release" / BINARY
    with sealed_executable.SealedExecutable(binary) as executable:
        normal = _run(
            [executable.command_path, str(support.RECEIPT_DIRECTORY)],
            cwd=context.repo_root,
            env=context.env,
            timeout=120,
            profile=process_runner.ProcessProfile.REPLAY,
            pass_fds=executable.pass_fds,
            phase="replay_normal_environment",
        )
        dev_env = context.env.copy()
        dev_env["RISC0_DEV_MODE"] = "1"
        dev = _run(
            [executable.command_path, str(support.RECEIPT_DIRECTORY)],
            cwd=context.repo_root,
            env=dev_env,
            timeout=120,
            profile=process_runner.ProcessProfile.REPLAY,
            pass_fds=executable.pass_fds,
            phase="replay_dev_environment",
        )
        if normal.stderr or dev.stderr or normal.stdout != dev.stdout:
            raise RuntimeError("normal and dev-environment replay outputs differ")
        _, report_errors = support.validate_replay_report(normal.stdout)
        if report_errors:
            raise RuntimeError("live replay report failed exact validation")
        negatives = live_controls.run_negative_controls(
            executable.command_path,
            executable.pass_fds,
            context.env,
            context.target_directory,
        )
        identity = executable.identity
    return LiveReplay(
        identity.sha256,
        identity.size_bytes,
        identity.transport,
        graph,
        negatives,
        normal.stdout,
    )


def _require_snapshot_closure(source_root: Path) -> None:
    closure = support.source_closure(source_root)
    if any(
        (
            closure["file_count"] != support.EXPECTED_SOURCE_CLOSURE_FILES,
            closure["total_bytes"] != support.EXPECTED_SOURCE_CLOSURE_BYTES,
            closure["sha256"] != support.EXPECTED_SOURCE_CLOSURE_SHA256,
        )
    ):
        raise RuntimeError("private source snapshot closure mismatch")


def _live_facts(
    context: LiveContext,
    replay: LiveReplay,
    recorded_identity: Any,
) -> dict[str, Any]:
    graph_bytes = ("\n".join(replay.dependency_graph) + "\n").encode("utf-8")
    graph_sha256 = support.sha256_bytes(graph_bytes)
    recorded = (
        support.exact_execution_identity(recorded_identity)
        if recorded_identity is not None
        else None
    )
    graph_match = recorded is None or all(
        (
            len(replay.dependency_graph)
            == recorded["dependency_graph_package_count"],
            graph_sha256 == recorded["dependency_graph_sha256"],
        )
    )
    if not graph_match:
        raise RuntimeError("selected dependency graph identity mismatch")
    binary_match = recorded is not None and all(
        (
            replay.binary_sha256 == recorded["binary_sha256"],
            replay.binary_size_bytes == recorded["binary_size_bytes"],
            replay.binary_transport == recorded["binary_transport"],
        )
    )
    return {
        "binary_sha256": replay.binary_sha256,
        "binary_size_bytes": replay.binary_size_bytes,
        "binary_transport": replay.binary_transport,
        "dependency_graph_package_count": len(replay.dependency_graph),
        "dependency_graph_sha256": graph_sha256,
        "executed": True,
        "negative_controls": replay.negative_controls,
        "normal_and_dev_stdout_identical": True,
        "recorded_execution_identity_match": binary_match,
        "recorded_dependency_graph_identity_match": (
            graph_match if recorded is not None else None
        ),
        "recorded_evidence_parity": (
            binary_match and graph_match if recorded is not None else None
        ),
        "source_built_structural_replay_verified": True,
        "status": (
            "source_built_structural_replay_with_recorded_identity_match"
            if binary_match
            else "source_built_structural_replay_with_fresh_measured_identity"
        ),
        "stdout_sha256": support.sha256_bytes(replay.stdout),
        "stdout_size_bytes": len(replay.stdout),
        "toolchain_versions": context.toolchain_versions,
        "verified": True,
    }


def _run(
    command: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout: int,
    profile: Any,
    phase: str,
    pass_fds: tuple[int, ...] = (),
) -> subprocess.CompletedProcess[bytes]:
    process = process_runner.run_bounded(
        process_runner.ProcessRequest(
            command=tuple(command),
            cwd=cwd,
            env=env,
            timeout_seconds=timeout,
            output_limit_bytes=MAX_PROCESS_OUTPUT,
            profile=profile,
            pass_fds=pass_fds,
        )
    )
    if process.returncode != 0:
        diagnostic = process.stderr or process.stdout
        tail = diagnostic[-MAX_FAILURE_DIAGNOSTIC_BYTES:].decode(
            "utf-8", errors="backslashreplace"
        )
        raise RuntimeError(
            "subprocess failed: "
            f"phase={phase} returncode={process.returncode} diagnostic_tail={tail!r}"
        )
    return process


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=support.EVIDENCE_PATH)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--risc0-home", type=Path)
    parser.add_argument("--target-dir", type=Path)
    parser.add_argument("--write-new", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        if args.write_new:
            if not args.live:
                raise RuntimeError("--write-new requires --live")
            if args.risc0_home is None or args.target_dir is None:
                raise RuntimeError("live mode requires toolchain and target paths")
            report = live_create_check(args.risc0_home, args.target_dir)
            if not report.get("ok"):
                raise RuntimeError("live replay did not verify")
            live_facts = report["live"]
            record_writer.write_after_verified_live(args.evidence, report)
            report = validate_static(args.evidence)
            report["live"] = live_facts
            report["ok"] = bool(report.get("ok") and live_facts.get("verified"))
        elif args.live:
            if args.risc0_home is None or args.target_dir is None:
                raise RuntimeError("live mode requires toolchain and target paths")
            report = live_check(args.risc0_home, args.target_dir, args.evidence)
        else:
            report = validate_static(args.evidence)
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
        report = {
            "errors": [str(exc)],
            "ok": False,
            "schema": "zenodex/zrpf_v3_replay_evidence_check/v1",
        }
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())
