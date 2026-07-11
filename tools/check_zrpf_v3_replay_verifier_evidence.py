#!/usr/bin/env python3
"""Check or replay the exact retained ZRPF V3 receipt evidence lane."""

from __future__ import annotations

import argparse
import importlib
import json
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
sealed_executable = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_v3_replay_sealed_executable"
)

PACKAGE = "zenodex-zrpf-risc0-replay-verifier"
BINARY = "zenodex-zrpf-risc0-replay-verifier"
MAX_PROCESS_OUTPUT = 16 * 1024 * 1024
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
        metadata = path.lstat()
        if path.is_symlink() or not path.is_file() or metadata.st_size > 4 * 1024 * 1024:
            return None, ["evidence file is not a bounded regular file"]
        raw = path.read_bytes()
        value = support.strict_json_loads(raw)
    except OSError:
        return None, ["evidence file read failed"]
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        return None, [f"evidence JSON rejected: {exc}"]
    if not isinstance(value, dict):
        return None, ["evidence root must be an object"]
    return LoadedEvidence(value, raw), []


def validate_static(
    path: Path = support.EVIDENCE_PATH,
    repo_root: Path = support.REPO_ROOT,
) -> dict[str, Any]:
    loaded, errors = load_evidence(path)
    material = validate_materials(repo_root)
    errors.extend(material["errors"])
    try:
        expected = support.expected_evidence(repo_root)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        expected = None
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
            "receipt_artifacts_checked": (
                expected["retained_receipt_set"]["artifact_count"]
                if expected is not None
                else 0
            ),
            "source_files_checked": (
                expected["replay_source_closure"]["file_count"]
                if expected is not None
                else 0
            ),
            "static_evidence_valid": not errors,
        },
        "ok": not errors,
        "schema": "zenodex/zrpf_v3_replay_evidence_check/v1",
    }


def validate_materials(repo_root: Path = support.REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    try:
        expected = support.expected_evidence(repo_root)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        expected = None
        errors.append(f"static source or receipt validation failed: {exc}")
    errors.extend(verify_source_anchor(repo_root))
    return {
        "errors": errors,
        "facts": {
            "receipt_artifacts_checked": (
                expected["retained_receipt_set"]["artifact_count"]
                if expected is not None
                else 0
            ),
            "source_files_checked": (
                expected["replay_source_closure"]["file_count"]
                if expected is not None
                else 0
            ),
        },
        "ok": not errors,
        "schema": "zenodex/zrpf_v3_replay_material_check/v1",
    }


def verify_source_anchor(repo_root: Path) -> list[str]:
    errors: list[str] = []
    try:
        tree = _run(
            ["git", "show", "-s", "--format=%T", support.SOURCE_COMMIT],
            cwd=repo_root,
            env=environment.clean_environment(),
            timeout=30,
            profile=process_runner.ProcessProfile.TOOL,
        )
    except RuntimeError:
        return ["source anchor commit is unavailable"]
    if tree.stdout.decode("ascii", errors="replace").strip() != support.SOURCE_TREE:
        errors.append("source anchor tree mismatch")
    for _, relative in support.SOURCE_FILES:
        try:
            anchored = _run(
                ["git", "show", f"{support.SOURCE_COMMIT}:{relative}"],
                cwd=repo_root,
                env=environment.clean_environment(),
                timeout=30,
                profile=process_runner.ProcessProfile.TOOL,
            ).stdout
            current = (repo_root / relative).read_bytes()
        except (OSError, RuntimeError):
            errors.append(f"source anchor file unavailable: {relative}")
            continue
        if anchored != current:
            errors.append(f"source differs from anchor commit: {relative}")
    return errors


def live_check(
    risc0_home: Path,
    target_directory: Path,
    evidence_path: Path = support.EVIDENCE_PATH,
) -> dict[str, Any]:
    return _live_check(risc0_home, target_directory, validate_static(evidence_path))


def live_create_check(risc0_home: Path, target_directory: Path) -> dict[str, Any]:
    return _live_check(risc0_home, target_directory, validate_materials())


def _live_check(
    risc0_home: Path,
    target_directory: Path,
    static: dict[str, Any],
) -> dict[str, Any]:
    if not static["ok"]:
        return static | {"live": {"executed": False, "verified": False}}
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
    return static | {"live": _live_facts(context, replay)}


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
    ).stdout
    graph_text = graph.decode("utf-8")
    if any(token in graph_text for token in FORBIDDEN_GRAPH_TOKENS):
        raise RuntimeError("forbidden package is reachable in selected graph")
    return tuple(sorted({line for line in graph_text.splitlines() if line}))


def _build_and_replay(context: LiveContext, graph: tuple[str, ...]) -> LiveReplay:
    _run(
        [context.cargo, "build", "--frozen", "--release", "-p", PACKAGE],
        cwd=context.workspace,
        env=context.env,
        timeout=600,
        profile=process_runner.ProcessProfile.BUILD,
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


def _live_facts(context: LiveContext, replay: LiveReplay) -> dict[str, Any]:
    graph_bytes = ("\n".join(replay.dependency_graph) + "\n").encode("utf-8")
    return {
        "binary_sha256": replay.binary_sha256,
        "binary_size_bytes": replay.binary_size_bytes,
        "binary_transport": replay.binary_transport,
        "dependency_graph_package_count": len(replay.dependency_graph),
        "dependency_graph_sha256": support.sha256_bytes(graph_bytes),
        "executed": True,
        "negative_controls": replay.negative_controls,
        "normal_and_dev_stdout_identical": True,
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
        raise RuntimeError("subprocess exit code mismatch")
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
    except (OSError, RuntimeError, ValueError) as exc:
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
