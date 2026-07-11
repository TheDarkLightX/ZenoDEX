"""Pinned toolchain and Cargo-feature checks for ZRPF V3 replay."""

from __future__ import annotations

import importlib
import tomllib
from pathlib import Path

_MODULE_PREFIX = "tools." if __package__ else ""
environment = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_environment")
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")
process_runner = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_process")

MAX_VERSION_OUTPUT = 4 * 1024 * 1024
EXPECTED_VERSIONS = {
    "cargo": "cargo 1.94.1-dev (29ea6fb6a 2026-03-24)",
    "rustc": "rustc 1.94.1-dev (06e01cb0d 2026-04-09)",
    "rustdoc": "rustdoc 1.94.1-dev (06e01cb0d 2026-04-09)",
}


def verify_toolchain(
    risc0_home: Path,
    source_root: Path = support.REPO_ROOT,
) -> tuple[dict[str, Path], dict[str, str]]:
    lock = support.strict_json_loads(
        (source_root / support.TOOLCHAIN_LOCK_PATH).read_bytes()
    )
    if not isinstance(lock, dict):
        raise RuntimeError("toolchain lock is malformed")
    rows = lock.get("installed_artifacts")
    if not isinstance(rows, list):
        raise RuntimeError("toolchain lock artifacts are malformed")
    by_id = {row.get("id"): row for row in rows if isinstance(row, dict)}
    paths: dict[str, Path] = {}
    versions: dict[str, str] = {}
    for artifact_id in ("cargo", "rustc", "rustdoc"):
        row = by_id.get(artifact_id)
        if not isinstance(row, dict):
            raise RuntimeError("required toolchain artifact is absent")
        path = _bound_artifact(risc0_home, row)
        version = _version(path)
        if version != EXPECTED_VERSIONS[artifact_id]:
            raise RuntimeError("toolchain version mismatch")
        paths[artifact_id] = path
        versions[artifact_id] = version
    return paths, versions


def validate_manifest_features(source_root: Path = support.REPO_ROOT) -> None:
    for relative in (
        "zk/zrpf_risc0/replay_verifier/Cargo.toml",
        "zk/zrpf_risc0/verifier/Cargo.toml",
    ):
        manifest = tomllib.loads((source_root / relative).read_text("utf-8"))
        dependency = manifest.get("dependencies", {}).get("risc0-zkvm")
        if not isinstance(dependency, dict):
            raise RuntimeError("RISC0 dependency declaration is malformed")
        if dependency.get("default-features") is not False:
            raise RuntimeError("RISC0 default features are enabled")
        if sorted(dependency.get("features", [])) != ["disable-dev-mode", "std"]:
            raise RuntimeError("RISC0 verifier features drifted")


def _bound_artifact(risc0_home: Path, row: dict) -> Path:
    relative = row.get("relative_path")
    if not isinstance(relative, str):
        raise RuntimeError("toolchain artifact path is malformed")
    path = risc0_home / relative
    metadata = path.lstat()
    raw = path.read_bytes()
    if (
        path.is_symlink()
        or not path.is_file()
        or len(raw) != metadata.st_size
        or len(raw) != row.get("size_bytes")
        or support.sha256_bytes(raw) != row.get("sha256")
    ):
        raise RuntimeError("toolchain artifact binding mismatch")
    return path


def _version(path: Path) -> str:
    process = process_runner.run_bounded(
        process_runner.ProcessRequest(
            command=(str(path), "--version"),
            cwd=support.REPO_ROOT,
            env=environment.clean_environment(),
            timeout_seconds=30,
            output_limit_bytes=MAX_VERSION_OUTPUT,
        )
    )
    if process.returncode != 0 or process.stderr:
        raise RuntimeError("toolchain version command failed")
    return process.stdout.decode("utf-8").strip()
