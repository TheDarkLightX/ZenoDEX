"""Toolchain-lock commitments for proof metadata.

The lock binds the local proof and replay environment into a single root that
can be carried by ZenoLedger proof metadata. It records file hashes only; it
does not claim that every external binary was executed from these files.
"""

from __future__ import annotations

import hashlib
import tomllib
from pathlib import Path
from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import hash_v0

PROOF_TOOLCHAIN_LOCK_SCHEMA_V0 = "zenodex/proof_toolchain_lock/v0"

TOOLCHAIN_LOCK_STATIC_PATHS_V0: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "python",
        (
            "requirements-core.lock.txt",
            "requirements-agents.lock.txt",
            "requirements-dev.lock.txt",
        ),
    ),
    (
        "docker",
        (
            "Dockerfile",
            "docker-compose.yml",
        ),
    ),
    (
        "lean",
        (
            "lean-mathlib/lean-toolchain",
            "lean-mathlib/lakefile.lean",
            "lean-mathlib/Proofs.lean",
        ),
    ),
    (
        "rust-risc0",
        (),
    ),
    (
        "rust-tee",
        (
            "tools/confidential_attestation_verifier_rust/Cargo.lock",
            "tools/confidential_attestation_verifier_rust/Cargo.toml",
        ),
    ),
)


def toolchain_lock_paths_v0(root: Path) -> tuple[tuple[str, tuple[str, ...]], ...]:
    """Return proof-toolchain lock inputs present in a clean checkout."""

    root = root.resolve()
    lean_dynamic_paths = tuple(
        sorted(
            _relative_posix(path, root)
            for base in (root / "lean-mathlib/Proofs", root / "lean-mathlib/proof_receipts")
            for path in base.rglob("*")
            if path.is_file()
        )
    )
    risc0_dynamic_paths = _risc0_toolchain_paths_v0(root)
    return tuple(
        (
            group,
            paths + lean_dynamic_paths
            if group == "lean"
            else paths + risc0_dynamic_paths
            if group == "rust-risc0"
            else paths,
        )
        for group, paths in TOOLCHAIN_LOCK_STATIC_PATHS_V0
    )


def _risc0_toolchain_paths_v0(root: Path) -> tuple[str, ...]:
    """Discover every source manifest and lock in a RISC0 workspace."""

    zk_root = root / "zk"
    manifests = tuple(
        path
        for path in sorted(zk_root.rglob("Cargo.toml"))
        if path.is_file() and "target" not in path.relative_to(zk_root).parts
    )
    documents = {path: _load_cargo_toml(path, root) for path in manifests}
    workspace_roots = {
        _workspace_root(path, documents, zk_root)
        for path, document in documents.items()
        if _has_risc0_core_dependency(document)
    }
    paths: set[Path] = set()
    for workspace_root in workspace_roots:
        paths.update(
            path
            for path in workspace_root.rglob("Cargo.toml")
            if path.is_file() and "target" not in path.relative_to(workspace_root).parts
        )
        paths.add(workspace_root / "Cargo.lock")
    return tuple(_relative_posix(path, root) for path in sorted(paths))


def _load_cargo_toml(path: Path, root: Path) -> Mapping[str, Any]:
    try:
        value = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        rel_path = _relative_posix(path, root)
        raise ValueError(f"invalid Cargo manifest {rel_path}: {exc}") from exc
    return value


def _workspace_root(
    manifest_path: Path,
    documents: Mapping[Path, Mapping[str, Any]],
    zk_root: Path,
) -> Path:
    current = manifest_path.parent
    while current == zk_root or zk_root in current.parents:
        candidate = current / "Cargo.toml"
        document = documents.get(candidate)
        if document is not None and isinstance(document.get("workspace"), Mapping):
            return current
        if current == zk_root:
            break
        current = current.parent
    return manifest_path.parent


def _has_risc0_core_dependency(document: Mapping[str, Any]) -> bool:
    for table in _dependency_tables(document):
        for dependency_name, raw_spec in table.items():
            package_name = dependency_name
            if isinstance(raw_spec, Mapping) and isinstance(raw_spec.get("package"), str):
                package_name = raw_spec["package"]
            if package_name in {"risc0-build", "risc0-zkvm"}:
                return True
    return False


def _dependency_tables(document: Mapping[str, Any]) -> tuple[Mapping[str, Any], ...]:
    tables: list[Mapping[str, Any]] = []
    for section in ("dependencies", "dev-dependencies", "build-dependencies"):
        table = document.get(section)
        if isinstance(table, Mapping):
            tables.append(table)
    workspace = document.get("workspace")
    if isinstance(workspace, Mapping):
        table = workspace.get("dependencies")
        if isinstance(table, Mapping):
            tables.append(table)
    target = document.get("target")
    if isinstance(target, Mapping):
        for target_table in target.values():
            if not isinstance(target_table, Mapping):
                continue
            for section in ("dependencies", "dev-dependencies", "build-dependencies"):
                table = target_table.get(section)
                if isinstance(table, Mapping):
                    tables.append(table)
    return tuple(tables)


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def build_proof_toolchain_lock_manifest_v0(root: Path) -> dict[str, Any]:
    """Build a deterministic manifest for proof-relevant toolchain locks."""

    root = root.resolve()
    files: list[dict[str, Any]] = []
    for group, rel_paths in toolchain_lock_paths_v0(root):
        for rel_path in rel_paths:
            path = root / rel_path
            if not path.is_file():
                raise FileNotFoundError(f"missing proof toolchain lock input: {rel_path}")
            if path.is_symlink():
                raise ValueError(f"proof toolchain lock input must not be a symlink: {rel_path}")
            files.append(
                {
                    "group": group,
                    "path": rel_path,
                    "size_bytes": path.stat().st_size,
                    "sha256": _file_sha256(path),
                }
            )
    return {
        "schema": PROOF_TOOLCHAIN_LOCK_SCHEMA_V0,
        "version": 0,
        "files": files,
    }


def _relative_posix(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def proof_toolchain_lock_hash_v0(root: Path) -> str:
    """Hash the proof toolchain-lock manifest with ZenoLedger domain separation."""

    return hash_v0("proof_toolchain_lock_v0", build_proof_toolchain_lock_manifest_v0(root))
