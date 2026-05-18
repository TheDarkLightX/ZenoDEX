"""Toolchain-lock commitments for proof metadata.

The lock binds the local proof and replay environment into a single root that
can be carried by ZenoLedger proof metadata. It records file hashes only; it
does not claim that every external binary was executed from these files.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Any

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
        (
            "zk/state_proof_risc0/Cargo.lock",
            "zk/state_proof_risc0/Cargo.toml",
            "zk/state_proof_risc0/cli/Cargo.toml",
            "zk/state_proof_risc0/methods/Cargo.toml",
            "zk/state_proof_risc0/methods/guest/Cargo.toml",
            "zk/state_proof_risc0/shared/Cargo.toml",
        ),
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
    return tuple(
        (group, paths + lean_dynamic_paths if group == "lean" else paths)
        for group, paths in TOOLCHAIN_LOCK_STATIC_PATHS_V0
    )


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
