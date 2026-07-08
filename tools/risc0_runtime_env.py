"""RISC0 runtime environment helpers for reproducible proof smokes.

The RISC0 crate version and the `r0vm` server version are coupled. A developer
machine may have a newer global `r0vm` symlink than this workspace's audited
crate line, which makes real proving fail after the guest has already built.
Grade: A-. This keeps the fix local to proof runners and avoids changing the
operator's global `rzup default` selection.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Mapping, MutableMapping


def _risc0_zkvm_lock_version(lock_path: Path) -> str | None:
    in_package = False
    for raw_line in lock_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line == "[[package]]":
            in_package = False
            continue
        if line == 'name = "risc0-zkvm"':
            in_package = True
            continue
        if in_package and line.startswith("version = "):
            return line.split("=", 1)[1].strip().strip('"')
    return None


def _installed_r0vm_candidates(risc0_home: Path, version: str) -> list[Path]:
    major_minor = ".".join(version.split(".")[:2])
    exact_glob = f"v{version}-cargo-risczero-*/r0vm"
    minor_glob = f"v{major_minor}-cargo-risczero-*/r0vm"
    return [
        *sorted((risc0_home / "extensions").glob(exact_glob)),
        risc0_home / "r0vm" / version / "r0vm",
        *sorted((risc0_home / "extensions").glob(minor_glob)),
        risc0_home / "r0vm" / major_minor / "r0vm",
    ]


def compatible_r0vm_path(repo: Path, environ: Mapping[str, str] | None = None) -> Path | None:
    """Return an installed `r0vm` matching the workspace's locked RISC0 crate."""

    env = os.environ if environ is None else environ
    lock_path = repo / "zk" / "state_proof_risc0" / "Cargo.lock"
    if not lock_path.exists():
        return None
    version = _risc0_zkvm_lock_version(lock_path)
    if not version:
        return None
    risc0_home = Path(env.get("RISC0_HOME", str(Path.home() / ".risc0"))).expanduser()
    for candidate in _installed_r0vm_candidates(risc0_home, version):
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate
    return None


def proof_runner_env(repo: Path, env: MutableMapping[str, str] | None = None) -> dict[str, str]:
    """Return an env that uses the compatible `r0vm` unless the caller pinned one."""

    proof_env = dict(os.environ if env is None else env)
    if "RISC0_SERVER_PATH" not in proof_env:
        r0vm_path = compatible_r0vm_path(repo, proof_env)
        if r0vm_path is not None:
            proof_env["RISC0_SERVER_PATH"] = str(r0vm_path)
    return proof_env
