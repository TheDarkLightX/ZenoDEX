#!/usr/bin/env python3
"""Build the exact, source-bound O-004 operator-surface registry."""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.operator_surface_registry_v1 import (  # noqa: E402
    ARTIFACT_RELATIVE_PATH_V1,
    OperatorSurfaceRegistryRejectV1,
    _sha256_v1,
    build_registry_bytes_v1,
    read_artifact_file_v1,
)


def _target_v1(root: Path) -> Path:
    return root.resolve(strict=True) / ARTIFACT_RELATIVE_PATH_V1


def _write_exact_bytes_v1(path: Path, data: bytes) -> None:
    """Atomically replace only the reserved regular artifact."""

    if path.is_symlink():
        raise OperatorSurfaceRegistryRejectV1(
            "ARTIFACT_SYMLINK", str(path), "refusing to replace a symlinked registry"
        )
    descriptor = -1
    temporary = ""
    try:
        descriptor, temporary = tempfile.mkstemp(
            prefix=f".{path.name}.",
            dir=path.parent,
        )
        os.fchmod(descriptor, 0o644)
    except OSError as exc:
        raise OperatorSurfaceRegistryRejectV1("ARTIFACT_OPEN", str(path), type(exc).__name__) from exc
    try:
        offset = 0
        while offset < len(data):
            written = os.write(descriptor, data[offset:])
            if written <= 0:
                raise OperatorSurfaceRegistryRejectV1(
                    "ARTIFACT_WRITE", str(path), "short write while replacing registry"
                )
            offset += written
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = -1
        os.replace(temporary, path)
        temporary = ""
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        if temporary:
            try:
                os.unlink(temporary)
            except OSError:
                pass


def build_operator_surface_registry_v1(root: Path = REPO_ROOT) -> bytes:
    """Build the canonical bytes without modifying the worktree."""

    return build_registry_bytes_v1(root)


def write_operator_surface_registry_v1(root: Path = REPO_ROOT) -> dict[str, object]:
    """Regenerate the sole reserved O-004 artifact after exact source capture."""

    data = build_operator_surface_registry_v1(root)
    target = _target_v1(root)
    _write_exact_bytes_v1(target, data)
    return {
        "artifact_path": str(ARTIFACT_RELATIVE_PATH_V1),
        "artifact_sha256": _sha256_v1(data),
        "ok": True,
    }


def check_operator_surface_registry_bytes_v1(root: Path = REPO_ROOT) -> dict[str, object]:
    """Confirm the checked-in artifact is exactly the builder projection."""

    expected = build_operator_surface_registry_v1(root)
    target = _target_v1(root)
    observed = read_artifact_file_v1(target)
    if observed != expected:
        return {
            "artifact_path": str(ARTIFACT_RELATIVE_PATH_V1),
            "artifact_sha256": _sha256_v1(observed),
            "finding": "REGISTRY_ARTIFACT_DRIFT",
            "ok": False,
        }
    return {
        "artifact_path": str(ARTIFACT_RELATIVE_PATH_V1),
        "artifact_sha256": _sha256_v1(expected),
        "ok": True,
    }


def _failure(code: str) -> dict[str, object]:
    return {
        "artifact_path": str(ARTIFACT_RELATIVE_PATH_V1),
        "artifact_sha256": "",
        "finding": code,
        "ok": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--check", action="store_true", help="verify bytes without writing")
    parser.add_argument("--json", action="store_true", help="accepted for uniform checker invocation")
    args = parser.parse_args(argv)
    try:
        report = (
            check_operator_surface_registry_bytes_v1(args.root)
            if args.check
            else write_operator_surface_registry_v1(args.root)
        )
    except OperatorSurfaceRegistryRejectV1 as exc:
        report = _failure(exc.code)
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        report = _failure(type(exc).__name__)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
