#!/usr/bin/env python3
"""Build or replay-check the O-008A dependency-resolution admission artifact."""

from __future__ import annotations

import argparse
import os
import stat
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.o008a_dependency_resolution_admission_v2 import (  # noqa: E402
    ARTIFACT_PATH,
    AdmissionReject,
    artifact_bytes,
)


def _existing_regular_bytes(path: Path) -> bytes:
    try:
        metadata = path.lstat()
    except OSError as exc:
        raise AdmissionReject("OUTPUT_READ", str(path), type(exc).__name__) from exc
    if not stat.S_ISREG(metadata.st_mode):
        raise AdmissionReject("OUTPUT_TYPE", str(path), "regular file required")
    return path.read_bytes()


def _write_regular(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and not stat.S_ISREG(path.lstat().st_mode):
        raise AdmissionReject("OUTPUT_TYPE", str(path), "regular file required")
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags, 0o644)
    try:
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise AdmissionReject("OUTPUT_WRITE", str(path), "short write")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--stage-a-commit", required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--stdout", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.stdout and (args.output is not None or args.check):
        parser.error("--stdout cannot be combined with --output or --check")
    root = args.root.resolve(strict=True)
    expected = artifact_bytes(root, args.stage_a_commit)
    if args.stdout:
        sys.stdout.buffer.write(expected)
        return 0
    output = args.output or (root / ARTIFACT_PATH)
    if not output.is_absolute():
        output = root / output
    if args.check:
        if _existing_regular_bytes(output) != expected:
            raise AdmissionReject(
                "ARTIFACT_REPLAY_DRIFT",
                str(output),
                "artifact differs from deterministic Stage A projection",
            )
        return 0
    _write_regular(output, expected)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
