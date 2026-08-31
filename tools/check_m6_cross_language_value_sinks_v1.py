#!/usr/bin/env python3
"""Check or render the bounded O-007B cross-language sink inventory."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.m6_cross_language_sinks.report import (  # noqa: E402
    MANIFEST_NAME,
    build_cross_language_report,
    render_manifest,
)


def _validate_existing_manifest(destination: Path) -> None:
    if not destination.exists():
        return
    try:
        value = json.loads(destination.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"existing cross-language manifest is invalid: {exc}") from exc
    if not isinstance(value, dict) or value.get("schema") != (
        "zenodex/m6-cross-language-value-sinks/v1"
    ):
        raise ValueError("existing cross-language manifest has the wrong schema")


def _atomic_write_manifest(root: Path) -> None:
    destination = root / "tools" / MANIFEST_NAME
    _validate_existing_manifest(destination)
    candidate = destination.with_name(f".{destination.name}.candidate")
    payload = (json.dumps(render_manifest(root), indent=2, sort_keys=True) + "\n").encode("utf-8")
    descriptor = -1
    candidate_created = False
    try:
        descriptor = os.open(
            candidate,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0),
            0o600,
        )
        candidate_created = True
        with os.fdopen(descriptor, "wb") as output:
            descriptor = -1
            output.write(payload)
            output.flush()
            os.fchmod(output.fileno(), 0o644)
            os.fsync(output.fileno())
        os.replace(candidate, destination)
        candidate_created = False
        directory = os.open(
            destination.parent,
            os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        if candidate_created:
            try:
                candidate.unlink()
            except FileNotFoundError:
                pass


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--emit-manifest", action="store_true")
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--require-release-ready", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    if args.emit_manifest and args.write_manifest:
        parser.error("choose only one manifest output mode")
    if args.emit_manifest:
        print(json.dumps(render_manifest(root), indent=2, sort_keys=True))
        return 0
    if args.write_manifest:
        _atomic_write_manifest(root)
        print(root / "tools" / MANIFEST_NAME)
        return 0
    report = build_cross_language_report(root)
    print(json.dumps(report, indent=2, sort_keys=True))
    if not report["ok"]:
        return 1
    return 0 if not args.require_release_ready or report["release_ready"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
