#!/usr/bin/env python3
"""Index compressed B09 parity artifacts and their uncompressed identities."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path


def _digest_stream(handle) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    for block in iter(lambda: handle.read(1024 * 1024), b""):
        digest.update(block)
        size += len(block)
    return digest.hexdigest(), size


def _entry(path: Path) -> dict[str, object]:
    if path.suffix == ".gz":
        with gzip.open(path, "rb") as handle:
            digest, size = _digest_stream(handle)
        return {
            "compressed_path": path.name,
            "compressed_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "compressed_size": path.stat().st_size,
            "uncompressed_path": path.stem,
            "uncompressed_sha256": digest,
            "uncompressed_size": size,
        }
    digest, size = _digest_stream(path.open("rb"))
    return {
        "path": path.name,
        "sha256": digest,
        "size": size,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("artifact_dir", type=Path)
    args = parser.parse_args()
    entries = [
        _entry(path)
        for path in sorted(args.artifact_dir.iterdir())
        if path.is_file() and path.name != "TASK_B09_ARTIFACT_INDEX.json"
    ]
    output = {
        "schema_version": "zenodex.fcis.m6.b09-artifact-index.v1",
        "entries": entries,
    }
    (args.artifact_dir / "TASK_B09_ARTIFACT_INDEX.json").write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
