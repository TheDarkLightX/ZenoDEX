"""Fail-closed checker for the P4B5A dynamic-apportionment prompt packet."""

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

PACKET_DIR = Path(__file__).resolve().parent
REPOSITORY_ROOT = PACKET_DIR.parents[3]
MANIFEST_PATH = PACKET_DIR / "CONTEXT_MANIFEST.json"


def _git_bytes(baseline_head: str, path: str) -> bytes:
    return subprocess.check_output(
        ["git", "show", f"{baseline_head}:{path}"],
        cwd=REPOSITORY_ROOT,
    )


def _entry_bytes(*, baseline_head: str, path: str) -> bytes:
    filesystem_path = REPOSITORY_ROOT / path
    if filesystem_path.is_file():
        return filesystem_path.read_bytes()
    return _git_bytes(baseline_head, path)


def main() -> None:
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    if manifest.get("schema") != "zenodex/fcis/p4b5a-context-manifest/v1":
        raise SystemExit("invalid manifest schema")

    baseline_head = manifest.get("baseline_head")
    if type(baseline_head) is not str or len(baseline_head) != 40:
        raise SystemExit("invalid baseline_head")

    entries = manifest.get("entries")
    if type(entries) is not list or not entries:
        raise SystemExit("manifest entries must be a nonempty list")

    seen: set[str] = set()
    for entry in entries:
        if type(entry) is not dict:
            raise SystemExit("manifest entry must be an object")
        path = entry.get("path")
        expected_size = entry.get("size_bytes")
        expected_sha = entry.get("sha256")
        if type(path) is not str or path in seen:
            raise SystemExit(f"invalid or duplicate path: {path!r}")
        if type(expected_size) is not int or expected_size < 0:
            raise SystemExit(f"invalid size for {path}")
        if type(expected_sha) is not str or len(expected_sha) != 64:
            raise SystemExit(f"invalid sha256 for {path}")
        seen.add(path)

        content = _entry_bytes(baseline_head=baseline_head, path=path)
        actual_sha = hashlib.sha256(content).hexdigest()
        if len(content) != expected_size:
            raise SystemExit(
                f"size mismatch for {path}: expected {expected_size}, got {len(content)}"
            )
        if actual_sha != expected_sha:
            raise SystemExit(
                f"sha256 mismatch for {path}: expected {expected_sha}, got {actual_sha}"
            )

    print(
        json.dumps(
            {
                "ok": True,
                "baseline_head": baseline_head,
                "entry_count": len(entries),
            },
            sort_keys=True,
            separators=(",", ":"),
        )
    )


if __name__ == "__main__":
    main()
