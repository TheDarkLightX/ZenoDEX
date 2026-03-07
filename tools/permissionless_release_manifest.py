#!/usr/bin/env python3
"""Build a deterministic release manifest for static/operator artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _iter_files(dist_dir: Path) -> list[Path]:
    return sorted(path for path in dist_dir.rglob("*") if path.is_file())


def build_manifest(
    *,
    dist_dir: Path,
    api_base: str,
    base_path: str,
    cid: str | None,
) -> dict[str, Any]:
    files = []
    for path in _iter_files(dist_dir):
        rel = path.relative_to(dist_dir).as_posix()
        files.append(
            {
                "path": rel,
                "size_bytes": int(path.stat().st_size),
                "sha256": _sha256_file(path),
            }
        )
    return {
        "schema": "zenodex/permissionless_release_manifest/v1",
        "artifact_kind": "static_frontend",
        "base_path": str(base_path),
        "api_base": str(api_base),
        "cid": (str(cid) if cid else None),
        "file_count": len(files),
        "files": files,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a deterministic release manifest for a static bundle")
    parser.add_argument("--dist-dir", required=True, help="Path to built static bundle")
    parser.add_argument("--out", required=True, help="Output JSON file")
    parser.add_argument("--api-base", default="", help="Optional API base baked into the deployment shape")
    parser.add_argument("--base-path", default="./", help="Static hosting base path used for the build")
    parser.add_argument("--cid", default="", help="Optional IPFS CID")
    args = parser.parse_args(argv)

    dist_dir = Path(args.dist_dir).resolve()
    if not dist_dir.is_dir():
        raise SystemExit(f"dist dir does not exist: {dist_dir}")

    out_path = Path(args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    manifest = build_manifest(
        dist_dir=dist_dir,
        api_base=str(args.api_base),
        base_path=str(args.base_path),
        cid=str(args.cid).strip() or None,
    )
    out_path.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(str(out_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
