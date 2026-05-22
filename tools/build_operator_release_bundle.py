#!/usr/bin/env python3
"""Build and verify a small operator release bundle manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import tarfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "zenodex.operator_release_bundle.v0"
DEFAULT_INCLUDE = (
    "bin/zenoctl",
    "tools/zenoctl.py",
    "tools/zeno_ledger_node.py",
    "Dockerfile.hashlocked",
    "Dockerfile.operator-tools",
    "docker-compose.two-node.yml",
    "docker-compose.multimachine.yml",
    "scripts/install_zenodex.sh",
    "scripts/install_zenodex.ps1",
    "docs/DEPLOYMENT_QUICKSTART.md",
)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _file_entry(root: Path, relpath: str) -> dict[str, Any]:
    path = root / relpath
    if not path.is_file():
        raise FileNotFoundError(relpath)
    return {
        "path": relpath,
        "size": path.stat().st_size,
        "sha256": _sha256_file(path),
    }


def build_manifest(root: Path = ROOT, include: tuple[str, ...] = DEFAULT_INCLUDE) -> dict[str, Any]:
    files = [_file_entry(root, relpath) for relpath in include]
    body = {
        "schema": SCHEMA,
        "files": files,
    }
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {**body, "manifest_sha256": "sha256:" + hashlib.sha256(encoded).hexdigest()}


def verify_manifest(manifest: dict[str, Any], root: Path = ROOT) -> None:
    if manifest.get("schema") != SCHEMA:
        raise ValueError("manifest schema mismatch")
    for entry in manifest.get("files", []):
        relpath = str(entry["path"])
        expected = _file_entry(root, relpath)
        if entry != expected:
            raise ValueError(f"manifest file binding mismatch: {relpath}")
    rebuilt = build_manifest(root, tuple(str(entry["path"]) for entry in manifest["files"]))
    if manifest != rebuilt:
        raise ValueError("manifest hash mismatch")


def build_archive(root: Path, out: Path) -> dict[str, Any]:
    manifest = build_manifest(root)
    out.parent.mkdir(parents=True, exist_ok=True)
    manifest_bytes = json.dumps(manifest, indent=2, sort_keys=True).encode("utf-8")
    with tarfile.open(out, "w:gz") as archive:
        for entry in manifest["files"]:
            archive.add(root / str(entry["path"]), arcname=str(entry["path"]))
        info = tarfile.TarInfo("operator_release_manifest.json")
        info.size = len(manifest_bytes)
        archive.addfile(info, fileobj=__import__("io").BytesIO(manifest_bytes))
    archive_sha256 = _sha256_file(out)
    return {**manifest, "archive": str(out), "archive_sha256": archive_sha256}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()

    if args.verify is not None:
        manifest = json.loads(args.verify.read_text(encoding="utf-8"))
        verify_manifest(manifest, args.repo_root)
        print(json.dumps({"schema": SCHEMA, "ok": True, "status": "verify"}, sort_keys=True))
        return 0

    if args.out is None:
        manifest = build_manifest(args.repo_root)
    else:
        manifest = build_archive(args.repo_root, args.out)
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
