#!/usr/bin/env python3
"""Build and verify a small operator release bundle."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import re
import sys
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
DEFAULT_OUT_DIR = ROOT / "dist"
SAFE_VERSION_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")


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


def _require_safe_version(version: str) -> str:
    if not SAFE_VERSION_RE.fullmatch(version):
        raise ValueError(
            "version must be 1-128 chars and contain only letters, numbers, dot, underscore, or dash"
        )
    return version


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
    for key in ("schema", "files", "manifest_sha256"):
        if manifest.get(key) != rebuilt[key]:
            raise ValueError("manifest hash mismatch")
    allowed_extra = {"archive", "archive_sha256"}
    extra_keys = set(manifest) - set(rebuilt)
    if not extra_keys <= allowed_extra:
        raise ValueError("manifest hash mismatch")
    archive = manifest.get("archive")
    archive_sha256 = manifest.get("archive_sha256")
    if archive is not None or archive_sha256 is not None:
        if not isinstance(archive, str) or not isinstance(archive_sha256, str):
            raise ValueError("archive metadata must include archive and archive_sha256 strings")
        archive_path = Path(archive)
        if archive_path.is_file() and _sha256_file(archive_path) != archive_sha256:
            raise ValueError("archive hash mismatch")


def build_archive(root: Path, out: Path) -> dict[str, Any]:
    manifest = build_manifest(root)
    out.parent.mkdir(parents=True, exist_ok=True)
    manifest_bytes = json.dumps(manifest, indent=2, sort_keys=True).encode("utf-8")
    with tarfile.open(out, "w:gz") as archive:
        for entry in manifest["files"]:
            archive.add(root / str(entry["path"]), arcname=str(entry["path"]))
        info = tarfile.TarInfo("operator_release_manifest.json")
        info.size = len(manifest_bytes)
        archive.addfile(info, fileobj=io.BytesIO(manifest_bytes))
    archive_sha256 = _sha256_file(out)
    return {**manifest, "archive": str(out), "archive_sha256": archive_sha256}


def build_versioned_archive(*, root: Path, out_dir: Path, version: str) -> dict[str, Any]:
    safe_version = _require_safe_version(version)
    archive = out_dir / f"zenodex-operator-{safe_version}.tar.gz"
    result = build_archive(root, archive)
    manifest_path = archive.with_suffix(archive.suffix + ".manifest.json")
    manifest_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {
        "schema": "zenodex.operator_release_bundle.result.v0",
        "ok": True,
        "version": safe_version,
        "archive": str(archive),
        "archive_sha256": result["archive_sha256"],
        "manifest": str(manifest_path),
        "manifest_sha256": result["manifest_sha256"],
    }


def verify_manifest_file(path: Path, root: Path = ROOT) -> dict[str, Any]:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    verify_manifest(manifest, root)
    return {
        "schema": "zenodex.operator_release_bundle.result.v0",
        "ok": True,
        "status": "verify",
        "manifest": str(path),
        "manifest_sha256": manifest["manifest_sha256"],
    }


def _print_json(payload: dict[str, Any], *, compact: bool) -> None:
    if compact:
        print(json.dumps(payload, sort_keys=True))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command")

    build = subparsers.add_parser("build", help="build a versioned operator tarball")
    build.add_argument("--repo-root", type=Path, default=ROOT)
    build.add_argument("--version", required=True)
    build.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    build.add_argument("--json", action="store_true")

    verify = subparsers.add_parser("verify", help="verify an operator bundle manifest")
    verify.add_argument("--repo-root", type=Path, default=ROOT)
    verify.add_argument("--manifest", type=Path, required=True)
    verify.add_argument("--json", action="store_true")

    parser.add_argument("--repo-root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    parser.add_argument("--out", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--verify", type=Path, help=argparse.SUPPRESS)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    try:
        if args.command == "build":
            payload = build_versioned_archive(
                root=args.repo_root.resolve(),
                out_dir=args.out_dir,
                version=args.version,
            )
            _print_json(payload, compact=args.json)
            return 0

        if args.command == "verify":
            payload = verify_manifest_file(args.manifest, args.repo_root.resolve())
            _print_json(payload, compact=args.json)
            return 0

        # Backwards-compatible legacy flags.
        if args.verify is not None:
            payload = verify_manifest_file(args.verify, args.repo_root.resolve())
            print(json.dumps({"schema": SCHEMA, "ok": payload["ok"], "status": "verify"}, sort_keys=True))
            return 0

        if args.out is None:
            payload = build_manifest(args.repo_root.resolve())
        else:
            payload = build_archive(args.repo_root.resolve(), args.out)
        _print_json(payload, compact=False)
        return 0
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
