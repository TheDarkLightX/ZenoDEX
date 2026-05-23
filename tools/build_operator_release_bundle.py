#!/usr/bin/env python3
"""Build a deterministic ZenoDEX operator release bundle."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import sys
import tarfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "zenodex.operator_release_bundle.v0"

INCLUDE_PATHS = (
    "bin",
    "scripts",
    "src",
    "tools",
    "config",
    "formal",
    ".docker",
    ".dockerignore",
    "Dockerfile",
    "Dockerfile.hashlocked",
    "Dockerfile.operator-tools",
    "Dockerfile.production-hashlocked",
    "docker-compose.yml",
    "docker-compose.local.yml",
    "docker-compose.local-testnet.yml",
    "docker-compose.two-node.yml",
    "docker-compose.multimachine.yml",
    "docker-compose.permissionless.yml",
    "docker-compose.testnet-demo.yml",
    "generated/batch_auction_settler_v1/python_ref/batch_auction_settler_v1_ref.py",
    "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py",
    "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
    "generated/perp_python/perp_epoch_isolated_v2_ref.py",
    "generated/perp_python/perp_epoch_isolated_v3_ref.py",
    "packages/zeno-proof-client",
    "requirements-core.lock.txt",
    "requirements-dev.lock.txt",
    "requirements-agents.lock.txt",
    "pyproject.toml",
    "pytest.ini",
    "README.md",
    "docs/DEPLOYMENT_QUICKSTART.md",
    "docs/DOCKER_HASHLOCKED_DEPLOYMENT.md",
    "docs/LOCAL_TESTNET_QUICKSTART.md",
    "docs/PERMISSIONLESS_HOSTING.md",
    "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json",
    "docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md",
    "docs/ZENO_SDK_BROWSER_WALLET_SYNC.md",
    "docs/assurance",
    "docs/claims_registry.yaml",
    "docs/tau_supported_runtime_contract.json",
)

EXCLUDED_PARTS = {
    ".git",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".tau_history",
    "__pycache__",
    "build",
    "dist",
    "external",
    "internal",
    "mutants",
    "node_modules",
    "runs",
    "target",
    "_secbin",
    ".venv",
    "venv",
}

EXCLUDED_SUFFIXES = (
    ".pyc",
    ".pyo",
    ".log",
    ".tmp",
    ".tau_history",
)


@dataclass(frozen=True)
class BundleFile:
    relative_path: str
    size_bytes: int
    sha256: str


def build_operator_release_bundle(
    *,
    root: Path = ROOT,
    out_dir: Path,
    version: str,
) -> dict[str, Any]:
    root = root.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    files = _collect_bundle_files(root)
    if not files:
        raise ValueError("operator release bundle would be empty")

    archive_name = f"zenodex-operator-{_safe_version(version)}.tar.gz"
    archive_path = out_dir / archive_name
    _write_tar_gz(root=root, files=files, archive_path=archive_path, prefix=f"zenodex-operator-{version}")
    archive_sha256 = _sha256_file(archive_path)

    manifest_body = {
        "schema": SCHEMA,
        "version": version,
        "archive_name": archive_name,
        "archive_sha256": archive_sha256,
        "file_count": len(files),
        "total_size_bytes": sum(item.size_bytes for item in files),
        "files": [
            {
                "path": item.relative_path,
                "size_bytes": item.size_bytes,
                "sha256": item.sha256,
            }
            for item in files
        ],
    }
    manifest_path = out_dir / f"{archive_name}.manifest.json"
    manifest_path.write_text(json.dumps(manifest_body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    manifest_sha256 = _sha256_file(manifest_path)
    return {
        "schema": "zenodex.operator_release_bundle.build_report.v0",
        "ok": True,
        "version": version,
        "archive": str(archive_path),
        "archive_path": str(archive_path),
        "manifest": str(manifest_path),
        "manifest_path": str(manifest_path),
        "archive_sha256": archive_sha256,
        "manifest_sha256": manifest_sha256,
        "file_count": len(files),
        "total_size_bytes": manifest_body["total_size_bytes"],
    }


def verify_operator_release_manifest(*, manifest_path: Path, archive_path: Path | None = None) -> dict[str, Any]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    errors: list[str] = []
    if not isinstance(manifest, dict):
        return _verify_report(["manifest must be a JSON object"])
    if manifest.get("schema") != SCHEMA:
        errors.append("manifest schema mismatch")
    files = manifest.get("files")
    if not isinstance(files, list) or not files:
        errors.append("manifest files must be a non-empty list")
    if not isinstance(manifest.get("file_count"), int) or manifest.get("file_count") != len(files or []):
        errors.append("manifest file_count mismatch")

    archive = archive_path or manifest_path.parent / str(manifest.get("archive_name", ""))
    if not archive.is_file():
        errors.append(f"archive missing: {archive}")
    else:
        actual_sha = _sha256_file(archive)
        if actual_sha != manifest.get("archive_sha256"):
            errors.append("archive_sha256 mismatch")

    seen: set[str] = set()
    for index, item in enumerate(files if isinstance(files, list) else []):
        if not isinstance(item, dict):
            errors.append(f"files[{index}] must be an object")
            continue
        relpath = item.get("path")
        if not isinstance(relpath, str) or not relpath:
            errors.append(f"files[{index}].path must be non-empty")
            continue
        if relpath in seen:
            errors.append(f"duplicate file path: {relpath}")
        seen.add(relpath)
        if not _is_safe_relative_path(relpath):
            errors.append(f"unsafe file path: {relpath}")
        if not isinstance(item.get("size_bytes"), int) or item.get("size_bytes") < 0:
            errors.append(f"invalid file size: {relpath}")
        if not _looks_sha256(item.get("sha256")):
            errors.append(f"invalid file sha256: {relpath}")

    if archive.is_file() and not errors:
        errors.extend(_verify_archive_members(archive=archive, manifest=manifest))

    return _verify_report(errors)


def _verify_report(errors: list[str]) -> dict[str, Any]:
    return {
        "schema": "zenodex.operator_release_bundle.verify_report.v0",
        "ok": not errors,
        "status": "verify",
        "errors": errors,
    }


def _collect_bundle_files(root: Path) -> list[BundleFile]:
    relpaths: set[str] = set()
    for include in INCLUDE_PATHS:
        path = root / include
        if path.is_file():
            relpaths.add(include)
        elif path.is_dir():
            for child in sorted(path.rglob("*")):
                if child.is_file():
                    rel = child.relative_to(root).as_posix()
                    if _include_file(rel):
                        relpaths.add(rel)

    files: list[BundleFile] = []
    for rel in sorted(relpaths):
        path = root / rel
        files.append(BundleFile(relative_path=rel, size_bytes=path.stat().st_size, sha256=_sha256_file(path)))
    return files


def _include_file(relpath: str) -> bool:
    path = Path(relpath)
    if not _is_safe_relative_path(relpath):
        return False
    if any(part in EXCLUDED_PARTS for part in path.parts):
        return False
    if relpath.endswith(EXCLUDED_SUFFIXES):
        return False
    return True


def _is_safe_relative_path(relpath: str) -> bool:
    path = Path(relpath)
    return relpath != "" and not path.is_absolute() and ".." not in path.parts


def _write_tar_gz(*, root: Path, files: Iterable[BundleFile], archive_path: Path, prefix: str) -> None:
    with archive_path.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT) as tar:
                for item in files:
                    path = root / item.relative_path
                    arcname = f"{prefix}/{item.relative_path}"
                    info = tar.gettarinfo(str(path), arcname=arcname)
                    info.uid = 0
                    info.gid = 0
                    info.uname = ""
                    info.gname = ""
                    info.mtime = 0
                    with path.open("rb") as fh:
                        tar.addfile(info, fh)


def _verify_archive_members(*, archive: Path, manifest: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    expected = {str(item["path"]): item for item in manifest["files"]}
    prefix = f"zenodex-operator-{manifest.get('version')}/"
    with tarfile.open(archive, "r:gz") as tar:
        members = [member for member in tar.getmembers() if member.isfile()]
        observed: set[str] = set()
        for member in members:
            if not member.name.startswith(prefix):
                errors.append(f"archive member outside bundle prefix: {member.name}")
                continue
            relpath = member.name[len(prefix) :]
            observed.add(relpath)
            expected_item = expected.get(relpath)
            if expected_item is None:
                errors.append(f"archive contains unexpected file: {relpath}")
                continue
            extracted = tar.extractfile(member)
            if extracted is None:
                errors.append(f"archive member could not be read: {relpath}")
                continue
            payload = extracted.read()
            if len(payload) != expected_item["size_bytes"]:
                errors.append(f"archive member size mismatch: {relpath}")
            if hashlib.sha256(payload).hexdigest() != expected_item["sha256"]:
                errors.append(f"archive member sha256 mismatch: {relpath}")
        missing = sorted(set(expected) - observed)
        for relpath in missing:
            errors.append(f"archive missing manifest file: {relpath}")
    return errors


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _looks_sha256(value: object) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(char in "0123456789abcdef" for char in value)


def _safe_version(version: str) -> str:
    if not version or any(char not in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-" for char in version):
        raise ValueError("version must contain only ASCII letters, digits, dot, underscore, or dash")
    return version


def _print_json(report: dict[str, Any], *, compact: bool) -> None:
    if compact:
        print(json.dumps(report, sort_keys=True))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    build = sub.add_parser("build", help="build an operator release bundle")
    build.add_argument("--repo-root", type=Path, default=ROOT)
    build.add_argument("--out-dir", type=Path, required=True)
    build.add_argument("--version", default="dev")
    build.add_argument("--json", action="store_true")

    verify = sub.add_parser("verify", help="verify an operator release bundle manifest")
    verify.add_argument("--repo-root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    verify.add_argument("--manifest", type=Path, required=True)
    verify.add_argument("--archive", type=Path)
    verify.add_argument("--json", action="store_true")

    args = parser.parse_args(argv)
    try:
        if args.command == "build":
            report = build_operator_release_bundle(
                root=args.repo_root,
                out_dir=args.out_dir,
                version=args.version,
            )
            _print_json(report, compact=bool(args.json))
            return 0
        if args.command == "verify":
            report = verify_operator_release_manifest(manifest_path=args.manifest, archive_path=args.archive)
            _print_json(report, compact=bool(args.json))
            return 0 if report["ok"] else 1
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 2
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
