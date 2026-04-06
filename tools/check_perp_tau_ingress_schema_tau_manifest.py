#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "perp_tau_ingress_schema_tau_manifest.json"


class ManifestError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def _as_dict(obj: Any, *, ctx: str) -> Mapping[str, Any]:
    _require(isinstance(obj, dict), f"{ctx}: expected object")
    return obj


def _load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise ManifestError(f"failed to read JSON {path}: {exc}") from exc


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_tree(paths: Iterable[Path], *, root: Path) -> str:
    h = hashlib.sha256()
    files: list[Path] = []
    ignored_parts = {".git", "__pycache__", ".mypy_cache", ".pytest_cache"}
    ignored_suffixes = {".pyc", ".pyo", ".o", ".a", ".so"}

    for base in paths:
        if base.is_file():
            files.append(base)
            continue
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*")):
            if not path.is_file():
                continue
            if any(part in ignored_parts for part in path.parts):
                continue
            if path.suffix in ignored_suffixes:
                continue
            files.append(path)

    for path in files:
        rel = path.relative_to(root).as_posix().encode("utf-8")
        h.update(rel)
        h.update(b"\0")
        h.update(_sha256_file(path).encode("ascii"))
        h.update(b"\0")
    return h.hexdigest()


def _git_stdout(*args: str) -> str:
    tau_root = REPO_ROOT / "external" / "tau-lang"
    try:
        proc = subprocess.run(
            ["git", "-C", str(tau_root), *args],
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as exc:
        raise ManifestError("git is required for Tau manifest checks") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "").strip() or str(exc)
        raise ManifestError(f"failed to inspect tau-lang checkout: {detail}") from exc
    return proc.stdout.strip()


def _find_tau_bin() -> str:
    candidates = [
        REPO_ROOT / "external" / "tau-lang" / "build-Release" / "tau",
        REPO_ROOT / "external" / "tau-lang" / "build" / "tau",
    ]
    for path in candidates:
        if path.is_file() and path.stat().st_mode & 0o111:
            return str(path)
    path_env = subprocess.run(["bash", "-lc", "command -v tau || true"], check=True, capture_output=True, text=True)
    found = path_env.stdout.strip()
    if found:
        return found
    raise ManifestError("tau binary not found")


def _tau_version() -> str:
    tau_bin = _find_tau_bin()
    try:
        proc = subprocess.run([tau_bin, "--version"], check=True, capture_output=True, text=True)
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "").strip() or str(exc)
        raise ManifestError(f"failed to get tau version: {detail}") from exc
    return proc.stdout.strip().splitlines()[0]


def _check_source_files(entries: list[Mapping[str, Any]]) -> None:
    for entry in entries:
        rel = str(entry["path"])
        expected = str(entry["sha256"])
        path = REPO_ROOT / rel
        _require(path.is_file(), f"missing source/test file: {rel}")
        actual = _sha256_file(path)
        _require(actual == expected, f"source hash mismatch for {rel}: {actual} != {expected}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate the pinned perps Tau ingress schema manifest.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    args = parser.parse_args(argv)

    manifest_path = args.manifest.resolve()
    manifest = _as_dict(_load_json(manifest_path), ctx=str(manifest_path))
    _require(int(manifest.get("manifest_version", -1)) == 1, "manifest_version mismatch")

    toolchain = _as_dict(manifest.get("toolchain"), ctx="toolchain")
    tau_root = REPO_ROOT / "external" / "tau-lang"
    _require(tau_root.exists(), f"tau-lang not found at {tau_root}")
    tau_head = _git_stdout("rev-parse", "HEAD")
    tau_tree = _sha256_tree([tau_root / "README.md", tau_root / "src", tau_root / "include"], root=tau_root)
    _require(tau_head == toolchain["tau_lang_code_hash"], "tau-lang code hash drifted from manifest")
    _require(tau_tree == toolchain["tau_lang_tree_sha256"], "tau-lang tree drifted from manifest")
    _require(_tau_version() == toolchain["tau_version"], "tau binary version drifted from manifest")

    source_files = manifest.get("source_files")
    _require(isinstance(source_files, list), "source_files must be a list")
    _check_source_files([_as_dict(entry, ctx="source_files[]") for entry in source_files])

    print("ok")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ManifestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
