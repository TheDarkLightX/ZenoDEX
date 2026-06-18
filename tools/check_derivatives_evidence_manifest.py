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
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "derivatives_evidence_manifest.json"


class ManifestError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def _as_dict(obj: Any, *, ctx: str) -> Mapping[str, Any]:
    _require(isinstance(obj, dict), f"{ctx}: expected object")
    return obj


def _require_json_int(value: object, *, ctx: str) -> int:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    raise ManifestError(f"{ctx}: expected int")


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
    ignored_suffixes = {".pyc", ".pyo"}

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
    esso_root = REPO_ROOT / "external" / "ESSO"
    try:
        proc = subprocess.run(
            ["git", "-C", str(esso_root), *args],
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as exc:
        raise ManifestError("git is required for derivatives evidence manifest checks") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "").strip() or str(exc)
        raise ManifestError(f"failed to inspect ESSO checkout: {detail}") from exc
    return proc.stdout.strip()


def _solver_version(cmd: str) -> str:
    try:
        proc = subprocess.run([cmd, "--version"], check=True, capture_output=True, text=True)
    except FileNotFoundError as exc:
        raise ManifestError(f"required solver {cmd!r} is missing") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "").strip() or str(exc)
        raise ManifestError(f"failed to get version for solver {cmd!r}: {detail}") from exc
    return proc.stdout.strip().splitlines()[0]


def _check_source_files(entries: list[Mapping[str, Any]]) -> None:
    for entry in entries:
        rel = str(entry["path"])
        expected = str(entry["sha256"])
        path = REPO_ROOT / rel
        _require(path.is_file(), f"missing source/test file: {rel}")
        actual = _sha256_file(path)
        _require(actual == expected, f"source hash mismatch for {rel}: {actual} != {expected}")


def _check_verify_multi(entry: Mapping[str, Any]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    report = _as_dict(_load_json(report_path), ctx=str(report_path))

    _require(report.get("model_id") == entry["model_id"], f"{report_path}: model_id mismatch")
    _require(report.get("ir_hash") == entry["ir_hash"], f"{report_path}: ir_hash mismatch")
    _require(report.get("verdict") == "VERIFIED", f"{report_path}: verdict must be VERIFIED")
    _require(int(report.get("failed_queries", -1)) == 0, f"{report_path}: failed_queries != 0")
    _require(int(report.get("inconclusive_queries", -1)) == 0, f"{report_path}: inconclusive_queries != 0")
    _require(int(report.get("passed_queries", -1)) == int(entry["passed_queries"]), f"{report_path}: passed_queries mismatch")

    scope = _as_dict(report.get("scope"), ctx=f"{report_path}: scope")
    _require(scope.get("kind") == "inductive", f"{report_path}: scope.kind mismatch")
    _require(int(scope.get("k", -1)) == 1, f"{report_path}: scope.k mismatch")
    _require(
        int(scope.get("solver_timeout_ms", -1)) == int(entry["solver_timeout_ms"]),
        f"{report_path}: solver_timeout_ms mismatch",
    )
    _require(bool(scope.get("fail_closed", False)), f"{report_path}: scope.fail_closed=false")

    expected_solvers = list(entry["solvers"])
    z3_expected = "z3" in expected_solvers
    cvc5_expected = "cvc5" in expected_solvers
    _require(bool(report.get("z3_passed", False)) == z3_expected, f"{report_path}: z3_passed mismatch")
    if cvc5_expected:
        _require(bool(report.get("cvc5_available", False)), f"{report_path}: cvc5_available=false")
        _require(bool(report.get("cvc5_passed", False)), f"{report_path}: cvc5_passed=false")
    else:
        _require(report.get("cvc5_available") in (False, None), f"{report_path}: unexpected cvc5 availability")
        _require(report.get("cvc5_passed") in (False, None), f"{report_path}: unexpected cvc5_passed value")

    _require(bool(report.get("solvers_agreed", False)), f"{report_path}: solvers_agreed=false")

    tool_versions = _as_dict(report.get("tool_versions"), ctx=f"{report_path}: tool_versions")
    expected_toolchain = _as_dict(entry["toolchain"], ctx=f"{report_path}: toolchain")
    _require(
        tool_versions.get("esso_code_hash") == expected_toolchain["esso_code_hash"],
        f"{report_path}: ESSO code hash mismatch",
    )
    solver_versions = _as_dict(tool_versions.get("solvers"), ctx=f"{report_path}: tool_versions.solvers")
    for solver_name in expected_solvers:
        _require(
            solver_versions.get(solver_name) == expected_toolchain["solvers"][solver_name],
            f"{report_path}: solver version mismatch for {solver_name}",
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check the pinned derivatives evidence manifest.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST), help="Path to derivatives evidence manifest JSON")
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest).resolve()
    manifest = _as_dict(_load_json(manifest_path), ctx=str(manifest_path))

    _require(
        _require_json_int(manifest.get("manifest_version"), ctx="manifest_version") == 1,
        "unsupported derivatives evidence manifest version",
    )

    toolchain = _as_dict(manifest.get("toolchain"), ctx="toolchain")
    esso_root = REPO_ROOT / "external" / "ESSO"
    _require(esso_root.exists(), f"ESSO not found at {esso_root}")
    esso_head = _git_stdout("rev-parse", "HEAD")
    esso_tree = _sha256_tree([esso_root / "pyproject.toml", esso_root / "ESSO"], root=esso_root)
    _require(esso_head == toolchain["esso_code_hash"], "ESSO code hash drifted from derivatives evidence manifest")
    _require(esso_tree == toolchain["esso_tree_sha256"], "ESSO tree drifted from derivatives evidence manifest")

    expected_solvers = _as_dict(toolchain.get("solvers"), ctx="toolchain.solvers")
    for solver_name, expected_version in expected_solvers.items():
        _require(_solver_version(str(solver_name)) == expected_version, f"solver version drift for {solver_name}")

    _check_source_files(list(manifest.get("source_files") or []))
    for entry in list(manifest.get("verify_multi") or []):
        _check_verify_multi(_as_dict(entry, ctx="verify_multi entry"))

    print("ok")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ManifestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
