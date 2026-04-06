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
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "zusd_risky_ops_assurance_manifest.json"


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
        raise ManifestError("git is required for zUSD risky-ops manifest checks") from exc
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


def _check_validate(entry: Mapping[str, Any]) -> None:
    model_path = REPO_ROOT / str(entry["model_path"])
    report = _as_dict(
        _load_json(REPO_ROOT / str(entry["report_path"])),
        ctx=str(REPO_ROOT / str(entry["report_path"])),
    )
    _require(report.get("command") == "validate", "validate report: command mismatch")
    _require(bool(report.get("ok", False)), "validate report: ok=false")
    report_model = Path(str(report.get("model", ""))).resolve()
    _require(report_model == model_path.resolve(), "validate report: model mismatch")
    _require(report.get("ir_hash") == entry["ir_hash"], "validate report: ir_hash mismatch")
    _require(report.get("errors") == [], "validate report: errors present")
    _require(model_path.is_file(), f"missing model file: {model_path}")


def _check_shell_lint(entry: Mapping[str, Any]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require(bool(report.get("ok", False)), f"{report_path}: ok=false")
    _require(report.get("command") == "shell-lint", f"{report_path}: command mismatch")
    _require(report.get("ir_hash") == entry["ir_hash"], f"{report_path}: ir_hash mismatch")

    adapter = _as_dict(report.get("adapter"), ctx=f"{report_path}: adapter")
    _require(adapter.get("spec") == entry["adapter_spec"], f"{report_path}: adapter spec mismatch")

    expected = _as_dict(report.get("expected"), ctx=f"{report_path}: expected")
    got = _as_dict(report.get("got"), ctx=f"{report_path}: got")
    _require(expected.get("actions") == entry["actions"], f"{report_path}: expected actions mismatch")
    _require(expected.get("effects") == entry["effects"], f"{report_path}: expected effects mismatch")
    _require(got.get("actions") == entry["actions"], f"{report_path}: got actions mismatch")
    _require(got.get("effects") == entry["effects"], f"{report_path}: got effects mismatch")
    _require(report.get("issues") == [], f"{report_path}: shell-lint reported issues")


def _check_verify_shell(entry: Mapping[str, Any]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require(bool(report.get("ok", False)), f"{report_path}: ok=false")
    _require(report.get("command") == "verify-shell", f"{report_path}: command mismatch")
    _require(report.get("ir_hash") == entry["ir_hash"], f"{report_path}: ir_hash mismatch")
    _require(report.get("mode") == entry["mode"], f"{report_path}: mode mismatch")
    _require(int(report.get("seed", -1)) == int(entry["seed"]), f"{report_path}: seed mismatch")
    _require(int(report.get("traces", -1)) == int(entry["traces"]), f"{report_path}: traces mismatch")
    _require(int(report.get("max_steps", -1)) == int(entry["max_steps"]), f"{report_path}: max_steps mismatch")
    _require(
        int(report.get("determinism_trials", -1)) == int(entry["determinism_trials"]),
        f"{report_path}: determinism_trials mismatch",
    )
    _require(report.get("failure") is None, f"{report_path}: verify-shell failure is not null")

    adapter = _as_dict(report.get("adapter"), ctx=f"{report_path}: adapter")
    _require(adapter.get("spec") == entry["adapter_spec"], f"{report_path}: adapter spec mismatch")
    _require(
        Path(str(report.get("model", ""))).name == Path(str(entry["kernel_path"])).name,
        f"{report_path}: model file mismatch",
    )

    determinism = _as_dict(report.get("determinism"), ctx=f"{report_path}: determinism")
    _require(bool(determinism.get("ok", False)), f"{report_path}: determinism.ok=false")
    fingerprints = list(determinism.get("fingerprints") or [])
    _require(len(fingerprints) >= 2, f"{report_path}: fewer than 2 fingerprints")
    _require(len(set(fingerprints)) == 1, f"{report_path}: fingerprints diverged")
    _require(fingerprints[0] == entry["fingerprint"], f"{report_path}: fingerprint mismatch")


def _check_verify_multi(entry: Mapping[str, Any], toolchain: Mapping[str, Any]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require(report.get("model_id") == entry["model_id"], f"{report_path}: model_id mismatch")
    _require(report.get("ir_hash") == entry["ir_hash_short"], f"{report_path}: ir_hash mismatch")
    _require(report.get("verdict") == entry["verdict"], f"{report_path}: verdict mismatch")
    _require(bool(report.get("z3_passed", False)) == bool(entry["z3_passed"]), f"{report_path}: z3_passed mismatch")
    _require(
        bool(report.get("cvc5_available", False)) == bool(entry["cvc5_available"]),
        f"{report_path}: cvc5_available mismatch",
    )
    _require(
        bool(report.get("cvc5_passed", False)) == bool(entry["cvc5_passed"]),
        f"{report_path}: cvc5_passed mismatch",
    )
    _require(
        bool(report.get("solvers_agreed", False)) == bool(entry["solvers_agreed"]),
        f"{report_path}: solvers_agreed mismatch",
    )
    _require(int(report.get("total_queries", -1)) == int(entry["total_queries"]), f"{report_path}: total_queries mismatch")
    _require(
        int(report.get("passed_queries", -1)) == int(entry["passed_queries"]),
        f"{report_path}: passed_queries mismatch",
    )
    _require(
        int(report.get("failed_queries", -1)) == int(entry["failed_queries"]),
        f"{report_path}: failed_queries mismatch",
    )
    _require(
        int(report.get("inconclusive_queries", -1)) == int(entry["inconclusive_queries"]),
        f"{report_path}: inconclusive_queries mismatch",
    )
    _require(report.get("disagreements") == entry["disagreements"], f"{report_path}: disagreements mismatch")
    _require(report.get("notes") == entry["notes"], f"{report_path}: notes mismatch")

    scope = _as_dict(report.get("scope"), ctx=f"{report_path}: scope")
    _require(scope.get("kind") == entry["scope_kind"], f"{report_path}: scope.kind mismatch")
    _require(int(scope.get("k", -1)) == int(entry["k"]), f"{report_path}: scope.k mismatch")
    _require(
        int(scope.get("solver_timeout_ms", -1)) == int(entry["solver_timeout_ms"]),
        f"{report_path}: solver_timeout_ms mismatch",
    )
    _require(bool(scope.get("fail_closed", False)) == bool(entry["fail_closed"]), f"{report_path}: fail_closed mismatch")

    versions = _as_dict(report.get("tool_versions"), ctx=f"{report_path}: tool_versions")
    _require(versions.get("esso_code_hash") == toolchain["esso_code_hash"], f"{report_path}: ESSO hash mismatch")

    solvers = _as_dict(versions.get("solvers"), ctx=f"{report_path}: tool_versions.solvers")
    expected_solvers = _as_dict(toolchain.get("solvers"), ctx="toolchain.solvers")
    _require(solvers.get("z3") == entry["report_solver_versions"]["z3"], f"{report_path}: z3 report version mismatch")
    _require(
        solvers.get("cvc5") == entry["report_solver_versions"]["cvc5"],
        f"{report_path}: cvc5 report version mismatch",
    )
    _require(_solver_version("z3") == expected_solvers["z3"], f"{report_path}: z3 binary version drift")
    _require(_solver_version("cvc5") == expected_solvers["cvc5"], f"{report_path}: cvc5 binary version drift")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check the pinned zUSD risky-ops assurance manifest.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST), help="Path to zUSD risky-ops assurance manifest JSON")
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest).resolve()
    manifest = _as_dict(_load_json(manifest_path), ctx=str(manifest_path))

    _require(int(manifest.get("manifest_version", 0)) == 1, "unsupported zUSD risky-ops assurance manifest version")

    toolchain = _as_dict(manifest.get("toolchain"), ctx="toolchain")
    esso_root = REPO_ROOT / "external" / "ESSO"
    _require(esso_root.exists(), f"ESSO not found at {esso_root}")
    esso_head = _git_stdout("rev-parse", "HEAD")
    esso_tree = _sha256_tree([esso_root / "pyproject.toml", esso_root / "ESSO"], root=esso_root)
    _require(esso_head == toolchain["esso_code_hash"], "ESSO code hash drifted from zUSD risky-ops manifest")
    _require(esso_tree == toolchain["esso_tree_sha256"], "ESSO tree drifted from zUSD risky-ops manifest")

    expected_solvers = _as_dict(toolchain.get("solvers"), ctx="toolchain.solvers")
    for solver_name, expected_version in expected_solvers.items():
        _require(_solver_version(str(solver_name)) == expected_version, f"solver version drift for {solver_name}")

    _check_source_files(list(manifest.get("source_files") or []))
    _check_validate(_as_dict(manifest.get("validate"), ctx="validate"))
    _check_shell_lint(_as_dict(manifest.get("shell_lint"), ctx="shell_lint"))
    _check_verify_shell(_as_dict(manifest.get("verify_shell"), ctx="verify_shell"))
    _check_verify_multi(_as_dict(manifest.get("verify_multi"), ctx="verify_multi"), toolchain)

    for rel in list(manifest.get("adapter_regression_tests") or []):
        path = REPO_ROOT / str(rel)
        _require(path.is_file(), f"missing adapter regression test: {rel}")

    print("ok")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ManifestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
