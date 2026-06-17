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
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "batch_auction_ifql_vmo_manifest.json"


class ManifestError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def _as_dict(obj: Any, *, ctx: str) -> Mapping[str, Any]:
    _require(isinstance(obj, dict), f"{ctx}: expected object")
    return obj


def _require_json_bool(value: object, *, ctx: str) -> bool:
    _require(isinstance(value, bool), f"{ctx}: expected bool")
    return value


def _require_true(value: object, *, ctx: str) -> None:
    _require(_require_json_bool(value, ctx=ctx) is True, f"{ctx}=false")


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
        raise ManifestError("git is required for batch-auction IFQL/VMO manifest checks") from exc
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
        _require(path.is_file(), f"missing source file: {rel}")
        actual = _sha256_file(path)
        _require(actual == expected, f"source hash mismatch for {rel}: {actual} != {expected}")


def _check_intent_lint(entry: Mapping[str, Any]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require_true(report.get("ok"), ctx=f"{report_path}: ok")
    _require(report.get("schema") == "esso-intent-report/v1", f"{report_path}: schema mismatch")
    _require(report.get("intent_hash") == entry["intent_hash"], f"{report_path}: intent_hash mismatch")
    intent_source = Path(str(report.get("intent_source", ""))).resolve()
    expected_source = (REPO_ROOT / str(entry["intent_source"])).resolve()
    _require(intent_source == expected_source, f"{report_path}: intent_source mismatch")
    issues = report.get("issues") or []
    _require(isinstance(issues, list), f"{report_path}: issues must be a list")
    hard_issues = [
        issue
        for issue in issues
        if isinstance(issue, dict) and str(issue.get("severity", "")).lower() == "error"
    ]
    _require(not hard_issues, f"{report_path}: intent lint reported hard issues")

    stats = _as_dict(report.get("stats"), ctx=f"{report_path}: stats")
    _require(int(stats.get("nodes", -1)) == int(entry["nodes"]), f"{report_path}: nodes mismatch")
    _require(
        int(stats.get("leaf_nodes", -1)) == int(entry["leaf_nodes"]),
        f"{report_path}: leaf_nodes mismatch",
    )
    _require(
        int(stats.get("leaf_nodes_mapped", -1)) == int(entry["leaf_nodes_mapped"]),
        f"{report_path}: leaf_nodes_mapped mismatch",
    )

    coverage = _as_dict(report.get("coverage"), ctx=f"{report_path}: coverage")
    required = _as_dict(coverage.get("required"), ctx=f"{report_path}: coverage.required")
    _require(
        _require_json_bool(required.get("ok"), ctx=f"{report_path}: coverage.required.ok")
        is _require_json_bool(entry.get("required_ok"), ctx=f"{report_path}: expected required_ok"),
        f"{report_path}: required coverage mismatch",
    )


def _check_ifql_report(entry: Mapping[str, Any]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require_true(report.get("ok"), ctx=f"{report_path}: report ok")
    _require_true(report.get("ok_effective"), ctx=f"{report_path}: report ok_effective")
    _require(report.get("schema") == "esso-ifql-report/v1", f"{report_path}: schema mismatch")
    _require(report.get("report_hash") == entry["report_hash"], f"{report_path}: report_hash mismatch")
    _require(report.get("issues") == [], f"{report_path}: IFQL issues present")

    inputs = _as_dict(report.get("inputs"), ctx=f"{report_path}: report.inputs")
    model = _as_dict(inputs.get("model"), ctx=f"{report_path}: report.inputs.model")
    _require(model.get("ir_hash") == entry["model_ir_hash"], f"{report_path}: model ir_hash mismatch")
    _require(model.get("model_id") == entry["model_id"], f"{report_path}: model_id mismatch")

    node_ids = [node.get("id") for node in report.get("nodes") or [] if isinstance(node, dict)]
    _require(node_ids == entry["node_ids"], f"{report_path}: node_ids mismatch")


def _check_ifql_vmo(entry: Mapping[str, Any]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    out = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require_true(out.get("ok"), ctx=f"{report_path}: out ok")
    _require(out.get("fiber") == entry["fiber"], f"{report_path}: fiber mismatch")
    _require(out.get("intent_id") == entry["intent_id"], f"{report_path}: intent_id mismatch")
    _require(out.get("schema") == "esso-ifql-vmo/v1", f"{report_path}: out schema mismatch")
    observables = _as_dict(out.get("observables"), ctx=f"{report_path}: observables")
    _require(observables.get("state_vars") == entry["observed_state_vars"], f"{report_path}: observed state vars mismatch")
    _require(observables.get("effects") == [], f"{report_path}: observed effects mismatch")

    vmo = _as_dict(out.get("vmo"), ctx=f"{report_path}: vmo")
    _require_true(vmo.get("ok"), ctx=f"{report_path}: vmo ok")
    _require(vmo.get("schema") == "esso-vmo/v1", f"{report_path}: vmo schema mismatch")
    _require(vmo.get("vmo_hash") == entry["vmo_hash"], f"{report_path}: vmo_hash mismatch")
    _require(vmo.get("preserves") == entry["preserves"], f"{report_path}: preserves mismatch")

    checks = vmo.get("checks") or []
    _require(isinstance(checks, list) and len(checks) == 2, f"{report_path}: expected 2 VMO checks")
    mode_check = next((c for c in checks if isinstance(c, dict) and c.get("kind") == "z3.observational_equivalence"), None)
    _require(mode_check is not None, f"{report_path}: missing observational equivalence check")
    _require(mode_check.get("mode") == entry["mode"], f"{report_path}: observational mode mismatch")
    _require_true(mode_check.get("ok"), ctx=f"{report_path}: observational equivalence")
    result = _as_dict(mode_check.get("result"), ctx=f"{report_path}: observational result")
    _require(result.get("status") == "PASS", f"{report_path}: observational status mismatch")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate the pinned batch-auction IFQL/VMO manifest.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    args = parser.parse_args(argv)

    manifest_path = args.manifest.resolve()
    manifest = _as_dict(_load_json(manifest_path), ctx=str(manifest_path))
    _require(int(manifest.get("manifest_version", -1)) == 1, "manifest_version mismatch")

    toolchain = _as_dict(manifest.get("toolchain"), ctx="toolchain")
    esso_root = REPO_ROOT / "external" / "ESSO"
    _require(esso_root.exists(), f"ESSO not found at {esso_root}")
    esso_head = _git_stdout("rev-parse", "HEAD")
    esso_tree = _sha256_tree([esso_root / "pyproject.toml", esso_root / "ESSO"], root=esso_root)
    _require(esso_head == toolchain["esso_code_hash"], "ESSO code hash drifted from batch-auction IFQL/VMO manifest")
    _require(esso_tree == toolchain["esso_tree_sha256"], "ESSO tree drifted from batch-auction IFQL/VMO manifest")

    solvers = _as_dict(toolchain.get("solvers"), ctx="toolchain.solvers")
    for solver_name, expected_version in solvers.items():
        _require(_solver_version(str(solver_name)) == expected_version, f"solver version drift for {solver_name}")

    source_files = manifest.get("source_files")
    _require(isinstance(source_files, list), "source_files must be a list")
    _check_source_files([_as_dict(entry, ctx="source_files[]") for entry in source_files])

    _check_intent_lint(_as_dict(manifest.get("intent_lint"), ctx="intent_lint"))
    _check_ifql_report(_as_dict(manifest.get("reference_ifql"), ctx="reference_ifql"))
    _check_ifql_report(_as_dict(manifest.get("candidate_ifql"), ctx="candidate_ifql"))
    _check_ifql_vmo(_as_dict(manifest.get("vmo_full"), ctx="vmo_full"))
    _check_ifql_vmo(_as_dict(manifest.get("vmo_no_extra"), ctx="vmo_no_extra"))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ManifestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
