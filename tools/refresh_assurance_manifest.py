#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import check_zusd_repay_assurance_manifest as base


REPO_ROOT = Path(__file__).resolve().parents[1]


class RefreshError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RefreshError(message)


def _load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise RefreshError(f"failed to read JSON {path}: {exc}") from exc


def _dump_json(path: Path, obj: Any) -> None:
    path.write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")


def _repo_rel(path_str: str) -> str:
    path = Path(path_str)
    if path.is_absolute():
        try:
            return path.resolve().relative_to(REPO_ROOT.resolve()).as_posix()
        except Exception as exc:
            raise RefreshError(f"path {path_str} is outside repo root {REPO_ROOT}") from exc
    return path.as_posix()


def _load_report(report_path: str) -> dict[str, Any]:
    path = REPO_ROOT / report_path
    _require(path.is_file(), f"missing report file: {report_path}")
    report = _load_json(path)
    _require(isinstance(report, dict), f"report {report_path}: expected object")
    return report


def _refresh_toolchain(manifest: dict[str, Any]) -> None:
    toolchain = manifest.get("toolchain")
    _require(isinstance(toolchain, dict), "toolchain: expected object")

    esso_root = REPO_ROOT / "external" / "ESSO"
    _require(esso_root.exists(), f"ESSO not found at {esso_root}")

    solvers = toolchain.get("solvers")
    solver_names = list(solvers.keys()) if isinstance(solvers, dict) and solvers else ["z3", "cvc5"]

    manifest["toolchain"] = {
        "esso_code_hash": base._git_stdout("rev-parse", "HEAD"),
        "esso_tree_sha256": base._sha256_tree([esso_root / "pyproject.toml", esso_root / "ESSO"], root=esso_root),
        "solvers": {name: base._solver_version(name) for name in solver_names},
    }


def _refresh_source_files(manifest: dict[str, Any]) -> None:
    entries = manifest.get("source_files")
    _require(isinstance(entries, list), "source_files must be a list")
    for entry in entries:
        _require(isinstance(entry, dict), "source_files[]: expected object")
        rel = str(entry["path"])
        path = REPO_ROOT / rel
        _require(path.is_file(), f"missing source/test file: {rel}")
        entry["sha256"] = base._sha256_file(path)


def _refresh_validate(entry: dict[str, Any]) -> None:
    report = _load_report(str(entry["report_path"]))
    entry["model_path"] = _repo_rel(str(report["model"]))
    entry["ir_hash"] = str(report["ir_hash"])


def _refresh_shell_lint(entry: dict[str, Any]) -> None:
    report = _load_report(str(entry["report_path"]))
    adapter = report.get("adapter") or {}
    expected = report.get("expected") or {}
    got = report.get("got") or {}
    actions = list(expected.get("actions") or got.get("actions") or [])
    effects = list(expected.get("effects") or got.get("effects") or [])
    entry["adapter_spec"] = str(adapter["spec"])
    entry["ir_hash"] = str(report["ir_hash"])
    entry["actions"] = actions
    entry["effects"] = effects


def _refresh_verify_shell(entry: dict[str, Any]) -> None:
    report = _load_report(str(entry["report_path"]))
    adapter = report.get("adapter") or {}
    determinism = report.get("determinism") or {}
    fingerprints = list(determinism.get("fingerprints") or [])
    _require(fingerprints, f"{entry['report_path']}: missing determinism fingerprints")
    entry["kernel_path"] = _repo_rel(str(report["model"]))
    entry["adapter_spec"] = str(adapter["spec"])
    entry["ir_hash"] = str(report["ir_hash"])
    entry["mode"] = str(report["mode"])
    entry["seed"] = int(report["seed"])
    entry["traces"] = int(report["traces"])
    entry["max_steps"] = int(report["max_steps"])
    entry["determinism_trials"] = int(report["determinism_trials"])
    entry["fingerprint"] = str(fingerprints[0])


def _refresh_verify_multi(entry: dict[str, Any]) -> None:
    report = _load_report(str(entry["report_path"]))
    scope = report.get("scope") or {}
    tool_versions = report.get("tool_versions") or {}
    solvers = tool_versions.get("solvers") or {}
    entry["model_id"] = str(report["model_id"])
    entry["ir_hash_short"] = str(report["ir_hash"])
    entry["verdict"] = str(report["verdict"])
    entry["z3_passed"] = bool(report["z3_passed"])
    entry["cvc5_available"] = bool(report["cvc5_available"])
    entry["cvc5_passed"] = bool(report["cvc5_passed"])
    entry["solvers_agreed"] = bool(report["solvers_agreed"])
    entry["total_queries"] = int(report["total_queries"])
    entry["passed_queries"] = int(report["passed_queries"])
    entry["failed_queries"] = int(report["failed_queries"])
    entry["inconclusive_queries"] = int(report["inconclusive_queries"])
    entry["disagreements"] = list(report.get("disagreements") or [])
    entry["notes"] = list(report.get("notes") or [])
    entry["scope_kind"] = str(scope["kind"])
    entry["k"] = int(scope["k"])
    entry["solver_timeout_ms"] = int(scope["solver_timeout_ms"])
    entry["fail_closed"] = bool(scope["fail_closed"])
    entry["report_solver_versions"] = {str(k): str(v) for k, v in solvers.items()}


def _refresh_section(manifest: dict[str, Any], key: str, fn) -> None:
    value = manifest.get(key)
    if value is None:
        return
    if isinstance(value, dict):
        fn(value)
        return
    if isinstance(value, list):
        for entry in value:
            _require(isinstance(entry, dict), f"{key}[]: expected object")
            fn(entry)
        return
    raise RefreshError(f"{key}: expected object or list")


def refresh_manifest(path: Path) -> None:
    manifest = _load_json(path)
    _require(isinstance(manifest, dict), f"{path}: expected object")
    _require(int(manifest.get("manifest_version", 0)) == 1, f"{path}: unsupported manifest_version")
    _refresh_toolchain(manifest)
    _refresh_source_files(manifest)
    _refresh_section(manifest, "validate", _refresh_validate)
    _refresh_section(manifest, "shell_lint", _refresh_shell_lint)
    _refresh_section(manifest, "verify_shell", _refresh_verify_shell)
    _refresh_section(manifest, "verify_multi", _refresh_verify_multi)
    _dump_json(path, manifest)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Refresh pinned assurance manifest fields from current reports and source files.")
    parser.add_argument("manifests", nargs="+", type=Path, help="Manifest JSON file(s) to refresh")
    args = parser.parse_args(argv)

    for raw_path in args.manifests:
        path = raw_path.resolve()
        refresh_manifest(path)
        print(f"refreshed: {path.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
