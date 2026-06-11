#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "autogovnext_governance_lane_assurance_manifest.json"

REQUIRED_COMMAND_IDS = frozenset(
    {
        "focused_pytest",
        "lean_bounded_drift",
        "proof_client_package_integration",
        "proof_client_package_sync",
        "proof_client_package_tests",
        "py_compile",
        "ui_sdk_tests",
    }
)
REQUIRED_NON_CLAIMS = frozenset(
    {
        "does_not_authorize_settlement",
        "does_not_train_q_table_online",
        "does_not_implement_governance_authority_reset_yet",
    }
)


class ManifestError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def _as_dict(value: Any, *, ctx: str) -> Mapping[str, Any]:
    _require(isinstance(value, dict), f"{ctx}: expected object")
    return value


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


def _repo_path(rel: str) -> Path:
    path = (REPO_ROOT / rel).resolve()
    try:
        path.relative_to(REPO_ROOT)
    except ValueError as exc:
        raise ManifestError(f"path escapes repository: {rel}") from exc
    return path


def _check_source_files(entries: object) -> list[dict[str, str]]:
    _require(isinstance(entries, list) and entries, "source_files must be a non-empty list")
    seen: set[str] = set()
    checked: list[dict[str, str]] = []
    for raw in entries:
        entry = _as_dict(raw, ctx="source_files[]")
        rel = str(entry.get("path", ""))
        expected = str(entry.get("sha256", ""))
        _require(rel and rel not in seen, f"duplicate or empty source path: {rel!r}")
        _require(len(expected) == 64 and all(ch in "0123456789abcdef" for ch in expected), f"{rel}: invalid sha256")
        seen.add(rel)
        path = _repo_path(rel)
        _require(path.is_file(), f"missing source/test/workflow file: {rel}")
        actual = _sha256_file(path)
        _require(actual == expected, f"source hash mismatch for {rel}: {actual} != {expected}")
        checked.append({"path": rel, "sha256": actual})
    return checked


def _normalize_argv(argv: object) -> list[str]:
    _require(isinstance(argv, list) and argv, "command argv must be a non-empty list")
    out: list[str] = []
    for raw in argv:
        _require(isinstance(raw, str) and raw, "command argv entries must be non-empty strings")
        out.append(sys.executable if raw == "{python}" else raw)
    return out


def _check_commands(commands: object, *, run_commands: bool) -> list[dict[str, Any]]:
    _require(isinstance(commands, list) and commands, "required_commands must be a non-empty list")
    by_id: dict[str, Mapping[str, Any]] = {}
    for raw in commands:
        command = _as_dict(raw, ctx="required_commands[]")
        command_id = str(command.get("id", ""))
        _require(command_id and command_id not in by_id, f"duplicate or empty command id: {command_id!r}")
        by_id[command_id] = command
    missing = sorted(REQUIRED_COMMAND_IDS - set(by_id))
    _require(not missing, f"missing required command(s): {', '.join(missing)}")

    results: list[dict[str, Any]] = []
    for command_id in sorted(REQUIRED_COMMAND_IDS):
        command = by_id[command_id]
        expected_exit = int(command.get("expected_exit", -1))
        _require(expected_exit == 0, f"{command_id}: expected_exit must be 0")
        argv = _normalize_argv(command.get("argv"))
        if not run_commands:
            results.append({"id": command_id, "checked": "metadata_only", "argv": argv})
            continue
        proc = subprocess.run(argv, cwd=REPO_ROOT, text=True, capture_output=True, check=False)
        if proc.returncode != expected_exit:
            tail = (proc.stderr or proc.stdout or "").strip().splitlines()[-20:]
            raise ManifestError(f"{command_id}: exit {proc.returncode} != {expected_exit}: {' | '.join(tail)}")
        results.append({"id": command_id, "checked": "executed", "argv": argv})
    return results


def check_manifest(*, manifest_path: Path, run_commands: bool = False) -> dict[str, Any]:
    manifest = _as_dict(_load_json(manifest_path), ctx=str(manifest_path))
    _require(int(manifest.get("manifest_version", -1)) == 1, "manifest_version mismatch")
    _require(manifest.get("production_security_claim") is False, "production_security_claim must remain false")

    non_claims = manifest.get("non_claims")
    _require(isinstance(non_claims, list), "non_claims must be a list")
    missing_non_claims = sorted(REQUIRED_NON_CLAIMS - {str(item) for item in non_claims})
    _require(not missing_non_claims, f"missing non_claim(s): {', '.join(missing_non_claims)}")

    checked_files = _check_source_files(manifest.get("source_files"))
    checked_commands = _check_commands(manifest.get("required_commands"), run_commands=run_commands)
    return {
        "ok": True,
        "schema": "zenodex/autogovnext_governance_lane_assurance_check/v1",
        "manifest_path": str(manifest_path),
        "source_file_count": len(checked_files),
        "commands": checked_commands,
        "production_security_claim": False,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check the AutoGovNEXT governance-lane assurance manifest.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--run-commands", action="store_true", help="execute the manifest's focused verification commands")
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    args = parser.parse_args(argv)

    try:
        report = check_manifest(manifest_path=args.manifest.resolve(), run_commands=args.run_commands)
    except ManifestError as exc:
        if args.json:
            print(json.dumps({"ok": False, "error": str(exc)}, indent=2, sort_keys=True))
        else:
            print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
