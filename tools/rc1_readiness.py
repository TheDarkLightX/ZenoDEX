#!/usr/bin/env python3
"""RC1 readiness status/check CLI for the conservative ZenoDEX release surface."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

import yaml


REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = REPO_ROOT / "tools" / "rc1_scope_manifest.json"
CLAIMS_REGISTRY_PATH = REPO_ROOT / "docs" / "claims_registry.yaml"

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

try:
    from tools.permissionless_assurance import _status_payload as assurance_status_payload
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from permissionless_assurance import _status_payload as assurance_status_payload

try:
    from tools.render_rc1_verified_surface_matrix import matrix_status as rc1_matrix_status
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from render_rc1_verified_surface_matrix import matrix_status as rc1_matrix_status

try:
    from tools.render_rc1_supported_runtime_path import runtime_path_status as rc1_runtime_path_status
except ModuleNotFoundError:  # pragma: no cover - script execution path
    from render_rc1_supported_runtime_path import runtime_path_status as rc1_runtime_path_status


class RC1Error(RuntimeError):
    pass


_LOCAL_SCOPE_TOPLEVELS = {
    "docs",
    "formal",
    "generated",
    "src",
    "tests",
    "tools",
}


def _load_manifest(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RC1Error(f"missing RC1 scope manifest: {path.relative_to(REPO_ROOT)}") from exc
    except json.JSONDecodeError as exc:
        raise RC1Error(f"invalid RC1 scope manifest JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise RC1Error("RC1 scope manifest must be an object")
    if data.get("schema") != "zenodex/rc1-scope-manifest/v1":
        raise RC1Error("RC1 scope manifest has unexpected schema")
    return data


def _load_claim_statuses(path: Path) -> dict[str, str]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RC1Error(f"missing claims registry: {path.relative_to(REPO_ROOT)}") from exc
    except yaml.YAMLError as exc:
        raise RC1Error(f"invalid claims registry YAML: {exc}") from exc
    if not isinstance(data, dict) or not isinstance(data.get("claims"), list):
        raise RC1Error("claims registry is malformed")
    out: dict[str, str] = {}
    for item in data["claims"]:
        if not isinstance(item, dict):
            continue
        claim_id = item.get("id")
        status = item.get("status")
        if isinstance(claim_id, str) and isinstance(status, str):
            out[claim_id] = status
    return out


def _maybe_add_scope_path(paths: set[str], raw: object) -> None:
    if not isinstance(raw, str):
        return
    rel = raw.strip()
    if not rel or rel == "..." or rel.startswith("-"):
        return
    candidate = Path(rel)
    if candidate.is_absolute() or not candidate.parts:
        return
    if candidate.parts[0] not in _LOCAL_SCOPE_TOPLEVELS:
        return
    paths.add(candidate.as_posix())


def collect_rc1_scope_paths(root: Path, manifest: dict[str, Any]) -> list[str]:
    scope_paths: set[str] = set()

    for key in ("required_docs", "required_files", "excluded_experimental_surfaces"):
        for item in manifest.get(key, []):
            _maybe_add_scope_path(scope_paths, item)

    http_boundary = manifest.get("supported_http_boundary")
    if isinstance(http_boundary, dict):
        _maybe_add_scope_path(scope_paths, http_boundary.get("file"))

    for command in manifest.get("supported_commands", []):
        if not isinstance(command, list):
            continue
        for part in command:
            _maybe_add_scope_path(scope_paths, part)

    for surface in manifest.get("verified_surfaces", []):
        if not isinstance(surface, dict):
            continue
        for key in ("docs", "paths", "routes"):
            for item in surface.get(key, []):
                _maybe_add_scope_path(scope_paths, item)
        for command in surface.get("commands", []):
            if not isinstance(command, list):
                continue
            for part in command:
                _maybe_add_scope_path(scope_paths, part)

    runtime = manifest.get("supported_runtime_path")
    if isinstance(runtime, dict):
        for key in ("read_only_http_boundary", "spot_submission_path", "zusd_wallet_transport"):
            entry = runtime.get(key)
            if not isinstance(entry, dict):
                continue
            for field in ("file", "doc", "cli", "signing_doc", "auth_message_path", "nonce_state_path", "entrypoint"):
                _maybe_add_scope_path(scope_paths, entry.get(field))
            for field in ("tests", "notes"):
                values = entry.get(field)
                if isinstance(values, list):
                    for item in values:
                        _maybe_add_scope_path(scope_paths, item)
            commands = entry.get("commands")
            if isinstance(commands, list):
                for command in commands:
                    if not isinstance(command, list):
                        continue
                    for part in command:
                        _maybe_add_scope_path(scope_paths, part)

    return sorted(scope_paths)


def _missing_paths(root: Path, rel_paths: Sequence[str]) -> list[str]:
    return [rel for rel in rel_paths if not (root / rel).exists()]


def _route_presence(root: Path, rel_path: str, routes: Sequence[str]) -> dict[str, bool]:
    text = (root / rel_path).read_text(encoding="utf-8")
    return {route: (route in text) for route in routes}


def _build_status_payload(
    *,
    root: Path,
    manifest: dict[str, Any],
    assurance_payload: dict[str, Any],
    claim_statuses: dict[str, str],
) -> dict[str, Any]:
    required_docs = [str(item) for item in manifest.get("required_docs", [])]
    required_files = [str(item) for item in manifest.get("required_files", [])]
    rc1_scope_paths = collect_rc1_scope_paths(root, manifest)
    dirty_paths = [str(item) for item in assurance_payload.get("dirty_paths", [])]
    rc1_scoped_dirty_paths = sorted(path for path in dirty_paths if path in set(rc1_scope_paths))
    http_boundary = manifest.get("supported_http_boundary", {})
    if not isinstance(http_boundary, dict):
        raise RC1Error("supported_http_boundary must be an object")
    http_file = str(http_boundary.get("file", ""))
    http_routes = [str(item) for item in http_boundary.get("routes", [])]
    excluded_claim_ids = [str(item) for item in manifest.get("excluded_claims_expected_disputed", [])]

    missing_docs = _missing_paths(root, required_docs)
    missing_files = _missing_paths(root, required_files)
    missing_http_file = [] if (root / http_file).exists() else [http_file]
    route_presence = _route_presence(root, http_file, http_routes) if not missing_http_file else {route: False for route in http_routes}
    missing_routes = [route for route, present in route_presence.items() if not present]

    excluded_claim_statuses = {claim_id: claim_statuses.get(claim_id, "missing") for claim_id in excluded_claim_ids}
    excluded_claims_not_disputed = [
        claim_id for claim_id, status in excluded_claim_statuses.items() if status != "disputed"
    ]
    require_runtime_path_check = "docs/RC1_SUPPORTED_RUNTIME_PATH.md" in required_docs
    require_matrix_check = "docs/RC1_VERIFIED_SURFACE_MATRIX.md" in required_docs
    runtime_path = (
        rc1_runtime_path_status(root=root, manifest=manifest)
        if require_runtime_path_check
        else {"ok": True, "path": "docs/RC1_SUPPORTED_RUNTIME_PATH.md", "error": None}
    )
    matrix = (
        rc1_matrix_status(
            root=root,
            manifest=manifest,
            claim_statuses=claim_statuses,
            assurance_payload=assurance_payload,
        )
        if require_matrix_check
        else {"ok": True, "path": "docs/RC1_VERIFIED_SURFACE_MATRIX.md", "error": None}
    )

    assurance_snapshot = assurance_payload.get("assurance_snapshot", {})
    tla_claim_summary = assurance_payload.get("tla_claim_summary", {})
    lanes = assurance_payload.get("lanes", [])
    release_lane_files_present = False
    if isinstance(lanes, list):
        for lane in lanes:
            if isinstance(lane, dict) and lane.get("name") == "release":
                release_lane_files_present = bool(lane.get("ready"))
                break

    checks = {
        "scope_docs_present": not missing_docs,
        "required_files_present": not missing_files and not missing_http_file,
        "supported_http_routes_present": not missing_routes and not missing_http_file,
        "supported_runtime_path_ok": bool(runtime_path.get("ok")),
        "verified_surface_matrix_ok": bool(matrix.get("ok")),
        "assurance_snapshot_ok": bool(assurance_snapshot.get("ok")),
        "tla_claim_summary_ok": bool(tla_claim_summary.get("ok")),
        "release_lane_files_present": release_lane_files_present,
        "clean_tree": int(assurance_payload.get("dirty_count", 0)) == 0,
        "excluded_claims_still_disputed": not excluded_claims_not_disputed,
    }
    unmet = [name for name, ok in checks.items() if not ok]

    return {
        "schema": "zenodex/rc1-readiness-status/v1",
        "manifest_path": "tools/rc1_scope_manifest.json",
        "overall_ok": not unmet,
        "checks": checks,
        "unmet_criteria": unmet,
        "dirty_count": int(assurance_payload.get("dirty_count", 0)),
        "rc1_scope_paths": rc1_scope_paths,
        "rc1_scope_count": len(rc1_scope_paths),
        "rc1_scoped_dirty_paths": rc1_scoped_dirty_paths,
        "rc1_scoped_dirty_count": len(rc1_scoped_dirty_paths),
        "required_docs": required_docs,
        "missing_docs": missing_docs,
        "required_files": required_files,
        "missing_files": missing_files + missing_http_file,
        "supported_http_boundary": {
            "file": http_file,
            "routes": http_routes,
            "route_presence": route_presence,
            "missing_routes": missing_routes,
        },
        "excluded_claims_expected_disputed": excluded_claim_statuses,
        "assurance": {
            "snapshot_ok": bool(assurance_snapshot.get("ok")),
            "snapshot_error": assurance_snapshot.get("error"),
            "supported_runtime_path_ok": bool(runtime_path.get("ok")),
            "supported_runtime_path_error": runtime_path.get("error"),
            "supported_runtime_path_path": runtime_path.get("path"),
            "verified_surface_matrix_ok": bool(matrix.get("ok")),
            "verified_surface_matrix_error": matrix.get("error"),
            "verified_surface_matrix_path": matrix.get("path"),
            "tla_claim_summary_ok": bool(tla_claim_summary.get("ok")),
            "tla_claim_summary_error": tla_claim_summary.get("error"),
            "release_lane_files_present": release_lane_files_present,
            "branch": assurance_payload.get("branch"),
        },
        "supported_commands": manifest.get("supported_commands", []),
        "excluded_experimental_surfaces": manifest.get("excluded_experimental_surfaces", []),
    }


def build_status_payload(root: Path = REPO_ROOT) -> dict[str, Any]:
    manifest = _load_manifest(root / "tools" / "rc1_scope_manifest.json")
    claim_statuses = _load_claim_statuses(root / "docs" / "claims_registry.yaml")
    assurance = assurance_status_payload()
    return _build_status_payload(
        root=root,
        manifest=manifest,
        assurance_payload=assurance,
        claim_statuses=claim_statuses,
    )


def _print_status(payload: dict[str, Any]) -> None:
    print("ZenoDex RC1 Readiness")
    print(f"manifest: {payload['manifest_path']}")
    print(f"overall: {'READY' if payload['overall_ok'] else 'BLOCKED'}")
    print(f"dirty tree: {payload['dirty_count']} paths")
    print(f"rc1 scoped dirty paths: {payload['rc1_scoped_dirty_count']}")
    print()
    print("Checks")
    for name, ok in payload["checks"].items():
        print(f"  [{'OK' if ok else 'BLOCK'}] {name}")
    if payload["unmet_criteria"]:
        print()
        print("Unmet criteria")
        for item in payload["unmet_criteria"]:
            print(f"  - {item}")
    if payload["missing_docs"]:
        print()
        print("Missing docs")
        for rel in payload["missing_docs"]:
            print(f"  - {rel}")
    supported_runtime_path_path = payload["assurance"].get("supported_runtime_path_path")
    supported_runtime_path_error = payload["assurance"].get("supported_runtime_path_error")
    if supported_runtime_path_path:
        print()
        print("Supported runtime path")
        if supported_runtime_path_error:
            print(f"  [BLOCK] {supported_runtime_path_path}: {supported_runtime_path_error}")
        else:
            state = "OK" if payload["checks"]["supported_runtime_path_ok"] else "STALE"
            print(f"  [{state}] {supported_runtime_path_path}")
    verified_surface_matrix_path = payload["assurance"].get("verified_surface_matrix_path")
    verified_surface_matrix_error = payload["assurance"].get("verified_surface_matrix_error")
    if verified_surface_matrix_path:
        print()
        print("Verified surface matrix")
        if verified_surface_matrix_error:
            print(f"  [BLOCK] {verified_surface_matrix_path}: {verified_surface_matrix_error}")
        else:
            state = "OK" if payload["checks"]["verified_surface_matrix_ok"] else "STALE"
            print(f"  [{state}] {verified_surface_matrix_path}")
    if payload["missing_files"]:
        print()
        print("Missing files")
        for rel in payload["missing_files"]:
            print(f"  - {rel}")
    scoped_dirty_paths = payload.get("rc1_scoped_dirty_paths", [])
    if scoped_dirty_paths:
        print()
        print("RC1 scoped dirty paths")
        limit = 20
        for rel in scoped_dirty_paths[:limit]:
            print(f"  - {rel}")
        remaining = len(scoped_dirty_paths) - limit
        if remaining > 0:
            print(f"  - ... and {remaining} more")
    if payload["supported_http_boundary"]["missing_routes"]:
        print()
        print("Missing supported HTTP routes")
        for route in payload["supported_http_boundary"]["missing_routes"]:
            print(f"  - {route}")
    excluded = payload["excluded_claims_expected_disputed"]
    if excluded:
        print()
        print("Excluded disputed claims")
        for claim_id, status in excluded.items():
            print(f"  - {claim_id}: {status}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check the conservative RC1 release boundary.")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.add_argument("--check", action="store_true", help="exit nonzero when RC1 is not yet ready")
    args = parser.parse_args(argv)

    try:
        payload = build_status_payload()
    except RC1Error as exc:
        if args.format == "json":
            print(json.dumps({"ok": False, "error": str(exc)}, indent=2, sort_keys=True))
        else:
            print(f"error: {exc}")
        return 1

    if args.format == "json":
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        _print_status(payload)

    if args.check and not payload["overall_ok"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
