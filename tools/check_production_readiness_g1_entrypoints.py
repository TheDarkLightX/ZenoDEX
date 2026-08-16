#!/usr/bin/env python3
"""Check the exact-subject G1 mounted-entrypoint inventory.

The audit joins the frozen 33-command transition registry to the source-level
writer inventory and the M6 research publication surfaces.  It records the
candidate route, reference/durable research routes, and external-effect
journal without treating any of them as a production publication capability.
Dynamic imports, generated code, credentials, deployment wiring, and runtime
reachability remain explicit UNKNOWN surfaces.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_ENTRYPOINTS_V1.json"
BASE_SOURCE_SUBJECT = "e8059cb5e27e80c2f8ba627501d6097f3c5e6b0c"
SOURCE_SUBJECT = "5361df3ad977a53a7a773cc53730fc57405e25fc"
SCHEMA = "zenodex/production-readiness-g1-entrypoints/v1"
SOURCE_SUBJECT_ROLE = "RESEARCH_REPAIR_DESCENDANT_OVERLAY"
SOURCE_RELATION_SCOPE = "ANCESTRY_ONLY_RESEARCH_OVERLAY"

sys.path.insert(0, str(REPO_ROOT))

from tools import check_m6_writer_inventory as writer_inventory  # noqa: E402
from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402
from tools.production_readiness_g1_entrypoint_contract import (  # noqa: E402
    PINNED_PATHS,
    SOURCE_MARKERS,
    SURFACE_SPECS,
    WRITER_MANIFEST_PATH,
)

EXPECTED_COMMANDS = semantics.EXPECTED_COMMANDS
EXPECTED_DISABLED = semantics.EXPECTED_DISABLED

def _run_git(repo_root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _source_pins(repo_root: Path) -> list[dict[str, str]]:
    pins: list[dict[str, str]] = []
    for path in PINNED_PATHS:
        frozen = _run_git(repo_root, "show", f"{SOURCE_SUBJECT}:{path}").encode()
        current = (repo_root / path).read_bytes()
        if current != frozen:
            raise ValueError(f"source drift from frozen subject: {path}")
        pins.append({"path": path, "sha256": _sha256_bytes(frozen), "subject": SOURCE_SUBJECT})
    return pins


def _verify_repair_descends_from_base(repo_root: Path) -> None:
    relation = subprocess.run(
        ["git", "merge-base", "--is-ancestor", BASE_SOURCE_SUBJECT, SOURCE_SUBJECT],
        cwd=repo_root,
        check=False,
    )
    if relation.returncode != 0:
        raise ValueError("frozen repair source subject does not descend from the frozen base subject")


def _record_definition(definitions: dict[str, list[ast.AST]], name: str, node: ast.AST) -> None:
    definitions.setdefault(name, []).append(node)


def _class_method_definitions(node: ast.ClassDef) -> tuple[tuple[str, ast.AST], ...]:
    return tuple(
        (f"{node.name}.{child.name}", child)
        for child in node.body
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
    )


def _definition_pairs(tree: ast.Module) -> tuple[tuple[str, ast.AST], ...]:
    pairs: list[tuple[str, ast.AST]] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            pairs.append((node.name, node))
        elif isinstance(node, ast.ClassDef):
            pairs.extend(_class_method_definitions(node))
    return tuple(pairs)


def _definitions(tree: ast.Module) -> dict[str, tuple[ast.AST, ...]]:
    definitions: dict[str, list[ast.AST]] = {}
    for name, node in _definition_pairs(tree):
        _record_definition(definitions, name, node)
    return {name: tuple(nodes) for name, nodes in definitions.items()}


def _reexport_line(tree: ast.Module, symbol: str) -> int | None:
    for node in tree.body:
        if not isinstance(node, ast.ImportFrom):
            continue
        if any(alias.name == symbol for alias in node.names):
            return node.lineno
    return None


def _surface_observations(repo_root: Path) -> list[dict[str, Any]]:
    observations: list[dict[str, Any]] = []
    for spec in SURFACE_SPECS:
        path = str(spec["path"])
        source_path = repo_root / path
        tree = ast.parse(source_path.read_text(encoding="utf-8"), filename=path)
        if spec["kind"] == "reexport":
            line = _reexport_line(tree, str(spec["symbol"]))
            if line is None:
                raise ValueError(f"surface re-export is missing: {path}:{spec['symbol']}")
        else:
            qualified = (
                f"{spec['class']}.{spec['symbol']}"
                if spec["class"] is not None
                else str(spec["symbol"])
            )
            nodes = _definitions(tree).get(qualified, ())
            if len(nodes) != 1:
                raise ValueError(f"surface definition count is not one: {path}:{qualified}")
            line = getattr(nodes[0], "lineno", None)
        observations.append(
            {
                "authority": spec["authority"],
                "class": spec["class"],
                "id": spec["id"],
                "kind": spec["kind"],
                "line": line,
                "path": path,
                "status": spec["status"],
                "symbol": spec["symbol"],
            }
        )
    return observations


def _validate_source_markers(repo_root: Path) -> dict[str, list[str]]:
    observed: dict[str, list[str]] = {}
    for path, markers in SOURCE_MARKERS.items():
        source = (repo_root / path).read_text(encoding="utf-8")
        missing = [marker for marker in markers if marker not in source]
        if missing:
            raise ValueError(f"source markers missing from {path}: {missing}")
        observed[path] = list(markers)
    return observed


def _writer_inventory_summary(repo_root: Path) -> dict[str, Any]:
    report = writer_inventory.check_m6_writer_inventory(repo_root)
    if report["ok"] is not True:
        raise ValueError("source-level writer inventory is structurally invalid")
    statuses: dict[str, int] = {}
    for entry in report["entrypoints"]:
        status = str(entry["m6_mount_status"])
        statuses[status] = statuses.get(status, 0) + 1
    m6_entries = [
        {
            "class": entry["class"],
            "entrypoint_id": entry["entrypoint_id"],
            "m6_mount_status": entry["m6_mount_status"],
            "path": entry["path"],
            "symbol": entry["symbol"],
        }
        for entry in report["entrypoints"]
        if str(entry["path"]).startswith("src/core/m6_")
        or str(entry["path"]).startswith("src/integration/m6_")
    ]
    declared_production = [
        entry["entrypoint_id"]
        for entry in report["entrypoints"]
        if str(entry["m6_mount_status"]) not in {
            "M6_RESEARCH_ONLY",
            "SEPARATE_RESEARCH_NOT_M6",
            "UNMOUNTED_LEGACY",
        }
    ]
    return {
        "manifest": WRITER_MANIFEST_PATH,
        "manifest_checker_ok": report["ok"],
        "entrypoint_count": report["entrypoint_count"],
        "unmounted_entrypoint_count": report["unmounted_entrypoint_count"],
        "coverage_row_count": report["coverage_row_count"],
        "open_coverage_count": report["open_coverage_count"],
        "release_ready": report["release_ready"],
        "m6_production_mounted": report["m6_production_mounted"],
        "production_authority": report["production_authority"],
        "mount_status_counts": dict(sorted(statuses.items())),
        "m6_entrypoints": sorted(m6_entries, key=lambda entry: str(entry["entrypoint_id"])),
        "declared_production_entrypoint_ids": sorted(declared_production),
    }


def _command_routes(semantic_document: Mapping[str, Any]) -> list[dict[str, Any]]:
    entries = semantic_document["command_registry"]
    if len(entries) != len(EXPECTED_COMMANDS):
        raise ValueError("semantic registry does not cover the exact command count")
    routes: list[dict[str, Any]] = []
    for entry in entries:
        routes.append(
            {
                "id": entry["id"],
                "enum_member": entry["enum_member"],
                "workflow_family": entry["workflow_family"],
                "disabled_by_frozen_source": entry["id"]
                in {command.value for command in EXPECTED_DISABLED},
                "core_transition": entry["core_transition"],
                "core_transition_status": entry["core_transition_status"],
                "candidate_surface": "src/core/m6_safe_mount_transition_v1.py:run_m6_transition_v1",
                "reference_publication_routes": [
                    "src/integration/m6_commit_port_v1.py:M6CommitPortV1.publish",
                    "src/integration/m6_durable_store_v1.py:M6DurableLedgerStoreV1.publish",
                ],
                "mounted_entrypoint": "UNMOUNTED_RESEARCH_ONLY",
                "production_writer_declared": False,
                "status": "GAP_OPEN_PROFILE_DECISION_AND_PRODUCTION_MOUNT",
            }
        )
    return routes


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    _verify_repair_descends_from_base(repo_root)
    source_pins = _source_pins(repo_root)
    semantic_document = semantics.build_document(repo_root)
    source_markers = _validate_source_markers(repo_root)
    surfaces = _surface_observations(repo_root)
    writer_summary = _writer_inventory_summary(repo_root)
    command_routes = _command_routes(semantic_document)
    if len(command_routes) != 33:
        raise ValueError("entrypoint audit did not produce the exact 33 command routes")
    if writer_summary["declared_production_entrypoint_ids"]:
        raise ValueError("research writer inventory unexpectedly declares a production entrypoint")
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_ENTRYPOINT_AUDIT_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": {
            "base_commit": BASE_SOURCE_SUBJECT,
            "repair_commit": SOURCE_SUBJECT,
            "subject_role": SOURCE_SUBJECT_ROLE,
            "base_to_repair_relation": {
                "base_is_ancestor_of_repair": True,
                "relation_scope": SOURCE_RELATION_SCOPE,
                "semantic_equivalence": "NOT_PROVED",
            },
            "base_semantics_artifacts_remain_authoritative": True,
            "current_head_must_descend_from_base": True,
            "current_source_pins_subject": SOURCE_SUBJECT,
            "source_authority": "frozen source bytes at the exact verified repair descendant",
        },
        "source_pins": source_pins,
        "source_evidence_method": "AST_DEFINITION_INVENTORY_AND_SOURCE_LEVEL_WRITER_MANIFEST",
        "source_markers": source_markers,
        "surface_inventory": surfaces,
        "writer_inventory": writer_summary,
        "command_routes": command_routes,
        "production_publication_capability": {
            "status": "NONE_DECLARED_BY_EXACT_SOURCE_LEVEL_INVENTORY",
            "declared_production_entrypoint_count": 0,
            "reference_and_durable_routes_are_research_only": True,
            "finality_verifier_implementation": "PORT_ONLY_NO_IMPLEMENTATION",
            "dynamic_runtime_reachability": "UNKNOWN_NOT_CHECKED",
            "generated_code_and_deployment_wiring": "UNKNOWN_NOT_CHECKED",
            "required_before_mount": [
                "selected profile and beneficial owner for every enabled command",
                "production ZenoLedger publication capability with finality authority",
                "one exact writer route for every enabled value-moving command",
                "no-bypass evidence covering legacy and generated entrypoints",
                "terminal, migration, and replay evidence for every enabled route",
            ],
        },
        "g1_exit_gate": {
            "complete": False,
            "status": "BLOCKED_NO_DECLARED_PRODUCTION_WRITER_AND_OPEN_PROFILE_DECISIONS",
            "command_count": len(command_routes),
            "command_routes_with_core_handlers": len(command_routes),
            "command_routes_with_declared_production_writer": 0,
            "writer_inventory_unmounted_entrypoint_count": writer_summary["unmounted_entrypoint_count"],
            "claim": "The static route inventory is exact and research-only; no production mount is evidenced.",
        },
        "nonclaims": [
            "Static definition presence does not prove dynamic reachability or deployment wiring.",
            "The writer inventory is source-level and does not cover generated code, credentials, workers, or database callers.",
            "A reference commit port, durable filesystem store, or outbox journal is not a production ZenoLedger writer.",
            "This audit does not implement, prove, mount, or authorize any command.",
            "A passing audit does not establish M6Ready or production readiness.",
        ],
    }


def _load(path: Path) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    with path.open(encoding="utf-8") as stream:
        value = json.load(stream, object_pairs_hook=hook)
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(value, dict):
        raise ValueError("artifact root must be an object")
    return value


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(_encoded(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def check_artifact(path: Path, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    observed: dict[str, Any] = {}
    repair_relation = subprocess.run(
        ["git", "merge-base", "--is-ancestor", BASE_SOURCE_SUBJECT, SOURCE_SUBJECT],
        cwd=repo_root,
        check=False,
    )
    if repair_relation.returncode != 0:
        errors.append("frozen repair source subject does not descend from the frozen base subject")
    for label, subject in (("base", BASE_SOURCE_SUBJECT), ("repair", SOURCE_SUBJECT)):
        ancestry = subprocess.run(
            ["git", "merge-base", "--is-ancestor", subject, "HEAD"],
            cwd=repo_root,
            check=False,
        )
        if ancestry.returncode != 0:
            errors.append(f"current HEAD does not descend from the frozen {label} source subject")
    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if observed != expected:
            errors.append("artifact differs from the exact-subject generated entrypoint audit")
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))

    routes = observed.get("command_routes")
    route_count = len(routes) if isinstance(routes, list) else 0
    production_writer_count = (
        sum(1 for route in routes if isinstance(route, dict) and route.get("production_writer_declared") is True)
        if isinstance(routes, list)
        else 0
    )
    writer_inventory_observed = observed.get("writer_inventory")
    unmounted_count = (
        writer_inventory_observed.get("unmounted_entrypoint_count", 0)
        if isinstance(writer_inventory_observed, dict)
        else 0
    )
    return {
        "schema": "zenodex/production-readiness-g1-entrypoints-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "command_route_count": route_count,
        "declared_production_writer_count": production_writer_count,
        "writer_inventory_unmounted_entrypoint_count": unmounted_count,
        "surface_count": len(observed.get("surface_inventory", []))
        if isinstance(observed.get("surface_inventory"), list)
        else 0,
        "errors": errors,
        "nonclaim": "PASS means only that the research entrypoint audit is exact and source-bound; it does not promote a mount or production readiness.",
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, build_document(args.repo_root))
    report = check_artifact(args.output, args.repo_root)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("PASS" if report["ok"] else "FAIL")
        for error in report["errors"]:
            print(f"error: {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
