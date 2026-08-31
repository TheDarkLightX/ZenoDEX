"""Fail-closed report construction for the reviewed O-007B manifest."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, cast

from tools.m6_cross_language_sinks.inventory import (
    MANIFEST_SCHEMA,
    build_cross_language_projection,
    compare_projection_to_manifest,
)

MANIFEST_NAME = "m6_cross_language_value_sink_manifest_v1.json"

NONCLAIMS = (
    "This inventory does not establish runtime reachability, mediation, sole-publisher closure, or production durability.",
    "Dynamic import declarations record exact observed sites; unresolved dispatch and indirect administrative reachability remain O-007C work.",
    "Tau outputs and RISC0 journals are proposals until a separately verified publication capability consumes them.",
    "Declared generated-code ownership is not a pinned generator replay and grants no proof or release authority.",
    "No production, settlement, release, mount, migration, or value-moving authority is granted.",
)


def render_manifest(root: Path) -> dict[str, object]:
    return {
        "nonclaims": list(NONCLAIMS),
        "projection": build_cross_language_projection(root),
        "review_status": "UNREVIEWED",
        "schema": MANIFEST_SCHEMA,
        "scope": (
            "Every Git-tracked Rust and Tau source; every .sh, shell-shebang, and Dockerfile "
            "source; generated Python reference code under generated/ and src/fire/kernel/; "
            "dynamic imports are observed in the O-007A Python deployment closure."
        ),
    }


def _load_manifest(path: Path) -> tuple[dict[str, Any] | None, list[str], str | None]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return None, [f"cannot read cross-language manifest: {exc}"], None
    digest = hashlib.sha256(raw).hexdigest()
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        return None, [f"cross-language manifest is not canonical JSON data: {exc}"], digest
    if not isinstance(value, dict):
        return None, ["cross-language manifest must be an object"], digest
    return value, [], digest


def build_cross_language_report(root: Path) -> dict[str, object]:
    root = root.resolve()
    projection = build_cross_language_projection(root)
    manifest, findings, manifest_sha256 = _load_manifest(root / "tools" / MANIFEST_NAME)
    discovery_findings = cast(list[str], projection["discovery_findings"])
    dynamic_imports = cast(list[dict[str, Any]], projection["dynamic_import_declarations"])
    generated_include_owners = cast(list[dict[str, str]], projection["generated_include_owners"])
    generated_python_owners = cast(list[dict[str, str]], projection["generated_python_owners"])
    findings.extend(discovery_findings)
    if manifest is not None:
        findings.extend(compare_projection_to_manifest(projection, manifest))
    findings = sorted(set(findings))
    unmediated = cast(int, projection["unmediated_operation_count"])
    generated_replay = cast(bool, projection["generated_replay_ownership_complete"])
    unresolved_imports = sum(1 for row in dynamic_imports if row["target_status"] == "UNRESOLVED")
    ok = not findings
    return {
        "dynamic_import_declaration_count": len(dynamic_imports),
        "findings": findings,
        "generated_include_owner_count": len(generated_include_owners),
        "generated_python_owner_count": len(generated_python_owners),
        "generated_replay_ownership_complete": generated_replay,
        "manifest_sha256": manifest_sha256,
        "nonclaims": list(NONCLAIMS),
        "ok": ok,
        "operation_occurrence_counts": projection["operation_occurrence_counts"],
        "operation_row_counts": projection["operation_row_counts"],
        "o007b_bounded_inventory_status": "COMPLETE" if ok else "OPEN",
        "production_authority": False,
        "projection_root": projection["projection_root"],
        "reviewed_projection_matches_current_subject": ok,
        "release_ready": ok and unmediated == 0 and generated_replay and unresolved_imports == 0,
        "schema": "zenodex/m6-cross-language-value-sink-check/v1",
        "source_counts": projection["source_counts"],
        "source_provenance_counts": projection["source_provenance_counts"],
        "tracked_candidate_count": projection["tracked_candidate_count"],
        "unmediated_operation_count": unmediated,
        "unresolved_dynamic_import_count": unresolved_imports,
        "vm01_status": "OPEN",
    }
