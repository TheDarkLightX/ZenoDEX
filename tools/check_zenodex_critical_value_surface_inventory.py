#!/usr/bin/env python3
"""Validate ZenoDEX critical value-surface source inventory."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

DEFAULT_MANIFEST = ROOT / "docs" / "ZENODEX_CRITICAL_VALUE_SURFACE_INVENTORY_V0.json"
DEFAULT_TRANSITION_CLOSURE = ROOT / "docs" / "ZENODEX_TRANSITION_PROFILE_CLOSURE_V0.json"
DEFAULT_HOST_COVERAGE = ROOT / "docs" / "ZENODEX_HOST_INDEPENDENT_COVERAGE_V0.json"

SCHEMA = "zenodex.critical_value_surface_inventory.v0"
REPORT_SCHEMA = "zenodex.critical_value_surface_inventory_report.v0"
CHECKER_COMMAND = "python3 tools/check_zenodex_critical_value_surface_inventory.py"
CHECKER_TEST_COMMAND = "pytest -q tests/tools/test_check_zenodex_critical_value_surface_inventory.py"

AUTHORITY_PUBLIC_DATA = {
    "deterministic_replay": "public_inputs_and_replay_artifacts",
    "zkvm_proof": "public_inputs_and_proof_artifacts",
}
UNSUPPORTED_AUTHORITY = "fail_closed_non_admitted"
REQUIRED_CLAIM_BOUNDARY = {
    "surface_inventory_scope": "critical_value_moving_runtime_and_proof_surfaces",
    "full_node_host_independence": "supported_scoped",
    "succinct_everything_host_independence": "frontier_open",
}
REQUIRED_CLAIM_BOUNDARY_FLAGS = {
    "source_inventory_is_claim_control",
    "unmapped_source_symbols_fail_closed",
    "ui_and_docs_do_not_authorize_transitions",
}

REQUIRED_TRANSITION_GROUP_IDS = {
    "spot_intent_full_node_replay_v1",
    "spot_v1_risc0_supported_transition_proof_v1",
    "upba_exact_out_full_node_replay_v1",
    "oracle_critical_action_full_node_replay_v1",
    "perps_bounded_full_node_replay_v1",
    "zusd_lifecycle_full_node_replay_v1",
    "proof_mining_reward_full_node_replay_v1",
}
REQUIRED_UNSUPPORTED_ENTRY_IDS = {
    "spot_v1_rejected_receipts_proof_rejected",
    "spot_v1_swap_exact_out_proof_rejected",
    "spot_v1_upba_batch_clearing_proof_rejected",
    "spot_v1_multi_hop_proof_rejected",
    "spot_v1_native_asset_sync_proof_rejected",
}


def validate_critical_value_surface_inventory_v0(
    manifest: Any,
    *,
    transition_closure_path: Path = DEFAULT_TRANSITION_CLOSURE,
    host_coverage_path: Path = DEFAULT_HOST_COVERAGE,
    repo_root: Path = ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != SCHEMA:
        errors.append("schema mismatch")

    transition_groups, unsupported_entries = _load_transition_closure(transition_closure_path, errors)
    _validate_claim_boundary(_mapping(obj.get("claim_boundary"), "claim_boundary", errors), errors)
    _validate_release_gates(obj.get("release_gates"), host_coverage_path, errors)

    critical_reports: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    inventory_ids: set[str] = set()
    mapped_group_ids: set[str] = set()
    mapped_families_by_group: dict[str, set[str]] = {}
    for index, raw_surface in enumerate(_list(obj.get("critical_source_surfaces"), "critical_source_surfaces", errors)):
        report = _validate_critical_source_surface(
            raw_surface,
            index=index,
            transition_groups=transition_groups,
            repo_root=repo_root,
        )
        critical_reports.append(report)
        errors.extend(f"critical_source_surfaces[{index}]: {error}" for error in report["errors"])
        surface_id = report["id"]
        if surface_id:
            if surface_id in seen_ids:
                errors.append(f"critical_source_surfaces[{index}]: duplicate id")
            seen_ids.add(surface_id)
            inventory_ids.add(surface_id)
        for group_id in report["transition_closure_group_ids"]:
            mapped_group_ids.add(group_id)
            mapped_families_by_group.setdefault(group_id, set()).update(report["families"])

    unsupported_reports: list[dict[str, Any]] = []
    mapped_unsupported_ids: set[str] = set()
    for index, raw_surface in enumerate(
        _list(obj.get("unsupported_source_surfaces"), "unsupported_source_surfaces", errors)
    ):
        report = _validate_unsupported_source_surface(
            raw_surface,
            index=index,
            unsupported_entries=unsupported_entries,
            repo_root=repo_root,
        )
        unsupported_reports.append(report)
        errors.extend(f"unsupported_source_surfaces[{index}]: {error}" for error in report["errors"])
        surface_id = report["id"]
        if surface_id:
            if surface_id in seen_ids:
                errors.append(f"unsupported_source_surfaces[{index}]: duplicate id")
            seen_ids.add(surface_id)
            inventory_ids.add(surface_id)
        mapped_unsupported_ids.update(report["unsupported_closure_entry_ids"])

    scan_reports: list[dict[str, Any]] = []
    for index, raw_query in enumerate(_list(obj.get("source_scan_queries"), "source_scan_queries", errors)):
        report = _validate_source_scan_query(
            raw_query,
            index=index,
            inventory_ids=inventory_ids,
            repo_root=repo_root,
        )
        scan_reports.append(report)
        errors.extend(f"source_scan_queries[{index}]: {error}" for error in report["errors"])

    missing_required_groups = sorted(REQUIRED_TRANSITION_GROUP_IDS - mapped_group_ids)
    if missing_required_groups:
        errors.append("missing required transition closure groups: " + ",".join(missing_required_groups))
    missing_closure_groups = sorted(set(transition_groups) - mapped_group_ids)
    if missing_closure_groups:
        errors.append("transition closure groups not mapped by source inventory: " + ",".join(missing_closure_groups))
    for group_id, group in sorted(transition_groups.items()):
        group_families = _str_set(group.get("families"), f"transition_groups[{group_id}].families", errors)
        missing_families = sorted(group_families - mapped_families_by_group.get(group_id, set()))
        if missing_families:
            errors.append(f"{group_id} families not mapped by source inventory: {','.join(missing_families)}")

    missing_required_unsupported = sorted(REQUIRED_UNSUPPORTED_ENTRY_IDS - mapped_unsupported_ids)
    if missing_required_unsupported:
        errors.append("missing required unsupported proof entries: " + ",".join(missing_required_unsupported))
    missing_unsupported = sorted(set(unsupported_entries) - mapped_unsupported_ids)
    if missing_unsupported:
        errors.append("unsupported proof entries not mapped by source inventory: " + ",".join(missing_unsupported))

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "critical_source_surface_count": len(critical_reports),
        "unsupported_source_surface_count": len(unsupported_reports),
        "closure_group_count": len(transition_groups),
        "mapped_closure_group_count": len(set(transition_groups) & mapped_group_ids),
        "unsupported_closure_entry_count": len(unsupported_entries),
        "mapped_unsupported_closure_entry_count": len(set(unsupported_entries) & mapped_unsupported_ids),
        "source_scan_query_count": len(scan_reports),
        "critical_source_surfaces": critical_reports,
        "unsupported_source_surfaces": unsupported_reports,
        "source_scan_queries": scan_reports,
    }


def _validate_claim_boundary(boundary: Mapping[str, Any], errors: list[str]) -> None:
    for key, expected in sorted(REQUIRED_CLAIM_BOUNDARY.items()):
        if boundary.get(key) != expected:
            errors.append(f"claim_boundary.{key} must be {expected}")
    for key in sorted(REQUIRED_CLAIM_BOUNDARY_FLAGS):
        if boundary.get(key) is not True:
            errors.append(f"claim_boundary.{key} must be true")


def _validate_release_gates(value: Any, host_coverage_path: Path, errors: list[str]) -> None:
    gates = _str_list(value, "release_gates", errors)
    for required in (CHECKER_COMMAND, CHECKER_TEST_COMMAND):
        if required not in gates:
            errors.append(f"release_gates missing: {required}")
    try:
        host = json.loads(host_coverage_path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"host coverage manifest load failed: {exc}")
        return
    host_gates = _str_list(
        host.get("release_gates") if isinstance(host, Mapping) else None,
        "host release_gates",
        errors,
    )
    if CHECKER_COMMAND not in host_gates:
        errors.append("host coverage release_gates must include critical value surface inventory checker")


def _validate_critical_source_surface(
    raw_surface: Any,
    *,
    index: int,
    transition_groups: Mapping[str, Mapping[str, Any]],
    repo_root: Path,
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    surface = _mapping(raw_surface, "critical_source_surface", errors)
    surface_id = _str(surface.get("id"), "id", errors)
    group_ids = _str_list(surface.get("transition_closure_group_ids"), "transition_closure_group_ids", errors)
    authority_mode = _str(surface.get("authority_mode"), "authority_mode", errors)
    public_data = _str(surface.get("public_data_availability"), "public_data_availability", errors)
    paths = _str_list(surface.get("paths"), "paths", errors)
    required_symbols = _str_list(surface.get("required_symbols"), "required_symbols", errors)
    families = _str_set(surface.get("families"), "families", errors)
    limits = _str_list(surface.get("limits"), "limits", errors)

    if authority_mode not in AUTHORITY_PUBLIC_DATA:
        errors.append(f"authority_mode has unsupported value: {authority_mode}")
    elif public_data != AUTHORITY_PUBLIC_DATA[authority_mode]:
        errors.append(f"{authority_mode} requires {AUTHORITY_PUBLIC_DATA[authority_mode]}")
    if public_data == "metadata_only_non_transition":
        errors.append("value-moving source inventory cannot use metadata_only_non_transition")
    if not group_ids:
        errors.append("transition_closure_group_ids must be non-empty")
    if not families:
        errors.append("families must be non-empty")
    if not limits:
        errors.append("limits must be non-empty")

    allowed_families: set[str] = set()
    for group_id in group_ids:
        group = transition_groups.get(group_id)
        if group is None:
            errors.append(f"transition_closure_group_ids missing from transition closure: {group_id}")
            continue
        allowed_families.update(_str_set(group.get("families"), f"transition_group[{group_id}].families", errors))
        group_mode = _str(group.get("admission_mode"), f"transition_group[{group_id}].admission_mode", errors)
        if authority_mode and group_mode and authority_mode != group_mode:
            errors.append(f"authority_mode does not match transition closure group {group_id}: {group_mode}")
    extra_families = sorted(families - allowed_families)
    if extra_families:
        errors.append("families not present in referenced transition closure groups: " + ",".join(extra_families))

    text = _repo_text_for_paths(paths, repo_root=repo_root, field_name="paths", errors=errors)
    for symbol in required_symbols:
        if symbol not in text:
            errors.append(f"required symbol not found in paths: {symbol}")

    return {
        "id": surface_id,
        "transition_closure_group_ids": group_ids,
        "authority_mode": authority_mode,
        "public_data_availability": public_data,
        "families": sorted(families),
        "ok": not errors,
        "errors": errors,
    }


def _validate_unsupported_source_surface(
    raw_surface: Any,
    *,
    index: int,
    unsupported_entries: Mapping[str, Mapping[str, Any]],
    repo_root: Path,
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    surface = _mapping(raw_surface, "unsupported_source_surface", errors)
    surface_id = _str(surface.get("id"), "id", errors)
    entry_ids = _str_list(surface.get("unsupported_closure_entry_ids"), "unsupported_closure_entry_ids", errors)
    authority_mode = _str(surface.get("authority_mode"), "authority_mode", errors)
    public_data = _str(surface.get("public_data_availability"), "public_data_availability", errors)
    paths = _str_list(surface.get("paths"), "paths", errors)
    required_symbols = _str_list(surface.get("required_symbols"), "required_symbols", errors)
    limits = _str_list(surface.get("limits"), "limits", errors)

    if authority_mode != UNSUPPORTED_AUTHORITY:
        errors.append(f"unsupported source surfaces must use {UNSUPPORTED_AUTHORITY}")
    if public_data != UNSUPPORTED_AUTHORITY:
        errors.append(f"unsupported source surfaces must use public_data_availability={UNSUPPORTED_AUTHORITY}")
    if not entry_ids:
        errors.append("unsupported_closure_entry_ids must be non-empty")
    if not limits:
        errors.append("limits must be non-empty")
    for entry_id in entry_ids:
        if entry_id not in unsupported_entries:
            errors.append(f"unsupported_closure_entry_ids missing from transition closure: {entry_id}")

    text = _repo_text_for_paths(paths, repo_root=repo_root, field_name="paths", errors=errors)
    for symbol in required_symbols:
        if symbol not in text:
            errors.append(f"required symbol not found in paths: {symbol}")

    return {
        "id": surface_id,
        "unsupported_closure_entry_ids": entry_ids,
        "authority_mode": authority_mode,
        "public_data_availability": public_data,
        "ok": not errors,
        "errors": errors,
    }


def _validate_source_scan_query(
    raw_query: Any,
    *,
    index: int,
    inventory_ids: set[str],
    repo_root: Path,
) -> dict[str, Any]:
    del index
    errors: list[str] = []
    query = _mapping(raw_query, "source_scan_query", errors)
    query_id = _str(query.get("id"), "id", errors)
    paths = _str_list(query.get("paths"), "paths", errors)
    tokens = _str_list(query.get("required_tokens"), "required_tokens", errors)
    mapped_ids = _str_list(query.get("mapped_inventory_ids"), "mapped_inventory_ids", errors)
    if not mapped_ids:
        errors.append("mapped_inventory_ids must be non-empty")
    missing_ids = sorted(set(mapped_ids) - inventory_ids)
    if missing_ids:
        errors.append("mapped_inventory_ids missing from inventory: " + ",".join(missing_ids))

    text = _repo_text_for_paths(paths, repo_root=repo_root, field_name="paths", errors=errors)
    for token in tokens:
        if token not in text:
            errors.append(f"required token not found in paths: {token}")

    return {
        "id": query_id,
        "mapped_inventory_ids": mapped_ids,
        "ok": not errors,
        "errors": errors,
    }


def _load_transition_closure(path: Path, errors: list[str]) -> tuple[dict[str, Mapping[str, Any]], dict[str, Mapping[str, Any]]]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError) as exc:
        errors.append(f"transition closure manifest load failed: {exc}")
        return {}, {}
    if not isinstance(obj, Mapping):
        errors.append("transition closure manifest must be an object")
        return {}, {}
    groups: dict[str, Mapping[str, Any]] = {}
    for raw_group in _list(obj.get("admitted_transition_families"), "admitted_transition_families", errors):
        if isinstance(raw_group, Mapping) and isinstance(raw_group.get("id"), str):
            groups[str(raw_group["id"])] = raw_group
    unsupported: dict[str, Mapping[str, Any]] = {}
    for raw_entry in _list(obj.get("unsupported_proof_required_families"), "unsupported_proof_required_families", errors):
        if isinstance(raw_entry, Mapping) and isinstance(raw_entry.get("id"), str):
            unsupported[str(raw_entry["id"])] = raw_entry
    return groups, unsupported


def _repo_text_for_paths(paths: list[str], *, repo_root: Path, field_name: str, errors: list[str]) -> str:
    if not paths:
        errors.append(f"{field_name} must be non-empty")
        return ""
    root = repo_root.resolve()
    chunks: list[str] = []
    for rel_path in paths:
        candidate = (repo_root / rel_path).resolve()
        try:
            candidate.relative_to(root)
        except ValueError:
            errors.append(f"{field_name} path escapes repo: {rel_path}")
            continue
        if not candidate.is_file():
            errors.append(f"{field_name} path missing: {rel_path}")
            continue
        try:
            chunks.append(candidate.read_text(encoding="utf-8"))
        except UnicodeDecodeError as exc:
            errors.append(f"{field_name} path is not utf-8 text: {rel_path}: {exc}")
        except OSError as exc:
            errors.append(f"{field_name} path could not be read: {rel_path}: {exc}")
    return "\n".join(chunks)


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    return value


def _str(value: Any, name: str, errors: list[str]) -> str:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return ""
    return value


def _str_list(value: Any, name: str, errors: list[str]) -> list[str]:
    items = _list(value, name, errors)
    out: list[str] = []
    for index, item in enumerate(items):
        parsed = _str(item, f"{name}[{index}]", errors)
        if parsed:
            out.append(parsed)
    return out


def _str_set(value: Any, name: str, errors: list[str]) -> set[str]:
    return set(_str_list(value, name, errors))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--transition-closure", type=Path, default=DEFAULT_TRANSITION_CLOSURE)
    parser.add_argument("--host-coverage", type=Path, default=DEFAULT_HOST_COVERAGE)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_critical_value_surface_inventory_v0(
        manifest,
        transition_closure_path=args.transition_closure,
        host_coverage_path=args.host_coverage,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
