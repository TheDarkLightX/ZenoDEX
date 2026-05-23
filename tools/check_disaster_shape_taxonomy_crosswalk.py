#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_scenario_bridge import DISASTER_SEARCH_EXPANSION_AXES
from tools.disaster_shape_types import (
    AxisId,
    CoveragePosture,
    CrosswalkEntry,
    CrosswalkEntryId,
    PublicSourceId,
    PublicSourceRef,
)


SCHEMA = "zenodex/disaster-shape-taxonomy-crosswalk/v1"
DEFAULT_CROSSWALK = REPO_ROOT / "tools" / "disaster_shape_taxonomy_crosswalk.json"
VALID_POSTURES = {
    "seed_only",
    "covered_axis_family",
    "backlog_axis_family",
    "out_of_scope",
}


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as fh:
        payload = json.load(fh)
    if not isinstance(payload, dict):
        raise TypeError("crosswalk root must be a JSON object")
    return payload


def _axis_ids() -> set[AxisId]:
    return {AxisId(str(axis["axis_id"])) for axis in DISASTER_SEARCH_EXPANSION_AXES}


def _parse_public_source(source: dict[str, Any]) -> PublicSourceRef | None:
    source_id = source.get("id")
    name = source.get("name")
    url = source.get("url")
    role = source.get("role")
    if not isinstance(source_id, str) or not source_id:
        return None
    if not isinstance(name, str) or not name:
        return None
    if not isinstance(url, str) or not url:
        return None
    if not isinstance(role, str) or not role:
        return None
    return PublicSourceRef(
        source_id=PublicSourceId(source_id),
        name=name,
        url=url,
        role=role,
    )


def _as_posture(value: object) -> CoveragePosture | None:
    if value in VALID_POSTURES:
        return cast(CoveragePosture, value)
    return None


def _parse_entry(entry: dict[str, Any]) -> CrosswalkEntry | None:
    entry_id = entry.get("id")
    source_families = entry.get("source_families")
    mapped_axis_ids = entry.get("mapped_axis_ids")
    posture = _as_posture(entry.get("coverage_posture"))
    what_if = entry.get("what_if")
    if not isinstance(entry_id, str) or not entry_id:
        return None
    if not isinstance(source_families, list) or not all(
        isinstance(item, str) and item for item in source_families
    ):
        return None
    if not isinstance(mapped_axis_ids, list) or not all(
        isinstance(item, str) and item for item in mapped_axis_ids
    ):
        return None
    if posture is None:
        return None
    if not isinstance(what_if, str) or not what_if:
        return None
    return CrosswalkEntry(
        entry_id=CrosswalkEntryId(entry_id),
        source_families=tuple(source_families),
        mapped_axis_ids=tuple(AxisId(axis_id) for axis_id in mapped_axis_ids),
        coverage_posture=posture,
        what_if=what_if,
    )


def check_crosswalk(path: Path = DEFAULT_CROSSWALK, *, allow_unmapped: bool = False) -> dict[str, Any]:
    payload = _load_json(path)
    known_axes = _axis_ids()
    errors: list[str] = []
    warnings: list[str] = []

    if payload.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA!r}")

    public_sources = payload.get("public_sources")
    if not isinstance(public_sources, list) or not public_sources:
        errors.append("public_sources must be a non-empty list")
        public_source_ids: set[PublicSourceId] = set()
    else:
        public_source_ids = set()
        for idx, source in enumerate(public_sources):
            if not isinstance(source, dict):
                errors.append(f"public_sources[{idx}] must be an object")
                continue
            typed_source = _parse_public_source(source)
            source_id = source.get("id")
            if not isinstance(source_id, str) or not source_id:
                errors.append(f"public_sources[{idx}].id must be a non-empty string")
                continue
            typed_source_id = PublicSourceId(source_id)
            if typed_source_id in public_source_ids:
                errors.append(f"duplicate public source id: {source_id}")
            public_source_ids.add(typed_source_id)
            if typed_source is None:
                errors.append(f"public_sources[{idx}] must have non-empty id, name, url, and role")
            if not isinstance(source.get("url"), str) or not str(source.get("url")).startswith(("https://", "http://")):
                errors.append(f"public_sources[{idx}].url must be an http(s) URL")

    entries = payload.get("entries")
    if not isinstance(entries, list) or not entries:
        errors.append("entries must be a non-empty list")
        entries = []

    seen_entry_ids: set[CrosswalkEntryId] = set()
    mapped_axes: set[AxisId] = set()
    unknown_axes: dict[str, list[AxisId]] = {}
    source_family_count = 0

    for idx, entry in enumerate(entries):
        if not isinstance(entry, dict):
            errors.append(f"entries[{idx}] must be an object")
            continue
        typed_entry = _parse_entry(entry)
        entry_id = entry.get("id")
        if not isinstance(entry_id, str) or not entry_id:
            errors.append(f"entries[{idx}].id must be a non-empty string")
            entry_id = f"<entry-{idx}>"
        typed_entry_id = CrosswalkEntryId(entry_id)
        if typed_entry_id in seen_entry_ids:
            errors.append(f"duplicate entry id: {entry_id}")
        seen_entry_ids.add(typed_entry_id)

        posture = entry.get("coverage_posture")
        if posture not in VALID_POSTURES:
            errors.append(f"{entry_id}.coverage_posture must be one of {sorted(VALID_POSTURES)}")
        if typed_entry is None:
            errors.append(f"{entry_id} is not a fully typed crosswalk entry")

        families = entry.get("source_families")
        if not isinstance(families, list) or not families:
            errors.append(f"{entry_id}.source_families must be a non-empty list")
        else:
            source_family_count += len(families)
            for family_idx, family in enumerate(families):
                if not isinstance(family, str) or not family.strip():
                    errors.append(f"{entry_id}.source_families[{family_idx}] must be a non-empty string")

        mapped = entry.get("mapped_axis_ids")
        if not isinstance(mapped, list) or not mapped:
            errors.append(f"{entry_id}.mapped_axis_ids must be a non-empty list")
            continue
        local_seen: set[AxisId] = set()
        for axis_idx, axis_id in enumerate(mapped):
            if not isinstance(axis_id, str) or not axis_id:
                errors.append(f"{entry_id}.mapped_axis_ids[{axis_idx}] must be a non-empty string")
                continue
            typed_axis_id = AxisId(axis_id)
            if typed_axis_id in local_seen:
                errors.append(f"{entry_id}.mapped_axis_ids contains duplicate axis {axis_id!r}")
            local_seen.add(typed_axis_id)
            if typed_axis_id not in known_axes:
                unknown_axes.setdefault(entry_id, []).append(typed_axis_id)
            else:
                mapped_axes.add(typed_axis_id)

        what_if = entry.get("what_if")
        if not isinstance(what_if, str) or not what_if.strip():
            errors.append(f"{entry_id}.what_if must be a non-empty string")

    for entry_id, axis_ids in sorted(unknown_axes.items()):
        errors.append(f"{entry_id} maps unknown axes: {', '.join(sorted(str(axis_id) for axis_id in axis_ids))}")

    unmapped_axes = sorted(str(axis_id) for axis_id in known_axes - mapped_axes)
    if unmapped_axes and not allow_unmapped:
        errors.append(f"unmapped current disaster axes: {', '.join(unmapped_axes)}")
    elif unmapped_axes:
        warnings.append(f"unmapped current disaster axes: {', '.join(unmapped_axes)}")

    orphan_mappings = sorted(str(axis_id) for axis_id in mapped_axes - known_axes)
    ok = not errors
    return {
        "schema": "zenodex/disaster-shape-taxonomy-crosswalk-check/v1",
        "ok": ok,
        "crosswalk_path": str(path),
        "entry_count": len(entries),
        "public_source_count": len(public_source_ids),
        "source_family_count": source_family_count,
        "known_axis_count": len(known_axes),
        "mapped_axis_count": len(mapped_axes),
        "unmapped_axis_count": len(unmapped_axes),
        "unmapped_axis_ids": unmapped_axes,
        "orphan_mapping_count": len(orphan_mappings),
        "orphan_mapping_ids": orphan_mappings,
        "errors": errors,
        "warnings": warnings,
    }


def _print_text(result: dict[str, Any]) -> None:
    print(f"ok: {result['ok']}")
    print(f"entry_count: {result['entry_count']}")
    print(f"public_source_count: {result['public_source_count']}")
    print(f"source_family_count: {result['source_family_count']}")
    print(f"known_axis_count: {result['known_axis_count']}")
    print(f"mapped_axis_count: {result['mapped_axis_count']}")
    print(f"unmapped_axis_count: {result['unmapped_axis_count']}")
    print(f"orphan_mapping_count: {result['orphan_mapping_count']}")
    for warning in result["warnings"]:
        print(f"warning: {warning}")
    for error in result["errors"]:
        print(f"error: {error}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "crosswalk",
        nargs="?",
        type=Path,
        default=DEFAULT_CROSSWALK,
        help="Path to disaster_shape_taxonomy_crosswalk.json",
    )
    parser.add_argument("--allow-unmapped", action="store_true")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    result = check_crosswalk(args.crosswalk, allow_unmapped=bool(args.allow_unmapped))
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        _print_text(result)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
