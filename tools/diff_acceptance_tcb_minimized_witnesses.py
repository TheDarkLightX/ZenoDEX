#!/usr/bin/env python3
"""Diff two acceptance TCB minimized witness indexes."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Sequence


DEFAULT_COMPARE_FIELDS: tuple[str, ...] = (
    "target",
    "derivation",
    "outcome_label",
    "path_id",
    "path_length",
    "original_size",
    "minimized_size",
)


def _load_index(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _witness_map(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(witness["id"]): witness for witness in payload.get("witnesses", [])}


def _project(witness: dict[str, Any], fields: Sequence[str]) -> dict[str, Any]:
    return {field: witness.get(field) for field in fields}


def diff_indexes(left: dict[str, Any], right: dict[str, Any], *, compare_fields: Sequence[str] = DEFAULT_COMPARE_FIELDS) -> dict[str, Any]:
    left_map = _witness_map(left)
    right_map = _witness_map(right)
    left_ids = set(left_map)
    right_ids = set(right_map)

    added = sorted(right_ids - left_ids)
    removed = sorted(left_ids - right_ids)
    common = sorted(left_ids & right_ids)

    changed: list[dict[str, Any]] = []
    unchanged: list[str] = []
    for witness_id in common:
        left_view = _project(left_map[witness_id], compare_fields)
        right_view = _project(right_map[witness_id], compare_fields)
        if left_view == right_view:
            unchanged.append(witness_id)
            continue
        field_changes = {
            field: {"left": left_view.get(field), "right": right_view.get(field)}
            for field in compare_fields
            if left_view.get(field) != right_view.get(field)
        }
        changed.append(
            {
                "id": witness_id,
                "left_campaign_report": left.get("campaign_report"),
                "right_campaign_report": right.get("campaign_report"),
                "fields": field_changes,
            }
        )

    return {
        "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-diff/v1",
        "compare_fields": list(compare_fields),
        "left_count": len(left_map),
        "right_count": len(right_map),
        "added": [{"id": witness_id, "witness": right_map[witness_id]} for witness_id in added],
        "removed": [{"id": witness_id, "witness": left_map[witness_id]} for witness_id in removed],
        "changed": changed,
        "unchanged": unchanged,
    }


def _print_text(left_path: Path, right_path: Path, diff: dict[str, Any]) -> None:
    print("Acceptance TCB Minimized Witness Diff")
    print(f"left: {left_path}")
    print(f"right: {right_path}")
    print(f"left_count: {diff['left_count']}")
    print(f"right_count: {diff['right_count']}")
    print(f"added: {len(diff['added'])}")
    print(f"removed: {len(diff['removed'])}")
    print(f"changed: {len(diff['changed'])}")
    print(f"unchanged: {len(diff['unchanged'])}")
    for item in diff["changed"]:
        print(f"- changed:{item['id']}")
        for field, values in sorted(item["fields"].items()):
            print(f"  {field}: {values['left']} -> {values['right']}")
    for item in diff["added"]:
        print(f"- added:{item['id']}")
    for item in diff["removed"]:
        print(f"- removed:{item['id']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--left", required=True, help="left minimized witness index JSON")
    parser.add_argument("--right", required=True, help="right minimized witness index JSON")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    left_path = Path(args.left)
    right_path = Path(args.right)
    diff = diff_indexes(_load_index(left_path), _load_index(right_path))
    if args.format == "json":
        print(json.dumps(diff, indent=2, sort_keys=True))
    else:
        _print_text(left_path, right_path, diff)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
