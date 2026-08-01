"""Check the H01 durable-retraction field-to-table matrix."""

from __future__ import annotations

import json
from dataclasses import fields
from pathlib import Path
from typing import Any, cast

from src.core.fcis_durable_retraction import PublicationAtomV1

ROOT = Path(__file__).resolve().parents[1]
MATRIX_PATH = ROOT / "docs/research/m6_tasks/TASK_H01_DRA_TABLE_MATRIX_V1.json"
EXPECTED_SCHEMA = "zenodex.fcis.m6.dra-table-matrix.v1"


def _mapping(value: object, label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise ValueError(f"{label} must be an object")
    return cast(dict[str, Any], value)


def _sequence(value: object, label: str) -> list[object]:
    if type(value) is not list:
        raise ValueError(f"{label} must be a list")
    return cast(list[object], value)


def _text(mapping: dict[str, Any], key: str, label: str) -> str:
    value = mapping.get(key)
    if type(value) is not str or not value:
        raise ValueError(f"{label}.{key} must be nonempty text")
    return value


def check_matrix() -> None:
    payload = _mapping(json.loads(MATRIX_PATH.read_text(encoding="utf-8")), "matrix")
    if _text(payload, "schema_version", "matrix") != EXPECTED_SCHEMA:
        raise ValueError("matrix schema is not the H01 schema")
    if _text(payload, "source_type", "matrix") != "PublicationAtomV1":
        raise ValueError("matrix source type is not PublicationAtomV1")

    entries = _sequence(payload.get("fields"), "fields")
    expected = tuple(item.name for item in fields(PublicationAtomV1))
    actual: list[str] = []
    for index, raw_entry in enumerate(entries):
        entry = _mapping(raw_entry, f"fields[{index}]")
        field_name = _text(entry, "field", f"fields[{index}]")
        if field_name in actual:
            raise ValueError(f"duplicate atom field: {field_name}")
        actual.append(field_name)
        role = _text(entry, "representation_role", f"fields[{index}]")
        if role not in {"canonical-column", "checked-projection"}:
            raise ValueError(f"unsupported representation role: {role}")
        _text(entry, "table", f"fields[{index}]")
        _text(entry, "locator", f"fields[{index}]")
        _text(entry, "checked_relation", f"fields[{index}]")

    if tuple(actual) != expected:
        raise ValueError(f"matrix fields differ from PublicationAtomV1: {actual!r} != {expected!r}")
    if len(entries) != len(expected):
        raise ValueError("matrix contains a non-exhaustive field count")
    print("H01_TABLE_MATRIX_MATCH")


if __name__ == "__main__":
    check_matrix()
