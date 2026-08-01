#!/usr/bin/env python3
"""Build an independently anchored M6 D05 publisher inventory.

The configuration is a reviewed deployment/build input. The builder reads and
hashes every declared source file, constructs typed values, and derives the
inventory and topology roots without accepting a TCG certificate or any root
from the runtime candidate under review.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.core.fcis_tcg_inventory import (  # noqa: E402
    FCISM6TCGInventoryError,
    PublisherKindV1,
    PublisherSpecV1,
    ReviewedSourceV1,
    TCGPublisherInventoryV1,
    inventory_payload_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_tcg_inventory_v1.json")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_D05_TCG_INVENTORY_VECTOR.json")
_CONFIG_SCHEMA = "zenodex/fcis/m6/d05/tcg-publisher-inventory-config/v1"


class DuplicateJsonKey(ValueError):
    """Raised when the reviewed JSON configuration repeats a field."""


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateJsonKey(key)
        result[key] = value
    return result


def _load_json(path: Path) -> dict[str, object]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_strict_object,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateJsonKey) as exc:
        raise FCISM6TCGInventoryError(
            f"inventory configuration is not strict JSON: {path}"
        ) from exc
    if type(value) is not dict:
        raise FCISM6TCGInventoryError("inventory configuration must be an object")
    return cast(dict[str, object], value)


def _exact_str(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise FCISM6TCGInventoryError(f"{name} must be a nonempty string")
    return value


def _relative_path(value: object, name: str) -> str:
    path = _exact_str(value, name)
    if "\\" in path or path.startswith("/"):
        raise FCISM6TCGInventoryError(f"{name} must be a POSIX relative path")
    parts = path.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise FCISM6TCGInventoryError(f"{name} is not a canonical relative path")
    return path


def _object_list(value: object, name: str) -> tuple[dict[str, object], ...]:
    if type(value) is not list:
        raise FCISM6TCGInventoryError(f"{name} must be a JSON array")
    rows: list[dict[str, object]] = []
    for index, item in enumerate(value):
        if type(item) is not dict:
            raise FCISM6TCGInventoryError(f"{name}[{index}] must be an object")
        rows.append(cast(dict[str, object], item))
    return tuple(rows)


def _string_list(value: object, name: str) -> tuple[str, ...]:
    if type(value) is not list:
        raise FCISM6TCGInventoryError(f"{name} must be a JSON array")
    return tuple(_relative_path(item, f"{name}[{index}]") for index, item in enumerate(value))


def _resolve_source(path: str) -> Path:
    candidate = (_REPO_ROOT / path).resolve()
    try:
        candidate.relative_to(_REPO_ROOT)
    except ValueError as exc:
        raise FCISM6TCGInventoryError(f"source resolves outside the repository: {path}") from exc
    if not candidate.is_file():
        raise FCISM6TCGInventoryError(f"declared source is not a regular file: {path}")
    return candidate


def _source_sha256(path: Path) -> tuple[str, int]:
    raw = path.read_bytes()
    return hashlib.sha256(raw).hexdigest(), len(raw)


def _load_inventory(config_path: Path) -> TCGPublisherInventoryV1:
    config_bytes = config_path.read_bytes()
    raw = _load_json(config_path)
    expected_fields = {"schema", "profile_id", "deployment_sources", "publishers"}
    if set(raw) != expected_fields:
        raise FCISM6TCGInventoryError("inventory configuration fields are not exact")
    if raw["schema"] != _CONFIG_SCHEMA:
        raise FCISM6TCGInventoryError("inventory configuration schema is wrong")
    profile_id = _exact_str(raw["profile_id"], "profile_id")
    deployment_rows = _object_list(raw["deployment_sources"], "deployment_sources")
    deployment_paths: list[str] = []
    purposes: dict[str, set[str]] = {}
    for index, row in enumerate(deployment_rows):
        if set(row) != {"path", "purpose"}:
            raise FCISM6TCGInventoryError(f"deployment_sources[{index}] fields are not exact")
        path = _relative_path(row["path"], f"deployment_sources[{index}].path")
        purpose = _exact_str(row["purpose"], f"deployment_sources[{index}].purpose")
        deployment_paths.append(path)
        purposes.setdefault(path, set()).add(purpose)
    publisher_rows = _object_list(raw["publishers"], "publishers")
    publishers: list[PublisherSpecV1] = []
    for index, row in enumerate(publisher_rows):
        expected = {
            "publisher_id",
            "kind",
            "entrypoint",
            "source_paths",
            "effect_capable",
            "authority_sink",
        }
        if set(row) != expected:
            raise FCISM6TCGInventoryError(f"publishers[{index}] fields are not exact")
        kind_raw = _exact_str(row["kind"], f"publishers[{index}].kind")
        try:
            kind = PublisherKindV1(kind_raw)
        except ValueError as exc:
            raise FCISM6TCGInventoryError(f"publishers[{index}].kind is not supported") from exc
        source_paths = _string_list(
            row["source_paths"],
            f"publishers[{index}].source_paths",
        )
        publisher_id = _exact_str(
            row["publisher_id"],
            f"publishers[{index}].publisher_id",
        )
        for path in source_paths:
            purposes.setdefault(path, set()).add(f"publisher:{publisher_id}")
        if type(row["effect_capable"]) is not bool:
            raise FCISM6TCGInventoryError(f"publishers[{index}].effect_capable must be a bool")
        if type(row["authority_sink"]) is not bool:
            raise FCISM6TCGInventoryError(f"publishers[{index}].authority_sink must be a bool")
        publishers.append(
            PublisherSpecV1(
                publisher_id=publisher_id,
                kind=kind,
                entrypoint=_exact_str(
                    row["entrypoint"],
                    f"publishers[{index}].entrypoint",
                ),
                source_paths=source_paths,
                effect_capable=row["effect_capable"],
                authority_sink=row["authority_sink"],
            )
        )
    config_rel = config_path.relative_to(_REPO_ROOT).as_posix()
    purposes.setdefault(config_rel, set()).add("inventory_configuration")
    all_source_paths = tuple(sorted(purposes, key=lambda item: item.encode("utf-8")))
    sources: list[ReviewedSourceV1] = []
    for path in all_source_paths:
        source_sha256, source_bytes = _source_sha256(_resolve_source(path))
        purpose = ",".join(sorted(purposes[path], key=lambda item: item.encode("utf-8")))
        sources.append(
            ReviewedSourceV1(
                path=path,
                purpose=purpose,
                source_sha256=source_sha256,
                source_bytes=source_bytes,
            )
        )
    return TCGPublisherInventoryV1(
        profile_id=profile_id,
        configuration_path=config_rel,
        configuration_sha256=hashlib.sha256(config_bytes).hexdigest(),
        deployment_source_paths=tuple(deployment_paths),
        sources=tuple(sources),
        publishers=tuple(publishers),
    )


def build_payload(config_path: Path = _REPO_ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Build the D05 payload from configuration and current source bytes."""

    config = config_path.resolve()
    try:
        config.relative_to(_REPO_ROOT)
    except ValueError as exc:
        raise FCISM6TCGInventoryError("configuration must be inside the repository") from exc
    return inventory_payload_v1(_load_inventory(config))


def _write_payload(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload) + b"\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG_PATH)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT_PATH)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    config = args.config if args.config.is_absolute() else _REPO_ROOT / args.config
    output = args.output if args.output.is_absolute() else _REPO_ROOT / args.output
    payload = build_payload(config)
    if args.check:
        expected = output.read_bytes()
        actual = canonical_json_bytes(payload) + b"\n"
        if expected != actual:
            raise SystemExit("FAIL: D05 inventory vector is stale")
    else:
        _write_payload(output, payload)
    print(
        "D05_TCG_INVENTORY_MATCH",
        payload["topology_root"],
        payload["publisher_inventory_root"],
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
