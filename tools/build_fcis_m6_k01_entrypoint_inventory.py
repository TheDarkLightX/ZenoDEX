"""Build the source-bound K01 value-moving entrypoint inventory."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    FCIS_M6_K01_CONFIG_SCHEMA_V1,
    FCISM6K01Error,
    K01CommitRequirementV1,
    K01CoverageNoteV1,
    K01CoverageStatusV1,
    K01EntrypointV1,
    K01InventoryV1,
    K01LegacyStatusV1,
    K01NoteDispositionV1,
    K01ReachabilityV1,
    K01SourceV1,
    K01SurfaceKindV1,
    inventory_payload_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_k01_entrypoint_inventory_v1.json")
DEFAULT_OUTPUT_PATH = Path(
    "docs/research/m6_tasks/TASK_K01_VALUE_MOVING_ENTRYPOINT_INVENTORY_V1.json"
)


class _DuplicateJsonKey(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateJsonKey(key)
        result[key] = value
    return result


def _load_json(path: Path) -> dict[str, object]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object)
    except (OSError, UnicodeError, json.JSONDecodeError, _DuplicateJsonKey) as exc:
        raise FCISM6K01Error(f"strict JSON load failed for {path}") from exc
    if type(value) is not dict:
        raise FCISM6K01Error(f"JSON root is not an object: {path}")
    return cast(dict[str, object], value)


def _text(value: object, name: str, *, max_bytes: int = 512) -> str:
    if type(value) is not str or not value:
        raise FCISM6K01Error(f"{name} must be a nonempty string")
    if len(value.encode("utf-8")) > max_bytes:
        raise FCISM6K01Error(f"{name} exceeds its byte bound")
    return value


def _path(value: object, name: str) -> str:
    path = _text(value, name)
    if "\\" in path or path.startswith("/") or ".." in Path(path).parts:
        raise FCISM6K01Error(f"{name} must be a safe repository-relative path")
    if any(part in {"", "."} for part in path.split("/")):
        raise FCISM6K01Error(f"{name} is not canonical")
    return path


def _path_list(value: object, name: str, *, allow_empty: bool = False) -> tuple[str, ...]:
    if type(value) is not list:
        raise FCISM6K01Error(f"{name} must be a JSON array")
    if not allow_empty and not value:
        raise FCISM6K01Error(f"{name} must be nonempty")
    values = tuple(_path(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(values)) != len(values):
        raise FCISM6K01Error(f"{name} contains duplicates")
    if values != tuple(sorted(values, key=lambda item: item.encode("utf-8"))):
        raise FCISM6K01Error(f"{name} is not canonically ordered")
    return values


def _object_list(value: object, name: str) -> tuple[dict[str, object], ...]:
    if type(value) is not list:
        raise FCISM6K01Error(f"{name} must be a JSON array")
    rows: list[dict[str, object]] = []
    for index, item in enumerate(value):
        if type(item) is not dict:
            raise FCISM6K01Error(f"{name}[{index}] must be an object")
        rows.append(cast(dict[str, object], item))
    return tuple(rows)


def _resolve_source(path: str) -> Path:
    candidate = (_ROOT / path).resolve()
    try:
        candidate.relative_to(_ROOT)
    except ValueError as exc:
        raise FCISM6K01Error(f"source escapes repository: {path}") from exc
    if not candidate.is_file():
        raise FCISM6K01Error(f"source is not a regular file: {path}")
    return candidate


def _source_digest(path: Path) -> tuple[str, int]:
    raw = path.read_bytes()
    return hashlib.sha256(raw).hexdigest(), len(raw)


def _load_entrypoint(row: dict[str, object], index: int) -> K01EntrypointV1:
    expected = {
        "publisher_id",
        "kind",
        "symbol_path",
        "caller",
        "input_type",
        "state_effect_touched",
        "required_anf_commit_port_call",
        "legacy_status",
        "runtime_reachability_evidence",
        "value_moving",
        "authority_sink",
        "source_paths",
    }
    if set(row) != expected:
        raise FCISM6K01Error(f"entrypoints[{index}] fields are not exact")
    try:
        kind = K01SurfaceKindV1(_text(row["kind"], f"entrypoints[{index}].kind"))
        requirement = K01CommitRequirementV1(
            _text(
                row["required_anf_commit_port_call"],
                f"entrypoints[{index}].required_anf_commit_port_call",
            )
        )
        legacy_status = K01LegacyStatusV1(
            _text(row["legacy_status"], f"entrypoints[{index}].legacy_status")
        )
        reachability = K01ReachabilityV1(
            _text(
                row["runtime_reachability_evidence"],
                f"entrypoints[{index}].runtime_reachability_evidence",
            )
        )
    except ValueError as exc:
        raise FCISM6K01Error(f"entrypoints[{index}] has an unsupported enum") from exc
    if type(row["value_moving"]) is not bool or type(row["authority_sink"]) is not bool:
        raise FCISM6K01Error(f"entrypoints[{index}] booleans are not exact")
    return K01EntrypointV1(
        publisher_id=_text(row["publisher_id"], f"entrypoints[{index}].publisher_id"),
        kind=kind,
        symbol_path=_text(row["symbol_path"], f"entrypoints[{index}].symbol_path"),
        caller=_text(row["caller"], f"entrypoints[{index}].caller"),
        input_type=_text(row["input_type"], f"entrypoints[{index}].input_type"),
        state_effect_touched=_text(
            row["state_effect_touched"],
            f"entrypoints[{index}].state_effect_touched",
        ),
        required_anf_commit_port_call=requirement,
        legacy_status=legacy_status,
        runtime_reachability_evidence=reachability,
        value_moving=row["value_moving"],
        authority_sink=row["authority_sink"],
        source_paths=_path_list(row["source_paths"], f"entrypoints[{index}].source_paths"),
    )


def _load_note(row: dict[str, object], index: int) -> K01CoverageNoteV1:
    expected = {"surface_id", "disposition", "reason", "paths"}
    if set(row) != expected:
        raise FCISM6K01Error(f"coverage_notes[{index}] fields are not exact")
    try:
        disposition = K01NoteDispositionV1(
            _text(row["disposition"], f"coverage_notes[{index}].disposition")
        )
    except ValueError as exc:
        raise FCISM6K01Error(f"coverage_notes[{index}] has an unsupported disposition") from exc
    return K01CoverageNoteV1(
        surface_id=_text(row["surface_id"], f"coverage_notes[{index}].surface_id"),
        disposition=disposition,
        reason=_text(row["reason"], f"coverage_notes[{index}].reason", max_bytes=2048),
        paths=_path_list(row["paths"], f"coverage_notes[{index}].paths", allow_empty=True),
    )


def _load_inventory(config_path: Path) -> K01InventoryV1:
    config_bytes = config_path.read_bytes()
    raw = _load_json(config_path)
    expected = {
        "schema",
        "profile_id",
        "coverage_status",
        "deployment_source_paths",
        "entrypoints",
        "coverage_notes",
    }
    if set(raw) != expected:
        raise FCISM6K01Error("K01 configuration fields are not exact")
    if raw["schema"] != FCIS_M6_K01_CONFIG_SCHEMA_V1:
        raise FCISM6K01Error("K01 configuration schema is wrong")
    try:
        coverage_status = K01CoverageStatusV1(_text(raw["coverage_status"], "coverage_status"))
    except ValueError as exc:
        raise FCISM6K01Error("unsupported K01 coverage status") from exc
    config_rel = config_path.relative_to(_ROOT).as_posix()
    purposes: dict[str, set[str]] = {config_rel: {"inventory_configuration"}}
    deployment_paths = _path_list(raw["deployment_source_paths"], "deployment_source_paths")
    for path in deployment_paths:
        purposes.setdefault(path, set()).add("deployment_or_build_surface")
    entrypoints = tuple(
        sorted(
            (
                _load_entrypoint(row, index)
                for index, row in enumerate(_object_list(raw["entrypoints"], "entrypoints"))
            ),
            key=lambda item: item.publisher_id.encode("utf-8"),
        )
    )
    for entrypoint in entrypoints:
        for path in entrypoint.source_paths:
            purposes.setdefault(path, set()).add(f"publisher:{entrypoint.publisher_id}")
    notes = tuple(
        sorted(
            (
                _load_note(row, index)
                for index, row in enumerate(_object_list(raw["coverage_notes"], "coverage_notes"))
            ),
            key=lambda item: item.surface_id.encode("utf-8"),
        )
    )
    sources: list[K01SourceV1] = []
    for path in sorted(purposes, key=lambda item: item.encode("utf-8")):
        digest, byte_count = _source_digest(_resolve_source(path))
        sources.append(
            K01SourceV1(
                path=path,
                purpose=",".join(sorted(purposes[path], key=lambda item: item.encode("utf-8"))),
                source_sha256=digest,
                source_bytes=byte_count,
            )
        )
    return K01InventoryV1(
        profile_id=_text(raw["profile_id"], "profile_id"),
        configuration_path=config_rel,
        configuration_sha256=hashlib.sha256(config_bytes).hexdigest(),
        coverage_status=coverage_status,
        deployment_source_paths=deployment_paths,
        sources=tuple(sources),
        entrypoints=entrypoints,
        coverage_notes=notes,
    )


def build_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Build K01 evidence from the configuration and current source bytes."""

    config = config_path.resolve()
    try:
        config.relative_to(_ROOT)
    except ValueError as exc:
        raise FCISM6K01Error("configuration must be inside the repository") from exc
    return inventory_payload_v1(_load_inventory(config))


def _write_payload(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload) + b"\n")


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    config = _ROOT / DEFAULT_CONFIG_PATH
    output = _ROOT / DEFAULT_OUTPUT_PATH
    check = False
    index = 0
    while index < len(args):
        token = args[index]
        if token == "--check":
            check = True
        elif token == "--config" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            config = candidate if candidate.is_absolute() else _ROOT / candidate
        elif token == "--output" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            output = candidate if candidate.is_absolute() else _ROOT / candidate
        else:
            raise SystemExit(f"unknown or incomplete argument: {token}")
        index += 1
    payload = build_payload(config)
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: K01 entrypoint inventory vector is stale")
    else:
        _write_payload(output, payload)
    print("K01_ENTRYPOINT_INVENTORY_MATCH", payload["entrypoint_inventory_root"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
