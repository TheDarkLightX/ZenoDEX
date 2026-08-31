"""Exact finite-model and state-boundary bindings for complete BVA surfaces."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, cast

import yaml

from tools.bva.critical_surface_coverage_common_v1 import (
    CoverageManifestError,
    exact_keys,
    load_json_object,
    object_value,
    relative_repo_path,
    repo_file,
    require,
    sha256_canonical_json,
    sha256_file,
    string_list,
    valid_sha256,
)

STATE_BOUNDARY_SCHEMA = "zenodex/ml-boundary-bva/v1"
STATE_BOUNDARY_METHOD = "esso_z3_exact_state_edge_obligations_v3"
SOURCE_MODEL_KEYS = frozenset(
    {"path", "sha256", "require_bounded_scalars", "state_boundary_evidence"}
)
STATE_EVIDENCE_KEYS = frozenset({"path", "require_no_unresolved"})


class _UniqueKeyLoader(yaml.SafeLoader):
    pass


def _construct_unique_mapping(
    loader: _UniqueKeyLoader,
    node: yaml.nodes.MappingNode,
    deep: bool = False,
) -> dict[object, object]:
    result: dict[object, object] = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        try:
            duplicate = key in result
        except TypeError as exc:
            raise CoverageManifestError("source model has a non-scalar mapping key") from exc
        require(not duplicate, f"source model has duplicate YAML key: {key}")
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


_UniqueKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
    _construct_unique_mapping,
)


def _load_source_model(path: Path, *, context: str) -> Mapping[str, Any]:
    try:
        value = yaml.load(path.read_text(encoding="utf-8"), Loader=_UniqueKeyLoader)
    except CoverageManifestError:
        raise
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise CoverageManifestError(f"{context}: failed to load source model: {exc}") from exc
    return object_value(value, context=context)


def _expected_state_targets(
    state_vars: list[Mapping[str, Any]],
    *,
    surface_id: str,
) -> tuple[dict[tuple[str, int], tuple[str, ...]], int]:
    expected: dict[tuple[str, int], tuple[str, ...]] = {}
    labeled_count = 0
    for state_var in state_vars:
        type_obj = object_value(state_var.get("type"), context=f"{surface_id}.source.state_type")
        if type_obj.get("kind") != "int":
            continue
        field, low, high = (
            state_var.get("id"),
            type_obj.get("min"),
            type_obj.get("max"),
        )
        require(
            type(field) is str and type(low) is int and type(high) is int and low <= high,
            f"{surface_id}: malformed integer state boundary",
        )
        field_str = cast(str, field)
        low_int = cast(int, low)
        high_int = cast(int, high)
        labels_by_value: dict[int, list[str]] = {}
        for label, boundary in (
            ("min", low_int),
            ("min+1", min(low_int + 1, high_int)),
            ("max-1", max(high_int - 1, low_int)),
            ("max", high_int),
        ):
            labeled_count += 1
            labels_by_value.setdefault(boundary, []).append(label)
        for boundary, labels in labels_by_value.items():
            expected[(field_str, boundary)] = tuple(labels)
    return expected, labeled_count


def _check_witness(
    row: Mapping[str, Any],
    *,
    field: str,
    value: int,
    surface_id: str,
) -> None:
    pre_state = object_value(row.get("pre_state"), context=f"{surface_id}.witness.pre_state")
    require(pre_state.get(field) == value, f"{surface_id}: witness misses its boundary")
    require(
        row.get("witness_sha256") == sha256_canonical_json(pre_state),
        f"{surface_id}: state boundary witness hash mismatch",
    )


def _check_infeasible(row: Mapping[str, Any], *, surface_id: str) -> None:
    require(
        row.get("solver_result") == "unsat"
        and row.get("constraint_scope") == "state_domains_and_all_invariants",
        f"{surface_id}: infeasible target lacks exact model-UNSAT evidence",
    )


def _observe_boundary_rows(
    boundary: Mapping[str, Any],
    *,
    surface_id: str,
) -> dict[tuple[str, int], tuple[str, ...]]:
    observed: dict[tuple[str, int], tuple[str, ...]] = {}
    for status in ("witnesses", "infeasible"):
        raw_rows = boundary.get(status)
        require(type(raw_rows) is list, f"{surface_id}: {status} must be a list")
        for raw_row in cast(list[object], raw_rows):
            row = object_value(raw_row, context=f"{surface_id}.{status}")
            field, value = row.get("field"), row.get("value")
            labels = string_list(row.get("labels"), context=f"{surface_id}.{status}.labels")
            require(
                type(field) is str and type(value) is int,
                f"{surface_id}: malformed state boundary row",
            )
            key = (cast(str, field), cast(int, value))
            require(key not in observed, f"{surface_id}: duplicate state boundary target")
            observed[key] = tuple(labels)
            if status == "witnesses":
                _check_witness(row, field=key[0], value=key[1], surface_id=surface_id)
            else:
                _check_infeasible(row, surface_id=surface_id)
    return observed


def _check_state_evidence(
    *,
    repo_root: Path,
    surface_id: str,
    evidence: Mapping[str, Any],
    source_relative: Path,
    source_sha256: str,
    state_vars: list[Mapping[str, Any]],
) -> None:
    exact_keys(evidence, STATE_EVIDENCE_KEYS, context=f"{surface_id}.state_evidence")
    require(
        evidence.get("require_no_unresolved") is True,
        f"{surface_id}: complete surface must reject unresolved state boundaries",
    )
    relative = relative_repo_path(evidence.get("path"), context=f"{surface_id}.state_evidence.path")
    require(relative.parts[0] == "tests", f"{surface_id}: state evidence must live under tests")
    artifact = load_json_object(
        repo_file(repo_root, relative, context=f"{surface_id}.state_evidence"),
        context=str(relative),
    )
    require(
        artifact.get("schema") == STATE_BOUNDARY_SCHEMA,
        f"{surface_id}: state evidence schema mismatch",
    )
    require(
        artifact.get("model_path") == source_relative.as_posix(),
        f"{surface_id}: state evidence model path mismatch",
    )
    require(
        artifact.get("model_sha256") == source_sha256,
        f"{surface_id}: state evidence model hash mismatch",
    )
    boundary = object_value(
        artifact.get("state_boundary_witnesses"),
        context=f"{surface_id}.state_boundary_witnesses",
    )
    require(boundary.get("enabled") is True, f"{surface_id}: state boundary evidence disabled")
    require(
        boundary.get("method") == STATE_BOUNDARY_METHOD,
        f"{surface_id}: unsupported state boundary method",
    )
    unresolved = boundary.get("unresolved")
    require(type(unresolved) is list, f"{surface_id}: unresolved must be a list")
    require(
        not cast(list[object], unresolved), f"{surface_id}: unresolved state boundary obligations"
    )
    expected, labeled_count = _expected_state_targets(state_vars, surface_id=surface_id)
    observed = _observe_boundary_rows(boundary, surface_id=surface_id)
    require(observed == expected, f"{surface_id}: state boundary target inventory drift")
    require(
        boundary.get("target_count") == labeled_count, f"{surface_id}: labeled target count drift"
    )
    require(
        boundary.get("unique_target_count") == len(expected),
        f"{surface_id}: unique target count drift",
    )


def _model_inventory(
    model: Mapping[str, Any],
    *,
    surface_id: str,
) -> tuple[list[Mapping[str, Any]], list[Mapping[str, Any]]]:
    raw_actions, raw_state_vars = model.get("actions"), model.get("state_vars")
    require(type(raw_actions) is list, f"{surface_id}: source actions invalid")
    require(type(raw_state_vars) is list, f"{surface_id}: source state variables invalid")
    actions = [
        object_value(value, context=f"{surface_id}.source.actions")
        for value in cast(list[object], raw_actions)
    ]
    state_vars = [
        object_value(value, context=f"{surface_id}.source.state_vars")
        for value in cast(list[object], raw_state_vars)
    ]
    return actions, state_vars


def _check_parameters_and_bounds(
    surface: Mapping[str, Any],
    *,
    actions: list[Mapping[str, Any]],
    state_vars: list[Mapping[str, Any]],
    surface_id: str,
) -> None:
    declared = string_list(
        surface.get("action_parameters"),
        context=f"{surface_id}.action_parameters",
        allow_empty=True,
    )
    actual: list[object] = []
    typed_values: list[Mapping[str, Any]] = list(state_vars)
    for action in actions:
        raw_params = action.get("params", [])
        require(type(raw_params) is list, f"{surface_id}: source action parameters invalid")
        for raw_param in cast(list[object], raw_params):
            parameter = object_value(raw_param, context=f"{surface_id}.source.params")
            actual.append(f"{action.get('id')}.{parameter.get('id')}")
            typed_values.append(parameter)
    require(actual == declared, f"{surface_id}: action parameter inventory drift")
    for value in typed_values:
        type_obj = object_value(value.get("type"), context=f"{surface_id}.source.type")
        kind = type_obj.get("kind")
        require(kind in {"int", "bool"}, f"{surface_id}: unsupported source type {kind!r}")
        if kind == "int":
            low, high = type_obj.get("min"), type_obj.get("max")
            require(
                type(low) is int and type(high) is int and low <= high,
                f"{surface_id}: integer source type lacks finite ordered bounds",
            )


def check_source_binding(
    surface: Mapping[str, Any],
    *,
    repo_root: Path,
    surface_id: str,
    commands: list[str],
    authoritative_fields: list[str],
) -> None:
    source = object_value(surface.get("source_model"), context=f"{surface_id}.source_model")
    exact_keys(source, SOURCE_MODEL_KEYS, context=f"{surface_id}.source_model")
    relative = relative_repo_path(source.get("path"), context=f"{surface_id}.source_model.path")
    require(
        relative.parts[:2] == ("src", "kernels") and relative.suffix in {".yaml", ".yml"},
        f"{surface_id}: source model must be a kernel YAML file",
    )
    source_sha = source.get("sha256")
    require(valid_sha256(source_sha), f"{surface_id}: source model SHA-256 invalid")
    source_path = repo_file(repo_root, relative, context=f"{surface_id}.source_model")
    require(sha256_file(source_path) == source_sha, f"{surface_id}: source model SHA-256 drift")
    require(
        source.get("require_bounded_scalars") is True,
        f"{surface_id}: bounded scalar requirement missing",
    )
    actions, state_vars = _model_inventory(
        _load_source_model(source_path, context=str(relative)),
        surface_id=surface_id,
    )
    require(
        [value.get("id") for value in actions] == commands, f"{surface_id}: command inventory drift"
    )
    require(
        [value.get("id") for value in state_vars] == authoritative_fields,
        f"{surface_id}: authoritative field inventory drift",
    )
    _check_parameters_and_bounds(
        surface,
        actions=actions,
        state_vars=state_vars,
        surface_id=surface_id,
    )
    _check_state_evidence(
        repo_root=repo_root,
        surface_id=surface_id,
        evidence=object_value(
            source.get("state_boundary_evidence"),
            context=f"{surface_id}.state_evidence",
        ),
        source_relative=relative,
        source_sha256=cast(str, source_sha),
        state_vars=state_vars,
    )
