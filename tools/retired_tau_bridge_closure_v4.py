"""Pure, bounded V4 requalification of the retired Tau bridge certificate.

V4 replays the immutable V3 certificate and permits exactly five reviewed
legacy source-pin changes.  It deliberately delegates the original bridge,
route, discovery, dependency, and operation checks to V3.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Final, Mapping, NoReturn, TypeAlias, cast

from tools import retired_tau_bridge_closure_v3 as v3

ARTIFACT_SCHEMA_V4: Final = "zenodex/retired-tau-bridge-closure/v4"
CHECK_SCHEMA_V4: Final = "zenodex/retired-tau-bridge-closure-check/v4"
GENERATOR_COMMAND_V4: Final = "python3 tools/build_retired_tau_bridge_closure_v4.py"
OUTPUT_PATH_V4: Final = "docs/research/ZENODEX_RETIRED_TAU_BRIDGE_CLOSURE_V4.json"

PREDECESSOR_COMMIT_V4: Final = "abea06127ae3a6cd9aca38e18314673af7cd4ffb"
PREDECESSOR_SUBJECT_V4: Final = "ac468ec83f7a85b11e70508ee9d1e525f4f7ac2e"
PREDECESSOR_SHA256_V4: Final = (
    "bd66f99523f904821e6417c588e41b96ef9a219f573d6cc4293d671a4c165dac"
)

EXTRA_PIN_PATHS_V4: Final = (
    "docs/specifications/RETIRED_TAU_BRIDGE_REQUALIFICATION_V4.md",
    "tests/test_retired_tau_bridge_closure_v4.py",
    "tests/test_retired_tau_bridge_closure_v4_shell.py",
    "tools/build_retired_tau_bridge_closure_v4.py",
    "tools/check_retired_tau_bridge_closure_v4.py",
    "tools/retired_tau_bridge_closure_v4.py",
)
_APPROVED_CHANGED_PATHS_V4: Final = (
    "docs/PRODUCTION_BOUNDARY_CLOSURE_AUDIT.md",
    "src/integration/tau_testnet_dex_plugin.py",
    "src/integration/zusd_monetary_bridge.py",
    "tests/test_check_production_boundary.py",
    "tools/check_production_boundary.py",
)
APPROVED_CHANGED_PINS_V4: Final = {
    "docs/PRODUCTION_BOUNDARY_CLOSURE_AUDIT.md": (
        "6481afb8c7c60cd53e81b9e857ccf29e22060db1a47f22e7a8aa062fde0bba11"
    ),
    "src/integration/tau_testnet_dex_plugin.py": (
        "f5d23ff2825c2f708862cde1f473d0c3094a60e114d9650bea7db2629b211dfe"
    ),
    "src/integration/zusd_monetary_bridge.py": (
        "fcea353bd47022a3f9440bc1f33947419482fa9c6990dbd67c2b3a16fbd53bb6"
    ),
    "tests/test_check_production_boundary.py": (
        "e85013776f29544d795932e016e337106c932a6a8e98fa300ec54f86b9d7afcc"
    ),
    "tools/check_production_boundary.py": (
        "750e61b2a215e4d0ad99af5a48e022d0e40f9004a8fedc50ec0e8d0218eddcd9"
    ),
}
_ADAPTER_SNAPSHOTS_V4: Final = {
    "src/integration/tau_testnet_dex_plugin.py": (
        ("state.balances", "BalanceSnapshot", "BalanceTable", "_copy_balance_table"),
        ("state.nonces", "NonceSnapshot", "NonceTable", "_copy_nonce_table"),
    ),
    "src/integration/zusd_monetary_bridge.py": (
        ("state.balances", "BalanceSnapshot", "BalanceTable", "_copy_balance_table"),
        ("state.nonces", "NonceSnapshot", "NonceTable", "_copy_nonce_table"),
    ),
}
_CLAIM_CEILING_V4: Final = {
    "closed_value_movement_gates": 0,
    "production_authority": "NONE",
    "release_authority": "NONE",
    "settlement_authority": "NONE",
    "value_movement_authority": "NONE",
    "value_movement_claim_allowed": False,
}


@dataclass(frozen=True)
class QualificationSnapshotV4:
    """All byte inputs needed by the pure successor requalification."""

    current: v3.SubjectSnapshotV3
    predecessor: v3.SubjectSnapshotV3
    predecessor_artifact: bytes
    extra_sources: tuple[v3.SourceFileV3, ...]


ClosureRejectV4: TypeAlias = v3.ClosureRejectV3


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise ClosureRejectV4(code, path, detail)


def _parse_adapter(data: bytes, path: str) -> ast.Module:
    if type(data) is not bytes or len(data) > v3.MAX_SOURCE_BYTES_V3:
        _reject("ADAPTER_SOURCE", path, "requires bounded exact bytes")
    try:
        return ast.parse(data, filename=path)
    except (MemoryError, RecursionError, SyntaxError, ValueError) as exc:
        _reject("ADAPTER_SOURCE", path, type(exc).__name__)


def _one_top_level_function(tree: ast.Module, name: str, path: str) -> ast.FunctionDef:
    matches = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == name]
    if len(matches) != 1:
        _reject("ADAPTER_AST_SCOPE", path, f"expected one top-level {name}")
    return matches[0]


def _one_import(
    tree: ast.Module, module: str, path: str
) -> ast.ImportFrom:
    matches = [
        node
        for node in tree.body
        if isinstance(node, ast.ImportFrom) and node.level == 2 and node.module == module
    ]
    if len(matches) != 1:
        _reject("ADAPTER_AST_SCOPE", path, f"expected one existing import {module}")
    return matches[0]


def _normalized_adapter_ast_v4(previous: bytes, current: bytes, path: str) -> str:
    """Undo only the reviewed Snapshot imports and first-argument annotations."""

    old_tree = _parse_adapter(previous, path)
    new_tree = _parse_adapter(current, path)
    for module, snapshot_name, table_name, function_name in _ADAPTER_SNAPSHOTS_V4[path]:
        old_import = _one_import(old_tree, module, path)
        new_import = _one_import(new_tree, module, path)
        if any(alias.name == snapshot_name for alias in old_import.names):
            _reject("ADAPTER_IMPORT_BASELINE", path, snapshot_name)
        retained = [alias for alias in new_import.names if alias.name != snapshot_name]
        removed = [alias for alias in new_import.names if alias.name == snapshot_name]
        if (
            len(removed) != 1
            or removed[0].asname is not None
            or [(alias.name, alias.asname) for alias in retained]
            != [(alias.name, alias.asname) for alias in old_import.names]
        ):
            _reject("ADAPTER_IMPORT_DELTA", path, snapshot_name)
        new_import.names = retained

        old_function = _one_top_level_function(old_tree, function_name, path)
        new_function = _one_top_level_function(new_tree, function_name, path)
        if not old_function.args.args or not new_function.args.args:
            _reject("ADAPTER_ANNOTATION_SCOPE", path, function_name)
        old_argument, new_argument = old_function.args.args[0], new_function.args.args[0]
        if old_argument.annotation is None or new_argument.annotation is None:
            _reject("ADAPTER_ANNOTATION_SCOPE", path, function_name)
        expected = ast.parse(f"{table_name} | {snapshot_name}", mode="eval").body
        expected_old = ast.parse(table_name, mode="eval").body
        if (
            old_argument.arg != new_argument.arg
            or ast.dump(old_argument.annotation, include_attributes=False)
            != ast.dump(expected_old, include_attributes=False)
            or ast.dump(new_argument.annotation, include_attributes=False)
            != ast.dump(expected, include_attributes=False)
        ):
            _reject("ADAPTER_ANNOTATION_DELTA", path, function_name)
        new_argument.annotation = old_argument.annotation
    return ast.dump(new_tree, include_attributes=False)


def _validate_adapter_delta_v4(previous: bytes, current: bytes, path: str) -> None:
    if _normalized_adapter_ast_v4(previous, current, path) != ast.dump(
        _parse_adapter(previous, path), include_attributes=False
    ):
        _reject("ADAPTER_AST_DELTA", path, "remaining AST must be identical")


def _validate_configuration_v4() -> None:
    if EXTRA_PIN_PATHS_V4 != tuple(sorted(EXTRA_PIN_PATHS_V4)):
        _reject("EXTRA_PIN_ORDER", "extra sources", "paths must be sorted")
    if OUTPUT_PATH_V4 in EXTRA_PIN_PATHS_V4 or set(EXTRA_PIN_PATHS_V4) & set(
        v3.SUBJECT_PIN_PATHS_V3
    ):
        _reject("EXTRA_PIN_SCOPE", "extra sources", "receipt self-pin or legacy overlap")
    if tuple(sorted(APPROVED_CHANGED_PINS_V4)) != _APPROVED_CHANGED_PATHS_V4:
        _reject("APPROVED_PIN_SCOPE", "legacy sources", "approved path set drift")
    for path, digest in APPROVED_CHANGED_PINS_V4.items():
        if digest == "PENDING_ROOT_PIN":
            _reject("PENDING_ROOT_PIN", path, "root must finalize the reviewed successor pin")
        if type(digest) is not str or v3._SHA256_RE.fullmatch(digest) is None:
            _reject("APPROVED_PIN_SHA", path, "requires one lowercase SHA-256 digest")


def _predecessor_template_v4(snapshot: QualificationSnapshotV4) -> dict[str, object]:
    if type(snapshot) is not QualificationSnapshotV4:
        _reject("SNAPSHOT_TYPE", "snapshot", "requires exact QualificationSnapshotV4")
    if (
        type(snapshot.predecessor_artifact) is not bytes
        or len(snapshot.predecessor_artifact) > v3.MAX_ARTIFACT_BYTES_V3
    ):
        _reject("PREDECESSOR_ARTIFACT", "artifact", "requires bounded exact bytes")
    if v3._sha256(snapshot.predecessor_artifact) != PREDECESSOR_SHA256_V4:
        _reject("PREDECESSOR_ARTIFACT_SHA", "artifact", "immutable V3 receipt mismatch")
    predecessor = snapshot.predecessor
    if type(predecessor) is not v3.SubjectSnapshotV3:
        _reject("SNAPSHOT_TYPE", "predecessor", "requires exact SubjectSnapshotV3")
    if (
        predecessor.captured_head != PREDECESSOR_SUBJECT_V4
        or predecessor.rechecked_head != PREDECESSOR_SUBJECT_V4
        or predecessor.subject.commit != PREDECESSOR_SUBJECT_V4
    ):
        _reject("PREDECESSOR_SUBJECT", "predecessor", "requires the immutable Stage-A subject")
    v3.check_artifact_v3(snapshot.predecessor_artifact, predecessor)
    artifact = v3._decode_json_object(snapshot.predecessor_artifact, "predecessor artifact")
    evidence = artifact.get("evidence_subject")
    if evidence != {"commit": PREDECESSOR_SUBJECT_V4, "tree": predecessor.subject.tree}:
        _reject("PREDECESSOR_SUBJECT", "predecessor artifact", "receipt subject drift")
    return artifact


def _extra_source_map_v4(snapshot: QualificationSnapshotV4) -> dict[str, v3.SourceFileV3]:
    if type(snapshot.extra_sources) is not tuple:
        _reject("EXTRA_SOURCE_TYPE", "extra sources", "requires an exact tuple")
    current = snapshot.current
    if type(current) is not v3.SubjectSnapshotV3:
        _reject("SNAPSHOT_TYPE", "current", "requires exact SubjectSnapshotV3")
    extra_snapshot = v3.SourceSnapshotV3(
        commit=current.subject.commit,
        tree=current.subject.tree,
        files=snapshot.extra_sources,
    )
    return v3._validate_source_snapshot(
        extra_snapshot, expected_paths=EXTRA_PIN_PATHS_V4, role="successor extra sources"
    )


def _change_records_v4(
    previous: Mapping[str, v3.SourceFileV3], current: Mapping[str, v3.SourceFileV3]
) -> list[dict[str, str]]:
    observed = tuple(
        path for path in v3.SUBJECT_PIN_PATHS_V3 if previous[path].data != current[path].data
    )
    if observed != _APPROVED_CHANGED_PATHS_V4:
        _reject("LEGACY_PIN_DELTA", "legacy sources", ",".join(observed))
    records: list[dict[str, str]] = []
    for path in _APPROVED_CHANGED_PATHS_V4:
        old_hash, new_hash = v3._sha256(previous[path].data), v3._sha256(current[path].data)
        if new_hash != APPROVED_CHANGED_PINS_V4[path]:
            _reject("APPROVED_PIN_SHA", path, new_hash)
        if path in _ADAPTER_SNAPSHOTS_V4:
            _validate_adapter_delta_v4(previous[path].data, current[path].data, path)
            category, status = "IMMUTABILITY_SNAPSHOT_REPAIR", "AST_NORMALIZED_EQUAL"
        else:
            category, status = "SUCCESSOR_REQUALIFICATION", "EXACT_PIN_APPROVED"
        records.append(
            {
                "comparison_status": status,
                "evidence_category": category,
                "new_sha256": new_hash,
                "old_sha256": old_hash,
                "path": path,
            }
        )
    return records


def _current_derivation_v4(
    snapshot: v3.SubjectSnapshotV3,
    baseline: Mapping[str, v3.SourceFileV3],
    subject: Mapping[str, v3.SourceFileV3],
) -> tuple[list[dict[str, object]], dict[str, object], list[dict[str, object]]]:
    baseline_discovery, subject_discovery, current_discovery = v3._snapshot_discoveries(snapshot)
    if v3._path_set_sha256(v3.DIRECT_CONSUMER_PATHS_V3) != v3.DIRECT_CONSUMER_PATH_SET_SHA256_V3:
        _reject("SOURCE_SCOPE", "direct consumers", "fixed path-set digest drift")
    source = {path: item.data for path, item in subject.items()}
    v3._require_plan_and_current_tau(source)
    v3._require_route_witnesses(baseline, subject)
    import_rows, projection = v3._import_dependency_rows(baseline, subject)
    discovery = v3._require_discovery_closure(
        baseline_direct=v3.scan_bridge_import_edges_v3(
            {path: baseline[path].data for path in v3.DIRECT_CONSUMER_PATHS_V3}
        ),
        subject_direct=v3.scan_bridge_import_edges_v3(
            {path: subject[path].data for path in v3.DIRECT_CONSUMER_PATHS_V3}
        ),
        baseline_discovery=baseline_discovery,
        subject_discovery=subject_discovery,
        current_discovery=current_discovery,
    )
    baseline_manifest = v3._source_manifest(baseline, v3.DIRECT_CONSUMER_PATHS_V3)
    current_manifest = v3._source_manifest(subject, v3.DIRECT_CONSUMER_PATHS_V3)
    baseline_root = v3._manifest_root(baseline_manifest)
    if baseline_root != v3.EXPECTED_BASELINE_SOURCE_ROOT_V3:
        _reject("BASELINE_SOURCE_SET", "direct consumers", baseline_root)
    rows = import_rows + v3._manual_dependency_rows(baseline, subject)
    rows.sort(key=lambda row: str(row["dependency_id"]))
    v3._validate_dependency_rows(rows)
    import_counts = {
        classification: sum(row["classification"] == classification for row in import_rows)
        for classification in v3._CLASSIFICATIONS_V3
    }
    if import_counts != {"QUARANTINED": 0, "RESEARCH_ORACLE": 92, "REMOVED": 36}:
        _reject("IMPORT_CLASSIFICATION_COUNTS", "import projection", str(import_counts))
    projection.update(
        {
            "baseline_source_bytes": sum(cast(int, row["size"]) for row in baseline_manifest),
            "baseline_source_root_sha256": baseline_root,
            "current_source_bytes": sum(cast(int, row["size"]) for row in current_manifest),
            "current_source_root_sha256": v3._manifest_root(current_manifest),
            "current_route_source_root_sha256": v3._manifest_root(
                v3._source_manifest(subject, v3._ROUTE_PIN_PATHS_V3)
            ),
            "direct_consumer_path_count": len(v3.DIRECT_CONSUMER_PATHS_V3),
            "direct_consumer_path_set_sha256": v3.DIRECT_CONSUMER_PATH_SET_SHA256_V3,
            "import_classification_counts": import_counts,
            **discovery,
        }
    )
    return rows, projection, v3._operation_registry(rows)


def _preserve_v3_shape_v4(
    template: Mapping[str, object],
    rows: list[dict[str, object]],
    projection: Mapping[str, object],
    operations: list[dict[str, object]],
) -> None:
    old_projection = template.get("dependency_projection")
    old_registry = template.get("operation_registry")
    old_source = template.get("source_projection")
    if not all(type(value) is dict for value in (old_projection, old_registry, old_source)):
        _reject("PREDECESSOR_SHAPE", "predecessor artifact", "required projections missing")
    old_projection = cast(dict[str, object], old_projection)
    old_registry = cast(dict[str, object], old_registry)
    old_source = cast(dict[str, object], old_source)
    counts = {
        name: sum(row["classification"] == name for row in rows)
        for name in v3._CLASSIFICATIONS_V3
    }
    if old_projection.get("classification_counts") != counts or old_projection.get(
        "dependency_count"
    ) != len(rows):
        _reject("DEPENDENCY_CLASSIFICATION_DRIFT", "dependency rows", "V3 count drift")
    if old_registry.get("operation_rows") != operations:
        _reject("OPERATION_REGISTRY_DRIFT", "operation registry", "V3 operation drift")
    for field in (
        "baseline_edge_count",
        "baseline_edge_root_sha256",
        "current_edge_count",
        "current_edge_root_sha256",
        "current_only_edge_count",
        "removed_edge_count",
        "unchanged_edge_count",
        "baseline_source_bytes",
        "baseline_source_root_sha256",
        "direct_consumer_path_count",
        "direct_consumer_path_set_sha256",
        "import_classification_counts",
        "baseline_discovered_consumer_count",
        "baseline_discovered_edge_count",
        "baseline_python_path_count",
        "baseline_python_path_set_sha256",
        "python_discovery_scope",
    ):
        if projection.get(field) != old_source.get(field):
            _reject("V3_PROJECTION_DRIFT", field, "fixed V3 projection changed")


def _unsigned_artifact_v4(snapshot: QualificationSnapshotV4) -> dict[str, object]:
    _validate_configuration_v4()
    template = _predecessor_template_v4(snapshot)
    previous_baseline, previous_subject = v3._snapshot_sources(snapshot.predecessor)
    baseline, subject = v3._snapshot_sources(snapshot.current)
    if baseline != previous_baseline:
        _reject("BASELINE_PREDECESSOR_DRIFT", "baseline", "successor baseline changed")
    extras = _extra_source_map_v4(snapshot)
    changes = _change_records_v4(previous_subject, subject)
    rows, projection, operations = _current_derivation_v4(snapshot.current, baseline, subject)
    _preserve_v3_shape_v4(template, rows, projection, operations)
    unsigned = dict(template)
    unsigned.pop("certificate_root", None)
    unsigned.update(
        {
            "schema": ARTIFACT_SCHEMA_V4,
            "generator_command": GENERATOR_COMMAND_V4,
            "evidence_subject": {
                "commit": snapshot.current.subject.commit,
                "tree": snapshot.current.subject.tree,
            },
            "dependency_projection": {
                "classification_counts": {
                    name: sum(row["classification"] == name for row in rows)
                    for name in v3._CLASSIFICATIONS_V3
                },
                "dependency_count": len(rows),
                "dependency_rows": rows,
            },
            "operation_registry": {
                "current_operation_ids": list(v3.CURRENT_OPERATION_IDS_V3),
                "operation_rows": operations,
                "research_operation_ids": list(v3.RESEARCH_OPERATION_IDS_V3),
            },
            "source_projection": projection,
            "source_snapshot_pins": {
                "baseline": [
                    {"path": path, **v3._source_pin(baseline[path])}
                    for path in v3.BASELINE_PIN_PATHS_V3
                ],
                "subject": [
                    {"path": path, **v3._source_pin(subject[path])}
                    for path in v3.SUBJECT_PIN_PATHS_V3
                ],
            },
            "successor_binding": {
                "change_records": changes,
                "extra_source_pins": [
                    {"path": path, **v3._source_pin(extras[path])} for path in EXTRA_PIN_PATHS_V4
                ],
                "predecessor_artifact_sha256": PREDECESSOR_SHA256_V4,
                "predecessor_commit": PREDECESSOR_COMMIT_V4,
                "predecessor_subject": PREDECESSOR_SUBJECT_V4,
                "predecessor_subject_tree": snapshot.predecessor.subject.tree,
            },
        }
    )
    return unsigned


_ARTIFACT_FIELDS_V4: Final = frozenset({*v3._ARTIFACT_TOP_LEVEL_FIELDS_V3, "successor_binding"})
_SUCCESSOR_FIELDS_V4: Final = frozenset(
    {
        "change_records",
        "extra_source_pins",
        "predecessor_artifact_sha256",
        "predecessor_commit",
        "predecessor_subject",
        "predecessor_subject_tree",
    }
)


def build_artifact_v4(snapshot: QualificationSnapshotV4) -> bytes:
    unsigned = _unsigned_artifact_v4(snapshot)
    raw = v3.canonical_json_bytes_v3({**unsigned, "certificate_root": v3._sha256(v3.canonical_json_bytes_v3(unsigned))})
    if len(raw) > v3.MAX_ARTIFACT_BYTES_V3:
        _reject("ARTIFACT_SIZE", "artifact", f"{len(raw)} bytes")
    return raw


def _validate_artifact_v4(artifact: dict[str, object]) -> None:
    if set(artifact) != _ARTIFACT_FIELDS_V4 or artifact.get("schema") != ARTIFACT_SCHEMA_V4:
        _reject("ARTIFACT_FIELDS", "artifact", "closed V4 field set or schema drift")
    if artifact.get("generator_command") != GENERATOR_COMMAND_V4:
        _reject("GENERATOR_COMMAND", "artifact", "unexpected V4 generator")
    if artifact.get("claim_ceiling") != _CLAIM_CEILING_V4:
        _reject("AUTHORITY_PROMOTION", "claim_ceiling", "authority must remain NONE")
    binding = artifact.get("successor_binding")
    if type(binding) is not dict or set(binding) != _SUCCESSOR_FIELDS_V4:
        _reject("SUCCESSOR_BINDING", "artifact", "closed successor binding required")
    if (
        binding.get("predecessor_artifact_sha256") != PREDECESSOR_SHA256_V4
        or binding.get("predecessor_commit") != PREDECESSOR_COMMIT_V4
        or binding.get("predecessor_subject") != PREDECESSOR_SUBJECT_V4
    ):
        _reject("PREDECESSOR_BINDING", "artifact", "immutable predecessor drift")
    projection = artifact.get("dependency_projection")
    registry = artifact.get("operation_registry")
    if type(projection) is not dict or type(registry) is not dict:
        _reject("ARTIFACT_PROJECTION", "artifact", "dependency projection missing")
    rows = projection.get("dependency_rows")
    if type(rows) is not list or any(type(row) is not dict for row in rows):
        _reject("DEPENDENCY_ROW_SHAPE", "dependency_projection", "exact object rows required")
    typed_rows = cast(list[dict[str, object]], rows)
    v3._validate_dependency_rows(typed_rows)
    counts = {
        name: sum(row["classification"] == name for row in typed_rows)
        for name in v3._CLASSIFICATIONS_V3
    }
    if projection.get("classification_counts") != counts or projection.get("dependency_count") != len(
        typed_rows
    ) or registry.get("operation_rows") != v3._operation_registry(typed_rows):
        _reject("ARTIFACT_PROJECTION", "artifact", "dependency or operation replay drift")
    root = artifact.get("certificate_root")
    unsigned = dict(artifact)
    unsigned.pop("certificate_root", None)
    if type(root) is not str or root != v3._sha256(v3.canonical_json_bytes_v3(unsigned)):
        _reject("CERTIFICATE_ROOT", "artifact", "self-binding root mismatch")


def check_artifact_v4(raw: bytes, snapshot: QualificationSnapshotV4) -> dict[str, object]:
    if type(raw) is not bytes or len(raw) > v3.MAX_ARTIFACT_BYTES_V3:
        _reject("ARTIFACT_SIZE", "artifact", "requires bounded exact bytes")
    artifact = v3._decode_json_object(raw, "artifact")
    if v3.canonical_json_bytes_v3(artifact) != raw:
        _reject("NONCANONICAL_ARTIFACT", "artifact", "bytes are not canonical JSON")
    _validate_artifact_v4(artifact)
    if raw != build_artifact_v4(snapshot):
        _reject("ARTIFACT_REPLAY_MISMATCH", "artifact", "bytes differ from derivation")
    projection = cast(dict[str, object], artifact["dependency_projection"])
    source = cast(dict[str, object], artifact["source_projection"])
    return {
        "artifact_sha256": v3._sha256(raw),
        "classification_counts": projection["classification_counts"],
        "closed_value_movement_gates": 0,
        "current_only_import_edge_count": source["current_only_edge_count"],
        "dependency_count": projection["dependency_count"],
        "findings": [],
        "o003b_status": "COMPLETE_ON_STAGE_A_EVIDENCE_SUBJECT",
        "ok": True,
        "predecessor_artifact_sha256": PREDECESSOR_SHA256_V4,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": CHECK_SCHEMA_V4,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def failure_report_v4(exc: ClosureRejectV4) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "classification_counts": {},
        "closed_value_movement_gates": 0,
        "current_only_import_edge_count": None,
        "dependency_count": 0,
        "findings": [{"code": exc.code, "detail": exc.detail, "path": exc.path}],
        "o003b_status": "OPEN",
        "ok": False,
        "predecessor_artifact_sha256": PREDECESSOR_SHA256_V4,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": CHECK_SCHEMA_V4,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }
