"""AAA and RIPR evidence for the exact-subject O-005 completion certificate."""

from __future__ import annotations

import ast
import hashlib
import json
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest

import tools.build_m6_o005_requirements_floor_completion_v1 as build_shell
import tools.check_m6_o005_requirements_floor_completion_v1 as check_shell
import tools.m6_o005_requirements_floor_completion_v1 as core
from tools.m6_normative_requirements_v1 import canonical_json_bytes_v1

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_PATH = REPO_ROOT / "docs/research/M6_O005_REQUIREMENTS_FLOOR_COMPLETION_V1.json"
EXPECTED_ARTIFACT_SHA256 = "5c6812d21509432cd3b54c84a7a85e08fe040c294655e1c5fca0e9a8c610e47a"
REQUIRED_COUNTS = {
    "WORKFLOW": 18,
    "BDD": 81,
    "REQUIRED_SPEC_EXPANSION": 11,
    "CONFIRMED_FINDING": 8,
    "UNRESOLVED_POLICY": 20,
}
AUTHORITY_FIELDS = (
    "production_authority",
    "settlement_authority",
    "release_authority",
    "value_movement_authority",
)


@pytest.fixture(scope="module")
def snapshot() -> core.SubjectEvidenceSnapshotV1:
    return build_shell.load_subject_snapshot_v1(REPO_ROOT)


def _artifact_bytes() -> bytes:
    return ARTIFACT_PATH.read_bytes()


def _artifact_object() -> dict[str, object]:
    value = json.loads(_artifact_bytes())
    if type(value) is not dict:
        raise TypeError("certificate fixture must be an object")
    return value


def _source_map(snapshot: core.SubjectEvidenceSnapshotV1) -> dict[str, bytes]:
    return dict(snapshot.source_subject_bytes)


def _canonical_mutant(value: dict[str, object], *, repin_root: bool = True) -> bytes:
    if repin_root:
        unsigned = dict(value)
        unsigned.pop("certificate_root", None)
        value["certificate_root"] = hashlib.sha256(canonical_json_bytes_v1(unsigned)).hexdigest()
    return canonical_json_bytes_v1(value)


def _check_mutant(
    value: dict[str, object], snapshot: core.SubjectEvidenceSnapshotV1
) -> dict[str, object]:
    return core.check_requirements_floor_completion_artifact_v1(_canonical_mutant(value), snapshot)


def _assert_closed_failure(report: dict[str, object]) -> str:
    assert report["ok"] is False
    assert report["current_successor_o005_status"] == "OPEN"
    assert report["closed_value_movement_gates"] == 0
    assert report["manifest_complete"] is False
    assert report["requirements_closed"] is False
    assert report["semantic_closure_complete"] is False
    for field in AUTHORITY_FIELDS:
        assert report[field] == "NONE"
    findings = report["findings"]
    assert type(findings) is list and len(findings) == 1
    finding = findings[0]
    assert type(finding) is dict and type(finding.get("code")) is str
    return cast(str, finding["code"])


def test_given_exact_subject_when_built_and_checked_then_o005_only_is_complete(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    committed = _artifact_bytes()

    # Act
    built = core.build_requirements_floor_completion_artifact_v1(snapshot)
    report = core.check_requirements_floor_completion_artifact_v1(committed, snapshot)

    # Assert
    assert built == committed
    assert hashlib.sha256(committed).hexdigest() == EXPECTED_ARTIFACT_SHA256
    assert report == {
        "artifact_sha256": EXPECTED_ARTIFACT_SHA256,
        "closed_value_movement_gates": 0,
        "current_successor_o005_status": "COMPLETE_ON_EXACT_SUBJECT",
        "findings": [],
        "manifest_complete": False,
        "ok": True,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "requirements_closed": False,
        "schema": core.CHECK_SCHEMA_V1,
        "semantic_closure_complete": False,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def test_given_sources_when_independently_counted_then_all_138_rows_are_nonvacuous() -> None:
    # Arrange
    normative = json.loads((REPO_ROOT / core.NORMATIVE_ARTIFACT_PATH_V1).read_bytes())
    rows = normative["rows"]

    # Act
    observed_counts = {
        kind: sum(type(row) is dict and row.get("kind") == kind for row in rows)
        for kind in REQUIRED_COUNTS
    }
    required_rows = [
        row for row in rows if type(row) is dict and row.get("kind") in REQUIRED_COUNTS
    ]

    # Assert
    assert observed_counts == REQUIRED_COUNTS
    assert len(required_rows) == 138
    assert all(type(row.get("edges")) is list and len(row["edges"]) > 0 for row in required_rows)
    policies = [row for row in required_rows if row["kind"] == "UNRESOLVED_POLICY"]
    assert [row["requirement_id"] for row in policies] == [f"UP-{i:02d}" for i in range(1, 21)]
    assert {row["status"] for row in policies} == {"UNRESOLVED_POLICY_NOT_SELECTABLE"}


def test_given_sources_when_independently_joined_then_resolution_relations_are_bijections() -> None:
    # Arrange
    normative = json.loads((REPO_ROOT / core.NORMATIVE_ARTIFACT_PATH_V1).read_bytes())
    resolutions = json.loads((REPO_ROOT / core.RESOLUTION_ARTIFACT_PATH_V1).read_bytes())
    missing = [
        target["missing_target_concept_id"]
        for target in normative["targets"]
        if target["target_type"] == "MISSING_TARGET_CONCEPT"
    ]
    routes = [
        target["route_id"]
        for target in normative["targets"]
        if target["target_type"] == "REQUIRED_ROUTE"
    ]

    # Act
    resolution_sources = [
        row["source_missing_target_concept_id"] for row in resolutions["resolution_rows"]
    ]
    resolution_targets = [row["target_id"] for row in resolutions["resolution_rows"]]
    route_sources = [row["source_route_id"] for row in resolutions["route_resolution_rows"]]

    # Assert
    assert len(missing) == len(set(missing)) == 12
    assert resolution_sources == missing
    assert len(resolution_targets) == len(set(resolution_targets)) == 12
    assert len(routes) == len(set(routes)) == 4
    assert route_sources == routes


def test_given_certificate_when_read_then_narrow_and_global_statuses_are_distinct() -> None:
    # Arrange
    certificate = _artifact_object()

    # Act
    completion = certificate["o005_completion"]
    ceiling = certificate["claim_ceiling"]

    # Assert
    assert type(completion) is dict
    assert type(ceiling) is dict
    assert completion == {
        "closes_only": ["incomplete_requirements_registry"],
        "current_successor_o005_status": "COMPLETE_ON_EXACT_SUBJECT",
        "plan_baseline_gap_status": "OPEN",
        "plan_obligation_id": "O-005",
    }
    assert ceiling["closed_value_movement_gates"] == 0
    assert ceiling["manifest_complete"] is False
    assert ceiling["requirements_closed"] is False
    assert ceiling["semantic_target_inventory_complete"] is False
    assert ceiling["semantic_policy_closure_complete"] is False
    floor = certificate["requirements_floor"]
    assert type(floor) is dict
    assert floor["unresolved_policy_inventory_complete"] is True
    assert ceiling["semantic_closure_complete"] is False


def test_given_descendant_head_when_pinned_files_are_unchanged_then_certificate_is_stable(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    descendant = replace(
        snapshot,
        captured_git_head="a" * 40,
        rechecked_git_head="a" * 40,
        evidence_subject_is_current_ancestor=True,
    )

    # Act
    rebuilt = core.build_requirements_floor_completion_artifact_v1(descendant)

    # Assert
    assert rebuilt == _artifact_bytes()


@pytest.mark.parametrize(
    ("field", "value", "code"),
    [
        ("rechecked_git_head", "b" * 40, "HEAD_CHANGED"),
        ("evidence_subject_is_current_ancestor", False, "SUBJECT_NOT_ANCESTOR"),
        ("evidence_subject_tree", "c" * 40, "SUBJECT_TREE"),
        ("captured_git_head", 7, "SNAPSHOT_HEAD_TYPE"),
        ("evidence_subject_is_current_ancestor", 1, "ANCESTRY_TYPE"),
    ],
)
def test_given_snapshot_binding_mutant_when_built_then_typed_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1,
    field: str,
    value: object,
    code: str,
) -> None:
    # Arrange
    mutant = replace(cast(Any, snapshot), **{field: value})

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core.build_requirements_floor_completion_artifact_v1(mutant)
    assert captured.value.code == code


def test_given_current_content_drift_when_built_then_rejects_exact_file(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    rows = list(snapshot.current_content_bytes)
    path, raw = rows[1]
    rows[1] = (path, raw + b"\n")

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core.build_requirements_floor_completion_artifact_v1(
            replace(snapshot, current_content_bytes=tuple(rows))
        )
    assert captured.value.code == "CURRENT_CONTENT"
    assert captured.value.path == path


def test_given_subject_bytes_drift_when_built_then_sha_binding_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    rows = list(snapshot.source_subject_bytes)
    path, raw = rows[1]
    rows[1] = (path, raw + b"\n")

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core.build_requirements_floor_completion_artifact_v1(
            replace(snapshot, source_subject_bytes=tuple(rows))
        )
    assert captured.value.code == "SOURCE_SHA256"
    assert captured.value.path == path


def test_given_hostile_git_entry_component_when_built_then_comparison_hook_is_not_called(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    class ExplodingEqual:
        def __eq__(self, other: object) -> bool:
            raise AssertionError("hostile equality hook executed")

    # Arrange
    rows = list(snapshot.current_head_entries)
    path, mode, object_type, _blob = rows[0]
    rows[0] = (path, mode, object_type, cast(str, ExplodingEqual()))

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core.build_requirements_floor_completion_artifact_v1(
            replace(snapshot, current_head_entries=tuple(rows))
        )
    assert captured.value.code == "GIT_BLOB_BINDING"


class _HostilePath:
    def __fspath__(self) -> str:
        raise AssertionError("hostile __fspath__ executed")

    def __str__(self) -> str:
        raise AssertionError("hostile __str__ executed")


@pytest.mark.parametrize("hostile", [_HostilePath(), "bad\x00path", "bad\ud800path"])
def test_given_hostile_root_when_checked_then_failure_is_typed_and_closed(hostile: object) -> None:
    # Arrange / Act
    report = check_shell.check_m6_o005_requirements_floor_completion_v1(cast(Path, hostile))

    # Assert
    code = _assert_closed_failure(report)
    assert code in {"FILE_PATH_TYPE", "FILE_PATH_ENCODING"}


@pytest.mark.parametrize("operation", ["unknown", "missing"])
def test_given_certificate_field_set_mutant_when_checked_then_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1, operation: str
) -> None:
    # Arrange
    mutant = _artifact_object()
    if operation == "unknown":
        mutant["unexpected"] = None
    else:
        mutant.pop("status")

    # Act
    report = _check_mutant(mutant, snapshot)

    # Assert
    assert _assert_closed_failure(report) == "FIELD_SET"


def test_given_duplicate_json_key_when_checked_then_rejects_before_semantics(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    raw = b'{"schema":"x","schema":"y"}'

    # Act
    report = core.check_requirements_floor_completion_artifact_v1(raw, snapshot)

    # Assert
    assert _assert_closed_failure(report) == "JSON_JSON_DECODE"


def test_given_reordered_json_when_checked_then_noncanonical_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    value = _artifact_object()
    reordered = {key: value[key] for key in reversed(tuple(value))}
    raw = json.dumps(reordered, ensure_ascii=True, separators=(",", ":")).encode("ascii")

    # Act
    report = core.check_requirements_floor_completion_artifact_v1(raw, snapshot)

    # Assert
    assert _assert_closed_failure(report) == "JSON_NONCANONICAL"


@pytest.mark.parametrize(
    ("path", "value"),
    [
        (("claim_ceiling", "closed_value_movement_gates"), True),
        (("claim_ceiling", "closed_value_movement_gates"), 1),
        (("claim_ceiling", "manifest_complete"), True),
        (("claim_ceiling", "requirements_closed"), True),
        (("claim_ceiling", "semantic_closure_complete"), True),
        (("claim_ceiling", "semantic_policy_closure_complete"), True),
        (("claim_ceiling", "semantic_target_inventory_complete"), True),
        (("claim_ceiling", "structural_mapping_complete"), True),
        (("claim_ceiling", "production_authority"), "ACTIVE"),
        (("claim_ceiling", "settlement_authority"), "ACTIVE"),
        (("claim_ceiling", "release_authority"), "ACTIVE"),
        (("claim_ceiling", "migration_authority"), "ACTIVE"),
        (("claim_ceiling", "value_movement_authority"), "ACTIVE"),
    ],
)
def test_given_claim_promotion_mutant_when_checked_then_never_promotes(
    snapshot: core.SubjectEvidenceSnapshotV1,
    path: tuple[str, str],
    value: object,
) -> None:
    # Arrange
    mutant = _artifact_object()
    parent = mutant[path[0]]
    assert type(parent) is dict
    parent[path[1]] = value

    # Act
    report = _check_mutant(mutant, snapshot)

    # Assert
    assert _assert_closed_failure(report) in {"INTEGER_TYPE", "CERTIFICATE_MISMATCH"}


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("closes_only", []),
        ("closes_only", ["incomplete_requirements_registry", "VM-01"]),
        ("current_successor_o005_status", "COMPLETE_PRODUCTION"),
        ("plan_baseline_gap_status", "CLOSED"),
        ("plan_obligation_id", "O-006"),
    ],
)
def test_given_o005_scope_mutant_when_checked_then_exact_derived_certificate_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1, field: str, value: object
) -> None:
    # Arrange
    mutant = _artifact_object()
    completion = mutant["o005_completion"]
    assert type(completion) is dict
    completion[field] = value

    # Act
    report = _check_mutant(mutant, snapshot)

    # Assert
    assert _assert_closed_failure(report) in {
        "CERTIFICATE_CLOSES_COUNT",
        "CERTIFICATE_MISMATCH",
        "LIST_LIMIT",
    }


@pytest.mark.parametrize("count", [13, 14, 15])
def test_given_certificate_pin_count_neighbor_when_checked_then_only_14_reaches_exact_match(
    snapshot: core.SubjectEvidenceSnapshotV1, count: int
) -> None:
    # Arrange
    mutant = _artifact_object()
    pins = mutant["source_file_pins"]
    assert type(pins) is list
    if count == 13:
        pins.pop()
    elif count == 15:
        pins.append(deepcopy(pins[-1]))

    # Act
    report = _check_mutant(mutant, snapshot)

    # Assert
    if count == 14:
        assert report["ok"] is True
    else:
        assert _assert_closed_failure(report) == "CERTIFICATE_PIN_COUNT"


@pytest.mark.parametrize("required_count", [137, 138, 139])
def test_given_required_row_count_boundary_when_derived_then_only_138_accepts(
    snapshot: core.SubjectEvidenceSnapshotV1, required_count: int
) -> None:
    # Arrange
    source = _source_map(snapshot)
    normative = json.loads(source[core.NORMATIVE_ARTIFACT_PATH_V1])
    rows = normative["rows"]
    assert type(rows) is list
    if required_count == 137:
        rows.pop(next(i for i, row in enumerate(rows) if row["kind"] == "WORKFLOW"))
    elif required_count == 139:
        extra = deepcopy(next(row for row in rows if row["kind"] == "WORKFLOW"))
        extra["requirement_id"] = "WF-999"
        rows.append(extra)
    source[core.NORMATIVE_ARTIFACT_PATH_V1] = canonical_json_bytes_v1(normative)

    # Act / Assert
    if required_count == 138:
        floor, _, _ = core._derive_requirements_floor_v1(source)
        assert floor["required_row_count"] == 138
    else:
        with pytest.raises(core.CompletionRejectV1) as captured:
            core._derive_requirements_floor_v1(source)
        assert captured.value.code == "NORMATIVE_ROW_COUNT"


def test_given_each_required_row_kind_when_one_edge_list_is_empty_then_vacuity_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange / Act / Assert
    for kind in REQUIRED_COUNTS:
        source = _source_map(snapshot)
        normative = json.loads(source[core.NORMATIVE_ARTIFACT_PATH_V1])
        row = next(candidate for candidate in normative["rows"] if candidate["kind"] == kind)
        row["edges"] = []
        source[core.NORMATIVE_ARTIFACT_PATH_V1] = canonical_json_bytes_v1(normative)
        with pytest.raises(core.CompletionRejectV1) as captured:
            core._derive_requirements_floor_v1(source)
        assert captured.value.code == "VACUOUS_EDGE"


def test_given_one_row_kind_count_mutant_when_derived_then_exact_partition_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    source = _source_map(snapshot)
    normative = json.loads(source[core.NORMATIVE_ARTIFACT_PATH_V1])
    row = next(candidate for candidate in normative["rows"] if candidate["kind"] == "WORKFLOW")
    row["kind"] = "BDD"
    source[core.NORMATIVE_ARTIFACT_PATH_V1] = canonical_json_bytes_v1(normative)

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core._derive_requirements_floor_v1(source)
    assert captured.value.code == "NORMATIVE_KIND_COUNTS"


def test_given_policy_status_mutant_when_derived_then_policy_remains_nonselectable(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    source = _source_map(snapshot)
    normative = json.loads(source[core.NORMATIVE_ARTIFACT_PATH_V1])
    row = next(
        candidate for candidate in normative["rows"] if candidate["kind"] == "UNRESOLVED_POLICY"
    )
    row["status"] = "SELECTABLE"
    source[core.NORMATIVE_ARTIFACT_PATH_V1] = canonical_json_bytes_v1(normative)

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core._derive_requirements_floor_v1(source)
    assert captured.value.code == "UP_POLICY_STATUS"


def test_given_policy_inventory_claim_mutant_when_checked_then_inventory_fact_is_derived(
    snapshot: core.SubjectEvidenceSnapshotV1,
) -> None:
    # Arrange
    mutant = _artifact_object()
    floor = mutant["requirements_floor"]
    assert type(floor) is dict
    floor["unresolved_policy_inventory_complete"] = False

    # Act
    report = _check_mutant(mutant, snapshot)

    # Assert
    assert _assert_closed_failure(report) == "CERTIFICATE_MISMATCH"


@pytest.mark.parametrize("status", ["CLOSED", "PASS", "ACTIVE", "UNKNOWN"])
def test_given_nonopen_plan_vm_status_when_parsed_then_baseline_promotion_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1, status: str
) -> None:
    # Arrange
    source = _source_map(snapshot)
    plan = json.loads(source[core.PLAN_PATH_V1])
    plan["value_movement_gates"][0]["status"] = status
    source[core.PLAN_PATH_V1] = json.dumps(plan, sort_keys=True).encode("utf-8")

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core._parse_plan_baseline_v1(source)
    assert captured.value.code == "PLAN_VM_PROMOTION"


@pytest.mark.parametrize("count", [11, 12, 13])
def test_given_resolution_count_boundary_when_derived_then_only_12_accepts(
    snapshot: core.SubjectEvidenceSnapshotV1, count: int
) -> None:
    # Arrange
    source = _source_map(snapshot)
    _, missing_ids, route_ids = core._derive_requirements_floor_v1(source)
    resolutions = json.loads(source[core.RESOLUTION_ARTIFACT_PATH_V1])
    rows = resolutions["resolution_rows"]
    assert type(rows) is list
    if count == 11:
        rows.pop()
    elif count == 13:
        rows.append(deepcopy(rows[-1]))
    source[core.RESOLUTION_ARTIFACT_PATH_V1] = canonical_json_bytes_v1(resolutions)

    # Act / Assert
    if count == 12:
        result = core._derive_resolution_bijections_v1(source, missing_ids, route_ids)
        assert result["proposed_target_resolution_count"] == 12
    else:
        with pytest.raises(core.CompletionRejectV1) as captured:
            core._derive_resolution_bijections_v1(source, missing_ids, route_ids)
        assert captured.value.code == "RESOLUTION_ROW_COUNT"


@pytest.mark.parametrize("count", [3, 4, 5])
def test_given_route_count_boundary_when_derived_then_only_4_accepts(
    snapshot: core.SubjectEvidenceSnapshotV1, count: int
) -> None:
    # Arrange
    source = _source_map(snapshot)
    _, missing_ids, route_ids = core._derive_requirements_floor_v1(source)
    resolutions = json.loads(source[core.RESOLUTION_ARTIFACT_PATH_V1])
    rows = resolutions["route_resolution_rows"]
    assert type(rows) is list
    if count == 3:
        rows.pop()
    elif count == 5:
        rows.append(deepcopy(rows[-1]))
    source[core.RESOLUTION_ARTIFACT_PATH_V1] = canonical_json_bytes_v1(resolutions)

    # Act / Assert
    if count == 4:
        result = core._derive_resolution_bijections_v1(source, missing_ids, route_ids)
        assert result["route_resolution_count"] == 4
    else:
        with pytest.raises(core.CompletionRejectV1) as captured:
            core._derive_resolution_bijections_v1(source, missing_ids, route_ids)
        assert captured.value.code == "ROUTE_ROW_COUNT"


@pytest.mark.parametrize("mutation", ["reorder_sources", "duplicate_target", "duplicate_route"])
def test_given_resolution_bijection_mutant_when_derived_then_relation_rejects(
    snapshot: core.SubjectEvidenceSnapshotV1, mutation: str
) -> None:
    # Arrange
    source = _source_map(snapshot)
    _, missing_ids, route_ids = core._derive_requirements_floor_v1(source)
    resolutions = json.loads(source[core.RESOLUTION_ARTIFACT_PATH_V1])
    resolution_rows = resolutions["resolution_rows"]
    route_rows = resolutions["route_resolution_rows"]
    assert type(resolution_rows) is list and type(route_rows) is list
    if mutation == "reorder_sources":
        resolution_rows[0], resolution_rows[1] = resolution_rows[1], resolution_rows[0]
        expected_code = "RESOLUTION_SOURCE_BIJECTION"
    elif mutation == "duplicate_target":
        resolution_rows[1]["target_id"] = resolution_rows[0]["target_id"]
        expected_code = "DUPLICATE_ID"
    else:
        route_rows[1]["resolution_id"] = route_rows[0]["resolution_id"]
        expected_code = "DUPLICATE_ID"
    source[core.RESOLUTION_ARTIFACT_PATH_V1] = canonical_json_bytes_v1(resolutions)

    # Act / Assert
    with pytest.raises(core.CompletionRejectV1) as captured:
        core._derive_resolution_bijections_v1(source, missing_ids, route_ids)
    assert captured.value.code == expected_code


@pytest.mark.parametrize("delta", [-1, 0, 1])
def test_given_artifact_byte_limit_neighbor_when_decoded_then_limit_is_exact(delta: int) -> None:
    # Arrange
    size = core.MAX_ARTIFACT_BYTES_V1 + delta
    prefix = b'{"a":"'
    suffix = b'"}'
    raw = prefix + b"a" * (size - len(prefix) - len(suffix)) + suffix
    assert len(raw) == size

    # Act / Assert
    if delta <= 0:
        assert core._decode_canonical_object(raw, "specimen", core.MAX_ARTIFACT_BYTES_V1)["a"]
    else:
        with pytest.raises(core.CompletionRejectV1) as captured:
            core._decode_canonical_object(raw, "specimen", core.MAX_ARTIFACT_BYTES_V1)
        assert captured.value.code == "JSON_BYTE_LIMIT"


@pytest.mark.parametrize("delta", [-1, 0, 1])
def test_given_source_file_byte_limit_neighbor_when_snapshotted_then_limit_is_exact(
    snapshot: core.SubjectEvidenceSnapshotV1, delta: int
) -> None:
    # Arrange
    size = core.MAX_EVIDENCE_FILE_BYTES_V1 + delta
    rows = list(snapshot.source_subject_bytes)
    path, _ = rows[0]
    rows[0] = (path, b"x" * size)
    specimen = replace(snapshot, source_subject_bytes=tuple(rows))

    # Act / Assert
    if delta <= 0:
        observed = core._snapshot_bytes(specimen, current=False)
        assert len(observed[path]) == size
    else:
        with pytest.raises(core.CompletionRejectV1) as captured:
            core._snapshot_bytes(specimen, current=False)
        assert captured.value.code == "SNAPSHOT_FILE_LIMIT"


@pytest.mark.parametrize("count", [13, 14, 15])
def test_given_source_pin_count_neighbor_when_snapshot_validated_then_only_14_accepts(
    snapshot: core.SubjectEvidenceSnapshotV1, count: int
) -> None:
    # Arrange
    source_rows = list(snapshot.source_subject_bytes)
    current_rows = list(snapshot.current_content_bytes)
    if count == 13:
        source_rows.pop()
        current_rows.pop()
    elif count == 15:
        source_rows.append(source_rows[-1])
        current_rows.append(current_rows[-1])
    specimen = replace(
        snapshot,
        source_subject_bytes=tuple(source_rows),
        current_content_bytes=tuple(current_rows),
    )

    # Act / Assert
    if count == 14:
        assert core.build_requirements_floor_completion_artifact_v1(specimen) == _artifact_bytes()
    else:
        with pytest.raises(core.CompletionRejectV1) as captured:
            core.build_requirements_floor_completion_artifact_v1(specimen)
        assert captured.value.code == "SNAPSHOT_FILE_COUNT"


def test_given_runtime_sources_when_scanned_then_no_validation_uses_python_assert() -> None:
    # Arrange
    source_paths = (
        REPO_ROOT / "tools/m6_o005_requirements_floor_completion_v1.py",
        REPO_ROOT / "tools/build_m6_o005_requirements_floor_completion_v1.py",
        REPO_ROOT / "tools/check_m6_o005_requirements_floor_completion_v1.py",
    )

    # Act
    assert_nodes = [
        (path, node.lineno)
        for path in source_paths
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8")))
        if isinstance(node, ast.Assert)
    ]

    # Assert
    assert assert_nodes == []
