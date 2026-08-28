"""AAA evidence for O-005's deterministic research-only requirements registry."""

from __future__ import annotations

import hashlib
import json
import os
import sys
import tracemalloc
from copy import deepcopy
from dataclasses import replace
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

import tools.build_m6_normative_requirements_v1 as build_shell
import tools.check_m6_normative_requirements_v1 as check_shell
import tools.m6_normative_requirements_v1 as core
from tools.build_m6_normative_requirements_v1 import (
    ARTIFACT_MAX_BYTES_V1,
    REPO_ROOT,
    ShellRejectV1,
    _atomic_replace_regular_file_v1,
    _git_binary_v1,
    _git_environment_v1,
    _read_bounded_regular_file_v1,
    _run_git_v1,
    build_artifacts_v1,
    load_source_snapshot_v1,
)
from tools.check_m6_normative_requirements_v1 import check_m6_normative_requirements_v1
from tools.m6_normative_requirements_v1 import (
    SOURCE_SUBJECT_COMMIT_V1,
    SOURCE_SUBJECT_TREE_V1,
    RequirementsRejectV1,
    SourceSnapshotV1,
    build_requirements_registry_v1,
    canonical_json_bytes_v1,
    check_requirements_registry_v1,
    decode_json_object_v1,
)

TEST_QUALITY_V2: dict[str, object] = {
    "obligation": "O-005",
    "mapping_oracle_grade": 1,
    "mapping_oracle_grade_rationale": (
        "The generator and checker share the same deterministic mapping core, so exact "
        "regeneration detects drift but is not an independent semantic oracle."
    ),
    "selected_vector_oracle_grade": 2,
    "selected_vector_oracle_grade_rationale": (
        "Selected semantic tests use literal expected target and relation vectors that do not "
        "derive their expected values from the mapping tables."
    ),
    "ripr": [
        "mutate one authoritative semantic or shell-boundary obligation",
        "propagate the mutation through canonical bytes or a bounded shell input",
        "observe one exact typed fail-closed finding",
        "retain the named mutant after repair",
    ],
    "semantic_mutants": [
        "MUT-VACUOUS-CAPABILITY-EDGE",
        "MUT-VACUOUS-REQUIREMENT-EDGE",
        "MUT-STALE-DONOR-PROMOTION",
        "MUT-PLAN-AUTHORITY-PROMOTION",
        "MUT-VM-GATE-PROMOTION",
        "MUT-PLAN-REQUIREMENTS-FLOOR-PROMOTION",
        "MUT-PLAN-OPERATOR-NESTED-PROMOTION",
        "MUT-PLAN-NORMATIVE-TEXT-PROMOTION",
        "MUT-PLAN-NONCLAIM-GRANT",
        "MUT-PLAN-BOOLEAN-ALIAS",
        "MUT-PLAN-MUTABLE-CROSS-FIELD-SNAPSHOT",
        "MUT-SHARED-ALIAS-VALIDATION-WORK-AMPLIFICATION",
        "MUT-HOSTILE-METACLASS-REJECTION-HOOK",
        "MUT-AMBIENT-RECURSION-LIMIT-ESCAPE",
        "MUT-MANIFEST-COMPLETION-PROMOTION",
        "MUT-BDD-WORKFLOW-INHERITANCE",
        "MUT-INVERSE-EDGE-ERASURE",
        "MUT-NONCANONICAL-EDGE-ORDER",
        "MUT-INVARIANT-FEATURE-COVERAGE",
        "MUT-NONANCESTOR-SUBJECT",
        "MUT-SAME-TYPE-TARGET-SUBSTITUTION",
        "MUT-RELATION-KIND-SUBSTITUTION",
    ],
    "nonclaims": [
        "Tests establish deterministic structural replay only.",
        "Tests do not establish implementation, proof, mounting, release, or value authority.",
        "Direct mutable-object canonicalization assumes caller-exclusive ownership; claim-bearing Plan admission accepts immutable bytes only.",
    ],
}

PLAN_R5_PROMOTION_MUTANT_V1 = "Production authority is ACTIVE and VM-01 is CLOSED."
PLAN_R5_GENERATED_MUTANT_COUNT_V1 = 2_408
PLAN_R5_FUTURE_REPIN_PATHS_V1: tuple[tuple[str, tuple[str | int, ...]], ...] = (
    ("subject", ("subject", "plan_commit_binding")),
    ("normative", ("normative_inputs", 0, "role")),
    ("historical", ("historical_inputs", 0, "authority")),
    ("advisory", ("advisory_reviews", 0, "verdict")),
    ("upstream", ("upstream_dependencies", 0, "classification")),
    ("policy", ("unresolved_semantic_decisions", 0, "topic")),
    ("obligation", ("next_obligations", 7, "required_evidence", 0)),
)


@lru_cache(maxsize=1)
def _snapshot() -> SourceSnapshotV1:
    return load_source_snapshot_v1(REPO_ROOT)


@lru_cache(maxsize=1)
def _artifact_bytes() -> bytes:
    return build_artifacts_v1(REPO_ROOT)[0]


def _artifact() -> dict[str, Any]:
    value = json.loads(_artifact_bytes())
    if type(value) is not dict:
        raise TypeError("generated artifact must be an object")
    return value


def _plan_v2() -> dict[str, Any]:
    """Return one independently mutable Plan V2 specimen for a named mutant."""

    value = json.loads(dict(_snapshot().document_bytes)[core.PLAN_PATH_V1])
    if type(value) is not dict:
        raise TypeError("Plan V2 source must decode to an object")
    return value


def _raw(value: dict[str, Any]) -> bytes:
    return canonical_json_bytes_v1(value)


def _canonical_plan_bytes_oracle_v1(plan: dict[str, Any]) -> bytes:
    """Independent stdlib oracle for the documented canonical JSON commitment."""

    return json.dumps(
        plan,
        allow_nan=False,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")


def _parse_plan_object_v1(
    plan: dict[str, Any],
) -> tuple[tuple[core.SimpleSourceV1, ...], dict[str, object], bytes]:
    """Cross the claim-bearing Plan boundary through immutable bytes only."""

    return core._parse_plan_v1(_canonical_plan_bytes_oracle_v1(plan))


def _repinned_plan_snapshot_v1(
    monkeypatch: pytest.MonkeyPatch, plan_bytes: bytes
) -> SourceSnapshotV1:
    """Model a later Plan-byte/source-blob repin without changing its semantic commitment."""

    baseline = _snapshot()
    replacement_blob = "f" * 40
    plan_sha256 = hashlib.sha256(plan_bytes).hexdigest()
    pins = list(core.SOURCE_PINS_V1)
    documents = list(baseline.document_bytes)
    source_entries = list(baseline.source_subject_entries)
    current_entries = list(baseline.current_head_entries)
    plan_index = next(index for index, pin in enumerate(pins) if pin.path == core.PLAN_PATH_V1)
    pins[plan_index] = replace(
        pins[plan_index], sha256=plan_sha256, git_blob_sha=replacement_blob
    )
    documents[plan_index] = (core.PLAN_PATH_V1, plan_bytes)
    replacement_entry = (core.PLAN_PATH_V1, "100644", "blob", replacement_blob)
    source_entries[plan_index] = replacement_entry
    current_entries[plan_index] = replacement_entry
    monkeypatch.setattr(core, "SOURCE_PINS_V1", tuple(pins))
    return replace(
        baseline,
        document_bytes=tuple(documents),
        source_subject_entries=tuple(source_entries),
        current_head_entries=tuple(current_entries),
    )


def _plan_path_value_v1(root: object, path: tuple[str | int, ...]) -> object:
    value = root
    for component in path:
        if type(component) is str and type(value) is dict:
            value = value[component]
        elif type(component) is int and type(value) is list:
            value = value[component]
        else:
            raise TypeError(f"invalid Plan mutation path: {path!r}")
    return value


def _plan_mutation_specs_v1(
    value: object, path: tuple[str | int, ...] = ()
) -> list[tuple[str, tuple[str | int, ...], object]]:
    """Generate parser-independent field and collection mutations from JSON structure."""

    specs: list[tuple[str, tuple[str | int, ...], object]]
    if type(value) is dict:
        specs = [("unknown-field", path, PLAN_R5_PROMOTION_MUTANT_V1)]
        for key in sorted(value):
            child_path = (*path, key)
            specs.append(("omit-field", child_path, None))
            specs.extend(_plan_mutation_specs_v1(value[key], child_path))
        return specs
    if type(value) is list:
        if not value:
            return [("one", path, [PLAN_R5_PROMOTION_MUTANT_V1])]
        specs = [
            ("zero", path, []),
            ("max-neighbor", path, [*deepcopy(value), deepcopy(value[-1])]),
        ]
        if len(value) > 1:
            specs.append(("one", path, [deepcopy(value[0])]))
        for index, item in enumerate(value):
            specs.extend(
                (
                    (
                        f"omit-index-{index}",
                        path,
                        [
                            deepcopy(entry)
                            for item_index, entry in enumerate(value)
                            if item_index != index
                        ],
                    ),
                    (
                        f"duplicate-index-{index}",
                        path,
                        [
                            *deepcopy(value[: index + 1]),
                            deepcopy(item),
                            *deepcopy(value[index + 1 :]),
                        ],
                    ),
                )
            )
            specs.extend(_plan_mutation_specs_v1(item, (*path, index)))
        for index in range(len(value) - 1):
            if value[index] != value[index + 1]:
                reordered = deepcopy(value)
                reordered[index], reordered[index + 1] = reordered[index + 1], reordered[index]
                specs.append((f"reorder-{index}-{index + 1}", path, reordered))
        return specs
    if type(value) is str:
        return [("mutate-str", path, f"{value} {PLAN_R5_PROMOTION_MUTANT_V1}")]
    if type(value) is bool:
        return [("mutate-bool", path, not value)]
    if type(value) is int:
        return [("mutate-int", path, value + 1)]
    raise TypeError(f"unsupported Plan value at {path!r}: {type(value).__name__}")


def _apply_plan_mutation_v1(
    plan: dict[str, Any], operation: str, path: tuple[str | int, ...], value: object
) -> None:
    if not path:
        if operation != "unknown-field":
            raise ValueError(operation)
        plan["__r5_unknown_promotion__"] = value
        return
    parent = _plan_path_value_v1(plan, path[:-1])
    key = path[-1]
    if operation == "omit-field":
        if type(parent) is not dict or type(key) is not str:
            raise TypeError(path)
        del parent[key]
    elif operation == "unknown-field":
        target = _plan_path_value_v1(plan, path)
        if type(target) is not dict:
            raise TypeError(path)
        target["__r5_unknown_promotion__"] = value
    elif type(parent) is dict and type(key) is str:
        parent[key] = value
    elif type(parent) is list and type(key) is int:
        parent[key] = value
    else:
        raise TypeError(path)


def _plan_nonempty_list_paths_v1(
    value: object, path: tuple[str | int, ...] = ()
) -> list[tuple[tuple[str | int, ...], int]]:
    if type(value) is dict:
        return [
            item
            for key in sorted(value)
            for item in _plan_nonempty_list_paths_v1(value[key], (*path, key))
        ]
    if type(value) is list:
        return [
            (path, len(value)),
            *[
                item
                for index, item_value in enumerate(value)
                for item in _plan_nonempty_list_paths_v1(item_value, (*path, index))
            ],
        ]
    return []


def _report(value: dict[str, Any], snapshot: SourceSnapshotV1 | None = None) -> dict[str, Any]:
    report = check_requirements_registry_v1(_raw(value), snapshot or _snapshot()).to_json()
    if type(report) is not dict:
        raise TypeError("checker report must be an object")
    return report


def _codes(report: dict[str, Any]) -> list[str]:
    findings = report["findings"]
    if type(findings) is not list:
        raise TypeError("findings must be a list")
    return [finding["code"] for finding in findings]


def _row(value: dict[str, Any], requirement_id: str) -> dict[str, Any]:
    matches = [row for row in value["rows"] if row["requirement_id"] == requirement_id]
    if len(matches) != 1:
        raise LookupError(requirement_id)
    return matches[0]


def _target(value: dict[str, Any], target_id: str) -> dict[str, Any]:
    matches = [target for target in value["targets"] if target["target_id"] == target_id]
    if len(matches) != 1:
        raise LookupError(target_id)
    return matches[0]


def _expect_core_reject(raw: bytes) -> RequirementsRejectV1:
    with pytest.raises(RequirementsRejectV1) as captured:
        decode_json_object_v1(raw, "hostile")
    return captured.value


def test_quality_contract_has_exact_oracle_grade_and_nonclaims() -> None:
    # Arrange.
    contract = TEST_QUALITY_V2

    # Act.
    mapping_grade = contract["mapping_oracle_grade"]
    selected_vector_grade = contract["selected_vector_oracle_grade"]
    mutants = contract["semantic_mutants"]
    nonclaims = contract["nonclaims"]

    # Assert.
    assert type(mapping_grade) is int
    assert mapping_grade == 1
    assert type(selected_vector_grade) is int
    assert selected_vector_grade == 2
    assert contract["mapping_oracle_grade_rationale"]
    assert contract["selected_vector_oracle_grade_rationale"]
    assert type(mutants) is list
    assert type(nonclaims) is list
    assert len(mutants) >= 7
    assert len(nonclaims) == 3


def test_registry_replays_exact_inventory_partition_and_claim_ceiling() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    report = _report(artifact)

    # Assert.
    assert report["ok"] is True
    assert artifact["structural_counts"] == {
        "ambiguous_capability_scope_count": 2,
        "bdd_count": 81,
        "capability_count": 103,
        "ce_count": 8,
        "cross_cutting_capability_scope_count": 0,
        "disabled_capability_direct_scope_count": 2,
        "disabled_capability_target_count": 9,
        "enabled_capability_bdd_direct_scope_count": 46,
        "enabled_direct_capability_ce_and_rse_only_scope_count": 2,
        "enabled_direct_capability_rse_only_scope_count": 1,
        "enabled_direct_capability_semantic_scope_count": 54,
        "enabled_direct_capability_wf_or_bdd_scope_count": 51,
        "enabled_direct_capability_workflow_only_scope_count": 5,
        "exclusion_count": 4,
        "global_obligation_count": 5,
        "invariant_count": 14,
        "missing_target_concept_count": 12,
        "requirement_count": 152,
        "route_count": 4,
        "rse_count": 11,
        "target_count": 142,
        "up_count": 20,
        "workflow_count": 18,
    }
    for field in (
        "manifest_complete",
        "production_promotion",
        "release_eligible",
        "requirements_closed",
        "semantic_capability_coverage_complete",
        "semantic_closure_complete",
        "structural_mapping_complete",
        "value_movement_claim_allowed",
    ):
        assert artifact[field] is False
        assert report[field] is False
    assert artifact["source_row_census_complete"] is True
    assert report["source_row_census_complete"] is True
    assert artifact["semantic_target_inventory_complete"] is False
    assert report["semantic_target_inventory_complete"] is False
    assert artifact["production_authority"] == "NONE"
    assert artifact["settlement_authority"] == "NONE"
    assert report["production_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"


def test_r5_canonical_plan_commitment_matches_independent_oracle() -> None:
    # Arrange.
    plan = _plan_v2()

    # Act.
    actual = hashlib.sha256(_canonical_plan_bytes_oracle_v1(plan)).hexdigest()

    # Assert.
    assert actual == core.PLAN_CANONICAL_SHA256_V1


@pytest.mark.parametrize(
    ("specimen", "expected"),
    (
        (None, b"null"),
        (False, b"false"),
        (True, b"true"),
        (0, b"0"),
        (-1, b"-1"),
        ("", b'""'),
        ('quote=" slash=\\ newline=\n', b'"quote=\\" slash=\\\\ newline=\\n"'),
        (
            "snowman=\u2603 non-bmp=\U0001f600",
            b'"snowman=\\u2603 non-bmp=\\ud83d\\ude00"',
        ),
        ([], b"[]"),
        ({}, b"{}"),
        (
            [None, False, 0, "x", {"b": 2, "a": 1}],
            b'[null,false,0,"x",{"a":1,"b":2}]',
        ),
        (
            {"z": [], "a": {"unicode": "\u00e9", "negative": -7}},
            b'{"a":{"negative":-7,"unicode":"\\u00e9"},"z":[]}',
        ),
    ),
)
def test_r5_iterative_canonical_encoder_matches_literal_fixed_vectors(
    specimen: object, expected: bytes
) -> None:
    # Act.
    actual = core.canonical_json_bytes_v1(specimen)

    # Assert.
    assert actual == expected


def test_r5_preserves_o005_source_inventory_mapping() -> None:
    # Arrange.
    snapshot = _snapshot()

    # Act.
    sources = core.parse_sources_v1(snapshot)

    # Assert.
    assert len(sources.workflows) == 18
    assert sum(len(workflow.scenarios) for workflow in sources.workflows) == 81
    assert len(sources.expansions) == 11
    assert len(sources.findings) == 8
    assert len(sources.policies) == 20


@pytest.mark.parametrize(
    ("path", "value", "expected_code", "expected_suffix"),
    (
        (("authority", "production_authority"), "ACTIVE", "SOURCE_PROMOTION", "production_authority"),
        (("authority", "release_ready"), True, "SOURCE_PROMOTION", "release_ready"),
        (("admission_model", "authority_effect"), "ACTIVE", "SOURCE_PROMOTION", "admission_model"),
        (
            ("baseline_verdict", "closed_value_movement_gates"),
            1,
            "SOURCE_PROMOTION",
            "closed_value_movement_gates",
        ),
        (
            ("value_movement_gates", 0, "status"),
            "CLOSED",
            "SOURCE_PROMOTION",
            "value_movement_gates[0].status",
        ),
        (
            ("release_gate", "whole_value_movement_claim"),
            "ALLOWED",
            "SOURCE_PROMOTION",
            "whole_value_movement_claim",
        ),
        (
            ("requirements_floor", "manifest_complete"),
            True,
            "SOURCE_PROMOTION",
            "requirements_floor",
        ),
        (
            ("next_obligations", 5, "closes"),
            ["VM-01"],
            "SOURCE_PROMOTION",
            "next_obligations[5].closes[0]",
        ),
        (("gap_registry", 8, "status"), "CLOSED", "SOURCE_PROMOTION", "gap_registry[8].status"),
    ),
)
def test_r5_claim_ceiling_mutants_have_typed_rejects(
    path: tuple[str | int, ...], value: object, expected_code: str, expected_suffix: str
) -> None:
    # Arrange.
    plan = _plan_v2()
    _apply_plan_mutation_v1(plan, "replace", path, value)

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        _parse_plan_object_v1(plan)

    # Assert.
    assert captured.value.code == expected_code
    assert captured.value.path.endswith(expected_suffix)


@pytest.mark.parametrize(
    ("path", "value", "expected_code"),
    (
        (("authority", "release_ready"), 0, "TYPE_ERROR"),
        (("baseline_verdict", "closed_value_movement_gates"), False, "TYPE_ERROR"),
        (("value_movement_gates", 0, "status"), True, "TYPE_ERROR"),
        (("subject", "base_worktree_clean"), 1, "PLAN_SEMANTIC_COMMITMENT"),
    ),
)
def test_r5_bool_int_aliases_reject_deterministically(
    path: tuple[str | int, ...], value: object, expected_code: str
) -> None:
    # Arrange.
    plan = _plan_v2()
    _apply_plan_mutation_v1(plan, "replace", path, value)

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        _parse_plan_object_v1(plan)

    # Assert.
    assert captured.value.code == expected_code


@pytest.mark.parametrize("status", ("CLOSED", "PASS", "PASSED", "CLOSED_ON_SUBJECT", "UNKNOWN"))
def test_r5_vm_gate_status_allowlist_rejects_every_nonopen_status(status: str) -> None:
    # Arrange.
    plan = _plan_v2()
    _apply_plan_mutation_v1(plan, "replace", ("value_movement_gates", 0, "status"), status)

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        _parse_plan_object_v1(plan)

    # Assert.
    assert captured.value.code == "SOURCE_PROMOTION"
    assert captured.value.path.endswith("value_movement_gates[0].status")


@pytest.mark.parametrize("operation", ("omit-field", "unknown-field"))
def test_r5_claim_subobjects_have_closed_field_sets(operation: str) -> None:
    # Arrange.
    plan = _plan_v2()
    path = ("authority", "production_ready") if operation == "omit-field" else ("authority",)
    _apply_plan_mutation_v1(plan, operation, path, PLAN_R5_PROMOTION_MUTANT_V1)

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        _parse_plan_object_v1(plan)

    # Assert.
    assert captured.value.code == "CLOSED_FIELDS"
    assert captured.value.path.endswith(".authority")


def test_r5_hostile_python_object_and_duplicate_json_key_reject_before_admission() -> None:
    # Arrange.
    plan = _plan_v2()
    subject = plan["subject"]
    if type(subject) is not dict:
        raise TypeError("subject must be an object")
    subject["base_worktree_clean"] = object()
    duplicate_key = b'{"authority":{"production_authority":"NONE","production_authority":"ACTIVE"}}'

    # Act.
    with pytest.raises(RequirementsRejectV1) as hostile_captured:
        core._parse_plan_v1(plan)  # type: ignore[arg-type]
    duplicate_captured = _expect_core_reject(duplicate_key)

    # Assert.
    assert hostile_captured.value.code == "JSON_BYTES_TYPE"
    assert duplicate_captured.code == "JSON_DECODE"


def test_r5_plan_boundary_rejects_mutable_cross_field_snapshot_before_field_access() -> None:
    # Arrange. This is the minimized construction-level closure for a trace
    # that combined authority and gate-count fields which never coexisted.
    plan = _plan_v2()
    authority = plan["authority"]
    baseline = plan["baseline_verdict"]
    if type(authority) is not dict or type(baseline) is not dict:
        raise TypeError("Plan claim fields must be objects")
    authority["production_authority"] = "NONE"
    baseline["closed_value_movement_gates"] = 1

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        core._parse_plan_v1(plan)  # type: ignore[arg-type]

    # Assert. The claim-bearing parser admits immutable bytes only, so no
    # schedule can assemble a synthetic cross-field state from this object.
    assert captured.value.code == "JSON_BYTES_TYPE"
    assert authority["production_authority"] == "NONE"
    assert baseline["closed_value_movement_gates"] == 1


@pytest.mark.parametrize("sign", (-1, 1))
def test_r5_direct_integer_digit_limit_has_exact_bva_and_typed_reject(sign: int) -> None:
    # Arrange.
    limit = core.MAX_JSON_INTEGER_MAGNITUDE_EXCLUSIVE_V1
    specimens = (
        (sign * 10 ** (core.MAX_JSON_INTEGER_DIGITS_V1 - 2), "ACCEPTED"),
        (sign * (limit - 1), "ACCEPTED"),
        (sign * limit, "JSON_INTEGER_LIMIT"),
    )

    # Act.
    outcomes: list[tuple[str, str]] = []
    for amount, _expected in specimens:
        try:
            encoded = core.canonical_json_bytes_v1({"amount": amount})
        except RequirementsRejectV1 as captured:
            outcomes.append((captured.code, captured.path))
        else:
            outcomes.append(("ACCEPTED" if encoded else "EMPTY", "$.amount"))

    # Assert.
    assert outcomes == [(expected, "$.amount") for _amount, expected in specimens]


def test_r5_wide_list_below_long_key_has_bounded_path_allocation() -> None:
    # Arrange. The former eager path renderer repeated the 4,096-character key
    # for every list element and exceeded 34 MB of traced allocation.
    specimen = {"k" * 4_096: [None] * 8_192}

    # Act.
    tracemalloc.start()
    try:
        encoded = core.canonical_json_bytes_v1(specimen)
        _current, peak = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()

    # Assert. This is a RIPR resource oracle: linked path tokens keep breadth
    # independent of ancestor-string length while canonical encoding succeeds.
    assert encoded
    assert peak < 8_000_000


def test_r5_direct_cycle_rejects_at_depth_bound_with_bounded_finding_path() -> None:
    # Arrange.
    cycle: list[object] = []
    cycle.append(cycle)

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        core.canonical_json_bytes_v1({"cycle": cycle})

    # Assert.
    assert captured.value.code == "JSON_DEPTH_LIMIT"
    assert captured.value.path.startswith("$.cycle[0]")
    assert len(captured.value.path) <= core.MAX_FINDING_PATH_CHARS_V1


def test_r5_wide_direct_container_rejects_before_breadth_stack_allocation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange. The former traversal enqueued every child and diagnostic path
    # before observing the next node-limit violation.
    specimen = [None] * 100_000
    monkeypatch.setattr(core, "MAX_JSON_NODES_V1", 2)

    # Act.
    tracemalloc.start()
    try:
        with pytest.raises(RequirementsRejectV1) as captured:
            core.canonical_json_bytes_v1(specimen)
        _current, peak = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()

    # Assert.
    assert captured.value.code == "JSON_NODE_LIMIT"
    assert peak < 1_000_000


def test_r5_shared_alias_expansion_rejects_at_canonical_byte_limit() -> None:
    # Arrange. Shared Python references must be charged once per serialized
    # occurrence so an input object cannot expand to an unbounded JSON output.
    shared = "v" * 4_096
    specimen = {"items": [shared] * 8_192}

    # Act.
    tracemalloc.start()
    try:
        with pytest.raises(RequirementsRejectV1) as captured:
            core.canonical_json_bytes_v1(specimen)
        _current, peak = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()

    # Assert.
    assert captured.value.code == "JSON_BYTE_LIMIT"
    assert captured.value.path == "$.items[255]"
    assert peak < 4_000_000


def test_r5_shared_long_aliases_are_cumulatively_charged_before_unbounded_validation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange. A shallow 1,024-element list formerly rescanned a shared
    # 131,072-character value 1,024 times before canonical encoding rejected it.
    shared = "v" * core.MAX_JSON_STRING_CHARS_V1
    specimen = {"items": [shared] * 1_024}
    original = core._validate_json_string_v1
    validated_occurrences = 0

    def counted(value: str, path: str | core._JsonPathV1) -> None:
        nonlocal validated_occurrences
        validated_occurrences += 1
        original(value, path)

    monkeypatch.setattr(core, "_validate_json_string_v1", counted)

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        core.canonical_json_bytes_v1(specimen)

    # Assert. One key plus at most eight full shared-value occurrences exhaust
    # the one-MiB lower bound on canonical bytes.
    assert captured.value.code == "JSON_BYTE_LIMIT"
    assert validated_occurrences <= 9


@pytest.mark.parametrize("container_kind", ("dict", "list"))
def test_r5_canonical_encoding_uses_one_owned_snapshot_under_same_size_mutation(
    monkeypatch: pytest.MonkeyPatch, container_kind: str
) -> None:
    # Arrange. The mutation is injected while the selected value is being
    # validated, after the traversal has observed it and before encoding.
    specimen: dict[str, object] | list[object]
    specimen = {"value": "SAFE"} if container_kind == "dict" else ["SAFE"]
    original = core._validate_json_string_v1
    mutation_count = 0

    def mutate_source(value: str, path: str | core._JsonPathV1) -> None:
        nonlocal mutation_count
        original(value, path)
        if value != "SAFE" or mutation_count:
            return
        mutation_count += 1
        if type(specimen) is dict:
            specimen["value"] = "EVIL"
        else:
            if type(specimen) is not list:
                raise TypeError("specimen must be an exact JSON container")
            specimen[0] = "EVIL"

    monkeypatch.setattr(core, "_validate_json_string_v1", mutate_source)

    # Act.
    encoded = core.canonical_json_bytes_v1(specimen)

    # Assert. Encoding consumes the value already copied into the owned
    # snapshot; a caller mutation cannot change the admitted bytes.
    assert mutation_count == 1
    assert b"SAFE" in encoded
    assert b"EVIL" not in encoded


def test_r5_plan_extraction_uses_same_owned_snapshot_as_semantic_commitment(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange. Inject the former commitment-to-extraction race at the exact
    # boundary after commitment verification.
    plan = _plan_v2()
    policies = plan["unresolved_semantic_decisions"]
    if type(policies) is not list or type(policies[0]) is not dict:
        raise TypeError("Plan policy specimen must be an object")
    expected_topic = policies[0]["topic"]
    raw_plan = _canonical_plan_bytes_oracle_v1(plan)
    original = core._require_plan_semantic_commitment_v1

    def mutate_caller_after_commitment(document: dict[str, object]) -> None:
        original(document)
        policies[0]["topic"] = "FORGED_AFTER_COMMITMENT"

    monkeypatch.setattr(
        core, "_require_plan_semantic_commitment_v1", mutate_caller_after_commitment
    )

    # Act.
    parsed_policies, _floor, _anchors = core._parse_plan_v1(raw_plan)
    first_policy = json.loads(parsed_policies[0].fields_bytes)

    # Assert. The parser extracts from its owned committed snapshot.
    assert policies[0]["topic"] == "FORGED_AFTER_COMMITMENT"
    assert first_policy["topic"] == expected_topic


def test_r5_unsupported_type_rejection_does_not_invoke_hostile_metaclass() -> None:
    # Arrange.
    name_hook_calls = 0

    class HostileMeta(type):
        def __getattribute__(cls, name: str) -> object:
            nonlocal name_hook_calls
            if name == "__name__":
                name_hook_calls += 1
                raise RuntimeError("hostile metaclass name hook executed")
            return super().__getattribute__(name)

    class HostileValue(metaclass=HostileMeta):
        pass

    specimen = {"value": HostileValue()}

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        core.canonical_json_bytes_v1(specimen)

    # Assert.
    assert captured.value.code == "JSON_TYPE"
    assert name_hook_calls == 0


@pytest.mark.parametrize(
    ("recursion_limit", "expected"),
    (
        (core.MIN_PYTHON_RECURSION_LIMIT_V1 - 1, "JSON_RUNTIME_RECURSION_LIMIT"),
        (core.MIN_PYTHON_RECURSION_LIMIT_V1, "ACCEPTED"),
    ),
)
def test_r5_python_recursion_runtime_floor_has_exact_bva_and_typed_rejection(
    recursion_limit: int, expected: str
) -> None:
    # Arrange. Depth 64 is inside the declared JSON domain. The earlier
    # traversal leaked raw RecursionError under a low process-wide limit.
    specimen: object = None
    for _index in range(core.MAX_JSON_DEPTH_V1):
        specimen = [specimen]
    original_limit = sys.getrecursionlimit()

    # Act.
    try:
        sys.setrecursionlimit(recursion_limit)
        try:
            encoded = core.canonical_json_bytes_v1(specimen)
        except RequirementsRejectV1 as captured:
            outcome = captured.code
            encoded = b""
        else:
            outcome = "ACCEPTED"
    finally:
        sys.setrecursionlimit(original_limit)

    # Assert.
    assert outcome == expected
    if expected == "ACCEPTED":
        assert encoded.startswith(b"[")
        assert encoded.endswith(b"]")
        assert encoded.count(b"[") == core.MAX_JSON_DEPTH_V1


def test_r5_non_bmp_canonical_expansion_is_charged_at_byte_boundary() -> None:
    # Arrange. UTF-8 input can be compact while canonical ensure_ascii output
    # uses twelve bytes per non-BMP character.
    specimen = {"value": "\U0001f600" * 100_000}

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        core.canonical_json_bytes_v1(specimen)

    # Assert.
    assert captured.value.code == "JSON_BYTE_LIMIT"
    assert captured.value.path == "$"


def test_r5_repin_accepts_format_and_object_key_order_without_semantic_change(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange.
    plan = _plan_v2()
    reordered = {key: plan[key] for key in reversed(tuple(plan))}
    source_bytes = json.dumps(reordered, ensure_ascii=True, indent=2, sort_keys=False).encode("ascii")
    snapshot = _repinned_plan_snapshot_v1(monkeypatch, source_bytes)

    # Act.
    sources = core.parse_sources_v1(snapshot)

    # Assert.
    assert len(sources.policies) == 20
    assert sum(len(workflow.scenarios) for workflow in sources.workflows) == 81


@pytest.mark.parametrize(("family", "path"), PLAN_R5_FUTURE_REPIN_PATHS_V1)
def test_r5_semantic_rejection_survives_future_source_repin(
    monkeypatch: pytest.MonkeyPatch, family: str, path: tuple[str | int, ...]
) -> None:
    # Arrange.
    plan = _plan_v2()
    _apply_plan_mutation_v1(plan, f"future-repin-{family}", path, PLAN_R5_PROMOTION_MUTANT_V1)
    snapshot = _repinned_plan_snapshot_v1(monkeypatch, _canonical_plan_bytes_oracle_v1(plan))

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        core.parse_sources_v1(snapshot)

    # Assert.
    assert captured.value.code == "PLAN_SEMANTIC_COMMITMENT"


@pytest.mark.parametrize(
    ("path", "value"),
    (
        (("requirements_floor", "classification"), "COMPLETE_AND_RELEASE_READY"),
        (("baseline_verdict", "estimate_warning"), PLAN_R5_PROMOTION_MUTANT_V1),
        (("vm_gate_promotion", "rule"), "An individual obligation may close a VM gate."),
        (("nonclaims", 0), "This Plan grants release authority."),
    ),
)
def test_r5_r3_semantic_blockers_remain_rejected(
    path: tuple[str | int, ...], value: object
) -> None:
    # Arrange.
    plan = _plan_v2()
    _apply_plan_mutation_v1(plan, "r3-blocker", path, value)

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        _parse_plan_object_v1(plan)

    # Assert.
    assert captured.value.code == "PLAN_SEMANTIC_COMMITMENT"


def _assert_r5_mutation_surface_coverage_v1(
    plan: dict[str, Any], mutation_specs: list[tuple[str, tuple[str | int, ...], object]]
) -> None:
    mutation_keys = {(operation, path) for operation, path, _value in mutation_specs}
    root_omissions = {
        path[0]
        for operation, path, _value in mutation_specs
        if operation == "omit-field" and len(path) == 1
    }
    obligations = plan["next_obligations"]
    policies = plan["unresolved_semantic_decisions"]
    if type(obligations) is not list or type(policies) is not list:
        raise TypeError("Plan obligations and policies must be lists")
    operator_scalar_paths: list[tuple[str | int, ...]] = []
    evidence_paths: list[tuple[str | int, ...]] = []
    for obligation_index, obligation in enumerate(obligations):
        if type(obligation) is not dict or obligation["obligation_id"] == "O-005":
            continue
        for field in ("phase", "priority", "title"):
            operator_scalar_paths.append(("next_obligations", obligation_index, field))
        evidence = obligation["required_evidence"]
        if type(evidence) is not list:
            raise TypeError("required_evidence must be a list")
        evidence_paths.extend(
            ("next_obligations", obligation_index, "required_evidence", evidence_index)
            for evidence_index in range(len(evidence))
        )
    up_topic_paths = [
        ("unresolved_semantic_decisions", policy_index, "topic")
        for policy_index in range(len(policies))
    ]
    list_operations: dict[tuple[str | int, ...], set[str]] = {}
    for operation, path, _value in mutation_specs:
        if operation in {"zero", "one", "max-neighbor"}:
            list_operations.setdefault(path, set()).add(operation)
    assert len(plan) == 24
    assert root_omissions == set(plan)
    assert len(operator_scalar_paths) + len(obligations) - 1 == 60
    assert len(evidence_paths) == 81
    assert len(up_topic_paths) == 20
    assert all(("mutate-str", path) in mutation_keys for path in operator_scalar_paths)
    assert all(("mutate-str", path) in mutation_keys for path in evidence_paths)
    assert all(("mutate-str", path) in mutation_keys for path in up_topic_paths)
    for list_path, length in _plan_nonempty_list_paths_v1(plan):
        if length > 0:
            assert {"zero", "max-neighbor"} <= list_operations[list_path]
            if length > 1:
                assert "one" in list_operations[list_path]
    assert any(operation == "unknown-field" for operation, _path, _value in mutation_specs)
    assert any(operation.startswith("duplicate-index-") for operation, _path, _value in mutation_specs)
    assert any(operation.startswith("reorder-") for operation, _path, _value in mutation_specs)


def test_r5_generated_plan_mutation_matrix_has_no_semantic_survivors() -> None:
    # Arrange.
    plan = _plan_v2()
    mutation_specs = _plan_mutation_specs_v1(plan)
    survivors: list[str] = []

    # Act.
    for operation, path, value in mutation_specs:
        mutant = deepcopy(plan)
        _apply_plan_mutation_v1(mutant, operation, path, value)
        try:
            _parse_plan_object_v1(mutant)
        except RequirementsRejectV1:
            continue
        rendered_path = ".".join(str(component) for component in path) or "<root>"
        survivors.append(f"{operation}:{rendered_path}")

    # Assert.
    _assert_r5_mutation_surface_coverage_v1(plan, mutation_specs)
    assert len(mutation_specs) == PLAN_R5_GENERATED_MUTANT_COUNT_V1
    assert survivors == []


def test_source_roles_preserve_current_checker_and_stale_donor_distinction() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    roles = {pin["path"]: pin for pin in artifact["source_pins"]}

    # Assert.
    assert roles[core.PLAN_PATH_V1]["source_role"] == (
        "CURRENT_CHECKER_VALID_RESEARCH_PLAN_PENDING_ADMISSION"
    )
    assert roles[core.MANIFEST_PATH_V1]["source_role"] == (
        "CURRENT_CHECKER_VALID_PROVISIONAL_CLOSED_NAME_MANIFEST"
    )
    assert roles[core.ATDD_PATH_V1]["source_gate_status"] == (
        "STALE_INTERNAL_PROVENANCE_RESEARCH_ONLY_DRAFT"
    )
    assert roles[core.LUNA_PATH_V1]["source_gate_status"] == (
        "STALE_INTERNAL_PROVENANCE_ADVISORY_ONLY"
    )


def test_capability_inverse_inventory_is_lane_qualified_and_disabled_is_not_coverage() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    capabilities = [
        target for target in artifact["targets"] if target["target_type"] == "LANE_CAPABILITY"
    ]
    disabled = [
        target
        for target in capabilities
        if target["lane_disposition"] == "DISABLED_PENDING_COMPLETE_PROFILE"
    ]

    # Assert.
    assert len(capabilities) == 103
    assert len({target["target_id"] for target in capabilities}) == 103
    assert all(target["target_id"].count(":") == 2 for target in capabilities)
    assert disabled
    assert all(target["status"] == "DISABLED_PENDING_COMPLETE_PROFILE" for target in disabled)
    for capability_id in (
        "registered_external_lock",
        "registered_external_burn",
        "registered_external_release",
        "registered_external_mint",
        "external_timeout",
        "external_refund",
    ):
        target = _target(artifact, f"lane_capability:EXTERNAL_CUSTODY:{capability_id}")
        assert target["inbound_edges"] == []


def test_global_and_missing_targets_are_typed_non_authoritative_and_not_capabilities() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    global_targets = [
        target for target in artifact["targets"] if target["target_type"] == "GLOBAL_OBLIGATION"
    ]
    missing_targets = [
        target
        for target in artifact["targets"]
        if target["target_type"] == "MISSING_TARGET_CONCEPT"
    ]

    # Assert.
    assert {target["global_obligation_id"] for target in global_targets} == {
        "atomic_publication_reopen_authority",
        "closed_command_language_and_profile_isolation",
        "committed_effect_membership",
        "whole_economic_delta_certificate",
        "workflow_model_evidence_coverage_registry",
    }
    assert {target["missing_target_concept_id"] for target in missing_targets} == {
        "generic_non_managed_burn",
        "generic_non_managed_issue",
        "pending_asset_bearing_intent_terminal_owner",
        "perps_realized_pnl_settlement",
        "perps_request_terminal_owner",
        "sealed_auction_batch_terminal_state",
        "sealed_auction_commitment_bond_inventory_payment_reservation_terminal_disposition",
        "sealed_auction_fee_allocation",
        "sealed_auction_fee_terminal_disposition",
        "sealed_auction_residue_terminal_disposition",
        "external_effect_delivery",
        "zusd_faucet_issuance_rejection",
    }
    assert all(target["status"] == "GLOBAL_OBLIGATION_UNIMPLEMENTED" for target in global_targets)
    assert all(
        target["status"] == "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST"
        for target in missing_targets
    )
    assert all(
        target["lane_id"] is None and target["capability_id"] is None for target in global_targets
    )
    assert all(
        target["lane_id"] is None and target["capability_id"] is None for target in missing_targets
    )


def test_global_obligation_rows_and_generic_issue_burn_gaps_keep_exact_concepts() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    global_target_by_row = {
        requirement_id: {
            edge["target_id"]
            for edge in _row(artifact, requirement_id)["edges"]
            if edge["relation_type"] == "GLOBAL_OBLIGATION_SCOPE"
        }
        for requirement_id in ("RSE-002", "RSE-003", "RSE-010", "RSE-011", "BDD-062")
    }
    rse007_targets = {
        edge["target_id"]
        for edge in _row(artifact, "RSE-007")["edges"]
        if not edge["target_id"].startswith("invariant:")
    }

    # Assert.
    assert global_target_by_row == {
        "BDD-062": {"global_obligation:committed_effect_membership"},
        "RSE-002": {"global_obligation:closed_command_language_and_profile_isolation"},
        "RSE-003": {"global_obligation:whole_economic_delta_certificate"},
        "RSE-010": {"global_obligation:atomic_publication_reopen_authority"},
        "RSE-011": {"global_obligation:workflow_model_evidence_coverage_registry"},
    }
    assert rse007_targets == {
        "lane_capability:SPOT_LIQUIDITY:pool_create",
        "missing_target_concept:generic_non_managed_burn",
        "missing_target_concept:generic_non_managed_issue",
    }
    assert "lane_capability:ASSET_TRANSFER:managed_issue" not in rse007_targets
    assert "lane_capability:ASSET_TRANSFER:managed_burn" not in rse007_targets


def test_research_nonclaims_disclose_pair_atomicity_and_directory_premise() -> None:
    # Arrange.
    nonclaims = _artifact()["nonclaims"]

    # Act.
    rendered = "\n".join(nonclaims)

    # Assert.
    assert "crash can leave a mixed pair" in rendered
    assert "trusted single-writer output directory" in rendered


def test_markdown_uses_requirements_scope_classification_and_disabled_direct_count() -> None:
    # Arrange.
    expected_count = _artifact()["structural_counts"]["disabled_capability_direct_scope_count"]

    # Act.
    markdown = build_artifacts_v1(REPO_ROOT)[1]

    # Assert.
    assert "These partitions describe requirements-scope classification." in markdown
    assert "These partitions describe requirement authority." not in markdown
    assert f"Disabled capability targets with direct semantic scope: {expected_count}" in markdown


def test_exact_bdd_parentage_and_invariant_source_laws_replay_with_inverse_coverage() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    bdd_rows = [row for row in artifact["rows"] if row["kind"] == "BDD"]
    invariant_rows = [row for row in artifact["rows"] if row["kind"] == "INVARIANT"]
    invariant_targets = [
        target for target in artifact["targets"] if target["target_type"] == "INVARIANT"
    ]

    # Assert.
    assert len(bdd_rows) == 81
    assert all(row["parent_requirement_id"].startswith("WF-") for row in bdd_rows)
    assert len(invariant_rows) == 14
    assert all(row["edges"] == [] for row in invariant_rows)
    assert len(invariant_targets) == 14
    for target in invariant_targets:
        assert target["source_fields"]["id"] == target["invariant_id"]
        assert target["source_fields"]["law"]
        assert any(
            edge["relation_type"]
            in {"BDD_INVARIANT_REFERENCE", "CE_INVARIANT_REFERENCE", "RSE_INVARIANT_SCOPE"}
            for edge in target["inbound_edges"]
        )


def test_workflow_semantics_do_not_infer_adjacent_policy_features() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    mapped = {
        requirement_id: {edge["target_id"] for edge in _row(artifact, requirement_id)["edges"]}
        for requirement_id in ("WF-04", "WF-10", "WF-12", "WF-13")
    }

    # Assert.
    assert mapped["WF-04"] == {
        "lane_capability:ZUSD_MONETARY:collateral_deposit",
        "lane_capability:ZUSD_MONETARY:collateral_withdraw",
    }
    assert mapped["WF-10"] == {
        "lane_capability:PERPS_MARKET:fee_allocation",
        "lane_capability:PERPS_MARKET:funding_accrual",
        "lane_capability:PERPS_MARKET:insurance_reserve",
        "lane_capability:PERPS_MARKET:position_adjust",
        "lane_capability:PERPS_MARKET:position_open",
        "lane_capability:PERPS_MARKET:terminal_closeout",
        "required_route:perps_epoch_settlement",
    }
    assert mapped["WF-12"] == {
        "lane_capability:ORACLE_MARKET:report_finality",
        "lane_capability:ORACLE_MARKET:report_submit",
    }
    assert mapped["WF-13"] == {
        "lane_capability:GOVERNANCE_MIGRATION:release_activation",
        "lane_capability:GOVERNANCE_MIGRATION:schema_migration",
        "lane_capability:GOVERNANCE_MIGRATION:writer_epoch_rotation",
    }


def test_cross_lane_liquidation_source_is_explicitly_ambiguous() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    edges = _row(artifact, "WF-09")["edges"]

    # Assert.
    assert {edge["relation_type"] for edge in edges} == {"AMBIGUOUS_SOURCE_SCOPE"}
    assert {edge["target_id"] for edge in edges} == {
        "lane_capability:PERPS_MARKET:liquidation",
        "lane_capability:ZUSD_MONETARY:liquidation",
        "required_route:perps_epoch_settlement",
        "required_route:zusd_liquidation_settlement",
    }
    for requirement_id in ("BDD-034", "BDD-035", "BDD-036", "BDD-037", "BDD-038"):
        child_edges = _row(artifact, requirement_id)["edges"]
        assert {
            edge["target_id"]
            for edge in child_edges
            if edge["relation_type"] == "AMBIGUOUS_SOURCE_SCOPE"
        } == {
            "lane_capability:PERPS_MARKET:liquidation",
            "lane_capability:ZUSD_MONETARY:liquidation",
        }
        assert all(not edge["target_id"].startswith("required_route:") for edge in child_edges)
        assert all(edge["relation_type"] != "CAPABILITY_SEMANTIC_SCOPE" for edge in child_edges)


def test_publication_recovery_rows_are_global_constraints_without_feature_semantics() -> None:
    # Arrange.
    artifact = _artifact()
    rows = [_row(artifact, item) for item in ("WF-14", "BDD-057", "BDD-058", "BDD-059", "BDD-060")]

    # Act.
    relations = {edge["relation_type"] for row in rows for edge in row["edges"]}
    targets = {edge["target_id"] for row in rows for edge in row["edges"]}

    # Assert.
    assert relations <= {
        "BDD_INVARIANT_REFERENCE",
        "CROSS_CUTTING_CONSTRAINT",
        "GLOBAL_OBLIGATION_SCOPE",
    }
    assert all(not target.startswith("lane_capability:") for target in targets)


def test_rse008_has_only_named_sealed_lifecycle_and_two_missing_terminal_owners() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    row = _row(artifact, "RSE-008")
    capability_edges = [
        edge for edge in row["edges"] if edge["target_id"].startswith("lane_capability:")
    ]
    missing_edges = [
        edge for edge in row["edges"] if edge["target_id"].startswith("missing_target_concept:")
    ]

    # Assert.
    assert {edge["target_id"] for edge in capability_edges} == {
        "lane_capability:SEALED_AUCTION:auction_cancel",
        "lane_capability:SEALED_AUCTION:auction_expiry",
        "lane_capability:SEALED_AUCTION:bond_accounting_location",
        "lane_capability:SEALED_AUCTION:refund",
        "lane_capability:SEALED_AUCTION:slash",
    }
    assert {edge["relation_type"] for edge in capability_edges} == {"CAPABILITY_SEMANTIC_SCOPE"}
    assert {edge["target_id"] for edge in missing_edges} == {
        "missing_target_concept:pending_asset_bearing_intent_terminal_owner",
        "missing_target_concept:perps_request_terminal_owner",
    }
    assert all(edge["relation_type"] == "MISSING_TARGET_CONCEPT_SCOPE" for edge in missing_edges)
    assert all("FARM_INCENTIVES" not in edge["target_id"] for edge in row["edges"])
    assert all("STRATEGY_ESCROW" not in edge["target_id"] for edge in row["edges"])
    assert row["status"] == "REQUIRED_EXPANSION_UNRESOLVED"


@pytest.mark.parametrize(
    ("requirement_id", "expected_domain_edges"),
    (
        (
            "BDD-077",
            {
                (
                    "CAPABILITY_SEMANTIC_SCOPE",
                    "lane_capability:SEALED_AUCTION:deterministic_clearing",
                ),
                (
                    "CAPABILITY_SEMANTIC_SCOPE",
                    "lane_capability:SEALED_AUCTION:inventory_settlement",
                ),
                ("CAPABILITY_SEMANTIC_SCOPE", "lane_capability:SEALED_AUCTION:payment_settlement"),
                ("CAPABILITY_SEMANTIC_SCOPE", "lane_capability:SEALED_AUCTION:refund"),
                ("CAPABILITY_SEMANTIC_SCOPE", "lane_capability:SEALED_AUCTION:slash"),
                (
                    "MISSING_TARGET_CONCEPT_SCOPE",
                    "missing_target_concept:sealed_auction_batch_terminal_state",
                ),
                (
                    "MISSING_TARGET_CONCEPT_SCOPE",
                    "missing_target_concept:sealed_auction_fee_allocation",
                ),
                (
                    "MISSING_TARGET_CONCEPT_SCOPE",
                    "missing_target_concept:sealed_auction_residue_terminal_disposition",
                ),
            },
        ),
        (
            "BDD-079",
            {
                ("CAPABILITY_SEMANTIC_SCOPE", "lane_capability:SEALED_AUCTION:auction_cancel"),
                ("CAPABILITY_SEMANTIC_SCOPE", "lane_capability:SEALED_AUCTION:auction_expiry"),
                (
                    "MISSING_TARGET_CONCEPT_SCOPE",
                    "missing_target_concept:sealed_auction_batch_terminal_state",
                ),
                (
                    "MISSING_TARGET_CONCEPT_SCOPE",
                    "missing_target_concept:sealed_auction_commitment_bond_inventory_payment_reservation_terminal_disposition",
                ),
                (
                    "MISSING_TARGET_CONCEPT_SCOPE",
                    "missing_target_concept:sealed_auction_fee_terminal_disposition",
                ),
            },
        ),
    ),
)
def test_sealed_auction_settlement_and_cancellation_terminal_concepts_are_literal(
    requirement_id: str, expected_domain_edges: set[tuple[str, str]]
) -> None:
    # Arrange.
    row = _row(_artifact(), requirement_id)

    # Act.
    observed = {
        (edge["relation_type"], edge["target_id"])
        for edge in row["edges"]
        if not edge["target_id"].startswith("invariant:")
    }

    # Assert.
    assert observed == expected_domain_edges


@pytest.mark.parametrize(
    ("requirement_id", "expected_edges"),
    (
        (
            "WF-15",
            {
                (
                    "CAPABILITY_SEMANTIC_SCOPE",
                    "lane_capability:EXTERNAL_CUSTODY:destination_idempotency",
                ),
                (
                    "CAPABILITY_SEMANTIC_SCOPE",
                    "lane_capability:EXTERNAL_CUSTODY:outbox_acknowledgment",
                ),
                ("MISSING_TARGET_CONCEPT_SCOPE", "missing_target_concept:external_effect_delivery"),
            },
        ),
        (
            "BDD-061",
            {
                ("BDD_INVARIANT_REFERENCE", "invariant:INV-010"),
                ("GLOBAL_OBLIGATION_SCOPE", "global_obligation:committed_effect_membership"),
                ("MISSING_TARGET_CONCEPT_SCOPE", "missing_target_concept:external_effect_delivery"),
            },
        ),
        (
            "BDD-063",
            {
                ("BDD_INVARIANT_REFERENCE", "invariant:INV-010"),
                (
                    "CAPABILITY_SEMANTIC_SCOPE",
                    "lane_capability:EXTERNAL_CUSTODY:destination_idempotency",
                ),
                ("MISSING_TARGET_CONCEPT_SCOPE", "missing_target_concept:external_effect_delivery"),
            },
        ),
        (
            "BDD-064",
            {
                ("BDD_INVARIANT_REFERENCE", "invariant:INV-010"),
                ("BDD_INVARIANT_REFERENCE", "invariant:INV-011"),
                ("MISSING_TARGET_CONCEPT_SCOPE", "missing_target_concept:external_effect_delivery"),
            },
        ),
        (
            "RSE-009",
            {
                (
                    "CAPABILITY_SEMANTIC_SCOPE",
                    "lane_capability:EXTERNAL_CUSTODY:destination_idempotency",
                ),
                (
                    "CAPABILITY_SEMANTIC_SCOPE",
                    "lane_capability:EXTERNAL_CUSTODY:outbox_acknowledgment",
                ),
                ("GLOBAL_OBLIGATION_SCOPE", "global_obligation:committed_effect_membership"),
                ("MISSING_TARGET_CONCEPT_SCOPE", "missing_target_concept:external_effect_delivery"),
                ("RSE_INVARIANT_SCOPE", "invariant:INV-010"),
                ("RSE_INVARIANT_SCOPE", "invariant:INV-011"),
            },
        ),
    ),
)
def test_external_delivery_is_not_aliased_to_acknowledgment_literal_vectors(
    requirement_id: str, expected_edges: set[tuple[str, str]]
) -> None:
    # Arrange.
    row = _row(_artifact(), requirement_id)

    # Act.
    observed = {(edge["relation_type"], edge["target_id"]) for edge in row["edges"]}

    # Assert.
    assert observed == expected_edges


def test_outbox_and_bounded_counterexamples_keep_exact_constraint_meaning() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    bdd062 = _row(artifact, "BDD-062")
    ce004 = _row(artifact, "CE-004")
    ce005 = _row(artifact, "CE-005")

    # Assert.
    assert "exclusion:unregistered_external_destination" not in {
        edge["target_id"] for edge in bdd062["edges"]
    }
    assert {edge["target_id"] for edge in ce004["edges"]} == {
        "global_obligation:atomic_publication_reopen_authority",
        "global_obligation:committed_effect_membership",
        "invariant:INV-009",
        "invariant:INV-010",
    }
    assert {edge["target_id"] for edge in ce005["edges"]} == {"invariant:INV-005"}
    assert ce004["source_fields"]["status"] == "REPAIRED_IN_BOUNDED_MODEL"
    assert ce005["source_fields"]["status"] == "REPAIRED_IN_BOUNDED_MODEL"


def test_no_bypass_shutdown_and_external_rows_preserve_narrow_scope() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    no_bypass = [
        _row(artifact, requirement_id)
        for requirement_id in ("WF-17", "BDD-069", "BDD-070", "BDD-071", "BDD-072")
    ]
    shutdown = [_row(artifact, item) for item in ("BDD-065", "BDD-066", "BDD-067")]

    # Assert.
    assert all(
        {edge["relation_type"] for edge in row["edges"]}
        <= {
            "BDD_INVARIANT_REFERENCE",
            "CROSS_CUTTING_CONSTRAINT",
            "GLOBAL_OBLIGATION_SCOPE",
        }
        for row in no_bypass
    )
    assert all(
        [edge for edge in row["edges"] if edge["relation_type"] == "EXCLUSION_SCOPE"]
        == [
            {
                "relation_type": "EXCLUSION_SCOPE",
                "target_id": "exclusion:zusd_emergency_shutdown",
            }
        ]
        for row in shutdown
    )
    assert {edge["target_id"] for edge in _row(artifact, "UP-18")["edges"]}.isdisjoint(
        {
            "lane_capability:EXTERNAL_CUSTODY:registered_external_lock",
            "lane_capability:EXTERNAL_CUSTODY:registered_external_burn",
            "lane_capability:EXTERNAL_CUSTODY:registered_external_release",
            "lane_capability:EXTERNAL_CUSTODY:registered_external_mint",
            "lane_capability:EXTERNAL_CUSTODY:external_timeout",
            "lane_capability:EXTERNAL_CUSTODY:external_refund",
        }
    )


def test_tokenomics_anchors_preserve_purchase_burn_route_and_hyperdeflation() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    anchors = artifact["semantic_anchors"]

    # Assert.
    assert anchors["buy_and_burn"] == (
        "Spend the governed quote-asset fee allocation through the release-selected Spot route "
        "and burn the exact ZDEX atoms received."
    )
    assert anchors["buy_and_burn_forbidden_substitutes"] == [
        "treasury_balance_burn_shortcut",
        "transfer_burn_substitution",
    ]
    assert anchors["rescaling"] == "No denomination rescaling under GlobalSettlementABI V1."
    assert "required_route:fee_funded_zdex_purchase_and_burn" in {
        edge["target_id"] for edge in _row(artifact, "UP-01")["edges"]
    }
    assert "required_route:fee_funded_zdex_purchase_and_burn" in {
        edge["target_id"] for edge in _row(artifact, "UP-14")["edges"]
    }
    assert all(
        edge["target_id"] != "required_route:fee_funded_zdex_purchase_and_burn"
        for edge in _row(artifact, "UP-20")["edges"]
    )
    for requirement_id in ("UP-01", "UP-12", "UP-14", "UP-20"):
        assert _row(artifact, requirement_id)["status"] == "UNRESOLVED_POLICY_NOT_SELECTABLE"


@pytest.mark.parametrize(
    ("requirement_id", "expected_domain_targets"),
    (
        (
            "BDD-016",
            {
                "lane_capability:ZUSD_MONETARY:collateral_deposit",
                "lane_capability:ZUSD_MONETARY:collateral_withdraw",
            },
        ),
        (
            "BDD-031",
            {
                "lane_capability:ZUSD_MONETARY:stability_pool_deposit",
                "lane_capability:ZUSD_MONETARY:stability_pool_withdraw",
            },
        ),
        (
            "BDD-039",
            {
                "lane_capability:PERPS_MARKET:position_adjust",
                "lane_capability:PERPS_MARKET:position_open",
            },
        ),
        (
            "BDD-040",
            {
                "lane_capability:PERPS_MARKET:position_adjust",
                "lane_capability:PERPS_MARKET:position_open",
            },
        ),
        (
            "BDD-041",
            {
                "lane_capability:PERPS_MARKET:fee_allocation",
                "lane_capability:PERPS_MARKET:funding_accrual",
                "lane_capability:PERPS_MARKET:insurance_reserve",
                "lane_capability:PERPS_MARKET:position_adjust",
                "missing_target_concept:perps_realized_pnl_settlement",
                "required_route:perps_epoch_settlement",
            },
        ),
        (
            "BDD-043",
            {
                "lane_capability:PERPS_MARKET:position_adjust",
                "lane_capability:PERPS_MARKET:position_open",
            },
        ),
        (
            "BDD-078",
            {
                "lane_capability:SEALED_AUCTION:refund",
                "lane_capability:SEALED_AUCTION:slash",
            },
        ),
    ),
)
def test_selected_bdd_conjunction_and_disjunction_vectors_are_literal_grade_two_oracles(
    requirement_id: str, expected_domain_targets: set[str]
) -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    observed = {
        edge["target_id"]
        for edge in _row(artifact, requirement_id)["edges"]
        if not edge["target_id"].startswith("invariant:")
    }

    # Assert.
    assert observed == expected_domain_targets


def test_all_81_bdd_rows_have_explicit_scenario_specific_decisions() -> None:
    # Arrange.
    expected_ids = tuple(f"BDD-{ordinal:03d}" for ordinal in range(1, 82))

    # Act.
    table_ids = tuple(requirement_id for requirement_id, _ in core.BDD_CAPABILITY_SPECS_V1)
    artifact_ids = tuple(
        row["requirement_id"] for row in _artifact()["rows"] if row["kind"] == "BDD"
    )

    # Assert.
    assert table_ids == expected_ids
    assert artifact_ids == expected_ids


_COUNT_BVA = (
    ("workflow_count", 17),
    ("workflow_count", 19),
    ("bdd_count", 80),
    ("bdd_count", 82),
    ("invariant_count", 13),
    ("invariant_count", 15),
    ("rse_count", 10),
    ("rse_count", 12),
    ("ce_count", 7),
    ("ce_count", 9),
    ("up_count", 19),
    ("up_count", 21),
    ("capability_count", 102),
    ("capability_count", 104),
    ("target_count", 141),
    ("target_count", 143),
    ("global_obligation_count", 4),
    ("global_obligation_count", 6),
    ("missing_target_concept_count", 11),
    ("missing_target_concept_count", 13),
    ("ambiguous_capability_scope_count", 1),
    ("ambiguous_capability_scope_count", 3),
    ("cross_cutting_capability_scope_count", -1),
    ("cross_cutting_capability_scope_count", 1),
    ("disabled_capability_direct_scope_count", 1),
    ("disabled_capability_direct_scope_count", 3),
    ("disabled_capability_target_count", 8),
    ("disabled_capability_target_count", 10),
    ("enabled_direct_capability_semantic_scope_count", 53),
    ("enabled_direct_capability_semantic_scope_count", 55),
    ("enabled_direct_capability_wf_or_bdd_scope_count", 50),
    ("enabled_direct_capability_wf_or_bdd_scope_count", 52),
    ("enabled_capability_bdd_direct_scope_count", 45),
    ("enabled_capability_bdd_direct_scope_count", 47),
    ("enabled_direct_capability_rse_only_scope_count", 0),
    ("enabled_direct_capability_rse_only_scope_count", 2),
    ("enabled_direct_capability_ce_and_rse_only_scope_count", 1),
    ("enabled_direct_capability_ce_and_rse_only_scope_count", 3),
    ("enabled_direct_capability_workflow_only_scope_count", 4),
    ("enabled_direct_capability_workflow_only_scope_count", 6),
)


@pytest.mark.parametrize(("field", "mutant_count"), _COUNT_BVA)
def test_bva_structural_and_authority_partition_counts_reject_neighbors(
    field: str, mutant_count: int
) -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    artifact["structural_counts"][field] = mutant_count

    # Act.
    report = _report(artifact)

    # Assert.
    assert report["ok"] is False
    assert _codes(report) == ["STRUCTURAL_COUNT_MISMATCH"]


def test_canonical_regeneration_is_deterministic_and_differential() -> None:
    # Arrange.
    snapshot = _snapshot()

    # Act.
    first_json, first_markdown = build_artifacts_v1(REPO_ROOT)
    second_json, second_markdown = build_artifacts_v1(REPO_ROOT)

    # Assert.
    assert first_json == second_json
    assert first_markdown == second_markdown
    assert build_requirements_registry_v1(snapshot).to_json() == json.loads(first_json)


def test_mut_vacuous_capability_edge_rejects() -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    _row(artifact, "BDD-001")["edges"] = []

    # Act.
    report = _report(artifact)

    # Assert.
    assert _codes(report) == ["VACUOUS_EDGE"]


@pytest.mark.parametrize(
    "requirement_id",
    ("WF-01", "BDD-001", "RSE-001", "CE-001", "UP-01"),
)
def test_mut_vacuous_mapping_rejects_each_noninvariant_source_kind(requirement_id: str) -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    _row(artifact, requirement_id)["edges"] = []

    # Act.
    report = _report(artifact)

    # Assert.
    assert _codes(report) == ["VACUOUS_EDGE"]


def test_mut_bdd_workflow_inheritance_rejects_scenario_specific_mapping() -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    _row(artifact, "BDD-013")["edges"] = deepcopy(_row(artifact, "WF-04")["edges"])

    # Act.
    report = _report(artifact)

    # Assert.
    assert _codes(report) == ["BDD_SCENARIO_EDGE_MISMATCH"]


def test_mut_bdd_parent_and_rse_ce_source_fields_reject_exact_replay_drift() -> None:
    # Arrange.
    parent_artifact = deepcopy(_artifact())
    rse_artifact = deepcopy(_artifact())
    ce_artifact = deepcopy(_artifact())
    _row(parent_artifact, "BDD-016")["parent_requirement_id"] = "WF-05"
    _row(rse_artifact, "RSE-008")["source_fields"]["claim"] = "mutated"
    _row(ce_artifact, "CE-004")["source_fields"]["status"] = "PROVED"

    # Act.
    parent_report = _report(parent_artifact)
    rse_report = _report(rse_artifact)
    ce_report = _report(ce_artifact)

    # Assert.
    assert _codes(parent_report) == ["BDD_PARENT_MISMATCH"]
    assert _codes(rse_report) == ["SOURCE_FIELDS_MISMATCH"]
    assert _codes(ce_report) == ["SOURCE_FIELDS_MISMATCH"]


def test_mut_inverse_edge_erasure_rejects_bidirectional_mapping() -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    _target(artifact, "lane_capability:ZUSD_MONETARY:zusd_mint")["inbound_edges"] = []

    # Act.
    report = _report(artifact)

    # Assert.
    assert _codes(report) == ["INVERSE_EDGE_MISMATCH"]


def test_mut_noncanonical_outbound_and_inverse_order_reject_exactly() -> None:
    # Arrange.
    outbound = deepcopy(_artifact())
    inbound = deepcopy(_artifact())
    _row(outbound, "WF-10")["edges"].reverse()
    inverse_target = _target(inbound, "invariant:INV-003")
    inverse_target["inbound_edges"].reverse()

    # Act.
    outbound_report = _report(outbound)
    inbound_report = _report(inbound)

    # Assert.
    assert _codes(outbound_report) == ["NONCANONICAL_EDGE_ORDER"]
    assert _codes(inbound_report) == ["NONCANONICAL_INVERSE_EDGE_ORDER"]


def test_mut_invariant_feature_edge_and_relation_kind_substitution_reject() -> None:
    # Arrange.
    invariant_artifact = deepcopy(_artifact())
    relation_artifact = deepcopy(_artifact())
    _row(invariant_artifact, "INV-003")["edges"] = [
        {
            "relation_type": "CAPABILITY_SEMANTIC_SCOPE",
            "target_id": "lane_capability:ASSET_TRANSFER:native_asset_accounting",
        }
    ]
    first_cross = next(
        edge
        for edge in _row(relation_artifact, "BDD-069")["edges"]
        if edge["relation_type"] == "CROSS_CUTTING_CONSTRAINT"
    )
    first_cross["relation_type"] = "RSE_INVARIANT_SCOPE"
    _row(relation_artifact, "BDD-069")["edges"].sort(
        key=lambda edge: (edge["relation_type"], edge["target_id"])
    )

    # Act.
    invariant_report = _report(invariant_artifact)
    relation_report = _report(relation_artifact)

    # Assert.
    assert _codes(invariant_report) == ["INVARIANT_EDGE_FORBIDDEN"]
    assert _codes(relation_report) == ["BDD_SCENARIO_EDGE_MISMATCH"]


def test_mut_same_type_target_substitution_rejects_literal_semantics() -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    row = _row(artifact, "BDD-039")
    position_open = next(
        edge
        for edge in row["edges"]
        if edge["target_id"] == "lane_capability:PERPS_MARKET:position_open"
    )
    position_open["target_id"] = "lane_capability:PERPS_MARKET:margin_deposit"
    row["edges"].sort(key=lambda edge: (edge["relation_type"], edge["target_id"]))

    # Act.
    report = _report(artifact)

    # Assert.
    assert _codes(report) == ["BDD_SCENARIO_EDGE_MISMATCH"]


def test_mapping_table_lookup_rejects_duplicate_keys_before_selection() -> None:
    # Arrange.
    duplicate_table = (("BDD-001", ("first",)), ("BDD-001", ("second",)))

    # Act.
    with pytest.raises(RequirementsRejectV1) as captured:
        core._table_value_v1(duplicate_table, "BDD-001", "hostile duplicate table")

    # Assert.
    assert captured.value.code == "MAPPING_TABLE_DUPLICATE_KEY"
    assert captured.value.path == "hostile duplicate table"


def test_target_spec_discriminant_rejects_wrong_id_extra_field_and_string_enum() -> None:
    # Arrange.
    valid_route = core.TargetSpecV1(
        target_id="required_route:route-a",
        target_type=core.TargetTypeV1.REQUIRED_ROUTE,
        lane_id=None,
        capability_id=None,
        route_id="route-a",
        exclusion_id=None,
        exclusion_disposition=None,
        invariant_id=None,
        lane_disposition=None,
        source_fields_bytes=None,
    )
    constructors = (
        lambda: replace(valid_route, target_id="required_route:route-b"),
        lambda: replace(valid_route, lane_id="EXTERNAL_CUSTODY"),
        lambda: core.TargetSpecV1(
            target_id="required_route:route-a",
            target_type="REQUIRED_ROUTE",  # type: ignore[arg-type]
            lane_id=None,
            capability_id=None,
            route_id="route-a",
            exclusion_id=None,
            exclusion_disposition=None,
            invariant_id=None,
            lane_disposition=None,
            source_fields_bytes=None,
        ),
    )

    # Act.
    rejections: list[RequirementsRejectV1] = []
    for constructor in constructors:
        with pytest.raises(RequirementsRejectV1) as captured:
            constructor()
        rejections.append(captured.value)

    # Assert.
    assert [rejection.code for rejection in rejections] == [
        "TARGET_SPEC_DISCRIMINANT",
        "TARGET_SPEC_DISCRIMINANT",
        "TARGET_SPEC_DISCRIMINANT",
    ]


def test_mut_relation_target_algebra_rejects_cross_cutting_capability_alias() -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    row = _row(artifact, "BDD-069")
    cross_edge = next(
        edge for edge in row["edges"] if edge["relation_type"] == "CROSS_CUTTING_CONSTRAINT"
    )
    cross_edge["target_id"] = "lane_capability:ASSET_TRANSFER:generic_transfer"
    row["edges"].sort(key=lambda edge: (edge["relation_type"], edge["target_id"]))

    # Act.
    report = _report(artifact)

    # Assert.
    assert _codes(report) == ["RELATION_TARGET_TYPE"]


def test_mut_stale_donor_promotion_and_authority_flags_reject() -> None:
    # Arrange.
    donor = deepcopy(_artifact())
    authority = deepcopy(_artifact())
    donor["source_pins"][2]["source_gate_status"] = "PROVED"
    authority["value_movement_claim_allowed"] = True

    # Act.
    donor_report = _report(donor)
    authority_report = _report(authority)

    # Assert.
    assert _codes(donor_report) == ["STALE_DONOR_PROMOTION"]
    assert _codes(authority_report) == ["PROMOTION_MUTATION"]


def test_mut_manifest_completion_rejects_before_semantic_closure() -> None:
    # Arrange.
    artifact = deepcopy(_artifact())
    artifact["manifest_complete"] = True

    # Act.
    report = _report(artifact)

    # Assert.
    assert _codes(report) == ["PROMOTION_MUTATION"]


def test_hostile_json_duplicate_key_exact_type_and_closed_root_reject() -> None:
    # Arrange.
    bool_count = deepcopy(_artifact())
    unknown_root = deepcopy(_artifact())
    bool_count["structural_counts"]["workflow_count"] = True
    unknown_root["unexpected"] = "hostile"

    # Act.
    duplicate = check_requirements_registry_v1(
        b'{"schema":"one","schema":"two"}', _snapshot()
    ).to_json()
    bool_report = _report(bool_count)
    root_report = _report(unknown_root)
    duplicate_findings = duplicate["findings"]

    # Assert.
    assert _codes(duplicate) == ["JSON_DECODE"]
    assert type(duplicate_findings) is list
    assert type(duplicate_findings[0]) is dict
    assert duplicate_findings[0]["detail"] == "ValueError: duplicate JSON key"
    assert _codes(bool_report) == ["TYPE_ERROR"]
    assert _codes(root_report) == ["CLOSED_FIELDS"]


def test_json_integer_digit_ceiling_is_independent_of_ambient_guard() -> None:
    # Arrange.
    original_limit = sys.get_int_max_str_digits()
    lengths = (
        core.MAX_JSON_INTEGER_DIGITS_V1 - 1,
        core.MAX_JSON_INTEGER_DIGITS_V1,
        core.MAX_JSON_INTEGER_DIGITS_V1 + 1,
    )

    # Act.
    try:
        sys.set_int_max_str_digits(0)
        outcomes: list[str] = []
        for length in lengths:
            raw = ('{"n":' + "1" * length + "}").encode("ascii")
            try:
                decode_json_object_v1(raw, "integer-bva")
            except RequirementsRejectV1 as exc:
                outcomes.append(exc.code)
            else:
                outcomes.append("ACCEPTED")
    finally:
        sys.set_int_max_str_digits(original_limit)

    # Assert.
    assert outcomes == ["ACCEPTED", "ACCEPTED", "JSON_DECODE"]


@pytest.mark.parametrize("token", ("0.0", "1e2", "-0.5"))
def test_json_float_tokens_reject_before_core_type_admission(token: str) -> None:
    # Arrange.
    raw = f'{{"value":{token}}}'.encode("ascii")

    # Act.
    rejection = _expect_core_reject(raw)

    # Assert.
    assert rejection.code == "JSON_DECODE"
    assert rejection.detail == "ValueError: floating-point JSON numbers are forbidden"


def test_failed_decode_never_reports_source_census_and_findings_are_bounded() -> None:
    # Arrange.
    oversized_path = "p\ud800" + "x" * 1_000
    oversized_detail = "d\n" + "y" * 2_000

    # Act.
    report = check_requirements_registry_v1(b"{", _snapshot()).to_json()
    finding = core._finding_v1("CODE", oversized_path, oversized_detail).to_json()

    # Assert.
    assert report["source_row_census_complete"] is False
    assert report["semantic_target_inventory_complete"] is False
    assert len(finding["path"]) <= core.MAX_FINDING_PATH_CHARS_V1
    assert len(finding["detail"]) <= core.MAX_FINDING_DETAIL_CHARS_V1
    assert "\ud800" not in finding["path"]
    assert "\n" not in finding["detail"]


@pytest.mark.parametrize(
    ("raw_artifact", "expected_code"),
    (
        (bytearray(b"{}"), "JSON_BYTES_TYPE"),
        (b"x" * (core.MAX_JSON_BYTES_V1 + 1), "JSON_BYTE_LIMIT"),
    ),
)
def test_direct_checker_rejects_type_or_size_before_sha256(
    monkeypatch: pytest.MonkeyPatch,
    raw_artifact: object,
    expected_code: str,
) -> None:
    # Arrange.
    snapshot = _snapshot()

    def forbidden_sha256(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("sha256 must not receive rejected artifact bytes")

    monkeypatch.setattr(core.hashlib, "sha256", forbidden_sha256)

    # Act.
    report = check_requirements_registry_v1(raw_artifact, snapshot).to_json()  # type: ignore[arg-type]

    # Assert.
    assert _codes(report) == [expected_code]
    assert report["artifact_sha256"] == ""


def test_json_byte_depth_node_string_and_surrogate_limits(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange.
    oversized = b" " * (core.MAX_JSON_BYTES_V1 + 1)

    # Act and Assert.
    assert _expect_core_reject(oversized).code == "JSON_BYTE_LIMIT"
    monkeypatch.setattr(core, "MAX_JSON_DEPTH_V1", 2)
    assert _expect_core_reject(b'{"a":{"b":{"c":0}}}').code == "JSON_DEPTH_LIMIT"
    monkeypatch.setattr(core, "MAX_JSON_DEPTH_V1", 64)
    monkeypatch.setattr(core, "MAX_JSON_NODES_V1", 2)
    assert _expect_core_reject(b'{"a":1}').code == "JSON_NODE_LIMIT"
    monkeypatch.setattr(core, "MAX_JSON_NODES_V1", 100_000)
    monkeypatch.setattr(core, "MAX_JSON_STRING_CHARS_V1", 2)
    assert _expect_core_reject(b'{"a":"xxx"}').code == "JSON_STRING_LIMIT"
    monkeypatch.setattr(core, "MAX_JSON_STRING_CHARS_V1", 131_072)
    assert _expect_core_reject(b'{"\\ud800":0}').code == "JSON_LONE_SURROGATE"
    assert _expect_core_reject(b'{"a":"\\udfff"}').code == "JSON_LONE_SURROGATE"


def test_json_memory_and_recursion_failures_are_typed(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange.
    def out_of_memory(*_args: object, **_kwargs: object) -> object:
        raise MemoryError("bounded test")

    # Act.
    monkeypatch.setattr(core.json, "loads", out_of_memory)
    rejection = _expect_core_reject(b"{}")

    # Assert.
    assert rejection.code == "JSON_DECODE"
    assert rejection.detail.startswith("MemoryError:")


def test_stateful_source_histories_allow_descendant_and_reject_ancestry_or_byte_drift() -> None:
    # Arrange.
    artifact = _artifact()
    baseline = _snapshot()
    descendant = replace(baseline, captured_git_head="a" * 40, rechecked_git_head="a" * 40)
    nonancestor = replace(descendant, source_subject_is_ancestor=False)
    changed_documents = list(baseline.document_bytes)
    path, raw = changed_documents[0]
    changed_documents[0] = (path, b"X" + raw[1:])
    changed_source = replace(baseline, document_bytes=tuple(changed_documents))

    # Act.
    reports = (
        _report(artifact, descendant),
        _report(artifact, nonancestor),
        _report(artifact, changed_source),
    )

    # Assert.
    assert reports[0]["ok"] is True
    assert _codes(reports[1]) == ["SOURCE_SUBJECT_NOT_ANCESTOR"]
    assert _codes(reports[2]) == ["SOURCE_SHA256_MISMATCH"]


def test_source_tree_entries_and_head_movement_reject_exactly() -> None:
    # Arrange.
    artifact = _artifact()
    baseline = _snapshot()
    source_entries = list(baseline.source_subject_entries)
    current_entries = list(baseline.current_head_entries)
    source_entries[0] = (*source_entries[0][:3], "0" * 40)
    current_entries[0] = (*current_entries[0][:3], "1" * 40)
    bad_shape = ((), *baseline.source_subject_entries[1:])

    # Act.
    source_report = _report(
        artifact, replace(baseline, source_subject_entries=tuple(source_entries))
    )
    current_report = _report(
        artifact, replace(baseline, current_head_entries=tuple(current_entries))
    )
    moved_report = _report(artifact, replace(baseline, rechecked_git_head="f" * 40))
    shape_report = _report(artifact, replace(baseline, source_subject_entries=bad_shape))  # type: ignore[arg-type]

    # Assert.
    assert _codes(source_report) == ["SOURCE_SUBJECT_ENTRY_MISMATCH"]
    assert _codes(current_report) == ["CURRENT_HEAD_ENTRY_MISMATCH"]
    assert _codes(moved_report) == ["SOURCE_HEAD_MOVED"]
    assert _codes(shape_report) == ["SOURCE_SUBJECT_ENTRY_SET"]


def test_safe_reader_accepts_regular_and_rejects_symlink_fifo_directory_and_oversize(
    tmp_path: Path,
) -> None:
    # Arrange.
    regular = tmp_path / "regular"
    regular.write_bytes(b"abc")
    symlink = tmp_path / "symlink"
    symlink.symlink_to(regular)
    fifo = tmp_path / "fifo"
    os.mkfifo(fifo)
    directory = tmp_path / "directory"
    directory.mkdir()
    oversized = tmp_path / "oversized"
    oversized.write_bytes(b"abcd")

    # Act.
    observed = _read_bounded_regular_file_v1(regular, 3, "regular")
    rejections: list[ShellRejectV1] = []
    for path, limit in ((symlink, 3), (fifo, 3), (directory, 3), (oversized, 3)):
        with pytest.raises(ShellRejectV1) as captured:
            _read_bounded_regular_file_v1(path, limit, path.name)
        rejections.append(captured.value)

    # Assert.
    assert observed == b"abc"
    assert [item.code for item in rejections] == [
        "FILE_SYMLINK",
        "FILE_NONREGULAR",
        "FILE_NONREGULAR",
        "FILE_SIZE_LIMIT",
    ]


def test_safe_reader_rejects_parent_symlink_and_name_too_long_with_stable_codes(
    tmp_path: Path,
) -> None:
    # Arrange.
    real_parent = tmp_path / "real-parent"
    real_parent.mkdir()
    (real_parent / "value").write_bytes(b"x")
    linked_parent = tmp_path / "linked-parent"
    linked_parent.symlink_to(real_parent, target_is_directory=True)
    overlong = tmp_path / ("x" * 5_000)

    # Act.
    with pytest.raises(ShellRejectV1) as parent_captured:
        _read_bounded_regular_file_v1(linked_parent / "value", 1, "parent-link")
    with pytest.raises(ShellRejectV1) as length_captured:
        _read_bounded_regular_file_v1(overlong, 1, "long-name")

    # Assert.
    assert parent_captured.value.code == "FILE_PARENT_SYMLINK"
    assert length_captured.value.code == "FILE_NAME_TOO_LONG"


@pytest.mark.parametrize(
    ("raised", "expected_code"),
    (
        (PermissionError(13, "denied"), "FILE_PERMISSION"),
        (InterruptedError(4, "interrupted"), "FILE_INTERRUPTED"),
    ),
)
def test_safe_reader_translates_expected_open_and_read_errors(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    raised: OSError,
    expected_code: str,
) -> None:
    # Arrange.
    regular = tmp_path / "regular"
    regular.write_bytes(b"abc")
    if isinstance(raised, PermissionError):
        original_open = build_shell.os.open

        def rejecting_open(path: str, *args: object, **kwargs: object) -> int:
            if path == "regular":
                raise raised
            return original_open(path, *args, **kwargs)

        monkeypatch.setattr(build_shell.os, "open", rejecting_open)
    else:
        monkeypatch.setattr(build_shell.os, "read", lambda *_args: (_ for _ in ()).throw(raised))

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        _read_bounded_regular_file_v1(regular, 3, "regular")

    # Assert.
    assert captured.value.code == expected_code


def test_open_parent_dir_translates_interrupted_intermediate_close_and_closes_new_fd(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange.
    nested = tmp_path / "one" / "two" / "value"
    nested.parent.mkdir(parents=True)
    opened_fds: list[int] = []
    close_interrupted = False
    real_open = os.open
    real_close = os.close

    def recording_open(*args: Any, **kwargs: Any) -> int:
        fd = real_open(*args, **kwargs)
        opened_fds.append(fd)
        return fd

    def interrupting_close(fd: int) -> None:
        nonlocal close_interrupted
        if not close_interrupted:
            close_interrupted = True
            real_close(fd)
            raise InterruptedError(4, "interrupted close")
        real_close(fd)

    monkeypatch.setattr(build_shell.os, "open", recording_open)
    monkeypatch.setattr(build_shell.os, "close", interrupting_close)

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        build_shell._open_parent_dir_v1(nested)
    newly_opened_fd = opened_fds[1]
    monkeypatch.undo()

    # Assert.
    assert captured.value.code == "FILE_INTERRUPTED"
    with pytest.raises(OSError):
        os.fstat(newly_opened_fd)


def test_checker_artifact_reader_rejects_symlink_fifo_and_oversize(tmp_path: Path) -> None:
    # Arrange.
    regular = tmp_path / "regular"
    regular.write_bytes(b"{}")
    symlink = tmp_path / "artifact-link"
    symlink.symlink_to(regular)
    fifo = tmp_path / "artifact-fifo"
    os.mkfifo(fifo)
    oversized = tmp_path / "artifact-big"
    oversized.write_bytes(b"x" * (ARTIFACT_MAX_BYTES_V1 + 1))

    # Act.
    reports = [
        check_m6_normative_requirements_v1(REPO_ROOT, path) for path in (symlink, fifo, oversized)
    ]

    # Assert.
    assert [_codes(report) for report in reports] == [
        ["FILE_SYMLINK"],
        ["FILE_NONREGULAR"],
        ["FILE_SIZE_LIMIT"],
    ]
    assert all(report["settlement_authority"] == "NONE" for report in reports)


def test_checker_failure_report_never_echoes_unbounded_source_path(tmp_path: Path) -> None:
    # Arrange.
    overlong = tmp_path / ("x" * 5_000)

    # Act.
    report = check_m6_normative_requirements_v1(REPO_ROOT, overlong)

    # Assert.
    assert _codes(report) == ["FILE_NAME_TOO_LONG"]
    assert "source" not in report
    findings = report["findings"]
    assert type(findings) is list
    finding = findings[0]
    assert type(finding) is dict
    path = finding["path"]
    detail = finding["detail"]
    assert type(path) is str
    assert type(detail) is str
    assert len(path) <= build_shell._SHELL_PATH_LIMIT_V1
    assert len(detail) <= build_shell._SHELL_DETAIL_LIMIT_V1


def test_atomic_writer_replaces_regular_file_and_refuses_output_symlink(tmp_path: Path) -> None:
    # Arrange.
    output = tmp_path / "output"
    output.write_bytes(b"old")
    target = tmp_path / "target"
    target.write_bytes(b"target")
    symlink = tmp_path / "link"
    symlink.symlink_to(target)
    directory = tmp_path / "directory"
    directory.mkdir()

    # Act.
    _atomic_replace_regular_file_v1(output, b"new")
    with pytest.raises(ShellRejectV1) as captured:
        _atomic_replace_regular_file_v1(symlink, b"hostile")
    with pytest.raises(ShellRejectV1) as directory_captured:
        _atomic_replace_regular_file_v1(directory, b"hostile")

    # Assert.
    assert output.read_bytes() == b"new"
    assert captured.value.code == "OUTPUT_SYMLINK"
    assert directory_captured.value.code == "OUTPUT_NONREGULAR"
    assert target.read_bytes() == b"target"


def test_atomic_writer_detects_temp_name_substitution_race(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange.
    output = tmp_path / "output"
    original_replace = build_shell.os.replace

    def substituting_replace(
        source: str,
        destination: str,
        *,
        src_dir_fd: int,
        dst_dir_fd: int,
    ) -> None:
        os.unlink(source, dir_fd=src_dir_fd)
        hostile_fd = os.open(source, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=src_dir_fd)
        try:
            os.write(hostile_fd, b"hostile")
        finally:
            os.close(hostile_fd)
        original_replace(
            source,
            destination,
            src_dir_fd=src_dir_fd,
            dst_dir_fd=dst_dir_fd,
        )

    monkeypatch.setattr(build_shell.os, "replace", substituting_replace)

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        _atomic_replace_regular_file_v1(output, b"expected")

    # Assert.
    assert captured.value.code == "OUTPUT_SUBSTITUTION_RACE"


def test_atomic_writer_detects_post_rename_destination_inode_replacement(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange.
    output = tmp_path / "output"
    hostile = tmp_path / "hostile"
    hostile.write_bytes(b"hostile!")
    original_replace = build_shell.os.replace

    def replacing_destination(
        source: str,
        destination: str,
        *,
        src_dir_fd: int,
        dst_dir_fd: int,
    ) -> None:
        original_replace(
            source,
            destination,
            src_dir_fd=src_dir_fd,
            dst_dir_fd=dst_dir_fd,
        )
        original_replace(
            hostile.name,
            destination,
            src_dir_fd=src_dir_fd,
            dst_dir_fd=dst_dir_fd,
        )

    monkeypatch.setattr(build_shell.os, "replace", replacing_destination)

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        _atomic_replace_regular_file_v1(output, b"expected")

    # Assert.
    assert captured.value.code == "OUTPUT_SUBSTITUTION_RACE"


def test_atomic_writer_detects_post_rename_same_inode_byte_mutation(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange.
    output = tmp_path / "output"
    original_replace = build_shell.os.replace

    def mutating_destination(
        source: str,
        destination: str,
        *,
        src_dir_fd: int,
        dst_dir_fd: int,
    ) -> None:
        original_replace(
            source,
            destination,
            src_dir_fd=src_dir_fd,
            dst_dir_fd=dst_dir_fd,
        )
        destination_fd = os.open(destination, os.O_WRONLY | os.O_TRUNC, dir_fd=dst_dir_fd)
        try:
            os.write(destination_fd, b"tampered")
        finally:
            os.close(destination_fd)

    monkeypatch.setattr(build_shell.os, "replace", mutating_destination)

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        _atomic_replace_regular_file_v1(output, b"expected")

    # Assert.
    assert captured.value.code == "OUTPUT_BYTE_MISMATCH"


def test_atomic_writer_translates_overlong_destination_without_traceback(tmp_path: Path) -> None:
    # Arrange.
    output = tmp_path / ("x" * 5_000)

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        _atomic_replace_regular_file_v1(output, b"value")

    # Assert.
    assert captured.value.code == "OUTPUT_NAME_TOO_LONG"


def test_builder_check_uses_safe_artifact_reader(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange.
    docs = tmp_path / "docs" / "research"
    docs.mkdir(parents=True)
    real = tmp_path / "real"
    real.write_bytes(b"{}")
    (tmp_path / build_shell.JSON_OUTPUT).symlink_to(real)
    (tmp_path / build_shell.MARKDOWN_OUTPUT).write_bytes(b"")
    monkeypatch.setattr(build_shell, "build_artifacts_v1", lambda _root: (b"{}", ""))

    # Act.
    result = build_shell.main(["--root", str(tmp_path), "--check"])

    # Assert.
    assert result == 2


def test_git_binary_ignores_ambient_path_and_environment_is_closed(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange.
    fake = tmp_path / "git"
    fake.write_text("#!/usr/bin/python3\nraise SystemExit(99)\n", encoding="utf-8")
    fake.chmod(0o755)
    monkeypatch.setenv("PATH", str(tmp_path))

    # Act.
    binary = _git_binary_v1()
    environment = _git_environment_v1()

    # Assert.
    assert binary != str(fake)
    assert os.path.isabs(binary)
    assert environment == {
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "HOME": "/dev/null",
        "LC_ALL": "C",
        "PATH": os.defpath,
    }


@pytest.mark.parametrize(
    ("program", "code", "timeout", "output_limit"),
    [
        ("import sys; sys.stderr.write('fail'); raise SystemExit(7)", "GIT_EXIT", 1.0, 64),
        ("import time; time.sleep(1)", "GIT_TIMEOUT", 0.02, 64),
        ("print('x' * 100)", "GIT_OUTPUT_LIMIT", 1.0, 16),
    ],
)
def test_git_failure_timeout_and_output_are_typed(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    program: str,
    code: str,
    timeout: float,
    output_limit: int,
) -> None:
    # Arrange.
    fake = tmp_path / "fake-git"
    fake.write_text(f"#!/usr/bin/python3\n{program}\n", encoding="utf-8")
    fake.chmod(0o755)
    monkeypatch.setattr(build_shell, "_git_binary_v1", lambda: str(fake))
    monkeypatch.setattr(build_shell, "GIT_TIMEOUT_SECONDS_V1", timeout)
    monkeypatch.setattr(build_shell, "GIT_OUTPUT_MAX_BYTES_V1", output_limit)

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        _run_git_v1(tmp_path, ("status",))

    # Assert.
    assert captured.value.code == code


def test_git_timeout_kills_live_descendant_process_group(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange.
    observation = tmp_path / "descendant.txt"
    fake = tmp_path / "fake-git"
    fake.write_text(
        "#!/usr/bin/python3\n"
        "import os, pathlib, subprocess, sys, time\n"
        "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])\n"
        f"pathlib.Path({str(observation)!r}).write_text("
        "f'{os.getpgrp()}:{child.pid}', encoding='ascii')\n"
        "time.sleep(60)\n",
        encoding="utf-8",
    )
    fake.chmod(0o755)
    monkeypatch.setattr(build_shell, "_git_binary_v1", lambda: str(fake))
    monkeypatch.setattr(build_shell, "GIT_TIMEOUT_SECONDS_V1", 0.5)

    # Act.
    with pytest.raises(ShellRejectV1) as captured:
        _run_git_v1(tmp_path, ("status",))
    process_group, child_pid = (int(value) for value in observation.read_text().split(":"))
    proc_stat = Path(f"/proc/{child_pid}/stat")
    descendant_state = proc_stat.read_text().split()[2] if proc_stat.exists() else "ABSENT"
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        process_group_alive = False
    else:
        process_group_alive = True

    # Assert.
    assert captured.value.code == "GIT_TIMEOUT"
    assert descendant_state in {"ABSENT", "Z"}
    assert process_group_alive is False or descendant_state == "Z"


def test_checker_cli_has_no_artifact_override() -> None:
    # Arrange.
    arguments = ["--artifact", "/tmp/hostile.json"]

    # Act.
    with pytest.raises(SystemExit) as captured:
        check_shell.main(arguments)

    # Assert.
    assert captured.value.code == 2


def test_builder_cli_returns_typed_json_for_overlong_root(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    # Arrange.
    overlong_root = tmp_path / ("x" * 5_000)

    # Act.
    result = build_shell.main(["--root", str(overlong_root), "--check"])
    output = json.loads(capsys.readouterr().out)

    # Assert.
    assert result == 2
    assert output["ok"] is False
    assert output["finding"]["code"] == "GIT_EXIT"
    assert "Traceback" not in output["finding"]["detail"]


def test_artifact_drift_history_restores_only_after_exact_regeneration() -> None:
    # Arrange.
    baseline = _artifact()
    mutated = deepcopy(baseline)
    _row(mutated, "BDD-001")["status"] = "IMPLEMENTED"
    restored = _artifact()

    # Act.
    history = (_report(baseline), _report(mutated), _report(restored))

    # Assert.
    assert history[0]["ok"] is True
    assert _codes(history[1]) == ["PROHIBITED_EVIDENCE_STATUS"]
    assert history[2]["ok"] is True
    assert baseline == restored


def test_source_subject_is_immutable_and_artifact_head_is_not_self_referential() -> None:
    # Arrange.
    artifact = _artifact()

    # Act.
    subject = artifact["subject"]

    # Assert.
    assert subject == {
        "artifact_commit_binding": "NONE",
        "artifact_commit_status": "GENERATED_CONTENT_NOT_SELF_REFERENTIAL",
        "source_subject_commit": SOURCE_SUBJECT_COMMIT_V1,
        "source_subject_tree": SOURCE_SUBJECT_TREE_V1,
    }
