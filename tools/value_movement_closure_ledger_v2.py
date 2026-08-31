"""Exact-subject, non-promotional value-movement closure ledger for O-005B."""

from __future__ import annotations

from pathlib import Path
from typing import Final, cast

from tools.operator_surface_registry_common_v2 import (
    HEX_40_V2,
    HEX_64_V2,
    OperatorSurfaceRegistryRejectV2,
    canonical_json_bytes_v2,
    decode_json_object_v2,
    reject_v2,
    sha256_hex_v2,
)

SCHEMA_V2: Final = "zenodex/value-movement-closure-ledger/v2"
CHECK_SCHEMA_V2: Final = "zenodex/value-movement-closure-ledger-check/v2"
ARTIFACT_RELATIVE_PATH_V2: Final = Path(
    "docs/research/ZENODEX_VALUE_MOVEMENT_CLOSURE_LEDGER_V2.json"
)
EXPECTED_ACTIVE_PLAN_COMMIT_V2: Final = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
EXPECTED_HISTORICAL_SUBJECT_V2: Final = "68b8749b19509325ba75ad33057a247c332d8339"
GATE_IDS_V2: Final = tuple(f"VM-{index:02d}" for index in range(1, 13))
NO_AUTHORITY_V2: Final = {
    "mount": "NONE",
    "production": "NONE",
    "release": "NONE",
    "settlement": "NONE",
    "value_movement": "NONE",
}

PLAN_PATH_V2: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
ACTIVE_PLAN_PATH_V2: Final = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
ADMISSION_PATH_V2: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
HISTORICAL_LEDGER_PATH_V2: Final = "docs/research/ZENODEX_VALUE_MOVEMENT_CLOSURE_STATUS_V1.json"
FORMAL_CLAIM_PATH_V2: Final = "docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md"

DEPENDENCY_ROWS_V2: Final = (
    (
        "O-003B",
        "docs/research/ZENODEX_RETIRED_TAU_BRIDGE_CLOSURE_V3.json",
        "zenodex/retired-tau-bridge-closure/v3",
        "RESEARCH_ONLY_O003B_COMPLETE_ON_STAGE_A_EVIDENCE_SUBJECT",
    ),
    (
        "O-004",
        "docs/research/ZENODEX_OPERATOR_SURFACE_REGISTRY_V2.json",
        "zenodex/operator-surface-registry/v2",
        "COMPLETE_SOURCE_BOUND_OPERATOR_REFERENCE_REGISTRY",
    ),
    (
        "O-005",
        "docs/research/M6_O005_REQUIREMENTS_FLOOR_COMPLETION_V1.json",
        "zenodex/m6-o005-requirements-floor-completion/v1",
        "RESEARCH_ONLY_O005_REQUIREMENTS_FLOOR_COMPLETE_ON_EXACT_SUBJECT",
    ),
    (
        "O-005-SEMANTIC-RESOLUTIONS",
        "docs/research/M6_O005_SEMANTIC_RESOLUTIONS_V1.json",
        "zenodex/m6-o005-semantic-resolutions/v1",
        "RESEARCH_ONLY_SOURCE_RESOLUTION_BIJECTION",
    ),
)

SOURCE_PATHS_V2: Final = tuple(
    sorted(
        {
            ACTIVE_PLAN_PATH_V2,
            ADMISSION_PATH_V2,
            FORMAL_CLAIM_PATH_V2,
            HISTORICAL_LEDGER_PATH_V2,
            PLAN_PATH_V2,
            "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json",
            *(row[1] for row in DEPENDENCY_ROWS_V2),
            "tests/test_check_value_movement_closure_ledger_v2.py",
            "tests/test_value_movement_closure_ledger_semantic_mutants_v2.py",
            "tools/__init__.py",
            "tools/build_value_movement_closure_ledger_v2.py",
            "tools/check_value_movement_closure_ledger_v2.py",
            "tools/operator_surface_registry_common_v2.py",
            "tools/operator_surface_registry_git_v2.py",
            "tools/operator_surface_registry_projection_v2.py",
            "tools/operator_surface_registry_v2.py",
            "tools/value_movement_closure_ledger_git_v2.py",
            "tools/value_movement_closure_ledger_v2.py",
        }
    )
)

_NONCLAIMS_V2: Final = (
    "The ledger closes only the current_closure_ledger_gap on one exact Stage-A subject.",
    "All twelve value-movement gates remain open and no historical row is current evidence.",
    "Ancestor dependency artifacts require their own point-of-use checkers and claim ceilings.",
    "No production, settlement, release, mount, migration, or value-moving authority is granted.",
    "Git executable integrity and process containment remain external premises.",
)


def _json_source_v2(sources: dict[str, bytes], path: str) -> dict[str, object]:
    try:
        raw = sources[path]
    except KeyError:
        reject_v2("SOURCE_DENOMINATOR", path, "required source missing")
    return decode_json_object_v2(raw, path)


def _one_mapping_v2(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict:
        reject_v2("SOURCE_SHAPE", path, "expected one object")
    return cast(dict[str, object], value)


def _one_list_v2(value: object, path: str) -> list[object]:
    if type(value) is not list:
        reject_v2("SOURCE_SHAPE", path, "expected one list")
    return cast(list[object], value)


def source_manifest_v2(sources: dict[str, bytes]) -> list[dict[str, str]]:
    if tuple(sources) != SOURCE_PATHS_V2:
        reject_v2("SOURCE_DENOMINATOR", "source_manifest", "closed ordered sources required")
    if any(type(raw) is not bytes for raw in sources.values()):
        reject_v2("SOURCE_DENOMINATOR", "source_manifest", "all sources must be bytes")
    return [{"path": path, "sha256": sha256_hex_v2(sources[path])} for path in SOURCE_PATHS_V2]


def _active_plan_projection_v2(sources: dict[str, bytes]) -> dict[str, object]:
    registry = _json_source_v2(sources, ACTIVE_PLAN_PATH_V2)
    plans = _one_list_v2(registry.get("active_plans"), f"{ACTIVE_PLAN_PATH_V2}.active_plans")
    if registry.get("active_plan_count") != 1 or len(plans) != 1:
        reject_v2(
            "ACTIVE_PLAN_CARDINALITY", ACTIVE_PLAN_PATH_V2, "exactly one active plan required"
        )
    plan = _one_mapping_v2(plans[0], f"{ACTIVE_PLAN_PATH_V2}.active_plans[0]")
    if plan.get("plan_commit") != EXPECTED_ACTIVE_PLAN_COMMIT_V2:
        reject_v2("ACTIVE_PLAN_SUBJECT", ACTIVE_PLAN_PATH_V2, "active plan commit drift")
    if plan.get("plan_path") != PLAN_PATH_V2:
        reject_v2("ACTIVE_PLAN_SUBJECT", ACTIVE_PLAN_PATH_V2, "active plan path drift")
    if registry.get("authority") != {
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }:
        reject_v2("AUTHORITY_DRIFT", ACTIVE_PLAN_PATH_V2, "active plan authority drift")
    return {
        "active_plan_commit": plan["plan_commit"],
        "active_plan_path": plan["plan_path"],
        "active_plan_sha256": plan.get("plan_sha256"),
        "admission_receipt_path": plan.get("admission_receipt_path"),
        "admission_receipt_payload_sha256": plan.get("admission_receipt_payload_sha256"),
    }


def _validate_admission_and_plan_v2(sources: dict[str, bytes], active: dict[str, object]) -> None:
    admission = _json_source_v2(sources, ADMISSION_PATH_V2)
    admitted = _one_mapping_v2(admission.get("admitted_plan"), f"{ADMISSION_PATH_V2}.admitted_plan")
    if admitted.get("commit") != active["active_plan_commit"]:
        reject_v2("ADMISSION_SUBJECT", ADMISSION_PATH_V2, "admission commit drift")
    if admission.get("receipt_payload_sha256") != active["admission_receipt_payload_sha256"]:
        reject_v2("ADMISSION_SUBJECT", ADMISSION_PATH_V2, "admission payload drift")
    if active.get("admission_receipt_path") != ADMISSION_PATH_V2:
        reject_v2("ADMISSION_SUBJECT", ACTIVE_PLAN_PATH_V2, "admission path drift")
    if active.get("active_plan_sha256") != sha256_hex_v2(sources[PLAN_PATH_V2]):
        reject_v2("ACTIVE_PLAN_SUBJECT", PLAN_PATH_V2, "plan content hash drift")
    if admitted.get("plan_sha256") != active.get("active_plan_sha256"):
        reject_v2("ADMISSION_SUBJECT", ADMISSION_PATH_V2, "admitted plan hash drift")
    normative = _one_list_v2(
        admission.get("normative_inputs"), f"{ADMISSION_PATH_V2}.normative_inputs"
    )
    formal_rows = [
        row for row in normative if type(row) is dict and row.get("path") == FORMAL_CLAIM_PATH_V2
    ]
    if len(formal_rows) != 1 or formal_rows[0].get("sha256") != sha256_hex_v2(
        sources[FORMAL_CLAIM_PATH_V2]
    ):
        reject_v2("FORMAL_CLAIM_BINDING", FORMAL_CLAIM_PATH_V2, "formal claim hash drift")
    plan = _json_source_v2(sources, PLAN_PATH_V2)
    verdict = _one_mapping_v2(plan.get("baseline_verdict"), f"{PLAN_PATH_V2}.baseline_verdict")
    if verdict.get("value_movement_gate_count") != len(GATE_IDS_V2):
        reject_v2("GATE_DENOMINATOR", PLAN_PATH_V2, "plan gate count drift")
    if verdict.get("current_ledger_status") != "STALE_REQUIRES_EXACT_SUBJECT_RECONCILIATION":
        reject_v2("HISTORICAL_DISPOSITION", PLAN_PATH_V2, "baseline ledger disposition drift")
    obligations = _one_list_v2(plan.get("next_obligations"), f"{PLAN_PATH_V2}.next_obligations")
    rows = [
        row for row in obligations if type(row) is dict and row.get("obligation_id") == "O-005B"
    ]
    if len(rows) != 1 or rows[0].get("closes") != ["current_closure_ledger_gap"]:
        reject_v2("O005B_CONTRACT", PLAN_PATH_V2, "O-005B obligation drift")
    historical_inputs = _one_list_v2(
        plan.get("historical_inputs"), f"{PLAN_PATH_V2}.historical_inputs"
    )
    donor_rows = [
        row
        for row in historical_inputs
        if type(row) is dict and row.get("path") == HISTORICAL_LEDGER_PATH_V2
    ]
    if len(donor_rows) != 1 or donor_rows[0].get("sha256") != sha256_hex_v2(
        sources[HISTORICAL_LEDGER_PATH_V2]
    ):
        reject_v2("HISTORICAL_BINDING", HISTORICAL_LEDGER_PATH_V2, "historical donor hash drift")


def _require_no_dependency_promotion_v2(value: dict[str, object], path: str) -> None:
    forbidden_truthy = (
        "closed_value_movement_gates",
        "production_promotion",
        "release_eligible",
        "value_movement_claim_allowed",
    )
    for field in forbidden_truthy:
        if value.get(field) not in (None, False, 0, []):
            reject_v2("DEPENDENCY_PROMOTION", path, f"{field} must remain empty or false")
    authority_fields = (
        "migration_authority",
        "production_authority",
        "release_authority",
        "settlement_authority",
        "value_movement_authority",
    )
    for field in authority_fields:
        if field in value and value.get(field) != "NONE":
            reject_v2("DEPENDENCY_PROMOTION", path, f"{field} must remain NONE")


def _dependency_projection_v2(sources: dict[str, bytes]) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for obligation_id, path, schema, status in DEPENDENCY_ROWS_V2:
        artifact = _json_source_v2(sources, path)
        if artifact.get("schema") != schema or artifact.get("status") != status:
            reject_v2("DEPENDENCY_STATUS", path, "dependency schema or status drift")
        _require_no_dependency_promotion_v2(artifact, path)
        if path.endswith("ZENODEX_RETIRED_TAU_BRIDGE_CLOSURE_V3.json"):
            ceiling = _one_mapping_v2(artifact.get("claim_ceiling"), f"{path}.claim_ceiling")
            _require_no_dependency_promotion_v2(ceiling, path)
            if ceiling.get("closed_value_movement_gates") != 0:
                reject_v2("DEPENDENCY_PROMOTION", path, "dependency closes a VM gate")
        if path.endswith("M6_O005_REQUIREMENTS_FLOOR_COMPLETION_V1.json"):
            ceiling = _one_mapping_v2(artifact.get("claim_ceiling"), f"{path}.claim_ceiling")
            _require_no_dependency_promotion_v2(ceiling, path)
            if ceiling.get("closed_value_movement_gates") != 0:
                reject_v2("DEPENDENCY_PROMOTION", path, "dependency closes a VM gate")
        if path.endswith("ZENODEX_OPERATOR_SURFACE_REGISTRY_V2.json"):
            if (
                artifact.get("authority") != NO_AUTHORITY_V2
                or artifact.get("vm_gates_closed") != []
            ):
                reject_v2("DEPENDENCY_PROMOTION", path, "operator registry authority drift")
        result.append(
            {
                "artifact_path": path,
                "artifact_sha256": sha256_hex_v2(sources[path]),
                "evidence_relation": "SOURCE_BOUND_ANCESTOR_RECHECK_AT_POINT_OF_USE",
                "obligation_id": obligation_id,
                "status": status,
            }
        )
    return result


def _historical_donor_rows_v2(sources: dict[str, bytes]) -> list[dict[str, object]]:
    historical = _json_source_v2(sources, HISTORICAL_LEDGER_PATH_V2)
    subject = _one_mapping_v2(historical.get("subject"), f"{HISTORICAL_LEDGER_PATH_V2}.subject")
    if historical.get("schema") != "zenodex/value-movement-closure-status/v1":
        reject_v2("HISTORICAL_SCHEMA", HISTORICAL_LEDGER_PATH_V2, "historical schema drift")
    authority = _one_mapping_v2(
        historical.get("authority"), f"{HISTORICAL_LEDGER_PATH_V2}.authority"
    )
    if authority.get("production_authority") != "NONE":
        reject_v2("HISTORICAL_PROMOTION", HISTORICAL_LEDGER_PATH_V2, "authority drift")
    if subject.get("commit") != EXPECTED_HISTORICAL_SUBJECT_V2:
        reject_v2("HISTORICAL_SUBJECT", HISTORICAL_LEDGER_PATH_V2, "historical subject drift")
    rows = _one_list_v2(historical.get("gate_status"), f"{HISTORICAL_LEDGER_PATH_V2}.gate_status")
    if [row.get("id") if type(row) is dict else None for row in rows] != list(GATE_IDS_V2):
        reject_v2("GATE_DENOMINATOR", HISTORICAL_LEDGER_PATH_V2, "historical gate IDs drift")
    result: list[dict[str, object]] = []
    for row in rows:
        gate = _one_mapping_v2(row, f"{HISTORICAL_LEDGER_PATH_V2}.gate_status")
        historical_status = gate.get("status")
        if historical_status not in {"GAP", "PARTIAL"}:
            reject_v2("HISTORICAL_PROMOTION", HISTORICAL_LEDGER_PATH_V2, "historical gate promoted")
        result.append(
            {
                "disposition": "STALE_DONOR_NOT_CURRENT_EVIDENCE",
                "gate_id": gate["id"],
                "historical_status": historical_status,
                "source_subject": EXPECTED_HISTORICAL_SUBJECT_V2,
            }
        )
    return result


def _current_gate_rows_v2() -> list[dict[str, object]]:
    return [
        {
            "closed": False,
            "current_promoted_evidence": [],
            "gate_id": gate_id,
            "status": "OPEN_NO_CURRENT_PROMOTION",
        }
        for gate_id in GATE_IDS_V2
    ]


def build_ledger_artifact_from_sources_v2(
    implementation_subject: str, sources: dict[str, bytes]
) -> dict[str, object]:
    if HEX_40_V2.fullmatch(implementation_subject) is None:
        reject_v2("IMPLEMENTATION_SUBJECT", "implementation_subject", "invalid commit")
    manifest = source_manifest_v2(sources)
    active = _active_plan_projection_v2(sources)
    _validate_admission_and_plan_v2(sources, active)
    return {
        "admitted_lineage": {
            **active,
            "implementation_subject": implementation_subject,
            "relation": "ACTIVE_PLAN_IS_ANCESTOR_OF_EXACT_STAGE_A_SUBJECT",
        },
        "authority": dict(NO_AUTHORITY_V2),
        "closed_gap": "current_closure_ledger_gap",
        "current_gate_rows": _current_gate_rows_v2(),
        "dependency_rows": _dependency_projection_v2(sources),
        "historical_donor_rows": _historical_donor_rows_v2(sources),
        "implementation_subject": implementation_subject,
        "nonclaims": list(_NONCLAIMS_V2),
        "schema": SCHEMA_V2,
        "source_manifest": manifest,
        "source_root_sha256": sha256_hex_v2(canonical_json_bytes_v2(manifest)),
        "status": "COMPLETE_CURRENT_EXACT_SUBJECT_LEDGER_ZERO_GATE_PROMOTION",
        "vm_gates_closed": [],
    }


def _validate_manifest_v2(value: dict[str, object]) -> None:
    manifest = value.get("source_manifest")
    if type(manifest) is not list or len(manifest) != len(SOURCE_PATHS_V2):
        reject_v2("SOURCE_MANIFEST_SHAPE", "source_manifest", "manifest denominator drift")
    rows = cast(list[object], manifest)
    normalized: list[dict[str, str]] = []
    for index, row in enumerate(rows):
        if type(row) is not dict or set(row) != {"path", "sha256"}:
            reject_v2("SOURCE_MANIFEST_SHAPE", f"source_manifest[{index}]", "row shape")
        mapping = cast(dict[str, object], row)
        path = mapping.get("path")
        digest = mapping.get("sha256")
        if type(path) is not str or type(digest) is not str or HEX_64_V2.fullmatch(digest) is None:
            reject_v2("SOURCE_MANIFEST_SHAPE", f"source_manifest[{index}]", "row types")
        normalized.append({"path": cast(str, path), "sha256": cast(str, digest)})
    if [row["path"] for row in normalized] != list(SOURCE_PATHS_V2):
        reject_v2("SOURCE_MANIFEST_SHAPE", "source_manifest", "path order drift")
    if value.get("source_root_sha256") != sha256_hex_v2(canonical_json_bytes_v2(normalized)):
        reject_v2("SOURCE_MANIFEST_SHAPE", "source_root_sha256", "root mismatch")


def validate_ledger_artifact_v2(artifact: object) -> None:
    if type(artifact) is not dict:
        reject_v2("ARTIFACT_SHAPE", "artifact", "root must be an object")
    value = cast(dict[str, object], artifact)
    expected_fields = {
        "admitted_lineage",
        "authority",
        "closed_gap",
        "current_gate_rows",
        "dependency_rows",
        "historical_donor_rows",
        "implementation_subject",
        "nonclaims",
        "schema",
        "source_manifest",
        "source_root_sha256",
        "status",
        "vm_gates_closed",
    }
    if set(value) != expected_fields:
        reject_v2("ARTIFACT_SHAPE", "artifact", "closed top-level fields required")
    if (
        value.get("schema") != SCHEMA_V2
        or value.get("status") != "COMPLETE_CURRENT_EXACT_SUBJECT_LEDGER_ZERO_GATE_PROMOTION"
    ):
        reject_v2("ARTIFACT_STATUS", "artifact", "schema or status drift")
    if value.get("authority") != NO_AUTHORITY_V2 or value.get("vm_gates_closed") != []:
        reject_v2("AUTHORITY_DRIFT", "authority", "authority and gate closure must remain empty")
    subject = value.get("implementation_subject")
    if type(subject) is not str or HEX_40_V2.fullmatch(subject) is None:
        reject_v2("IMPLEMENTATION_SUBJECT", "implementation_subject", "invalid commit")
    lineage = _one_mapping_v2(value.get("admitted_lineage"), "admitted_lineage")
    expected_lineage_fields = {
        "active_plan_commit",
        "active_plan_path",
        "active_plan_sha256",
        "admission_receipt_path",
        "admission_receipt_payload_sha256",
        "implementation_subject",
        "relation",
    }
    if set(lineage) != expected_lineage_fields:
        reject_v2("ADMITTED_LINEAGE", "admitted_lineage", "closed lineage fields required")
    if (
        lineage.get("implementation_subject") != subject
        or lineage.get("active_plan_commit") != EXPECTED_ACTIVE_PLAN_COMMIT_V2
        or lineage.get("active_plan_path") != PLAN_PATH_V2
        or lineage.get("admission_receipt_path") != ADMISSION_PATH_V2
        or lineage.get("relation") != "ACTIVE_PLAN_IS_ANCESTOR_OF_EXACT_STAGE_A_SUBJECT"
    ):
        reject_v2("ADMITTED_LINEAGE", "admitted_lineage", "subject lineage drift")
    if value.get("current_gate_rows") != _current_gate_rows_v2():
        reject_v2("CURRENT_GATE_PROMOTION", "current_gate_rows", "all gates must remain open")
    donors = _one_list_v2(value.get("historical_donor_rows"), "historical_donor_rows")
    if [row.get("gate_id") if type(row) is dict else None for row in donors] != list(GATE_IDS_V2):
        reject_v2("HISTORICAL_DISPOSITION", "historical_donor_rows", "gate denominator drift")
    if any(
        type(row) is not dict
        or set(row) != {"disposition", "gate_id", "historical_status", "source_subject"}
        or row.get("disposition") != "STALE_DONOR_NOT_CURRENT_EVIDENCE"
        or row.get("historical_status") not in {"GAP", "PARTIAL"}
        or row.get("source_subject") != EXPECTED_HISTORICAL_SUBJECT_V2
        for row in donors
    ):
        reject_v2("HISTORICAL_DISPOSITION", "historical_donor_rows", "donor label drift")
    dependencies = _one_list_v2(value.get("dependency_rows"), "dependency_rows")
    if [row.get("obligation_id") if type(row) is dict else None for row in dependencies] != [
        row[0] for row in DEPENDENCY_ROWS_V2
    ]:
        reject_v2("DEPENDENCY_DENOMINATOR", "dependency_rows", "dependency denominator drift")
    for index, dependency in enumerate(dependencies):
        if type(dependency) is not dict or set(dependency) != {
            "artifact_path",
            "artifact_sha256",
            "evidence_relation",
            "obligation_id",
            "status",
        }:
            reject_v2("DEPENDENCY_SHAPE", f"dependency_rows[{index}]", "closed row required")
        dependency_row = cast(dict[str, object], dependency)
        expected = DEPENDENCY_ROWS_V2[index]
        if (
            dependency_row.get("artifact_path") != expected[1]
            or dependency_row.get("status") != expected[3]
            or dependency_row.get("evidence_relation")
            != "SOURCE_BOUND_ANCESTOR_RECHECK_AT_POINT_OF_USE"
        ):
            reject_v2("DEPENDENCY_SHAPE", f"dependency_rows[{index}]", "dependency drift")
        digest = dependency_row.get("artifact_sha256")
        if type(digest) is not str or HEX_64_V2.fullmatch(digest) is None:
            reject_v2("DEPENDENCY_SHAPE", f"dependency_rows[{index}]", "invalid digest")
    if (
        value.get("nonclaims") != list(_NONCLAIMS_V2)
        or value.get("closed_gap") != "current_closure_ledger_gap"
    ):
        reject_v2("CLAIM_CEILING", "nonclaims", "claim ceiling drift")
    _validate_manifest_v2(value)


def build_ledger_artifact_v2(root: Path) -> dict[str, object]:
    from tools.value_movement_closure_ledger_git_v2 import build_ledger_artifact_from_repo_v2

    return build_ledger_artifact_from_repo_v2(root)


def build_ledger_bytes_v2(root: Path) -> bytes:
    return canonical_json_bytes_v2(build_ledger_artifact_v2(root))


def check_ledger_v2(root: Path) -> dict[str, object]:
    from tools.value_movement_closure_ledger_git_v2 import check_ledger_from_repo_v2

    return check_ledger_from_repo_v2(root)


ValueMovementClosureLedgerRejectV2 = OperatorSurfaceRegistryRejectV2

__all__ = [
    "ARTIFACT_RELATIVE_PATH_V2",
    "CHECK_SCHEMA_V2",
    "GATE_IDS_V2",
    "NO_AUTHORITY_V2",
    "SCHEMA_V2",
    "SOURCE_PATHS_V2",
    "ValueMovementClosureLedgerRejectV2",
    "build_ledger_artifact_from_sources_v2",
    "build_ledger_artifact_v2",
    "build_ledger_bytes_v2",
    "canonical_json_bytes_v2",
    "check_ledger_v2",
    "decode_json_object_v2",
    "sha256_hex_v2",
    "source_manifest_v2",
    "validate_ledger_artifact_v2",
]
