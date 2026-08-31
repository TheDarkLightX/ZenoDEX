"""Pure certificate model for the O-007C indirect sink closure."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Mapping, NoReturn, cast

from tools import o007a_deployed_sink_closure_v2 as o007a
from tools import o007b_cross_language_sink_closure_v2 as o007b_v2
from tools import o007b_cross_language_sink_closure_v3 as o007b_v3
from tools.m6_indirect_value_sinks.inventory import NONCLAIMS as INVENTORY_NONCLAIMS

ARTIFACT_PATH_V1 = "docs/research/ZENODEX_O007C_INDIRECT_SINK_CLOSURE_V1.json"
ARTIFACT_SCHEMA_V1 = "zenodex/o007c-indirect-sink-closure/v1"
CHECK_SCHEMA_V1 = "zenodex/o007c-indirect-sink-closure-check/v1"
CERTIFICATE_DOMAIN_V1 = b"zenodex/o007c-indirect-sink-closure-root/v1"

BASE_COMMIT_V1 = "624bcbe251fa7750afda5332f51b5bcb0b80c54d"
BASE_TREE_V1 = "f450849cef25e1228bb483d838baac7f1374c2c9"

PLAN_COMMIT_V1 = o007b_v3.PLAN_COMMIT_V3
PLAN_PATH_V1 = o007b_v3.PLAN_PATH_V3
PLAN_SHA256_V1 = o007b_v3.PLAN_SHA256_V3
ADMISSION_COMMIT_V1 = o007b_v3.ADMISSION_COMMIT_V3
ADMISSION_PATH_V1 = o007b_v3.ADMISSION_PATH_V3
ADMISSION_SHA256_V1 = o007b_v3.ADMISSION_SHA256_V3
PLAN_REGISTRY_PATH_V1 = o007b_v3.PLAN_REGISTRY_PATH_V3
PLAN_REGISTRY_SHA256_V1 = o007b_v3.PLAN_REGISTRY_SHA256_V3

O007B_V3_ARTIFACT_SHA256 = (
    "78588789509ecd00253ee4cb116a36e499851410966346fc726bfdbc9b07d88d"
)
O007B_V3_CERTIFICATE_ROOT = (
    "08d42e131097532aac17d5bd0c71c3f0b96d5c21c85799b3c7f7c57b572b7e98"
)
O007B_V3_STAGE_A = "540916ff4489e9c0f6605562d07995fdda88298d"
O007B_V3_STAGE_B = BASE_COMMIT_V1

STAGE_A_SOURCE_PATHS_V1 = (
    "tests/evidence/test_hygiene/THV1-20260831-o007c-indirect-sink-closure-v1.json",
    "tests/test_check_m6_indirect_value_sinks_v1.py",
    "tests/test_check_o007c_indirect_sink_closure_v1.py",
    "tools/build_o007c_indirect_sink_closure_v1.py",
    "tools/check_m6_indirect_value_sinks_v1.py",
    "tools/check_o007c_indirect_sink_closure_v1.py",
    "tools/m6_indirect_value_sink_registry_v1.json",
    "tools/m6_indirect_value_sinks/__init__.py",
    "tools/m6_indirect_value_sinks/dynamic.py",
    "tools/m6_indirect_value_sinks/inventory.py",
    "tools/m6_indirect_value_sinks/model.py",
    "tools/m6_indirect_value_sinks/report.py",
    "tools/o007c_indirect_sink_closure_v1.py",
)

PRESERVED_PATHS_V1 = tuple(
    sorted(
        set(
            o007a.STAGE_A_SOURCE_PATHS_V2
            + (o007a.ARTIFACT_PATH_V2,)
            + o007b_v2.STAGE_A_SOURCE_PATHS_V2
            + (o007b_v2.ARTIFACT_PATH_V2,)
            + o007b_v3.STAGE_A_SOURCE_PATHS_V3
            + (o007b_v3.ARTIFACT_PATH_V3,)
        )
    )
)

NORMATIVE_ANCHORS_V1 = ("INV-011", "RSE-009", "WF-13", "WF-14", "WF-15", "WF-17")
SPECIAL_STATUSES_V1 = (
    "MISSING_MOUNTED_WORKER_ENTRYPOINT",
    "UNMOUNTED_MIGRATION_ENTRYPOINT",
)

_O007B_REPORT_KEYS = {
    "artifact_sha256",
    "certificate_root",
    "current_applicable",
    "finding",
    "historical_valid",
    "migration_authority",
    "ok",
    "production_authority",
    "release_authority",
    "release_ready",
    "schema",
    "settlement_authority",
    "stage_a_commit",
    "stage_b_commit",
    "value_movement_authority",
    "verifier_authority",
    "vm01_status",
    "vm_gates_closed",
}
_INVENTORY_REPORT_KEYS = {
    "all_discovered_rows_dispositioned",
    "bounded_inventory_status",
    "candidate_source_root",
    "closed_local_target_set_disposition_count",
    "closed_static_registry_dynamic_count",
    "closed_value_movement_gates",
    "closure_gap_disposition_count",
    "dynamic_declaration_count",
    "dynamic_disposition_count",
    "derived_closed_static_registry_disposition_count",
    "derived_external_literal_disposition_count",
    "derived_local_literal_disposition_count",
    "evidence_tool_exclusion_count",
    "finding",
    "indirect_alias_count",
    "inventory_summary",
    "lifecycle_dispositions",
    "literal_dynamic_count",
    "migration_authority",
    "nonclaims",
    "o007a_bound_through_o007b_v3",
    "o007b_v3_current_applicable",
    "o007b_v3_historical_valid",
    "ok",
    "production_authority",
    "projection_root",
    "registry_sha256",
    "release_authority",
    "release_ready",
    "schema",
    "scope_candidate_count",
    "settlement_authority",
    "source_sink_observation_count",
    "source_sink_record_count",
    "source_bound_research_exclusion_disposition_count",
    "special_statuses",
    "unresolved_dynamic_count",
    "unresolved_dynamic_nonprimary_count",
    "unresolved_dynamic_primary_count",
    "value_movement_authority",
    "verifier_authority",
    "vm01_status",
    "vm_gates_closed",
    "workspace_candidate_count",
}

NONCLAIMS_V1 = (
    "The certificate closes a bounded source-disposition obligation and grants no runtime or writer authority.",
    "Exact source-bound exclusions do not promote excluded research or checker declarations as semantically harmless.",
    "Operator process boundaries remain unresolved and retain no authority.",
    "Dynamic target pins establish local file identity without proving generator replay or behavioral equivalence.",
    "A mounted committed-effect worker entrypoint is missing and migration remains unmounted.",
    "Callback and proof-callback inventories do not establish authenticated invocation or safe effect handling.",
    "VM-01 remains OPEN and no production, release, settlement, migration, verifier, or value-movement authority is granted.",
)


class O007CClosureRejectV1(ValueError):
    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code}: {path}: {detail}")
        self.code = code
        self.path = path
        self.detail = detail


def reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007CClosureRejectV1(code, path, detail)


@dataclass(frozen=True, slots=True)
class SourcePinV1:
    path: str
    git_blob_sha: str
    git_mode: str
    sha256: str
    size_bytes: int

    def to_json(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True, slots=True)
class StageASnapshotV1:
    stage_a_commit: str
    stage_a_tree: str
    stage_a_source_pins: tuple[SourcePinV1, ...]
    registry_sha256: str
    registry_inventory_summary: Mapping[str, object]
    registry_lifecycle_dispositions: tuple[Mapping[str, object], ...]
    registry_projection_root: str


def canonical_json_bytes_v1(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def certificate_root_v1(payload: object) -> str:
    return hashlib.sha256(
        CERTIFICATE_DOMAIN_V1 + b"\0" + canonical_json_bytes_v1(payload)
    ).hexdigest()


def claim_ceiling_v1() -> dict[str, object]:
    return {
        "closed_value_movement_gates": 0,
        "migration_authority": "NONE",
        "production_authority": "NONE",
        "release_authority": "NONE",
        "release_ready": False,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm_01_status": "OPEN",
    }


def require_o007b_v3(report: Mapping[str, object]) -> None:
    if set(report) != _O007B_REPORT_KEYS:
        reject("O007B_V3_REPORT", "keys", "closed report fields mismatch")
    expected = {
        "artifact_sha256": O007B_V3_ARTIFACT_SHA256,
        "certificate_root": O007B_V3_CERTIFICATE_ROOT,
        "current_applicable": True,
        "finding": None,
        "historical_valid": True,
        "migration_authority": "NONE",
        "ok": True,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "release_ready": False,
        "settlement_authority": "NONE",
        "stage_a_commit": O007B_V3_STAGE_A,
        "stage_b_commit": O007B_V3_STAGE_B,
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm01_status": "OPEN",
        "vm_gates_closed": [],
    }
    for key, expected_value in expected.items():
        if report.get(key) != expected_value:
            reject("O007B_V3_REPORT", key, "exact dependency identity or status mismatch")


def require_inventory_report(
    report: Mapping[str, object], snapshot: StageASnapshotV1
) -> None:
    if set(report) != _INVENTORY_REPORT_KEYS:
        reject("INVENTORY_REPORT", "keys", "closed report fields mismatch")
    summary = report.get("inventory_summary")
    if summary != snapshot.registry_inventory_summary:
        reject("INVENTORY_SUMMARY", "inventory_evidence", "registry summary mismatch")
    expected = {
        "all_discovered_rows_dispositioned": True,
        "bounded_inventory_status": "COMPLETE_RESEARCH_ONLY",
        "closed_value_movement_gates": 0,
        "finding": None,
        "migration_authority": "NONE",
        "o007a_bound_through_o007b_v3": True,
        "o007b_v3_current_applicable": True,
        "o007b_v3_historical_valid": True,
        "ok": True,
        "production_authority": "NONE",
        "projection_root": snapshot.registry_projection_root,
        "registry_sha256": snapshot.registry_sha256,
        "release_authority": "NONE",
        "release_ready": False,
        "schema": "zenodex/m6-indirect-value-sink-check/v1",
        "settlement_authority": "NONE",
        "special_statuses": list(SPECIAL_STATUSES_V1),
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm01_status": "OPEN",
        "vm_gates_closed": [],
    }
    for key, expected_value in expected.items():
        if report.get(key) != expected_value:
            reject("INVENTORY_REPORT", key, "exact status or registry binding mismatch")
    if not isinstance(summary, Mapping):
        reject("INVENTORY_SUMMARY", "inventory_evidence", "summary must be an object")
    if report.get("nonclaims") != list(INVENTORY_NONCLAIMS):
        reject("INVENTORY_NONCLAIMS", "inventory_evidence", "nonclaims mismatch")
    if report.get("lifecycle_dispositions") != list(
        snapshot.registry_lifecycle_dispositions
    ):
        reject("LIFECYCLE_DISPOSITIONS", "inventory_evidence", "registry rows mismatch")
    if report.get("candidate_source_root") != summary.get("candidate_source_root"):
        reject("CANDIDATE_SOURCE_ROOT", "inventory_evidence", "summary root mismatch")
    relations = {
        "closed_local_target_set_disposition_count": "closed_local_target_set_disposition_count",
        "closed_static_registry_dynamic_count": "closed_static_registry_dynamic_count",
        "closure_gap_disposition_count": "closure_gap_count",
        "derived_closed_static_registry_disposition_count": "derived_closed_static_registry_disposition_count",
        "derived_external_literal_disposition_count": "derived_external_literal_disposition_count",
        "derived_local_literal_disposition_count": "derived_local_literal_disposition_count",
        "dynamic_declaration_count": "dynamic_declaration_count",
        "dynamic_disposition_count": "dynamic_disposition_count",
        "evidence_tool_exclusion_count": "evidence_tool_exclusion_count",
        "indirect_alias_count": "indirect_alias_count",
        "literal_dynamic_count": "literal_dynamic_count",
        "scope_candidate_count": "scope_candidate_count",
        "source_sink_observation_count": "source_sink_observation_count",
        "source_sink_record_count": "source_sink_record_count",
        "source_bound_research_exclusion_disposition_count": "source_bound_research_exclusion_disposition_count",
        "unresolved_dynamic_count": "unresolved_dynamic_count",
        "unresolved_dynamic_nonprimary_count": "unresolved_dynamic_nonprimary_count",
        "unresolved_dynamic_primary_count": "unresolved_dynamic_primary_count",
        "workspace_candidate_count": "workspace_candidate_count",
    }
    for report_key, summary_key in relations.items():
        if report.get(report_key) != summary.get(summary_key):
            reject("INVENTORY_RELATION", report_key, summary_key)
    if report.get("dynamic_disposition_count") != summary.get("dynamic_declaration_count"):
        reject("DYNAMIC_DISPOSITION_COUNT", "inventory_evidence", "a declaration lacks a disposition")
    if summary.get("indirect_alias_count") != 0:
        reject("INDIRECT_ALIAS", "inventory_evidence", "indirect aliases must be absent")
    if summary.get("mounted_worker_launcher_count") != 0:
        reject("MOUNTED_WORKER", "inventory_evidence", "missing-worker status is stale")
    if summary.get("mounted_migration_launcher_count") != 0:
        reject("MOUNTED_MIGRATION", "inventory_evidence", "unmounted status is stale")
    workspace = summary.get("workspace_candidate_count")
    exclusions = summary.get("evidence_tool_exclusion_count")
    scope = summary.get("scope_candidate_count")
    if not all(type(value) is int for value in (workspace, exclusions, scope)):
        reject("SCOPE_COUNTS", "inventory_evidence", "counts must be exact integers")
    if cast(int, workspace) - cast(int, exclusions) != cast(int, scope):
        reject("SCOPE_FORMULA", "inventory_evidence", "candidate arithmetic mismatch")


def _dependency_bindings(report: Mapping[str, object]) -> dict[str, object]:
    return {
        "active_plan": {
            "admission_commit": ADMISSION_COMMIT_V1,
            "admission_path": ADMISSION_PATH_V1,
            "admission_sha256": ADMISSION_SHA256_V1,
            "plan_commit": PLAN_COMMIT_V1,
            "plan_path": PLAN_PATH_V1,
            "plan_sha256": PLAN_SHA256_V1,
            "registry_path": PLAN_REGISTRY_PATH_V1,
            "registry_sha256": PLAN_REGISTRY_SHA256_V1,
        },
        "o_007b_v3": dict(report),
    }


def build_artifact_v1(
    snapshot: StageASnapshotV1,
    *,
    inventory_report: Mapping[str, object],
    o007b_report: Mapping[str, object],
) -> dict[str, object]:
    require_o007b_v3(o007b_report)
    require_inventory_report(inventory_report, snapshot)
    payload: dict[str, object] = {
        "bounded_delta": (
            "Exact source-bound dispositions for non-primary Python value sinks, unresolved dynamic "
            "loaders, O-007A closure gaps, and recovery, migration, callback, worker, and "
            "administrative lifecycle surfaces."
        ),
        "claim_ceiling": claim_ceiling_v1(),
        "dependency_bindings": _dependency_bindings(o007b_report),
        "implementation_subject": {
            "commit": snapshot.stage_a_commit,
            "parent": BASE_COMMIT_V1,
            "tree": snapshot.stage_a_tree,
        },
        "inventory_evidence": dict(inventory_report),
        "mutation_killers": [
            "tests/test_check_m6_indirect_value_sinks_v1.py::test_closed_disposition_maps_reject_unknown_rows",
            "tests/test_check_m6_indirect_value_sinks_v1.py::test_target_boundaries_and_digest_fail_closed",
            "tests/test_check_o007c_indirect_sink_closure_v1.py::test_current_checker_rejects_path_write_bytes_alias_mutant",
        ],
        "nonclaims": list(NONCLAIMS_V1),
        "normative_anchors": list(NORMATIVE_ANCHORS_V1),
        "obligation": {
            "contributes_to": ["VM-01"],
            "gap_closed": "indirect_value_sink_disposition_gap",
            "obligation_id": "O-007C",
            "residual_statuses": list(SPECIAL_STATUSES_V1),
            "status": "RESEARCH_ONLY_O007C_V1_NO_VM_GATE",
        },
        "schema": ARTIFACT_SCHEMA_V1,
        "source_manifest": [pin.to_json() for pin in snapshot.stage_a_source_pins],
    }
    return {**payload, "certificate_root": certificate_root_v1(payload)}


def validate_artifact_v1(
    raw: bytes,
    snapshot: StageASnapshotV1,
    *,
    inventory_report: Mapping[str, object] | None = None,
    o007b_report: Mapping[str, object] | None = None,
) -> str:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                reject("DUPLICATE_JSON_KEY", ARTIFACT_PATH_V1, key)
            value[key] = item
        return value

    try:
        value = json.loads(raw, object_pairs_hook=reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        reject("ARTIFACT_JSON", ARTIFACT_PATH_V1, type(exc).__name__)
    if not isinstance(value, dict):
        reject("ARTIFACT_SHAPE", ARTIFACT_PATH_V1, "root must be an object")
    if canonical_json_bytes_v1(value) != raw:
        reject("ARTIFACT_CANONICAL", ARTIFACT_PATH_V1, "bytes must be canonical")
    certificate = value.pop("certificate_root", None)
    if not isinstance(certificate, str) or certificate != certificate_root_v1(value):
        reject("CERTIFICATE_ROOT", ARTIFACT_PATH_V1, "root mismatch")
    bindings = value.get("dependency_bindings")
    recorded_o007b: object = None
    if isinstance(bindings, dict):
        recorded_o007b = bindings.get("o_007b_v3")
    selected_o007b = recorded_o007b if o007b_report is None else o007b_report
    selected_inventory = value.get("inventory_evidence") if inventory_report is None else inventory_report
    if not isinstance(selected_o007b, Mapping):
        reject("O007B_V3_REPORT", "dependency_bindings", "report must be an object")
    if not isinstance(selected_inventory, Mapping):
        reject("INVENTORY_REPORT", "inventory_evidence", "report must be an object")
    expected = build_artifact_v1(
        snapshot,
        inventory_report=selected_inventory,
        o007b_report=selected_o007b,
    )
    if {**value, "certificate_root": certificate} != expected:
        reject("ARTIFACT_CONTENT", ARTIFACT_PATH_V1, "content differs from exact projection")
    return certificate
