"""Pure certificate model for the bounded O-007B cross-language inventory."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Mapping, NoReturn

ARTIFACT_PATH_V2 = "docs/research/ZENODEX_O007B_CROSS_LANGUAGE_SINK_CLOSURE_V2.json"
ARTIFACT_SCHEMA_V2 = "zenodex/o007b-cross-language-sink-closure/v2"
CERTIFICATE_DOMAIN_V2 = b"zenodex/o007b-cross-language-sink-closure-root/v2"

BASE_COMMIT_V2 = "0250ca4279c6ef673654e764e6ebd5f11d4b6542"
BASE_TREE_V2 = "6effeb3c28ba9474264f93a91293baadf21456e2"
PLAN_COMMIT_V2 = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
PLAN_PATH_V2 = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
PLAN_SHA256_V2 = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
ADMISSION_COMMIT_V2 = "c0fb36c62b20293ebc54fc530f3dfe2e8046576d"
ADMISSION_PATH_V2 = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
ADMISSION_SHA256_V2 = "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d"
PLAN_REGISTRY_PATH_V2 = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
PLAN_REGISTRY_SHA256_V2 = "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4"

O007A_ARTIFACT_PATH_V2 = "docs/research/ZENODEX_O007A_DEPLOYED_SINK_CLOSURE_V2.json"
O007A_ARTIFACT_SHA256_V2 = "4c28f1e02ff676eaedf76d0a1dc9c509bde423ed9ae00da22fbfe17242503a70"
O007A_CERTIFICATE_ROOT_V2 = "77ed63e11c29ae7ad8ad974aef8d323edd57b16e218df8ffc19f27d330269578"
O007A_STAGE_A_V2 = "565e9b8e4b0e13392a1a6af8058d961199dd8846"
O007A_STAGE_B_V2 = "916d8ffe96bebccd76457593f4177aa3fd510cb4"

O006_ARTIFACT_PATH_V2 = "docs/research/M6_O006_COMMAND_LANE_COMPLETION_V2.json"
O006_ARTIFACT_SHA256_V2 = "a78b187269264e37c2f18b896a90c4ebd6d50ebe66921749e3991a4d29e15988"
O006_CERTIFICATE_ROOT_V2 = "fb69388e585b3408ffae3adc3976d9a9135758d9df2867513548fd71cb2b4f8e"

SELECTED_DONOR_COMMIT_V2 = "7d6b4f5eb1124f6c09b2a2d5d46d06c8f695d9d0"
SELECTED_DONOR_PARENT_V2 = "4d286b11bc55f96acdfdf1cce2f2ab1334429c61"
SELECTED_DONOR_TREE_V2 = "a0c5bb5a20f60b954da02b77ad7bab072e70d9db"
REJECTED_RECEIPT_COMMIT_V1 = "1e5b50dfb32c8024b8a6444c704de2a44dfa1e8c"
REJECTED_RECEIPT_TREE_V1 = "878130a31756054da656e11f4b29e00ab795c572"
REJECTED_RECEIPT_SHA256_V1 = "8b3e7cb7530ad8a7fd9955079fafcf5cd6c357b2d74ee2063a0afe17b369d300"
REJECTED_RECEIPT_PATH_V1 = "docs/research/ZENODEX_O007B_CROSS_LANGUAGE_SINK_CLOSURE_V1.json"

DONOR_WRITE_SET_V2 = (
    "tests/test_check_m6_cross_language_value_sinks_v1.py",
    "tools/check_m6_cross_language_value_sinks_v1.py",
    "tools/m6_cross_language_sinks/__init__.py",
    "tools/m6_cross_language_sinks/inventory.py",
    "tools/m6_cross_language_sinks/model.py",
    "tools/m6_cross_language_sinks/operations.py",
    "tools/m6_cross_language_sinks/report.py",
    "tools/m6_cross_language_value_sink_manifest_v1.json",
)

STAGE_A_SOURCE_PATHS_V2 = (
    "tests/evidence/test_hygiene/THV1-20260831-o007b-cross-language-sink-closure-v2.json",
    "tests/test_check_m6_cross_language_value_sinks_v1.py",
    "tests/test_check_o007b_cross_language_sink_closure_v2.py",
    "tools/build_o007b_cross_language_sink_closure_v2.py",
    "tools/check_m6_cross_language_value_sinks_v1.py",
    "tools/check_o007b_cross_language_sink_closure_v2.py",
    "tools/m6_cross_language_sinks/__init__.py",
    "tools/m6_cross_language_sinks/inventory.py",
    "tools/m6_cross_language_sinks/model.py",
    "tools/m6_cross_language_sinks/operations.py",
    "tools/m6_cross_language_sinks/report.py",
    "tools/m6_cross_language_value_sink_manifest_v1.json",
    "tools/o007b_cross_language_sink_closure_v2.py",
)

EVIDENCE_SOURCE_PATHS_V2 = (
    PLAN_PATH_V2,
    ADMISSION_PATH_V2,
    PLAN_REGISTRY_PATH_V2,
    O007A_ARTIFACT_PATH_V2,
    O006_ARTIFACT_PATH_V2,
    "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json",
    "docs/research/ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json",
    "tools/build_m6_o006_command_lane_completion_v2.py",
    "tools/build_o007a_deployed_sink_closure_v2.py",
    "tools/check_m6_o006_command_lane_completion_v2.py",
    "tools/check_o007a_deployed_sink_closure_v2.py",
    "tools/m6_o006_command_lane_completion_v2.py",
    "tools/o007a_deployed_sink_closure_v2.py",
    "zk/global_settlement_abi_v1/src/release.rs",
    "zk/global_settlement_abi_v2/src/effect_values.rs",
)

NONCLAIMS_V2 = (
    "The inventory uses reviewed AST and lexical operation vocabularies; it does not prove that every possible sink syntax is enumerated.",
    "Dynamic-import declarations are bounded to the O-007A Python deployment closure; unresolved targets and recovery, migration, callback, worker, plugin, and administrative reachability remain O-007C work.",
    "Generated owner declarations do not establish reproducible generator replay, semantic equivalence, or build provenance.",
    "Static operation discovery does not establish runtime reachability, mediation, sole-publisher closure, terminal user-story closure, or production durability.",
    "VM-01 remains OPEN and no production, release, settlement, mount, migration, verifier, or value-movement authority is granted.",
)


class O007BClosureRejectV2(ValueError):
    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code}: {path}: {detail}")
        self.code = code
        self.path = path
        self.detail = detail


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007BClosureRejectV2(code, path, detail)


@dataclass(frozen=True, slots=True)
class SourcePinV2:
    path: str
    git_blob_sha: str
    git_mode: str
    sha256: str
    size_bytes: int

    def to_json(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True, slots=True)
class StageASnapshotV2:
    stage_a_commit: str
    stage_a_tree: str
    stage_a_source_pins: tuple[SourcePinV2, ...]
    evidence_source_pins: tuple[SourcePinV2, ...]


def canonical_json_bytes_v2(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def certificate_root_v2(payload: object) -> str:
    return hashlib.sha256(
        CERTIFICATE_DOMAIN_V2 + b"\0" + canonical_json_bytes_v2(payload)
    ).hexdigest()


def claim_ceiling_v2() -> dict[str, object]:
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


def _require_dependency_reports(
    o007a_check: Mapping[str, object], o006_check: Mapping[str, object]
) -> None:
    shared = {
        "current_applicable": True,
        "finding": None,
        "historical_valid": True,
        "migration_authority": "NONE",
        "ok": True,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
    }
    for name, report in (("o_007a", o007a_check), ("o_006", o006_check)):
        for key, expected in shared.items():
            if report.get(key) != expected:
                _reject("DEPENDENCY_REPORT", f"{name}.{key}", "exact check status mismatch")
    if (
        o007a_check.get("artifact_sha256") != O007A_ARTIFACT_SHA256_V2
        or o007a_check.get("certificate_root") != O007A_CERTIFICATE_ROOT_V2
        or o007a_check.get("stage_a_commit") != O007A_STAGE_A_V2
        or o007a_check.get("stage_b_commit") != O007A_STAGE_B_V2
        or o007a_check.get("vm01_status") != "OPEN"
        or o007a_check.get("vm_gates_closed") != []
    ):
        _reject("O007A_REPORT", "o_007a", "exact dependency identity mismatch")
    if (
        o006_check.get("artifact_sha256") != O006_ARTIFACT_SHA256_V2
        or o006_check.get("certificate_root") != O006_CERTIFICATE_ROOT_V2
        or o006_check.get("vm_gates_closed") != []
    ):
        _reject("O006_REPORT", "o_006", "exact dependency identity mismatch")


def _require_inventory(inventory: Mapping[str, object]) -> None:
    if inventory.get("report_ok") is not True:
        _reject("INVENTORY_REPORT", "inventory_evidence", "report must pass")
    if inventory.get("release_ready") is not False or inventory.get("vm01_status") != "OPEN":
        _reject("INVENTORY_CLAIM", "inventory_evidence", "claim ceiling drift")
    definitions = inventory.get("language_operation_definitions")
    if not isinstance(definitions, dict) or set(definitions) != {
        "PYTHON",
        "RUST",
        "SHELL",
        "TAU",
    }:
        _reject("OPERATION_DEFINITIONS", "inventory_evidence", "language set mismatch")
    command_lane = inventory.get("command_lane_consistency")
    if not isinstance(command_lane, dict) or not command_lane.get("rust_lane_ids_v2"):
        _reject("COMMAND_LANE", "inventory_evidence", "O-006 projection is absent")
    for key in ("unmediated_operation_count", "unresolved_dynamic_import_count"):
        value = inventory.get(key)
        if type(value) is not int or value <= 0:
            _reject("RESIDUAL_GAP", key, "must remain an explicit positive count")
    if inventory.get("generated_replay_ownership_complete") is not False:
        _reject("GENERATED_REPLAY", "inventory_evidence", "must remain an explicit gap")


def build_artifact_v2(
    snapshot: StageASnapshotV2,
    *,
    inventory: Mapping[str, object],
    o007a_check: Mapping[str, object],
    o006_check: Mapping[str, object],
) -> dict[str, object]:
    _require_dependency_reports(o007a_check, o006_check)
    _require_inventory(inventory)
    payload: dict[str, object] = {
        "bounded_delta": (
            "Cross-language operation discovery, generated ownership declarations, "
            "dynamic-import declarations, and O-006 command-target consistency only."
        ),
        "claim_ceiling": claim_ceiling_v2(),
        "dependency_bindings": {
            "active_plan": {
                "admission_commit": ADMISSION_COMMIT_V2,
                "admission_path": ADMISSION_PATH_V2,
                "admission_sha256": ADMISSION_SHA256_V2,
                "plan_commit": PLAN_COMMIT_V2,
                "plan_path": PLAN_PATH_V2,
                "plan_sha256": PLAN_SHA256_V2,
                "registry_path": PLAN_REGISTRY_PATH_V2,
                "registry_sha256": PLAN_REGISTRY_SHA256_V2,
            },
            "o_006": dict(o006_check),
            "o_007a": dict(o007a_check),
        },
        "donor_adjudication": {
            "rejected_receipt_commit": REJECTED_RECEIPT_COMMIT_V1,
            "rejected_receipt_path": REJECTED_RECEIPT_PATH_V1,
            "rejected_receipt_reason": (
                "It binds the rejected O-007A V1 lineage and stale O-006 evidence, omits "
                "current-history validation, extensionless shell, Dockerfile, and Fire generated owners."
            ),
            "rejected_receipt_sha256": REJECTED_RECEIPT_SHA256_V1,
            "selected_commit": SELECTED_DONOR_COMMIT_V2,
            "selected_parent": SELECTED_DONOR_PARENT_V2,
            "selected_reason": (
                "The source donor is the only candidate with the full operation-derived "
                "cross-language scanner and permanent counterexamples; its evidence was "
                "restaged and repaired on the exact current O-007A descendant."
            ),
            "selected_tree": SELECTED_DONOR_TREE_V2,
            "selected_write_set": list(DONOR_WRITE_SET_V2),
        },
        "implementation_subject": {
            "commit": snapshot.stage_a_commit,
            "parent": BASE_COMMIT_V2,
            "tree": snapshot.stage_a_tree,
        },
        "inventory_evidence": dict(inventory),
        "mutation_killers": [
            "tests/test_check_m6_cross_language_value_sinks_v1.py::test_cross_language_writer_alias_mutation_breaks_reviewed_projection",
            "tests/test_check_m6_cross_language_value_sinks_v1.py::test_projection_manifest_comparison_rejects_rewritten_observation_root",
            "tests/test_check_o007b_cross_language_sink_closure_v2.py::test_current_checker_rejects_cross_language_writer_mutation",
        ],
        "nonclaims": list(NONCLAIMS_V2),
        "obligation": {
            "contributes_to": ["VM-01"],
            "gap_closed": "cross_language_sink_coverage_gap",
            "obligation_id": "O-007B",
            "residual_aggregate_gaps": [
                "user_story_closure",
                "recovery_and_administrative_reachability",
                "terminal_path_closure",
            ],
            "status": "RESEARCH_ONLY_O007B_BOUNDED_COMPLETE_NO_VM_GATE",
        },
        "schema": ARTIFACT_SCHEMA_V2,
        "source_manifest": [
            pin.to_json() for pin in snapshot.stage_a_source_pins + snapshot.evidence_source_pins
        ],
    }
    return {**payload, "certificate_root": certificate_root_v2(payload)}


def validate_artifact_v2(
    raw: bytes,
    snapshot: StageASnapshotV2,
    *,
    inventory: Mapping[str, object] | None = None,
    o007a_check: Mapping[str, object] | None = None,
    o006_check: Mapping[str, object] | None = None,
) -> str:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in pairs:
            if key in result:
                _reject("DUPLICATE_JSON_KEY", ARTIFACT_PATH_V2, key)
            result[key] = item
        return result

    try:
        value = json.loads(raw, object_pairs_hook=reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("ARTIFACT_JSON", ARTIFACT_PATH_V2, type(exc).__name__)
    if not isinstance(value, dict):
        _reject("ARTIFACT_SHAPE", ARTIFACT_PATH_V2, "root must be an object")
    if canonical_json_bytes_v2(value) != raw:
        _reject("ARTIFACT_CANONICAL", ARTIFACT_PATH_V2, "bytes must be canonical")
    certificate = value.pop("certificate_root", None)
    if not isinstance(certificate, str) or certificate != certificate_root_v2(value):
        _reject("CERTIFICATE_ROOT", ARTIFACT_PATH_V2, "root mismatch")
    bindings = value.get("dependency_bindings")
    recorded_o007a: object = None
    recorded_o006: object = None
    if isinstance(bindings, dict):
        recorded_o007a = bindings.get("o_007a")
        recorded_o006 = bindings.get("o_006")
    selected_o007a = recorded_o007a if o007a_check is None else o007a_check
    selected_o006 = recorded_o006 if o006_check is None else o006_check
    selected_inventory = value.get("inventory_evidence") if inventory is None else inventory
    if not isinstance(selected_o007a, Mapping):
        _reject("O007A_REPORT", "dependency_bindings", "report must be an object")
    if not isinstance(selected_o006, Mapping):
        _reject("O006_REPORT", "dependency_bindings", "report must be an object")
    if not isinstance(selected_inventory, Mapping):
        _reject("INVENTORY_REPORT", "inventory_evidence", "must be an object")
    expected = build_artifact_v2(
        snapshot,
        inventory=selected_inventory,
        o007a_check=selected_o007a,
        o006_check=selected_o006,
    )
    if {**value, "certificate_root": certificate} != expected:
        _reject("ARTIFACT_CONTENT", ARTIFACT_PATH_V2, "content differs from exact projection")
    return certificate
