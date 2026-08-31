"""Pure certificate model for the O-007B V3 current-subject restage."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Mapping, NoReturn

from tools import o007b_cross_language_sink_closure_v2 as predecessor

ARTIFACT_PATH_V3 = "docs/research/ZENODEX_O007B_CROSS_LANGUAGE_SINK_CLOSURE_V3.json"
ARTIFACT_SCHEMA_V3 = "zenodex/o007b-cross-language-sink-closure/v3"
CHECK_SCHEMA_V3 = "zenodex/o007b-cross-language-sink-closure-check/v3"
CERTIFICATE_DOMAIN_V3 = b"zenodex/o007b-cross-language-sink-closure-root/v3"
MANIFEST_PATH_V3 = "tools/m6_cross_language_value_sink_manifest_v3.json"

BASE_COMMIT_V3 = "4cbe500f4c7fb38202c9d39ac21efc0340cde20b"
BASE_TREE_V3 = "4a95a997ad390d71331edab157f572f6b545b94a"

PLAN_COMMIT_V3 = predecessor.PLAN_COMMIT_V2
PLAN_PATH_V3 = predecessor.PLAN_PATH_V2
PLAN_SHA256_V3 = predecessor.PLAN_SHA256_V2
ADMISSION_COMMIT_V3 = predecessor.ADMISSION_COMMIT_V2
ADMISSION_PATH_V3 = predecessor.ADMISSION_PATH_V2
ADMISSION_SHA256_V3 = predecessor.ADMISSION_SHA256_V2
PLAN_REGISTRY_PATH_V3 = predecessor.PLAN_REGISTRY_PATH_V2
PLAN_REGISTRY_SHA256_V3 = predecessor.PLAN_REGISTRY_SHA256_V2

O007A_ARTIFACT_PATH_V3 = predecessor.O007A_ARTIFACT_PATH_V2
O007A_ARTIFACT_SHA256_V3 = predecessor.O007A_ARTIFACT_SHA256_V2
O007A_CERTIFICATE_ROOT_V3 = predecessor.O007A_CERTIFICATE_ROOT_V2
O007A_STAGE_A_V3 = predecessor.O007A_STAGE_A_V2
O007A_STAGE_B_V3 = predecessor.O007A_STAGE_B_V2
O006_ARTIFACT_PATH_V3 = predecessor.O006_ARTIFACT_PATH_V2
O006_ARTIFACT_SHA256_V3 = predecessor.O006_ARTIFACT_SHA256_V2
O006_CERTIFICATE_ROOT_V3 = predecessor.O006_CERTIFICATE_ROOT_V2

PREDECESSOR_ARTIFACT_PATH_V2 = predecessor.ARTIFACT_PATH_V2
PREDECESSOR_ARTIFACT_SHA256_V2 = (
    "e87bb5ae896eb602cdfa0be09f6363a1dd35c1eade6443e1fba81f4ede9852dc"
)
PREDECESSOR_CERTIFICATE_ROOT_V2 = (
    "d1d8b7547a6ed36827a3b1de240c48abb0865781d043fc6a85e5a80c1b5e6416"
)
PREDECESSOR_STAGE_A_V2 = "52b9341291fab78e3783b30a87c294f6733d0dd3"
PREDECESSOR_STAGE_B_V2 = "b042a95fbf1f119228a706beec42f571953600e1"

STAGE_A_SOURCE_PATHS_V3 = (
    "tests/evidence/test_hygiene/THV1-20260831-o007b-cross-language-sink-closure-v3.json",
    "tests/test_check_o007b_cross_language_sink_closure_v3.py",
    "tools/build_o007b_cross_language_sink_closure_v3.py",
    "tools/check_o007b_cross_language_sink_closure_v3.py",
    MANIFEST_PATH_V3,
    "tools/o007b_cross_language_sink_closure_v3.py",
)

V2_PRESERVED_PATHS = tuple(
    sorted(set(predecessor.STAGE_A_SOURCE_PATHS_V2 + (PREDECESSOR_ARTIFACT_PATH_V2,)))
)

CURRENT_CHANGED_SOURCE_PATHS_V3 = (
    "zk/global_settlement_abi_v2/src/asset_lane_state.rs",
    "zk/global_settlement_abi_v2/src/asset_origin_registry.rs",
    "zk/global_settlement_abi_v2/src/asset_origin_registry_types.rs",
    "zk/global_settlement_abi_v2/tests/asset_origin_golden.rs",
)

EVIDENCE_SOURCE_PATHS_V3 = tuple(
    sorted(
        set(
            predecessor.EVIDENCE_SOURCE_PATHS_V2
            + V2_PRESERVED_PATHS
            + CURRENT_CHANGED_SOURCE_PATHS_V3
            + (
                "docs/research/ZENODEX_O008A_DEPENDENCY_POLICY_BLOCKER_V1.json",
                "docs/research/evidence/ZENODEX_O008A_LOCAL_DEPENDENCY_EVIDENCE_V1.json",
            )
        )
    )
)

EXPECTED_INVENTORY_V3: dict[str, object] = {
    "dynamic_import_declaration_count": 14,
    "generated_include_owner_count": 12,
    "generated_python_owner_count": 26,
    "operation_occurrence_counts": {"RUST": 33, "SHELL": 359, "TAU": 2086},
    "operation_row_counts": {"RUST": 31, "SHELL": 108, "TAU": 503},
    "projection_root": "128200f8a6660d3e29e58f6b0e9752faf19896ffc5f6c3830c0d7a4a89126cc0",
    "source_counts": {"PYTHON": 26, "RUST": 293, "SHELL": 66, "TAU": 550},
    "source_provenance_counts": {"GENERATED_REFERENCE": 26, "HANDWRITTEN": 909},
    "tracked_candidate_count": 935,
    "unmediated_operation_count": 362,
    "unmediated_operation_root": (
        "a579a3d0e0545d9c035c7248da8ca50743fe88da3abea7a55fe90a6fe2475732"
    ),
    "unresolved_dynamic_import_count": 4,
}

REVIEWED_SOURCE_DELTA_FROM_V2 = (
    {
        "new_sha256": "fd86b7d70456f8b660b175400022a8dbc619257acf75842b702ac87000a2375c",
        "new_size_bytes": 13445,
        "old_sha256": "edae34c8a0ab3ceab373444c706bbd09261864f011b97e0e5d427a262988a893",
        "old_size_bytes": 13367,
        "path": CURRENT_CHANGED_SOURCE_PATHS_V3[0],
    },
    {
        "new_sha256": "0ace78787e46575ea225ba975d164b946dc8cfca44588b5d444cc61e4b34d647",
        "new_size_bytes": 13485,
        "old_sha256": "0aa6a0c8c6450b23599d88514e24e068930f5354abbf1cf90001466dcb0804d8",
        "old_size_bytes": 13295,
        "path": CURRENT_CHANGED_SOURCE_PATHS_V3[1],
    },
    {
        "new_sha256": "fccd9a67ead7df9be9a7d0d7f19e9cd471070594c07fd1fb89559174d68e12f4",
        "new_size_bytes": 14746,
        "old_sha256": "4d6bd2a4b64b48c02bd8f5d9cc7bf911a50832cd2d4642d4c97abf7197bd436d",
        "old_size_bytes": 14345,
        "path": CURRENT_CHANGED_SOURCE_PATHS_V3[2],
    },
    {
        "new_sha256": "24eb3d761b74fa3bdec5d05bd84825d230f106ec1828af2d49cd7af2a83aa67a",
        "new_size_bytes": 18412,
        "old_sha256": "ffa995201e6a2a02f7325f6913055798feab53ef8c63394870948a076dee9ac9",
        "old_size_bytes": 16036,
        "path": CURRENT_CHANGED_SOURCE_PATHS_V3[3],
    },
)

NONCLAIMS_V3 = (
    "The reviewed projection uses bounded AST and lexical vocabularies; it does not establish that every possible sink syntax is enumerated.",
    "The four reviewed source-row changes preserve the prior operation rows; this does not prove semantic equivalence of the changed Rust programs.",
    "Dynamic-import declarations remain bounded to the O-007A Python deployment closure; four targets remain unresolved for O-007C.",
    "Generated ownership declarations do not establish reproducible generator replay, semantic equivalence, or build provenance.",
    "Static discovery does not establish runtime reachability, mediation, sole-publisher closure, terminal user-story closure, or production durability.",
    "VM-01 remains OPEN and no production, release, settlement, mount, migration, verifier, or value-movement authority is granted.",
)


class O007BClosureRejectV3(ValueError):
    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code}: {path}: {detail}")
        self.code = code
        self.path = path
        self.detail = detail


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007BClosureRejectV3(code, path, detail)


@dataclass(frozen=True, slots=True)
class SourcePinV3:
    path: str
    git_blob_sha: str
    git_mode: str
    sha256: str
    size_bytes: int

    def to_json(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True, slots=True)
class StageASnapshotV3:
    stage_a_commit: str
    stage_a_tree: str
    stage_a_source_pins: tuple[SourcePinV3, ...]
    evidence_source_pins: tuple[SourcePinV3, ...]


def canonical_json_bytes_v3(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def certificate_root_v3(payload: object) -> str:
    return hashlib.sha256(
        CERTIFICATE_DOMAIN_V3 + b"\0" + canonical_json_bytes_v3(payload)
    ).hexdigest()


def claim_ceiling_v3() -> dict[str, object]:
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
                _reject("DEPENDENCY_REPORT", f"{name}.{key}", "exact status mismatch")
    if (
        o007a_check.get("artifact_sha256") != O007A_ARTIFACT_SHA256_V3
        or o007a_check.get("certificate_root") != O007A_CERTIFICATE_ROOT_V3
        or o007a_check.get("stage_a_commit") != O007A_STAGE_A_V3
        or o007a_check.get("stage_b_commit") != O007A_STAGE_B_V3
        or o007a_check.get("vm01_status") != "OPEN"
        or o007a_check.get("vm_gates_closed") != []
    ):
        _reject("O007A_REPORT", "o_007a", "exact dependency identity mismatch")
    if (
        o006_check.get("artifact_sha256") != O006_ARTIFACT_SHA256_V3
        or o006_check.get("certificate_root") != O006_CERTIFICATE_ROOT_V3
        or o006_check.get("vm_gates_closed") != []
    ):
        _reject("O006_REPORT", "o_006", "exact dependency identity mismatch")


def _require_inventory(inventory: Mapping[str, object]) -> None:
    if inventory.get("report_ok") is not True or inventory.get("report_findings") != []:
        _reject("INVENTORY_REPORT", "inventory_evidence", "report must pass exactly")
    if inventory.get("release_ready") is not False or inventory.get("vm01_status") != "OPEN":
        _reject("INVENTORY_CLAIM", "inventory_evidence", "claim ceiling drift")
    if inventory.get("generated_replay_ownership_complete") is not False:
        _reject("GENERATED_REPLAY", "inventory_evidence", "gap must remain explicit")
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
    for key, expected in EXPECTED_INVENTORY_V3.items():
        if inventory.get(key) != expected:
            _reject("INVENTORY_SUBJECT", key, "exact current-subject value mismatch")


def _dependency_bindings_v3(
    o007a_check: Mapping[str, object], o006_check: Mapping[str, object]
) -> dict[str, object]:
    return {
        "active_plan": {
            "admission_commit": ADMISSION_COMMIT_V3,
            "admission_path": ADMISSION_PATH_V3,
            "admission_sha256": ADMISSION_SHA256_V3,
            "plan_commit": PLAN_COMMIT_V3,
            "plan_path": PLAN_PATH_V3,
            "plan_sha256": PLAN_SHA256_V3,
            "registry_path": PLAN_REGISTRY_PATH_V3,
            "registry_sha256": PLAN_REGISTRY_SHA256_V3,
        },
        "o_006": dict(o006_check),
        "o_007a": dict(o007a_check),
    }


def _obligation_v3() -> dict[str, object]:
    return {
        "contributes_to": ["VM-01"],
        "gap_closed": "cross_language_sink_coverage_gap",
        "obligation_id": "O-007B",
        "residual_aggregate_gaps": [
            "user_story_closure",
            "recovery_and_administrative_reachability",
            "terminal_path_closure",
        ],
        "status": "RESEARCH_ONLY_O007B_V3_CURRENT_SUBJECT_NO_VM_GATE",
    }


def _predecessor_v2() -> dict[str, object]:
    return {
        "artifact_path": PREDECESSOR_ARTIFACT_PATH_V2,
        "artifact_sha256": PREDECESSOR_ARTIFACT_SHA256_V2,
        "certificate_root": PREDECESSOR_CERTIFICATE_ROOT_V2,
        "historical_valid": True,
        "stage_a_commit": PREDECESSOR_STAGE_A_V2,
        "stage_b_commit": PREDECESSOR_STAGE_B_V2,
        "superseded_current_applicability": True,
    }


def build_artifact_v3(
    snapshot: StageASnapshotV3,
    *,
    inventory: Mapping[str, object],
    o007a_check: Mapping[str, object],
    o006_check: Mapping[str, object],
) -> dict[str, object]:
    _require_dependency_reports(o007a_check, o006_check)
    _require_inventory(inventory)
    source_pins = snapshot.stage_a_source_pins + snapshot.evidence_source_pins
    payload: dict[str, object] = {
        "bounded_delta": (
            "Current-subject restage of the O-007B cross-language operation inventory "
            "after Asset Origin, resource-bound, formal, and O-008A blocker changes."
        ),
        "claim_ceiling": claim_ceiling_v3(),
        "dependency_bindings": _dependency_bindings_v3(o007a_check, o006_check),
        "implementation_subject": {
            "commit": snapshot.stage_a_commit,
            "parent": BASE_COMMIT_V3,
            "tree": snapshot.stage_a_tree,
        },
        "inventory_evidence": dict(inventory),
        "mutation_killers": [
            "tests/test_check_o007b_cross_language_sink_closure_v3.py::test_recertified_authority_count_or_root_mutant_rejects",
            "tests/test_check_o007b_cross_language_sink_closure_v3.py::test_reviewed_manifest_rejects_changed_projection",
            "tests/test_check_o007b_cross_language_sink_closure_v3.py::test_current_checker_rejects_new_cross_language_writer",
        ],
        "nonclaims": list(NONCLAIMS_V3),
        "obligation": _obligation_v3(),
        "predecessor_v2": _predecessor_v2(),
        "reviewed_source_delta_from_v2": {
            "changed_source_row_count": 4,
            "operation_delta_count": 0,
            "rows": list(REVIEWED_SOURCE_DELTA_FROM_V2),
        },
        "schema": ARTIFACT_SCHEMA_V3,
        "source_manifest": [pin.to_json() for pin in source_pins],
    }
    return {**payload, "certificate_root": certificate_root_v3(payload)}


def validate_artifact_v3(
    raw: bytes,
    snapshot: StageASnapshotV3,
    *,
    inventory: Mapping[str, object] | None = None,
    o007a_check: Mapping[str, object] | None = None,
    o006_check: Mapping[str, object] | None = None,
) -> str:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in pairs:
            if key in result:
                _reject("DUPLICATE_JSON_KEY", ARTIFACT_PATH_V3, key)
            result[key] = item
        return result

    try:
        value = json.loads(raw, object_pairs_hook=reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("ARTIFACT_JSON", ARTIFACT_PATH_V3, type(exc).__name__)
    if not isinstance(value, dict):
        _reject("ARTIFACT_SHAPE", ARTIFACT_PATH_V3, "root must be an object")
    if canonical_json_bytes_v3(value) != raw:
        _reject("ARTIFACT_CANONICAL", ARTIFACT_PATH_V3, "bytes must be canonical")
    certificate = value.pop("certificate_root", None)
    if not isinstance(certificate, str) or certificate != certificate_root_v3(value):
        _reject("CERTIFICATE_ROOT", ARTIFACT_PATH_V3, "root mismatch")
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
    expected = build_artifact_v3(
        snapshot,
        inventory=selected_inventory,
        o007a_check=selected_o007a,
        o006_check=selected_o006,
    )
    if {**value, "certificate_root": certificate} != expected:
        _reject("ARTIFACT_CONTENT", ARTIFACT_PATH_V3, "content differs from exact projection")
    return certificate
