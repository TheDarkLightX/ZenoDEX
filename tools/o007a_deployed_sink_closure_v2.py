"""Pure projection for the bounded O-007A deployed-sink closure receipt.

The receipt closes one plan row: static Python writer discovery from the exact
repository launcher sources under the selected public-testnet configuration.
It deliberately leaves VM-01 and every authority field open or ``NONE``.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Mapping, NoReturn

ARTIFACT_PATH_V2 = "docs/research/ZENODEX_O007A_DEPLOYED_SINK_CLOSURE_V2.json"
REJECTED_ARTIFACT_PATH_V1 = "docs/research/ZENODEX_O007A_DEPLOYED_SINK_CLOSURE_V1.json"

BASE_COMMIT_V2 = "bb981e259b114d1160d362552be114a01913fc59"
BASE_TREE_V2 = "54d34936d00371f9c309a586e550646c8b50dc86"

PLAN_COMMIT_V2 = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
PLAN_PATH_V2 = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
PLAN_SHA256_V2 = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
ADMISSION_COMMIT_V2 = "c0fb36c62b20293ebc54fc530f3dfe2e8046576d"
ADMISSION_PATH_V2 = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
ADMISSION_SHA256_V2 = "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d"
PLAN_REGISTRY_PATH_V2 = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
PLAN_REGISTRY_SHA256_V2 = "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4"

O005B_SUBJECT_COMMIT_V2 = "d04c9c16ab4a55b21fe8fc5e8d823254b412de1f"
O005B_ARTIFACT_PATH_V2 = "docs/research/ZENODEX_VALUE_MOVEMENT_CLOSURE_LEDGER_V2.json"
O005B_ARTIFACT_SHA256_V2 = "3ef68a8f24a54d5ae22172cc1c4ed23ba701da38bbf4b99a5f890c19cbc1dbca"

O006_ARTIFACT_PATH_V2 = "docs/research/M6_O006_COMMAND_LANE_COMPLETION_V2.json"
O006_ARTIFACT_SHA256_V2 = "a78b187269264e37c2f18b896a90c4ebd6d50ebe66921749e3991a4d29e15988"
O006_CERTIFICATE_ROOT_V2 = "fb69388e585b3408ffae3adc3976d9a9135758d9df2867513548fd71cb2b4f8e"

SELECTED_DONOR_COMMIT_V2 = "57351387ef7f0ad09e0a759baf8826f72d880c66"
SELECTED_DONOR_PARENT_V2 = "21fa295a42d455ced130a50ae66c84b3c1b32afa"
SELECTED_DONOR_TREE_V2 = "d046db12a4b1c9a408eb7c0494e35e4760decadd"
REJECTED_DONOR_COMMIT_V2 = "2085533fefd82d57fbd79049bff618dd9cf484db"
REJECTED_DONOR_TREE_V2 = "0aaa0a49d4ba664a832f3769a20c440812319637"
REPAIR_DONOR_COMMIT_V2 = "eb55de46eb90be1e5ba0c2f8562e00e2dc6c30d7"
REPAIR_DONOR_PARENT_V2 = "0503798586556d79719c8b999f29244c77c63c8b"
REPAIR_DONOR_TREE_V2 = "6eb565e9b4c4c8edc49e074fbca2464cd84b9018"
REJECTED_RECEIPT_COMMIT_V1 = "4d286b11bc55f96acdfdf1cce2f2ab1334429c61"
REJECTED_RECEIPT_TREE_V1 = "a9c6372ab4bc75bedbbe7694526af380dd08734c"

SELECTED_PROFILE_ID_V2 = "public-testnet"
SELECTED_PROFILE_PATH_V2 = "config/deploy/public-testnet.yaml"
SELECTED_PROFILE_SHA256_V2 = "23a07f7b5e9889a4f22790a0257e3a37545dfef68b25ea7fcad7e19b5c1fffd9"
LAUNCHER_SOURCES_ROOT_V2 = "a6758d242b6df7bb1aefa61d268788f0dd600211d9a688c9fbe33225a179a76d"

STAGE_A_SOURCE_PATHS_V2 = (
    "tests/evidence/test_hygiene/THV1-20260831-o007a-deployed-sink-closure-v2.json",
    "tests/test_check_m6_value_sinks_v2.py",
    "tests/test_check_o007a_deployed_sink_closure_v2.py",
    "tools/build_o007a_deployed_sink_closure_v2.py",
    "tools/check_m6_value_sinks_v2.py",
    "tools/check_o007a_deployed_sink_closure_v2.py",
    "tools/m6_value_sink_manifest_v2.json",
    "tools/m6_value_sinks/__init__.py",
    "tools/m6_value_sinks/deployment.py",
    "tools/m6_value_sinks/launchers.py",
    "tools/m6_value_sinks/manifest.py",
    "tools/m6_value_sinks/operations.py",
    "tools/m6_value_sinks/report.py",
    "tools/m6_value_sinks/scanner.py",
    "tools/o007a_deployed_sink_closure_v2.py",
)

LAUNCHER_SOURCE_PATHS_V2 = (
    ".docker/entrypoint.sh",
    "Dockerfile",
    "Dockerfile.hashlocked",
    "Dockerfile.operator-tools",
    "Dockerfile.production-hashlocked",
    "bin/zenoctl",
    "bin/zenodex-local-testnet",
    "bin/zenodex-oracle",
    "bin/zenodex-public-follower",
    "bin/zenodex-public-testnet",
    "bin/zenodex-public-testnet.command",
    "scripts/install_zenodex.sh",
)

EVIDENCE_SOURCE_PATHS_V2 = tuple(
    sorted(
        {
            *LAUNCHER_SOURCE_PATHS_V2,
            SELECTED_PROFILE_PATH_V2,
            PLAN_PATH_V2,
            ADMISSION_PATH_V2,
            PLAN_REGISTRY_PATH_V2,
            O005B_ARTIFACT_PATH_V2,
            O006_ARTIFACT_PATH_V2,
            "tools/zenoctl.py",
        }
    )
)

SELECTED_DONOR_WRITE_SET_V2 = (
    "tests/test_check_m6_value_sinks_v2.py",
    "tools/check_m6_value_sinks_v2.py",
    "tools/m6_value_sink_manifest_v2.json",
    "tools/m6_value_sinks/__init__.py",
    "tools/m6_value_sinks/deployment.py",
    "tools/m6_value_sinks/launchers.py",
    "tools/m6_value_sinks/manifest.py",
    "tools/m6_value_sinks/operations.py",
    "tools/m6_value_sinks/report.py",
    "tools/m6_value_sinks/scanner.py",
)
REJECTED_DONOR_WRITE_SET_V2 = (
    "tests/test_check_m6_value_sinks_v2.py",
    "tools/check_m6_value_sinks_v2.py",
    "tools/m6_value_sink_manifest_v2.json",
)
REVIEWED_RESTAGE_DELTA_PATHS_V2 = (
    "tests/test_check_m6_value_sinks_v2.py",
    "tools/m6_value_sinks/operations.py",
)
REPAIR_EXACT_PATHS_V2 = tuple(
    path for path in SELECTED_DONOR_WRITE_SET_V2 if path not in REVIEWED_RESTAGE_DELTA_PATHS_V2
)

EXPECTED_CLOSURE_V2: dict[str, object] = {
    "classified_identity_count": 162,
    "declared_closure_gap_count": 26,
    "declared_closure_gaps_root": "cc364c5e90b7cee332c35ed03effc3f13fa69b3d685b496c626d7465129017c9",
    "decoded_launcher_count": 12,
    "decoded_launchers_root": "1b2749584c3bdf4f210d5e9af22524f100681ac8944bcd98c8fed1531782da6a",
    "findings_root": "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945",
    "manifest_sha256": "521470b5e59b5bc3ba441216ae3bc69038f383422f8647da366b9c0b3c730e1e",
    "observed_occurrence_count": 181,
    "production_authority": False,
    "release_gap_count": 54,
    "release_gaps_root": "01b3fdc2b8a9ccbfaf6d674c06b1067f3c7a668eec662a6b900d82956c47b545",
    "release_ready": False,
    "report_ok": True,
    "report_sha256": "b72235f4e3cbf121802faf6f4f2aae4aa5239ecc0038b9c86d20a769180211d2",
    "sink_root": "68dff9d0b83ce9893bc50fb07b2801ce55b410b4fa79b90770e6c734f6ee8321",
    "static_reachable_unscanned_module_count": 1,
    "static_reachable_unscanned_modules_root": "18c6c870dd66e5a61116e5541852ca26af671e3042bac8d2dd4330f685afac63",
    "static_scanned_module_count": 463,
    "static_scanned_module_digests_root": "d692a1d19c2cb31056b5540f4a69f695806d6f2512216dcb6eba92f32763d331",
    "unmediated_static_writer_count": 54,
    "unmediated_static_writers_root": "01b3fdc2b8a9ccbfaf6d674c06b1067f3c7a668eec662a6b900d82956c47b545",
    "vm01_status": "OPEN",
}

NONCLAIMS_V2 = (
    "This receipt covers static Python closure from the exact decoded repository launcher sources and source-bound public-testnet configuration; no running deployment or runtime reachability is attested.",
    "Rust, Tau, shell bodies, generated code, native extensions, dynamic loading, callbacks, workers, recovery, migration, and administrative closure remain later obligations.",
    "The retained unmediated writers, typed closure gaps, and unscanned generated module remain explicit gaps; VM-01 remains OPEN and no production, release, settlement, mount, migration, verifier, or value-movement authority is granted.",
)


class O007AClosureRejectV2(ValueError):
    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code}: {path}: {detail}")
        self.code = code
        self.path = path
        self.detail = detail


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise O007AClosureRejectV2(code, path, detail)


@dataclass(frozen=True, slots=True)
class SourcePinV2:
    path: str
    git_blob_sha: str
    git_mode: str
    sha256: str
    size_bytes: int


@dataclass(frozen=True, slots=True)
class StageASnapshotV2:
    stage_a_commit: str
    stage_a_tree: str
    stage_a_source_pins: tuple[SourcePinV2, ...]
    evidence_source_pins: tuple[SourcePinV2, ...]


@dataclass(frozen=True, slots=True)
class CurrentEvidenceV2:
    closure: Mapping[str, object]
    launcher_sources: tuple[Mapping[str, str], ...]


def canonical_json_bytes_v2(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def canonical_root_v2(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _load_json(raw: bytes, *, path: str) -> Mapping[str, Any]:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                _reject("DUPLICATE_JSON_KEY", path, key)
            result[key] = value
        return result

    try:
        value = json.loads(raw, object_pairs_hook=reject_duplicates)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("ARTIFACT_JSON", path, type(exc).__name__)
    if not isinstance(value, Mapping):
        _reject("ARTIFACT_SHAPE", path, "root must be an object")
    return value


def _pins_by_path(snapshot: StageASnapshotV2) -> dict[str, SourcePinV2]:
    rows = snapshot.stage_a_source_pins + snapshot.evidence_source_pins
    by_path = {pin.path: pin for pin in rows}
    if len(by_path) != len(rows):
        _reject("SOURCE_PIN_DUPLICATE", "source_manifest", "duplicate source path")
    return by_path


def _require_snapshot(snapshot: StageASnapshotV2) -> None:
    stage_paths = tuple(pin.path for pin in snapshot.stage_a_source_pins)
    evidence_paths = tuple(pin.path for pin in snapshot.evidence_source_pins)
    if stage_paths != STAGE_A_SOURCE_PATHS_V2:
        _reject("STAGE_A_SOURCE_SET", "source_manifest", "Stage-A source set drift")
    if evidence_paths != EVIDENCE_SOURCE_PATHS_V2:
        _reject("EVIDENCE_SOURCE_SET", "source_manifest", "evidence source set drift")
    pins = _pins_by_path(snapshot)
    expected_hashes = {
        ADMISSION_PATH_V2: ADMISSION_SHA256_V2,
        O005B_ARTIFACT_PATH_V2: O005B_ARTIFACT_SHA256_V2,
        O006_ARTIFACT_PATH_V2: O006_ARTIFACT_SHA256_V2,
        PLAN_PATH_V2: PLAN_SHA256_V2,
        PLAN_REGISTRY_PATH_V2: PLAN_REGISTRY_SHA256_V2,
        SELECTED_PROFILE_PATH_V2: SELECTED_PROFILE_SHA256_V2,
    }
    for path, expected in expected_hashes.items():
        if pins[path].sha256 != expected:
            _reject("DEPENDENCY_SOURCE_DRIFT", path, "exact SHA-256 mismatch")


def _require_evidence(snapshot: StageASnapshotV2, evidence: CurrentEvidenceV2) -> None:
    if dict(evidence.closure) != EXPECTED_CLOSURE_V2:
        _reject("CLOSURE_EVIDENCE_DRIFT", "deployment_closure", "exact census or root drift")
    rows = tuple(dict(row) for row in evidence.launcher_sources)
    pins = _pins_by_path(snapshot)
    expected_rows = tuple(
        {"path": path, "sha256": pins[path].sha256} for path in LAUNCHER_SOURCE_PATHS_V2
    )
    if rows != expected_rows:
        _reject("LAUNCHER_SOURCE_DRIFT", "launcher_sources", "exact source rows drift")
    if canonical_root_v2(list(rows)) != LAUNCHER_SOURCES_ROOT_V2:
        _reject("LAUNCHER_SOURCE_ROOT", "launcher_sources", "root mismatch")


def _claim_ceiling() -> dict[str, object]:
    return {
        "closed_value_movement_gates": 0,
        "migration_authority": "NONE",
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm_01_status": "OPEN",
    }


def _dependencies() -> dict[str, object]:
    return {
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
        "o_005b": {
            "artifact_path": O005B_ARTIFACT_PATH_V2,
            "artifact_sha256": O005B_ARTIFACT_SHA256_V2,
            "closed_value_movement_gates": 0,
            "current_applicable": True,
            "historical_valid": True,
            "implementation_subject": O005B_SUBJECT_COMMIT_V2,
            "point_of_use_checker_ok": True,
            "stage_b_commit": REPAIR_DONOR_PARENT_V2,
            "status": "COMPLETE_CURRENT_EXACT_SUBJECT_LEDGER_ZERO_GATE_PROMOTION",
        },
        "o_006": {
            "artifact_path": O006_ARTIFACT_PATH_V2,
            "artifact_sha256": O006_ARTIFACT_SHA256_V2,
            "certificate_root": O006_CERTIFICATE_ROOT_V2,
            "current_applicable": True,
            "historical_valid": True,
            "point_of_use_checker_ok": True,
            "stage_b_commit": BASE_COMMIT_V2,
            "vm_gates_closed": [],
        },
    }


def _deployment_profile() -> dict[str, object]:
    profile = {
        "path": SELECTED_PROFILE_PATH_V2,
        "profile_id": SELECTED_PROFILE_ID_V2,
        "sha256": SELECTED_PROFILE_SHA256_V2,
    }
    return {
        "configuration_root": "c4fb264cb7cc5de3d3d280fe39c858cde675dcbcbb574e4b4f8cc7f508fcc83f",
        "launcher_selection_id": "ALL_DECLARED_REPOSITORY_LAUNCHERS_PROFILE_INVARIANT_V1",
        "profile_closure_root": "e91a5b175cd3c0e479abd8e449c7d047e3095ebb78a634b7f76a32f7f0b172e2",
        "profile_validation": "PASS_CURRENT_EXACT_PROFILE",
        "relation": "PROFILE_CONFIGURATION_BOUND_TO_PROFILE_INVARIANT_REPOSITORY_LAUNCHER_UNION",
        "selected_profile": profile,
        "selection_reason_code": "DEFAULT_PUBLIC_TESTNET_RESEARCH_CONFIGURATION",
    }


def _donor_selection() -> dict[str, object]:
    return {
        "candidate_relation": "SAME_PARENT_SAME_TITLE",
        "rejected": {
            "commit": REJECTED_DONOR_COMMIT_V2,
            "parent": SELECTED_DONOR_PARENT_V2,
            "tree": REJECTED_DONOR_TREE_V2,
            "write_set": list(REJECTED_DONOR_WRITE_SET_V2),
        },
        "repair_donor": {
            "commit": REPAIR_DONOR_COMMIT_V2,
            "parent": REPAIR_DONOR_PARENT_V2,
            "tree": REPAIR_DONOR_TREE_V2,
            "use": "reviewed modular hardening donor only",
        },
        "selected": {
            "commit": SELECTED_DONOR_COMMIT_V2,
            "parent": SELECTED_DONOR_PARENT_V2,
            "tree": SELECTED_DONOR_TREE_V2,
            "write_set": list(SELECTED_DONOR_WRITE_SET_V2),
        },
        "selection_reason_code": "MODULAR_OWNERSHIP_AND_MUTATION_SURFACE_DOMINANCE_V1",
        "selection_rule": "Select the same-parent candidate that owns separate launcher, closure, manifest, operation, scanner, and report modules plus their permanent tests.",
        "restage_relation": {
            "exact_repair_donor_paths": list(REPAIR_EXACT_PATHS_V2),
            "reviewed_delta_paths": list(REVIEWED_RESTAGE_DELTA_PATHS_V2),
            "reviewed_delta_reason_codes": [
                "ADD_PATH_LCHMOD_DEPLOYED_WRITER_MUTATION_KILLER",
                "REMOVE_MYPY_UNUSED_IGNORE_COMMENTS",
            ],
        },
    }


def _implementation_subject(snapshot: StageASnapshotV2) -> dict[str, object]:
    return {
        "base_commit": BASE_COMMIT_V2,
        "base_tree": BASE_TREE_V2,
        "commit": snapshot.stage_a_commit,
        "parent": BASE_COMMIT_V2,
        "source_manifest": [asdict(pin) for pin in snapshot.stage_a_source_pins],
        "tree": snapshot.stage_a_tree,
    }


def _fixed_body(snapshot: StageASnapshotV2, evidence: CurrentEvidenceV2) -> dict[str, object]:
    _require_snapshot(snapshot)
    _require_evidence(snapshot, evidence)
    launcher_rows = [dict(row) for row in evidence.launcher_sources]
    return {
        "bounded_delta": "Deployed launcher and deployment-profile Python closure only. VM-01 remains open.",
        "claim_ceiling": _claim_ceiling(),
        "dependencies": _dependencies(),
        "deployment_closure": {
            **dict(evidence.closure),
            "launcher_source_count": len(launcher_rows),
            "launcher_sources": launcher_rows,
            "launcher_sources_root": LAUNCHER_SOURCES_ROOT_V2,
        },
        "deployment_profile": _deployment_profile(),
        "donor_selection": _donor_selection(),
        "implementation_subject": _implementation_subject(snapshot),
        "mutation_killers": [
            "tests/test_check_m6_value_sinks_v2.py::test_path_lchmod_deployed_writer_mutant_fails_closed",
            "tests/test_check_m6_value_sinks_v2.py::test_relative_import_writer_fails_the_full_gate",
            "tests/test_check_m6_value_sinks_v2.py::test_atomic_manifest_regeneration_requires_exact_external_prior_digest",
            "tests/test_check_o007a_deployed_sink_closure_v2.py::test_mutation_given_launcher_source_root_drift_then_projection_rejects",
        ],
        "nonclaims": list(NONCLAIMS_V2),
        "obligation": {
            "contributes_to": ["VM-01"],
            "gap_closed": "deployed_launcher_sink_coverage_gap",
            "obligation_id": "O-007A",
            "status": "RESEARCH_ONLY_O007A_DEPLOYED_PROFILE_CLOSURE_COMPLETE_NO_VM_GATE",
        },
        "rejected_prior_receipt": {
            "commit": REJECTED_RECEIPT_COMMIT_V1,
            "disposition": "REJECTED_STALE_O006_DEPENDENCY_AND_NO_HISTORY_CHECKER",
            "path": REJECTED_ARTIFACT_PATH_V1,
            "sha256": "0d7a55c6cccc3cca33d2b27f57f0bb663411c70094225e1ef553cafe7ea513f6",
            "tree": REJECTED_RECEIPT_TREE_V1,
        },
        "schema": "zenodex/o007a-deployed-sink-closure/v2",
    }


def build_o007a_artifact_v2(snapshot: StageASnapshotV2, evidence: CurrentEvidenceV2) -> bytes:
    body = _fixed_body(snapshot, evidence)
    artifact = {**body, "certificate_root": canonical_root_v2(body)}
    return canonical_json_bytes_v2(artifact)


def _evidence_from_artifact(
    artifact: Mapping[str, Any], snapshot: StageASnapshotV2
) -> CurrentEvidenceV2:
    closure = artifact.get("deployment_closure")
    if not isinstance(closure, Mapping):
        _reject("ARTIFACT_SHAPE", "deployment_closure", "must be an object")
    rows = closure.get("launcher_sources")
    if not isinstance(rows, list) or not all(isinstance(row, Mapping) for row in rows):
        _reject("ARTIFACT_SHAPE", "launcher_sources", "must be an object list")
    closure_without_sources = {
        key: value
        for key, value in closure.items()
        if key not in {"launcher_source_count", "launcher_sources", "launcher_sources_root"}
    }
    return CurrentEvidenceV2(
        closure=closure_without_sources,
        launcher_sources=tuple(dict(row) for row in rows),
    )


def validate_o007a_artifact_v2(
    raw: bytes,
    snapshot: StageASnapshotV2,
    evidence: CurrentEvidenceV2 | None = None,
) -> str:
    artifact = _load_json(raw, path=ARTIFACT_PATH_V2)
    if raw != canonical_json_bytes_v2(artifact):
        _reject("ARTIFACT_NONCANONICAL", ARTIFACT_PATH_V2, "bytes are not canonical JSON")
    bound_evidence = evidence or _evidence_from_artifact(artifact, snapshot)
    expected = build_o007a_artifact_v2(snapshot, bound_evidence)
    if raw != expected:
        _reject("ARTIFACT_BINDING_DRIFT", ARTIFACT_PATH_V2, "exact projection mismatch")
    root = artifact.get("certificate_root")
    if not isinstance(root, str):
        _reject("CERTIFICATE_ROOT", ARTIFACT_PATH_V2, "missing root")
    return root
