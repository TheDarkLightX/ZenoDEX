#!/usr/bin/env python3
"""Fail-closed checker for the value-movement semantic closure ledger."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections.abc import Callable
from pathlib import Path
from typing import Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STATUS_PATH = Path(
    "docs/research/ZENODEX_VALUE_MOVEMENT_CLOSURE_STATUS_V1.json"
)
M6_ATDD_PATH = Path("docs/research/m6_global_economic_core_atdd_bdd_v1.json")
EXPECTED_GATE_IDS = tuple(f"VM-{index:02d}" for index in range(1, 13))
EXPECTED_GATE_EVIDENCE_ROOT = (
    "ec9e8f9fb9f1b0cd83ef7c55b4f617a0cea4f85a41952b41f6600f775b998690"
)
EXPECTED_SUBJECT_COMMIT = "84d702fbad7d8f8c81a44bb4aed0d3b300f5474c"
EXPECTED_TOP_LEVEL_FIELDS = frozenset(
    {
        "authority",
        "checker_dependencies",
        "claim_contract",
        "disaster_campaign",
        "gate_status",
        "implemented_slices",
        "independent_reviews",
        "known_semantic_conflicts",
        "live_gate_observations",
        "next_dependency_order",
        "nonclaims",
        "observed_at",
        "schema",
        "semantic_anchors",
        "subject",
        "tau_upstream",
    }
)
EXPECTED_BUY_AND_BURN = (
    "Atomically spend the governed quote-asset fee allocation through the "
    "selected authenticated Spot route and burn the exact ZDEX atoms received."
)
EXPECTED_CLAIM_STATUS = "DRAFT_REVISED_VERIFIER_RELEASE_BOUND"
EXPECTED_HYPERDEFLATION = (
    "No arbitrary fixed percentage of initial supply is required as a floor. "
    "Bind a retained-supply rule such as R(S)=ceil(p*S/q), 0<p<q, and "
    "burn<=S-R(S)."
)
EXPECTED_SEMANTIC_ANCHORS: Mapping[str, object] = {
    "self_custody_language": (
        "Key control determines practical custody. Same-ledger values are modeled "
        "by accounting location, accounting control domain, and claimant entitlement."
    ),
    "asset_precision": (
        "Eight decimal places; integer atoms; no floating point in consensus, "
        "accounting, proof, verifier, or settlement paths."
    ),
    "rescaling": (
        "No denomination rescaling under GlobalSettlementABI V1. Rescaling requires "
        "an ABI V2 migration that distinguishes conversion from issue or burn."
    ),
    "buy_and_burn": EXPECTED_BUY_AND_BURN,
    "buy_and_burn_exclusions": [
        "treasury-balance burn shortcut",
        "legacy transfer-burn substitution",
    ],
    "hosting_compensation": (
        "Separately named governed fee allocation with explicit eligibility, "
        "claimant, expiry, cancellation, and terminal-drain semantics."
    ),
    "hyperdeflation": EXPECTED_HYPERDEFLATION,
    "autonomous_governance": (
        "Autonomous governance and LLM agents may submit authenticated typed "
        "commands only. They receive no independent publication capability."
    ),
    "external_registry_default": (
        "Empty until a complete registered external finality, timeout, refund, "
        "acknowledgment, and idempotency profile is approved."
    ),
}
EXPECTED_IMPLEMENTED_SLICE_IDS = (
    "ECONOMIC_EFFECT_OCCURRENCE_V1",
    "PRODUCTION_BOUNDARY_FAIL_CLOSED_EXECUTION",
    "PUBLISHER_BOUND_EPOCH_VERIFICATION",
    "CERTIFIED_INITIAL_STATE_ADMISSION",
    "INITIAL_STATE_ATOM_COVERAGE_V1",
    "ECONOMIC_INITIAL_STATE_RISC0_GUEST_SOURCE_V1",
    "ECONOMIC_INITIAL_STATE_PREDECESSOR_BINDING_V1",
    "ECONOMIC_INITIAL_STATE_REPLAY_PRESERVATION_V1",
    "ECONOMIC_INITIAL_STATE_SOURCE_HEAD_ACTIVATION_V1",
    "GLOBAL_ECONOMIC_DURABLE_ACTIVATION_JOURNAL_V1",
    "GLOBAL_ECONOMIC_DURABLE_EPOCH_JOURNAL_V1",
    "GLOBAL_ECONOMIC_DURABLE_PUBLISHER_V1",
    "GLOBAL_ECONOMIC_CURRENT_AUTHORITY_HEAD_V1",
    "ECONOMIC_INITIAL_STATE_OUTBOX_CONTINUITY_V1",
    "ECONOMIC_INITIAL_STATE_TERMINAL_CONTINUITY_V1",
    "M6_ZDEX_SEMANTIC_DRIFT_GUARD",
    "M6_COMPLETE_CAPABILITY_REQUIREMENTS",
    "M6_CAPABILITY_PROFILE_BINDING",
    "PYTHON_VALUE_SINK_INVENTORY_V1",
    "M6_ASSET_PRECISION_PROFILE_BINDING_V1",
)
EXPECTED_IMPLEMENTED_SLICE_FIELD_SET_ROOT = (
    "cf298bbf6039db3d8948e99005373575603c8f2863d32104bfbf7c8219539c83"
)
EXPECTED_CLAIM_PATH = Path(
    "docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md"
)
EXPECTED_CAMPAIGN_PATH = Path(
    "docs/research/GLOBAL_ECONOMIC_COMPOSITION_DISASTER_CAMPAIGN_V1.md"
)
EXPECTED_CLAIM_SHA256 = "bdfc9d04065dd58699b075292d168e8215a362271beab1aa85c0851fa48fd0e3"
EXPECTED_CAMPAIGN_SHA256 = "f15740a45c7f6b4ad2531b343ba9ac60ec21550abff2ae2cfb7ae346b9f35fe8"
EXPECTED_VM12_EVIDENCE = (
    "This ledger binds clean scoped implementation subject "
    "84d702fbad7d8f8c81a44bb4aed0d3b300f5474c. The current-authority campaign "
    "preserves minimized second-store, in-flight revocation, revocation-capacity, "
    "historical-retry, decoder-nesting, authority rollback, and non-atomic "
    "migration histories. Two recorded runs have 176 passing tests: 167 adjacent "
    "initialization, verifier, activation, authority, epoch, publisher, and "
    "migration tests plus nine exhaustive value-sink tests. Touched Python passes "
    "Ruff and targeted mypy; the security scanner reported zero advisory "
    "findings. Independent max review returned GO for a research-only commit and "
    "production NO-GO. Anti-rollback authority, atomic migration retirement, "
    "authenticated successor admission, isolated executable attestation, "
    "sole-writer fencing, real Rust/RISC0 replay, objective finality, and complete "
    "release evidence remain absent."
)
CHECKER_DEPENDENCY_ARTIFACTS = {
    "asset_precision_checker_sha256": Path(
        "tools/check_m6_asset_precision_policy_v1.py"
    ),
    "value_sink_checker_sha256": Path("tools/check_m6_value_sinks_v1.py"),
    "m6_atdd_sha256": M6_ATDD_PATH,
    "asset_precision_policy_sha256": Path(
        "docs/research/ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json"
    ),
    "value_sink_manifest_sha256": Path("tools/m6_value_sink_manifest_v1.json"),
}
EXPECTED_M6_ZDEX_PRODUCTION_RULE = (
    "Only the exact ZDEX atoms produced by atomically spending a governed "
    "quote-asset fee allocation through the selected authenticated Spot route "
    "may burn. Each burn preserves R(S)=ceil(p*S/q), with 0<p<q and "
    "burn<=S-R(S); no fixed initial-supply percentage floor is authoritative."
)
EXPECTED_KNOWN_SEMANTIC_CONFLICTS = {
    "ABI_V1_PRECISION_RESCALE": "RESEARCH_ONLY_ABI_V2_MIGRATION_REQUIRED",
    "LEGACY_FIXED_SUPPLY_FLOOR": "LEGACY_INCOMPATIBLE_MUST_NOT_MOUNT",
    "M6_CAPABILITY_CATALOG_OMISSIONS": "OPEN_ADDITIONAL_CAPABILITIES_REQUIRED",
}
PUBLISHER_BOUND_SLICE_ID = "PUBLISHER_BOUND_EPOCH_VERIFICATION"
PUBLISHER_BOUND_SLICE_COMMIT = "408cf223723b001131c013cdb6382c70e56ad932"
PUBLISHER_BOUND_SLICE_ARTIFACTS = {
    "core_sha256": Path("src/core/global_economic_proof_v1.py"),
    "publisher_sha256": Path("src/integration/global_economic_commit_v1.py"),
}
REPLAY_SLICE_ID = "ECONOMIC_INITIAL_STATE_REPLAY_PRESERVATION_V1"
REPLAY_SLICE_COMMIT = "0d29ea7286bd302cf3e2135a7fc7511d78ef5816"
REPLAY_SLICE_ARTIFACTS = {
    "design_sha256": Path(
        "docs/research/ECONOMIC_INITIAL_STATE_REPLAY_PRESERVATION_V1.md"
    ),
    "python_sha256": Path(
        "src/core/economic_initial_state_replay_continuity_v1.py"
    ),
    "python_admission_sha256": Path("src/core/economic_initial_state_v1.py"),
    "python_unit_test_sha256": Path(
        "tests/core/test_economic_initial_state_replay_continuity_v1.py"
    ),
    "python_integration_test_sha256": Path(
        "tests/core/test_global_settlement_abi_v1.py"
    ),
    "golden_fixture_sha256": Path(
        "tests/data/global_settlement_abi_v1_golden.json"
    ),
    "golden_renderer_sha256": Path(
        "tools/render_global_settlement_abi_v1_golden.py"
    ),
    "rust_sha256": Path(
        "zk/global_settlement_abi_v1/src/"
        "economic_initial_state_replay_continuity.rs"
    ),
    "rust_admission_sha256": Path(
        "zk/global_settlement_abi_v1/src/economic_initial_state.rs"
    ),
    "rust_test_sha256": Path(
        "zk/global_settlement_abi_v1/tests/"
        "economic_initial_state_replay_continuity.rs"
    ),
    "risc0_shared_test_sha256": Path(
        "zk/economic_initial_state_risc0/shared/tests/"
        "initial_state_guest_contract.rs"
    ),
}
SOURCE_HEAD_SLICE_ID = "ECONOMIC_INITIAL_STATE_SOURCE_HEAD_ACTIVATION_V1"
SOURCE_HEAD_SLICE_ARTIFACTS = {
    "design_sha256": Path(
        "docs/research/ECONOMIC_INITIAL_STATE_SOURCE_HEAD_ACTIVATION_V1.md"
    ),
    "python_initial_state_sha256": Path("src/core/economic_initial_state_v1.py"),
    "python_publisher_verification_sha256": Path(
        "src/core/economic_initial_state_publisher_verification_v1.py"
    ),
    "python_commit_port_sha256": Path(
        "src/integration/global_economic_commit_v1.py"
    ),
    "python_test_sha256": Path("tests/core/test_global_settlement_abi_v1.py"),
}
DURABLE_ACTIVATION_SLICE_ID = "GLOBAL_ECONOMIC_DURABLE_ACTIVATION_JOURNAL_V1"
DURABLE_ACTIVATION_SLICE_COMMIT = "7b5b142e32c505261fbcea68ebb915464b187acb"
DURABLE_ACTIVATION_SLICE_ARTIFACTS = {
    "design_sha256": Path(
        "docs/research/GLOBAL_ECONOMIC_DURABLE_ACTIVATION_JOURNAL_V1.md"
    ),
    "python_core_sha256": Path(
        "src/core/global_economic_durable_activation_v1.py"
    ),
    "python_journal_sha256": Path(
        "src/integration/global_economic_migration_journal_v1.py"
    ),
    "python_test_sha256": Path(
        "tests/integration/test_global_economic_migration_journal_v1.py"
    ),
}
DURABLE_EPOCH_SLICE_ID = "GLOBAL_ECONOMIC_DURABLE_EPOCH_JOURNAL_V1"
DURABLE_EPOCH_SLICE_COMMIT = EXPECTED_SUBJECT_COMMIT
DURABLE_EPOCH_SLICE_ARTIFACTS = {
    "design_sha256": Path(
        "docs/research/GLOBAL_ECONOMIC_DURABLE_EPOCH_JOURNAL_V1.md"
    ),
    "python_bundle_sha256": Path(
        "src/integration/global_economic_durable_epoch_v1.py"
    ),
    "python_journal_sha256": Path(
        "src/integration/global_economic_epoch_journal_v1.py"
    ),
    "python_test_sha256": Path(
        "tests/integration/test_global_economic_epoch_journal_v1.py"
    ),
    "sink_manifest_sha256": Path("tools/m6_value_sink_manifest_v1.json"),
    "sink_test_sha256": Path("tests/test_check_m6_value_sinks_v1.py"),
}
DURABLE_PUBLISHER_SLICE_ID = "GLOBAL_ECONOMIC_DURABLE_PUBLISHER_V1"
DURABLE_PUBLISHER_SLICE_COMMIT = EXPECTED_SUBJECT_COMMIT
DURABLE_PUBLISHER_SLICE_ARTIFACTS = {
    "design_sha256": Path(
        "docs/research/GLOBAL_ECONOMIC_DURABLE_PUBLISHER_V1.md"
    ),
    "python_publisher_sha256": Path(
        "src/integration/global_economic_durable_publisher_v1.py"
    ),
    "python_proof_sha256": Path("src/core/global_economic_proof_v1.py"),
    "verifier_design_sha256": Path(
        "docs/research/GLOBAL_ECONOMIC_RECEIPT_VERIFIER_RELEASE_BINDING_V1.md"
    ),
    "python_verifier_registry_sha256": Path(
        "src/core/economic_receipt_verifier_registry_v1.py"
    ),
    "python_verifier_evidence_sha256": Path(
        "src/core/economic_receipt_verifier_evidence_v1.py"
    ),
    "python_verifier_deployment_sha256": Path(
        "src/core/economic_receipt_verifier_deployment_v1.py"
    ),
    "python_journal_sha256": Path(
        "src/integration/global_economic_epoch_journal_v1.py"
    ),
    "python_publisher_test_sha256": Path(
        "tests/integration/test_global_economic_durable_publisher_v1.py"
    ),
    "python_verifier_test_sha256": Path(
        "tests/core/test_economic_receipt_verifier_release_v1.py"
    ),
    "python_abi_test_sha256": Path(
        "tests/core/test_global_settlement_abi_v1.py"
    ),
    "python_journal_test_sha256": Path(
        "tests/integration/test_global_economic_epoch_journal_v1.py"
    ),
    "writer_manifest_sha256": Path("tools/m6_writer_inventory_manifest_v1.json"),
    "sink_manifest_sha256": Path("tools/m6_value_sink_manifest_v1.json"),
    "writer_test_sha256": Path("tests/test_check_m6_writer_inventory.py"),
    "sink_test_sha256": Path("tests/test_check_m6_value_sinks_v1.py"),
}
CURRENT_AUTHORITY_SLICE_ID = "GLOBAL_ECONOMIC_CURRENT_AUTHORITY_HEAD_V1"
CURRENT_AUTHORITY_SLICE_COMMIT = EXPECTED_SUBJECT_COMMIT
CURRENT_AUTHORITY_SLICE_ARTIFACTS = {
    "design_sha256": Path(
        "docs/research/GLOBAL_ECONOMIC_CURRENT_AUTHORITY_HEAD_V1.md"
    ),
    "python_core_sha256": Path(
        "src/core/global_economic_authority_head_v1.py"
    ),
    "python_authority_journal_sha256": Path(
        "src/integration/global_economic_authority_journal_v1.py"
    ),
    "python_publisher_sha256": Path(
        "src/integration/global_economic_durable_publisher_v1.py"
    ),
    "python_epoch_journal_sha256": Path(
        "src/integration/global_economic_epoch_journal_v1.py"
    ),
    "python_authority_test_sha256": Path(
        "tests/integration/test_global_economic_authority_journal_v1.py"
    ),
    "python_publisher_test_sha256": Path(
        "tests/integration/test_global_economic_durable_publisher_v1.py"
    ),
    "python_epoch_test_sha256": Path(
        "tests/integration/test_global_economic_epoch_journal_v1.py"
    ),
    "sink_manifest_sha256": Path("tools/m6_value_sink_manifest_v1.json"),
    "sink_test_sha256": Path("tests/test_check_m6_value_sinks_v1.py"),
}


def _object_without_duplicate_keys(
    pairs: list[tuple[str, object]],
) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load_exact_json(path: Path) -> Mapping[str, object]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_object_without_duplicate_keys,
    )
    if type(value) is not dict:
        raise TypeError("closure status root must be an object")
    return value


def _mapping(value: object, name: str, findings: list[str]) -> Mapping[str, object]:
    if type(value) is not dict:
        findings.append(f"{name} must be an object")
        return {}
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_live_gate_checkers_v1() -> tuple[
    Callable[[Path], dict[str, object]],
    Callable[[Path], dict[str, object]],
]:
    """Import checked live-gate helpers only after their source hashes pass."""

    if __package__:
        from tools.check_m6_asset_precision_policy_v1 import (
            check_m6_asset_precision_policy_v1,
        )
        from tools.check_m6_value_sinks_v1 import check_m6_value_sinks_v1
    else:
        from check_m6_asset_precision_policy_v1 import (
            check_m6_asset_precision_policy_v1,
        )
        from check_m6_value_sinks_v1 import (
            check_m6_value_sinks_v1,
        )
    return check_m6_asset_precision_policy_v1, check_m6_value_sinks_v1


def _git_blob_sha256_v1(
    root: Path,
    commit: object,
    relative_path: Path,
) -> str | None:
    """Hash one exact committed blob without invoking a shell."""

    if type(commit) is not str or re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        return None
    try:
        result = subprocess.run(
            [
                "git",
                "--no-replace-objects",
                "-C",
                str(root),
                "cat-file",
                "blob",
                f"{commit}:{relative_path.as_posix()}",
            ],
            check=False,
            capture_output=True,
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return hashlib.sha256(result.stdout).hexdigest()


def _validate_artifact_map_v1(
    root: Path,
    row: Mapping[str, object],
    subject_commit: object,
    artifacts: Mapping[str, Path],
    label: str,
    findings: list[str],
) -> None:
    """Bind recorded hashes to both the scoped checkout and exact subject tree."""

    for field, relative_path in artifacts.items():
        recorded = row.get(field)
        artifact = root / relative_path
        recorded_is_hash = (
            type(recorded) is str
            and re.fullmatch(r"[0-9a-f]{64}", recorded) is not None
        )
        if (
            not recorded_is_hash
            or not artifact.is_file()
            or _sha256(artifact) != recorded
        ):
            findings.append(f"{label} artifact hash mismatch: {field}")
        if (
            not recorded_is_hash
            or _git_blob_sha256_v1(root, subject_commit, relative_path) != recorded
        ):
            findings.append(f"{label} subject-tree artifact mismatch: {field}")


def validate_m6_zdex_semantic_anchor_v1(value: object) -> list[str]:
    """Reject the historical fixed-floor or shortcut-burn M6 semantics."""

    if type(value) is not dict:
        return ["M6 ATDD contract must be an object"]
    policies = value.get("managed_asset_policy")
    if type(policies) is not list or any(type(policy) is not dict for policy in policies):
        return ["M6 ATDD managed_asset_policy must be a list of objects"]
    zdex_rows = [
        policy for policy in policies if policy.get("asset_class") == "zdex_protocol_token"
    ]
    if len(zdex_rows) != 1:
        return ["M6 ATDD must contain exactly one ZDEX managed-asset policy"]
    row = zdex_rows[0]
    findings: list[str] = []
    if row.get("burn_authority") != "fee-funded protocol buy-and-burn transition":
        findings.append("M6 ATDD ZDEX burn authority drift")
    if row.get("production_rule") != EXPECTED_M6_ZDEX_PRODUCTION_RULE:
        findings.append("M6 ATDD ZDEX retained-supply or purchase-and-burn drift")
    return findings


def _validate_replay_slice_evidence_v1(
    root: Path,
    status: Mapping[str, object],
    subject_commit: object,
    findings: list[str],
) -> None:
    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
        return
    replay_rows = [row for row in slices if row.get("id") == REPLAY_SLICE_ID]
    if len(replay_rows) != 1:
        findings.append("replay slice evidence row must occur exactly once")
        return
    replay = replay_rows[0]
    if replay.get("commit") != REPLAY_SLICE_COMMIT:
        findings.append("replay slice implementation commit mismatch")
    if replay.get("artifact_subject_commit") != subject_commit:
        findings.append("replay slice artifact subject commit mismatch")
    _validate_artifact_map_v1(
        root,
        replay,
        subject_commit,
        REPLAY_SLICE_ARTIFACTS,
        "replay slice",
        findings,
    )

    try:
        fixture = _load_exact_json(
            root / REPLAY_SLICE_ARTIFACTS["golden_fixture_sha256"]
        )
    except (OSError, TypeError, ValueError, json.JSONDecodeError):
        findings.append("replay slice golden vector cannot be loaded")
        return
    vectors = fixture.get("vectors")
    if type(vectors) is not dict:
        findings.append("replay slice golden vectors must be an object")
        return
    vector = vectors.get("economic_initial_state_replay_continuity")
    if type(vector) is not dict:
        findings.append("replay slice golden vector must be an object")
        return
    expected_fields = {
        "golden_continuity_root": vector.get("expected_root"),
        "golden_canonical_bytes_sha256": vector.get("canonical_bytes_sha256"),
    }
    for field, expected in expected_fields.items():
        if type(expected) is not str or replay.get(field) != expected:
            findings.append(f"replay slice golden evidence mismatch: {field}")


def _validate_source_head_slice_evidence_v1(
    root: Path,
    status: Mapping[str, object],
    subject_commit: object,
    findings: list[str],
) -> None:
    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
        return
    source_head_rows = [
        row for row in slices if row.get("id") == SOURCE_HEAD_SLICE_ID
    ]
    if len(source_head_rows) != 1:
        findings.append("source-head slice evidence row must occur exactly once")
        return
    source_head = source_head_rows[0]
    if source_head.get("commit") != subject_commit:
        findings.append("source-head slice subject commit mismatch")
    _validate_artifact_map_v1(
        root,
        source_head,
        subject_commit,
        SOURCE_HEAD_SLICE_ARTIFACTS,
        "source-head slice",
        findings,
    )


def _validate_durable_activation_slice_evidence_v1(
    root: Path,
    status: Mapping[str, object],
    subject_commit: object,
    findings: list[str],
) -> None:
    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
        return
    durable_rows = [
        row for row in slices if row.get("id") == DURABLE_ACTIVATION_SLICE_ID
    ]
    if len(durable_rows) != 1:
        findings.append("durable activation slice evidence row must occur exactly once")
        return
    durable = durable_rows[0]
    if durable.get("commit") != DURABLE_ACTIVATION_SLICE_COMMIT:
        findings.append("durable activation slice implementation commit mismatch")
    if durable.get("artifact_subject_commit") != subject_commit:
        findings.append("durable activation slice artifact subject commit mismatch")
    _validate_artifact_map_v1(
        root,
        durable,
        subject_commit,
        DURABLE_ACTIVATION_SLICE_ARTIFACTS,
        "durable activation slice",
        findings,
    )


def _validate_durable_epoch_slice_evidence_v1(
    root: Path,
    status: Mapping[str, object],
    subject_commit: object,
    findings: list[str],
) -> None:
    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
        return
    durable_rows = [row for row in slices if row.get("id") == DURABLE_EPOCH_SLICE_ID]
    if len(durable_rows) != 1:
        findings.append("durable epoch slice evidence row must occur exactly once")
        return
    durable = durable_rows[0]
    if durable.get("commit") != DURABLE_EPOCH_SLICE_COMMIT:
        findings.append("durable epoch slice implementation commit mismatch")
    if durable.get("artifact_subject_commit") != subject_commit:
        findings.append("durable epoch slice artifact subject commit mismatch")
    _validate_artifact_map_v1(
        root,
        durable,
        subject_commit,
        DURABLE_EPOCH_SLICE_ARTIFACTS,
        "durable epoch slice",
        findings,
    )


def _validate_durable_publisher_slice_evidence_v1(
    root: Path,
    status: Mapping[str, object],
    subject_commit: object,
    findings: list[str],
) -> None:
    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
        return
    publisher_rows = [
        row for row in slices if row.get("id") == DURABLE_PUBLISHER_SLICE_ID
    ]
    if len(publisher_rows) != 1:
        findings.append("durable publisher slice evidence row must occur exactly once")
        return
    publisher = publisher_rows[0]
    if publisher.get("commit") != DURABLE_PUBLISHER_SLICE_COMMIT:
        findings.append("durable publisher slice implementation commit mismatch")
    if publisher.get("artifact_subject_commit") != subject_commit:
        findings.append("durable publisher slice artifact subject commit mismatch")
    _validate_artifact_map_v1(
        root,
        publisher,
        subject_commit,
        DURABLE_PUBLISHER_SLICE_ARTIFACTS,
        "durable publisher slice",
        findings,
    )


def _validate_current_authority_slice_evidence_v1(
    root: Path,
    status: Mapping[str, object],
    subject_commit: object,
    findings: list[str],
) -> None:
    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
        return
    rows = [row for row in slices if row.get("id") == CURRENT_AUTHORITY_SLICE_ID]
    if len(rows) != 1:
        findings.append("current authority slice evidence row must occur exactly once")
        return
    authority = rows[0]
    if authority.get("commit") != CURRENT_AUTHORITY_SLICE_COMMIT:
        findings.append("current authority slice implementation commit mismatch")
    if authority.get("artifact_subject_commit") != subject_commit:
        findings.append("current authority slice artifact subject commit mismatch")
    _validate_artifact_map_v1(
        root,
        authority,
        subject_commit,
        CURRENT_AUTHORITY_SLICE_ARTIFACTS,
        "current authority slice",
        findings,
    )


def _validate_publisher_bound_slice_evidence_v1(
    root: Path,
    status: Mapping[str, object],
    subject_commit: object,
    findings: list[str],
) -> None:
    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
        return
    rows = [row for row in slices if row.get("id") == PUBLISHER_BOUND_SLICE_ID]
    if len(rows) != 1:
        findings.append("publisher-bound slice evidence row must occur exactly once")
        return
    publisher_bound = rows[0]
    if publisher_bound.get("commit") != PUBLISHER_BOUND_SLICE_COMMIT:
        findings.append("publisher-bound slice implementation commit mismatch")
    if publisher_bound.get("artifact_subject_commit") != subject_commit:
        findings.append("publisher-bound slice artifact subject commit mismatch")
    _validate_artifact_map_v1(
        root,
        publisher_bound,
        subject_commit,
        PUBLISHER_BOUND_SLICE_ARTIFACTS,
        "publisher-bound slice",
        findings,
    )


def check_value_movement_closure_status_v1(
    root: Path = REPO_ROOT,
    status_path: Path | None = None,
) -> dict[str, object]:
    findings: list[str] = []
    source = status_path or root / DEFAULT_STATUS_PATH
    try:
        status = _load_exact_json(source)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        return {
            "schema": "zenodex/value-movement-closure-status-check/v1",
            "ok": False,
            "findings": [f"status ledger cannot be loaded: {type(exc).__name__}: {exc}"],
        }

    if status.get("schema") != "zenodex/value-movement-closure-status/v1":
        findings.append("closure status schema mismatch")
    if frozenset(status) != EXPECTED_TOP_LEVEL_FIELDS:
        findings.append("closure status top-level field set mismatch")

    subject = _mapping(status.get("subject"), "subject", findings)
    if frozenset(subject) != frozenset(
        {"branch", "commit", "scoped_worktree_clean_before_this_ledger"}
    ):
        findings.append("subject field set mismatch")
    commit = subject.get("commit")
    if type(commit) is not str or re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        findings.append("subject commit must be exact lowercase 40-hex")
    if commit != EXPECTED_SUBJECT_COMMIT:
        findings.append("subject commit differs from checker-pinned subject")
    if subject.get("scoped_worktree_clean_before_this_ledger") is not True:
        findings.append("ledger subject was not recorded from a clean scoped worktree")

    slices = status.get("implemented_slices")
    if type(slices) is not list or any(type(row) is not dict for row in slices):
        findings.append("implemented slices must be a list of objects")
    elif tuple(row.get("id") for row in slices) != EXPECTED_IMPLEMENTED_SLICE_IDS:
        findings.append("implemented slice IDs are incomplete, unknown, or unordered")
    else:
        field_shape = tuple(
            (row["id"], tuple(sorted(row)))
            for row in slices
        )
        field_shape_bytes = json.dumps(
            field_shape,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
        if (
            hashlib.sha256(field_shape_bytes).hexdigest()
            != EXPECTED_IMPLEMENTED_SLICE_FIELD_SET_ROOT
        ):
            findings.append("implemented slice field sets drift")

    dependencies = _mapping(
        status.get("checker_dependencies"),
        "checker dependencies",
        findings,
    )
    if frozenset(dependencies) != frozenset(CHECKER_DEPENDENCY_ARTIFACTS):
        findings.append("checker dependency field set mismatch")
    dependency_findings_before = len(findings)
    _validate_artifact_map_v1(
        root,
        dependencies,
        EXPECTED_SUBJECT_COMMIT,
        CHECKER_DEPENDENCY_ARTIFACTS,
        "checker dependency",
        findings,
    )
    dependencies_valid = len(findings) == dependency_findings_before

    _validate_replay_slice_evidence_v1(root, status, commit, findings)
    _validate_source_head_slice_evidence_v1(root, status, commit, findings)
    _validate_durable_activation_slice_evidence_v1(root, status, commit, findings)
    _validate_durable_epoch_slice_evidence_v1(root, status, commit, findings)
    _validate_durable_publisher_slice_evidence_v1(root, status, commit, findings)
    _validate_current_authority_slice_evidence_v1(root, status, commit, findings)
    _validate_publisher_bound_slice_evidence_v1(root, status, commit, findings)

    authority = _mapping(status.get("authority"), "authority", findings)
    expected_authority: dict[str, object] = {
        "claim_authority": "NONE",
        "production_authority": "NONE",
        "production_ready": False,
        "release_ready": False,
    }
    if dict(authority) != expected_authority:
        findings.append("authority or readiness nonclaim drift")

    claim = _mapping(status.get("claim_contract"), "claim contract", findings)
    if frozenset(claim) != frozenset({"path", "sha256", "status", "verdict"}):
        findings.append("claim contract field set mismatch")
    claim_path = claim.get("path")
    claim_sha = claim.get("sha256")
    if claim_path != EXPECTED_CLAIM_PATH.as_posix():
        findings.append("claim contract path is outside the closed contract")
    if type(claim_sha) is not str:
        findings.append("claim contract path and sha256 must be strings")
    else:
        if claim_sha != EXPECTED_CLAIM_SHA256:
            findings.append("claim contract differs from checker-pinned contract")
        resolved_claim = root / EXPECTED_CLAIM_PATH
        if resolved_claim.is_symlink():
            findings.append("claim contract must not be a symlink")
        if not resolved_claim.is_file() or _sha256(resolved_claim) != claim_sha:
            findings.append("claim contract hash mismatch")
    if claim.get("status") != EXPECTED_CLAIM_STATUS:
        findings.append("claim status drift")
    if claim.get("verdict") != "UNPROVED":
        findings.append("claim verdict must remain UNPROVED")

    campaign = _mapping(
        status.get("disaster_campaign"),
        "disaster campaign",
        findings,
    )
    if frozenset(campaign) != frozenset({"path", "sha256", "status"}):
        findings.append("disaster campaign field set mismatch")
    if campaign.get("path") != EXPECTED_CAMPAIGN_PATH.as_posix():
        findings.append("disaster campaign path is outside the closed contract")
    campaign_sha = campaign.get("sha256")
    if campaign_sha != EXPECTED_CAMPAIGN_SHA256:
        findings.append("disaster campaign differs from checker-pinned contract")
    if (
        type(campaign_sha) is not str
        or not (root / EXPECTED_CAMPAIGN_PATH).is_file()
        or _sha256(root / EXPECTED_CAMPAIGN_PATH) != campaign_sha
    ):
        findings.append("disaster campaign hash mismatch")
    if (root / EXPECTED_CAMPAIGN_PATH).is_symlink():
        findings.append("disaster campaign must not be a symlink")
    if campaign.get("status") != "TESTED_DISCOVERY":
        findings.append("disaster campaign status drift")

    semantics = _mapping(status.get("semantic_anchors"), "semantic anchors", findings)
    if frozenset(semantics) != frozenset(EXPECTED_SEMANTIC_ANCHORS):
        findings.append("semantic anchor key set mismatch")
    for field, expected in EXPECTED_SEMANTIC_ANCHORS.items():
        if semantics.get(field) != expected:
            if field == "buy_and_burn":
                findings.append("buy-and-burn semantic anchor drift")
            elif field == "hyperdeflation":
                findings.append("hyperdeflation semantic anchor drift")
            else:
                findings.append(f"semantic anchor drift: {field}")

    try:
        m6_atdd = _load_exact_json(root / M6_ATDD_PATH)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        findings.append(f"M6 ATDD semantic source cannot be loaded: {type(exc).__name__}: {exc}")
    else:
        findings.extend(validate_m6_zdex_semantic_anchor_v1(m6_atdd))

    conflict_rows = status.get("known_semantic_conflicts")
    if type(conflict_rows) is not list or any(type(row) is not dict for row in conflict_rows):
        findings.append("known semantic conflicts must be a list of objects")
    else:
        conflict_ids = [row.get("id") for row in conflict_rows]
        if conflict_ids != sorted(EXPECTED_KNOWN_SEMANTIC_CONFLICTS):
            findings.append("known semantic conflict IDs are incomplete or unordered")
        for row in conflict_rows:
            conflict_id = row.get("id")
            expected_status = EXPECTED_KNOWN_SEMANTIC_CONFLICTS.get(conflict_id)
            if row.get("status") != expected_status:
                findings.append(f"known semantic conflict status drift: {conflict_id}")
            paths = row.get("paths")
            if type(paths) is not list or not paths or any(type(path) is not str for path in paths):
                findings.append(f"known semantic conflict paths invalid: {conflict_id}")

    gate_rows = status.get("gate_status")
    if type(gate_rows) is not list or any(type(row) is not dict for row in gate_rows):
        findings.append("gate status must be a list of objects")
    else:
        gate_ids = tuple(row.get("id") for row in gate_rows)
        if gate_ids != EXPECTED_GATE_IDS:
            findings.append("VM gate IDs must be complete and ordered")
        if any(row.get("status") not in {"GAP", "PARTIAL"} for row in gate_rows):
            findings.append("a VM gate exceeds the currently supported claim ceiling")
        if any(type(row.get("evidence")) is not str or not row["evidence"] for row in gate_rows):
            findings.append("every VM gate requires nonempty evidence")
        if any(frozenset(row) != frozenset({"id", "status", "evidence"}) for row in gate_rows):
            findings.append("VM gate field set mismatch")
        gate_evidence_bytes = json.dumps(
            tuple(
                (row.get("id"), row.get("status"), row.get("evidence"))
                for row in gate_rows
            ),
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
        if hashlib.sha256(gate_evidence_bytes).hexdigest() != EXPECTED_GATE_EVIDENCE_ROOT:
            findings.append("VM gate evidence root drift")
        vm12_rows = [row for row in gate_rows if row.get("id") == "VM-12"]
        if len(vm12_rows) != 1 or vm12_rows[0].get("evidence") != EXPECTED_VM12_EVIDENCE:
            findings.append("VM-12 exact evidence receipt drift")

    tau = _mapping(status.get("tau_upstream"), "Tau upstream", findings)
    if tau.get("common_ancestor") is not False or tau.get("requalification_required") is not True:
        findings.append("Tau rewritten-history requalification status drift")
    if tau.get("full_side_by_side_build_run") is not False:
        findings.append("Tau full-build status exceeds recorded evidence")

    observations = _mapping(
        status.get("live_gate_observations"),
        "live gate observations",
        findings,
    )
    production_boundary = _mapping(
        observations.get("production_boundary"),
        "production boundary observation",
        findings,
    )
    if production_boundary.get("ok") is not False:
        findings.append("production boundary observation must remain failed")
    value_sink_observation = _mapping(
        observations.get("value_sink_inventory"),
        "value sink inventory observation",
        findings,
    )
    if dependencies_valid:
        check_precision, check_value_sinks = _load_live_gate_checkers_v1()
        live_value_sinks = check_value_sinks(root)
    else:
        live_value_sinks = {
            "ok": False,
            "classified_identity_count": -1,
            "observed_occurrence_count": -1,
            "release_gaps": [],
            "release_ready": False,
            "production_authority": False,
        }
        findings.append("live gate helpers skipped because dependency binding failed")
    release_gaps = live_value_sinks["release_gaps"]
    if type(release_gaps) is not list:
        findings.append("live value sink release gaps are not a list")
        release_gaps = []
    expected_value_sink_observation = {
        "exit_code": 0 if live_value_sinks["ok"] is True else 1,
        "classified_identity_count": live_value_sinks["classified_identity_count"],
        "observed_occurrence_count": live_value_sinks["observed_occurrence_count"],
        "release_gap_count": len(release_gaps),
        "release_ready": live_value_sinks["release_ready"],
        "production_authority": live_value_sinks["production_authority"],
    }
    if dict(value_sink_observation) != expected_value_sink_observation:
        findings.append("value sink inventory observation is stale or incomplete")
    if live_value_sinks["ok"] is not True:
        findings.append("live value sink inventory has findings")
    precision_observation = _mapping(
        observations.get("asset_precision_policy"),
        "asset precision policy observation",
        findings,
    )
    if dependencies_valid:
        live_precision = check_precision(
            root
            / "docs"
            / "research"
            / "ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json"
        )
    else:
        live_precision = {
            "ok": False,
            "decimal_places": -1,
            "atoms_per_display_unit": -1,
            "policy_root": "",
            "production_authority": False,
        }
    expected_precision_observation = {
        "exit_code": 0 if live_precision["ok"] is True else 1,
        "decimal_places": live_precision["decimal_places"],
        "atoms_per_display_unit": live_precision["atoms_per_display_unit"],
        "policy_root": live_precision["policy_root"],
        "production_authority": live_precision["production_authority"],
    }
    if dict(precision_observation) != expected_precision_observation:
        findings.append("asset precision policy observation is stale or incomplete")
    if live_precision["ok"] is not True:
        findings.append("live asset precision policy has findings")

    return {
        "schema": "zenodex/value-movement-closure-status-check/v1",
        "ok": not findings,
        "subject_commit": commit,
        "gate_count": len(gate_rows) if type(gate_rows) is list else 0,
        "production_authority": authority.get("production_authority"),
        "findings": findings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--status", type=Path)
    args = parser.parse_args(argv)
    report = check_value_movement_closure_status_v1(args.root, args.status)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
