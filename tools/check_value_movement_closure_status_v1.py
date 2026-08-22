#!/usr/bin/env python3
"""Fail-closed checker for the value-movement semantic closure ledger."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Mapping

if __package__:
    from tools.check_m6_asset_precision_policy_v1 import (
        check_m6_asset_precision_policy_v1,
    )
    from tools.check_m6_value_sinks_v1 import check_m6_value_sinks_v1
else:
    from check_m6_asset_precision_policy_v1 import check_m6_asset_precision_policy_v1
    from check_m6_value_sinks_v1 import check_m6_value_sinks_v1

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STATUS_PATH = Path(
    "docs/research/ZENODEX_VALUE_MOVEMENT_CLOSURE_STATUS_V1.json"
)
M6_ATDD_PATH = Path("docs/research/m6_global_economic_core_atdd_bdd_v1.json")
EXPECTED_GATE_IDS = tuple(f"VM-{index:02d}" for index in range(1, 13))
EXPECTED_SEMANTIC_KEYS = frozenset(
    {
        "asset_precision",
        "autonomous_governance",
        "buy_and_burn",
        "buy_and_burn_exclusions",
        "external_registry_default",
        "hosting_compensation",
        "hyperdeflation",
        "rescaling",
        "self_custody_language",
    }
)
EXPECTED_BUY_AND_BURN = (
    "Atomically spend the governed quote-asset fee allocation through the "
    "selected authenticated Spot route and burn the exact ZDEX atoms received."
)
EXPECTED_CLAIM_STATUS = "DRAFT_REVISED_SOURCE_HEAD_REVIEWED"
EXPECTED_HYPERDEFLATION = (
    "No arbitrary fixed percentage of initial supply is required as a floor. "
    "Bind a retained-supply rule such as R(S)=ceil(p*S/q), 0<p<q, and "
    "burn<=S-R(S)."
)
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
    for field, relative_path in REPLAY_SLICE_ARTIFACTS.items():
        artifact = root / relative_path
        recorded = replay.get(field)
        if (
            type(recorded) is not str
            or not artifact.is_file()
            or _sha256(artifact) != recorded
        ):
            findings.append(f"replay slice artifact hash mismatch: {field}")

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
    for field, relative_path in SOURCE_HEAD_SLICE_ARTIFACTS.items():
        artifact = root / relative_path
        recorded = source_head.get(field)
        if (
            type(recorded) is not str
            or not artifact.is_file()
            or _sha256(artifact) != recorded
        ):
            findings.append(f"source-head slice artifact hash mismatch: {field}")


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

    subject = _mapping(status.get("subject"), "subject", findings)
    commit = subject.get("commit")
    if type(commit) is not str or re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        findings.append("subject commit must be exact lowercase 40-hex")
    if subject.get("scoped_worktree_clean_before_this_ledger") is not True:
        findings.append("ledger subject was not recorded from a clean scoped worktree")

    _validate_replay_slice_evidence_v1(root, status, commit, findings)
    _validate_source_head_slice_evidence_v1(root, status, commit, findings)

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
    claim_path = claim.get("path")
    claim_sha = claim.get("sha256")
    if type(claim_path) is not str or type(claim_sha) is not str:
        findings.append("claim contract path and sha256 must be strings")
    else:
        resolved_claim = root / claim_path
        if not resolved_claim.is_file() or _sha256(resolved_claim) != claim_sha:
            findings.append("claim contract hash mismatch")
    if claim.get("status") != EXPECTED_CLAIM_STATUS:
        findings.append("claim status drift")
    if claim.get("verdict") != "UNPROVED":
        findings.append("claim verdict must remain UNPROVED")

    semantics = _mapping(status.get("semantic_anchors"), "semantic anchors", findings)
    if frozenset(semantics) != EXPECTED_SEMANTIC_KEYS:
        findings.append("semantic anchor key set mismatch")
    if semantics.get("buy_and_burn") != EXPECTED_BUY_AND_BURN:
        findings.append("buy-and-burn semantic anchor drift")
    if semantics.get("hyperdeflation") != EXPECTED_HYPERDEFLATION:
        findings.append("hyperdeflation semantic anchor drift")

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
    live_value_sinks = check_m6_value_sinks_v1(root)
    expected_value_sink_observation = {
        "exit_code": 0 if live_value_sinks["ok"] is True else 1,
        "classified_identity_count": live_value_sinks["classified_identity_count"],
        "observed_occurrence_count": live_value_sinks["observed_occurrence_count"],
        "release_gap_count": len(live_value_sinks["release_gaps"]),
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
    live_precision = check_m6_asset_precision_policy_v1(
        root / "docs" / "research" / "ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json"
    )
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
