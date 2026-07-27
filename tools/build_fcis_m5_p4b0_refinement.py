#!/usr/bin/env python3
"""Build canonical, unmounted M5-P4B0 legacy-refinement evidence."""

# ruff: noqa: E402 -- executable tools must add the repository root before src imports

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.core.fcis_legacy_refinement import evaluate_refinement_v1
from src.core.fcis_legacy_refinement_admission import (
    BASELINE_ARTIFACT_HASH_V1,
    DIFFERENTIAL_ARTIFACT_HASH_V1,
    PACKET_COMMIT_V1,
    PACKET_TREE_HASH_V1,
    REQUIRED_ANCESTOR_V1,
    admit_observation_pair_bytes_v1,
    decode_canonical_evidence_artifact_bytes_v1,
)
from src.core.fcis_legacy_refinement_policy import POLICY_HASH_V1, POLICY_VERSION_V1
from src.core.fcis_legacy_refinement_values import (
    InvalidEvidenceV1,
    MismatchV1,
    ObservationPairV1,
    RefinementDecisionV1,
    RefinesV1,
)
from src.state.canonical import canonical_json_bytes, sha256_hex

ARTIFACT_SCHEMA_V1 = "zenodex/fcis-m5-p4b0-refinement/v1"
ARTIFACT_PATH_V1 = Path("docs/research/FCIS_M5_P4B0_REFINEMENT_V1.json")
P4A_DIFFERENTIAL_PATH_V1 = Path("docs/research/FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json")
SOURCE_PATHS_V1 = (
    Path("src/core/fcis_legacy_refinement.py"),
    Path("src/core/fcis_legacy_refinement_admission.py"),
    Path("src/core/fcis_legacy_refinement_policy.py"),
    Path("src/core/fcis_legacy_refinement_schema.py"),
    Path("src/core/fcis_legacy_refinement_values.py"),
    Path("tools/build_fcis_m5_p4b0_refinement.py"),
    Path("tools/check_fcis_m5_p4b0_refinement.py"),
)
MUTATION_LEDGER_V1 = (
    ("M01", "result_kind", "P4B0-RESULT-001"),
    ("M02", "rejection_code", "P4B0-REJECT-002"),
    ("M03", "rejection_path", "P4B0-REJECT-002"),
    ("M04", "rejection_reason", "P4B0-REJECT-002"),
    ("M05", "state_balances", "P4B0-STATE-002"),
    ("M06", "state_pools", "P4B0-STATE-002"),
    ("M07", "state_lp", "P4B0-STATE-002"),
    ("M08", "state_nonces", "P4B0-STATE-002"),
    ("M09", "state_optional_modules", "P4B0-STATE-002"),
    ("M10", "economic_fees", "P4B0-ECON-001"),
    ("M11", "economic_settlement_order", "P4B0-ECON-001"),
    ("M12", "patch_expected_old", "P4B0-PATCH-002"),
    ("M13", "patch_missing_op", "P4B0-PATCH-002"),
    ("M14", "patch_duplicate_op", "P4B0-PATCH-002"),
    ("M15", "bundle_cross_candidate", "P4B0-BUNDLE-002"),
    ("M16", "receipt_cached_root", "P4B0-BUNDLE-002"),
    ("M17", "outbox_reorder", "P4B0-OUTBOX-001"),
    ("M18", "outbox_payload", "P4B0-OUTBOX-001"),
    ("M19", "replay_nonce", "P4B0-REPLAY-001"),
    ("M20", "replay_nullifier", "P4B0-REPLAY-001"),
    ("M21", "version_unknown", "P4B0-VERSION-002"),
    ("M22", "policy_wildcard", "P4B0-POLICY-002"),
    ("M23", "input_substitution", "P4B0-INPUT-002"),
    ("M24", "artifact_result_fabrication", "P4B0-MUTANTS-001"),
)


def _mapping(value: object, name: str) -> dict[str, object]:
    if type(value) is not dict:
        raise ValueError(f"{name} must be an exact object")
    return cast(dict[str, object], value)


def _sequence(value: object, name: str) -> list[object]:
    if type(value) is not list:
        raise ValueError(f"{name} must be an exact list")
    return cast(list[object], value)


def _load_p4a(repo_root: Path) -> dict[str, object]:
    raw = (repo_root / P4A_DIFFERENTIAL_PATH_V1).read_bytes()
    value = decode_canonical_evidence_artifact_bytes_v1(raw)
    artifact = _mapping(value, "P4A artifact")
    stored_hash = artifact.get("artifact_sha256")
    payload = {key: item for key, item in artifact.items() if key != "artifact_sha256"}
    recomputed_hash = sha256_hex(canonical_json_bytes(payload))
    if stored_hash != recomputed_hash:
        raise ValueError("P4A differential artifact self-hash mismatch")
    if stored_hash != DIFFERENTIAL_ARTIFACT_HASH_V1:
        raise ValueError("P4A differential artifact hash drift")
    if artifact.get("baseline_artifact_sha256") != BASELINE_ARTIFACT_HASH_V1:
        raise ValueError("P4A baseline artifact hash drift")
    return artifact


def _binding_source(
    fixture: dict[str, object],
    side: str,
) -> dict[str, object]:
    input_binding = _mapping(fixture["input_binding"], "input binding")
    raw = _mapping(input_binding[side], f"{side} input binding")
    return {
        "baseline_artifact_hash": BASELINE_ARTIFACT_HASH_V1,
        "command_bytes": raw["command_bytes"],
        "command_hash": raw["command_hash"],
        "command_kind": fixture["command_kind"],
        "context_bytes": raw["context_bytes"],
        "context_hash": raw["context_hash"],
        "differential_artifact_hash": DIFFERENTIAL_ARTIFACT_HASH_V1,
        "fixture_id": fixture["fixture_id"],
        "packet_commit": PACKET_COMMIT_V1,
        "packet_tree_hash": PACKET_TREE_HASH_V1,
        "pre_state_bytes": raw["state_snapshot_bytes"],
        "pre_state_root": raw["state_snapshot_root"],
        "reviewed_start_sha": REQUIRED_ANCESTOR_V1,
    }


def _pair_for_fixture(
    fixture: dict[str, object],
) -> ObservationPairV1:
    comparison = _mapping(fixture["comparison"], "fixture comparison")
    source = {
        "exact": {
            "binding": _binding_source(fixture, "exact"),
            "observation": comparison["exact"],
        },
        "legacy": {
            "binding": _binding_source(fixture, "legacy"),
            "observation": comparison["legacy"],
        },
    }
    admitted = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    if type(admitted) is not ObservationPairV1:
        raise ValueError(
            f"fixture {fixture['fixture_id']} admission failed: {getattr(admitted, 'code', 'unknown')}"
        )
    return admitted


def _witness_source(decision: RefinesV1) -> dict[str, object]:
    witness = decision.witness
    return {
        "baseline_artifact_hash": witness.baseline_artifact_hash,
        "command_hash": witness.command_hash,
        "context_hash": witness.context_hash,
        "differential_artifact_hash": witness.differential_artifact_hash,
        "fixture_id": witness.fixture_id,
        "packet_commit": witness.packet_commit,
        "packet_tree_hash": witness.packet_tree_hash,
        "policy_hash": witness.policy_hash,
        "policy_version": witness.policy_version,
        "pre_state_root": witness.pre_state_root,
        "reviewed_source_sha": witness.reviewed_source_sha,
        "version_deltas": [
            {
                "exact_value": delta.exact_value,
                "field_name": delta.field_name,
                "legacy_value": delta.legacy_value,
                "result_kind": delta.result_kind.value,
                "stable_id": delta.stable_id,
            }
            for delta in witness.version_deltas
        ],
    }


def decision_source_v1(decision: RefinementDecisionV1) -> dict[str, object]:
    if type(decision) is RefinesV1:
        return {"kind": "refines", "witness": _witness_source(decision)}
    if type(decision) is MismatchV1:
        return {
            "code": decision.code,
            "exact_value": decision.exact_value.hex(),
            "kind": "mismatch",
            "legacy_value": decision.legacy_value.hex(),
            "path": list(decision.path),
        }
    if type(decision) is InvalidEvidenceV1:
        return {"code": decision.code, "kind": "invalid_evidence", "path": list(decision.path)}
    raise TypeError("unknown refinement decision")


def _source_hashes(repo_root: Path) -> dict[str, object]:
    return {str(path): sha256_hex((repo_root / path).read_bytes()) for path in SOURCE_PATHS_V1}


def _artifact_payload(repo_root: Path) -> dict[str, object]:
    p4a = _load_p4a(repo_root)
    fixtures = _sequence(p4a["fixtures"], "P4A fixtures")
    rows: list[dict[str, object]] = []
    counts = {"invalid_evidence": 0, "mismatch": 0, "refines": 0}
    for raw_fixture in fixtures:
        fixture = _mapping(raw_fixture, "P4A fixture")
        pair = _pair_for_fixture(fixture)
        decision = evaluate_refinement_v1(pair)
        decision_source = decision_source_v1(decision)
        kind = cast(str, decision_source["kind"])
        counts[kind] += 1
        rows.append(
            {
                "command_kind": fixture["command_kind"],
                "decision": decision_source,
                "fixture_id": fixture["fixture_id"],
                "input_source_hash": pair.canonical_source_hash,
            }
        )
    verdict = "ALL_REFINE_REVIEW_REQUIRED" if counts["mismatch"] == 0 else "BLOCKED"
    if counts["invalid_evidence"]:
        verdict = "INVALID"
    return {
        "baseline_artifact_hash": BASELINE_ARTIFACT_HASH_V1,
        "differential_artifact_hash": DIFFERENTIAL_ARTIFACT_HASH_V1,
        "fixture_count": len(rows),
        "mount_authorized": False,
        "mutation_ledger": [
            {"mutant_id": mutant_id, "name": name, "test_id": test_id}
            for mutant_id, name, test_id in MUTATION_LEDGER_V1
        ],
        "outcome": "M5_P4B0_REFINEMENT_EVIDENCE_ONLY",
        "packet_commit": PACKET_COMMIT_V1,
        "packet_tree_hash": PACKET_TREE_HASH_V1,
        "policy_hash": POLICY_HASH_V1,
        "policy_version": POLICY_VERSION_V1,
        "required_ancestor": REQUIRED_ANCESTOR_V1,
        "result_counts": counts,
        "rows": rows,
        "schema": ARTIFACT_SCHEMA_V1,
        "source_hashes": _source_hashes(repo_root),
        "verdict": verdict,
    }


def build_artifact_v1(repo_root: Path) -> dict[str, object]:
    payload = _artifact_payload(repo_root)
    return {**payload, "artifact_sha256": sha256_hex(canonical_json_bytes(payload))}


def artifact_bytes_v1(repo_root: Path) -> bytes:
    return canonical_json_bytes(build_artifact_v1(repo_root))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    expected = artifact_bytes_v1(repo_root)
    artifact_path = repo_root / ARTIFACT_PATH_V1
    if args.check:
        if not artifact_path.exists() or artifact_path.read_bytes() != expected:
            print("P4B0 refinement artifact is stale")
            return 1
        print("P4B0 refinement artifact is current")
        return 0
    artifact_path.write_bytes(expected)
    artifact = build_artifact_v1(repo_root)
    print(
        "P4B0 refinement artifact written: "
        f"{artifact['result_counts']} verdict={artifact['verdict']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
