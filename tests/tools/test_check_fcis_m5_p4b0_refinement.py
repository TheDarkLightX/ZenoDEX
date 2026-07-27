"""P4B0-C evidence, semantic-mutation, and no-mount tests."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import cast

import pytest

from src.core.fcis_legacy_refinement_admission import REQUIRED_ANCESTOR_V1
from src.state.canonical import canonical_json_bytes, sha256_hex
from tools.build_fcis_m5_p4b0_refinement import (
    ARTIFACT_PATH_V1,
    MUTATION_LEDGER_V1,
    NO_MOUNT_SOURCE_HASHES_V1,
    artifact_bytes_v1,
    build_artifact_v1,
    verify_no_mount_sources_v1,
)
from tools.check_fcis_m5_p4b0_refinement import check_artifact_v1

REPO_ROOT = Path(__file__).resolve().parents[2]
ARTIFACT_PATH = REPO_ROOT / ARTIFACT_PATH_V1
_ZERO_DIGEST = "0x" + "00" * 32
_ONE_DIGEST = "0x" + "01" * 32


def _mapping(value: object) -> dict[str, object]:
    assert type(value) is dict
    return cast(dict[str, object], value)


def _sequence(value: object) -> list[object]:
    assert type(value) is list
    return cast(list[object], value)


def _clone_artifact() -> dict[str, object]:
    decoded = json.loads(ARTIFACT_PATH.read_bytes())
    return _mapping(decoded)


def _rehash(artifact: dict[str, object]) -> bytes:
    payload = {key: value for key, value in artifact.items() if key != "artifact_sha256"}
    artifact["artifact_sha256"] = sha256_hex(canonical_json_bytes(payload))
    return canonical_json_bytes(artifact)


def _rows(artifact: dict[str, object]) -> list[dict[str, object]]:
    return [_mapping(row) for row in _sequence(artifact["rows"])]


def _decision(row: dict[str, object]) -> dict[str, object]:
    return _mapping(row["decision"])


def _first_row(artifact: dict[str, object], kind: str) -> dict[str, object]:
    return next(row for row in _rows(artifact) if _decision(row)["kind"] == kind)


def _mutate_semantic_artifact(artifact: dict[str, object], mutant: str) -> None:
    rows = _rows(artifact)
    refine = _first_row(artifact, "refines")
    mismatch = _first_row(artifact, "mismatch")
    witness = _mapping(_decision(refine)["witness"])
    mismatch_decision = _decision(mismatch)
    counts = _mapping(artifact["result_counts"])
    source_hashes = _mapping(artifact["source_hashes"])
    ledger = _sequence(artifact["mutation_ledger"])

    if mutant == "mount_authorized":
        artifact["mount_authorized"] = True
    elif mutant == "outcome":
        artifact["outcome"] = "M5_P4B0_MOUNTED"
    elif mutant == "schema":
        artifact["schema"] = "zenodex/fcis-m5-p4b0-refinement/v2"
    elif mutant == "verdict":
        artifact["verdict"] = "ALL_REFINE_REVIEW_REQUIRED"
    elif mutant == "baseline_hash":
        artifact["baseline_artifact_hash"] = _ZERO_DIGEST
    elif mutant == "differential_hash":
        artifact["differential_artifact_hash"] = _ZERO_DIGEST
    elif mutant == "packet_commit":
        artifact["packet_commit"] = "0" * 40
    elif mutant == "packet_tree_hash":
        artifact["packet_tree_hash"] = _ZERO_DIGEST
    elif mutant == "required_ancestor":
        artifact["required_ancestor"] = "0" * 40
    elif mutant == "policy_hash":
        artifact["policy_hash"] = _ZERO_DIGEST
    elif mutant == "policy_version":
        artifact["policy_version"] = "attacker-policy"
    elif mutant == "fixture_count":
        artifact["fixture_count"] = 23
    elif mutant == "refine_count":
        counts["refines"] = 24
    elif mutant == "mismatch_count":
        counts["mismatch"] = 0
    elif mutant == "row_fixture_id":
        refine["fixture_id"] = "substituted-fixture"
    elif mutant == "row_command_kind":
        refine["command_kind"] = "UNKNOWN"
    elif mutant == "row_input_source_hash":
        refine["input_source_hash"] = _ZERO_DIGEST
    elif mutant == "witness_fixture_id":
        witness["fixture_id"] = "substituted-fixture"
    elif mutant == "witness_command_hash":
        witness["command_hash"] = _ZERO_DIGEST
    elif mutant == "witness_pre_state_root":
        witness["pre_state_root"] = _ZERO_DIGEST
    elif mutant == "witness_context_hash":
        witness["context_hash"] = _ZERO_DIGEST
    elif mutant == "witness_policy_hash":
        witness["policy_hash"] = _ZERO_DIGEST
    elif mutant == "witness_version_delta":
        delta = _mapping(_sequence(witness["version_deltas"])[0])
        delta["exact_value"] = "999"
    elif mutant == "mismatch_kind":
        mismatch_decision["kind"] = "refines"
    elif mutant == "mismatch_code":
        mismatch_decision["code"] = "fabricated_refinement"
    elif mutant == "mismatch_path":
        mismatch_decision["path"] = ["next_state", "balances"]
    elif mutant == "mismatch_legacy_value":
        mismatch_decision["legacy_value"] = "00"
    elif mutant == "mismatch_exact_value":
        mismatch_decision["exact_value"] = "00"
    elif mutant == "delete_row":
        rows.pop()
        artifact["rows"] = rows
    elif mutant == "duplicate_row":
        rows.append(rows[0])
        artifact["rows"] = rows
    elif mutant == "reorder_rows":
        rows[0], rows[1] = rows[1], rows[0]
        artifact["rows"] = rows
    elif mutant == "source_hash":
        first_path = sorted(source_hashes)[0]
        source_hashes[first_path] = _ONE_DIGEST
    elif mutant == "no_mount_source_hash":
        mounted_hashes = _mapping(artifact["no_mount_source_hashes"])
        first_path = sorted(mounted_hashes)[0]
        mounted_hashes[first_path] = _ONE_DIGEST
    elif mutant == "mutation_ledger":
        ledger.pop()
    else:
        raise AssertionError(f"unknown test mutant {mutant}")


SEMANTIC_MUTANTS = (
    "mount_authorized",
    "outcome",
    "schema",
    "verdict",
    "baseline_hash",
    "differential_hash",
    "packet_commit",
    "packet_tree_hash",
    "required_ancestor",
    "policy_hash",
    "policy_version",
    "fixture_count",
    "refine_count",
    "mismatch_count",
    "row_fixture_id",
    "row_command_kind",
    "row_input_source_hash",
    "witness_fixture_id",
    "witness_command_hash",
    "witness_pre_state_root",
    "witness_context_hash",
    "witness_policy_hash",
    "witness_version_delta",
    "mismatch_kind",
    "mismatch_code",
    "mismatch_path",
    "mismatch_legacy_value",
    "mismatch_exact_value",
    "delete_row",
    "duplicate_row",
    "reorder_rows",
    "source_hash",
    "no_mount_source_hash",
    "mutation_ledger",
)


def test_p4b0_determinism_001_two_clean_generations_are_byte_identical() -> None:
    """P4B0-DETERMINISM-001."""

    first = artifact_bytes_v1(REPO_ROOT)
    second = artifact_bytes_v1(REPO_ROOT)
    assert first == second == ARTIFACT_PATH.read_bytes()
    assert build_artifact_v1(REPO_ROOT)["policy_hash"] == _clone_artifact()["policy_hash"]


@pytest.mark.parametrize("mutant", SEMANTIC_MUTANTS)
def test_p4b0_mutants_001_rehashed_semantic_mutants_fail_rebuild(
    tmp_path: Path,
    mutant: str,
) -> None:
    """P4B0-MUTANTS-001 and matrix semantic attack families."""

    artifact = _clone_artifact()
    _mutate_semantic_artifact(artifact, mutant)
    raw = _rehash(artifact)
    stored_hash = artifact["artifact_sha256"]
    payload = {key: value for key, value in artifact.items() if key != "artifact_sha256"}
    assert stored_hash == sha256_hex(canonical_json_bytes(payload))
    mutated_path = tmp_path / f"{mutant}.json"
    mutated_path.write_bytes(raw)

    status, report = check_artifact_v1(
        REPO_ROOT,
        mutated_path,
        require_all_refine=False,
    )
    assert status == 1
    assert report["code"] == "semantic_rebuild_mismatch"


def test_p4b0_mutants_001_ledger_is_named_unique_and_large_enough() -> None:
    """P4B0-MUTANTS-001."""

    assert len(MUTATION_LEDGER_V1) == 60
    assert len({mutant_id for mutant_id, _, _ in MUTATION_LEDGER_V1}) == len(MUTATION_LEDGER_V1)
    assert all(test_id.startswith("P4B0-") for _, _, test_id in MUTATION_LEDGER_V1)


def test_p4b0_mutants_001_stale_outer_hash_is_distinguished(tmp_path: Path) -> None:
    artifact = _clone_artifact()
    artifact["verdict"] = "FABRICATED"
    mutated_path = tmp_path / "stale-hash.json"
    mutated_path.write_bytes(canonical_json_bytes(artifact))
    status, report = check_artifact_v1(REPO_ROOT, mutated_path, require_all_refine=False)
    assert status == 1
    assert report["code"] == "artifact_hash_mismatch"


def test_p4b0_gate_001_honest_mismatches_validate_as_blocked() -> None:
    """P4B0-GATE-001."""

    status, report = check_artifact_v1(REPO_ROOT, ARTIFACT_PATH, require_all_refine=False)
    assert status == 0
    assert report == {
        "code": "artifact_valid",
        "mount_authorized": False,
        "ok": True,
        "schema": "zenodex/fcis-m5-p4b0-refinement-check/v1",
        "verdict": "BLOCKED",
    }


def test_p4b0_gate_002_require_all_refine_fails_closed() -> None:
    """P4B0-GATE-002."""

    status, report = check_artifact_v1(REPO_ROOT, ARTIFACT_PATH, require_all_refine=True)
    assert status == 2
    assert report["code"] == "mismatches_block_promotion"
    assert report["mount_authorized"] is False


def test_p4b0_nomount_001_diff_is_confined_to_refinement_evidence() -> None:
    """P4B0-NOMOUNT-001."""

    completed = subprocess.run(
        ["git", "diff", "--name-only", f"{REQUIRED_ANCESTOR_V1}..HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    changed = set(completed.stdout.splitlines())
    allowed_prefixes = (
        "docs/research/FCIS_M5_P4B0_",
        "src/core/fcis_legacy_refinement",
        "tests/core/test_fcis_legacy_refinement",
        "tests/tools/test_check_fcis_",
        "tools/build_fcis_m5_p4b0_refinement.py",
        "tools/check_fcis_authority_snapshot_contract.py",
        "tools/check_fcis_m5_p4b0_refinement.py",
    )
    assert changed
    assert all(path.startswith(allowed_prefixes) for path in changed)
    assert "src/core/dex.py" not in changed


def test_p4b0_nomount_002_mounted_dispatch_does_not_import_refinement() -> None:
    """P4B0-NOMOUNT-002."""

    mounted = (REPO_ROOT / "src/core/dex.py").read_text(encoding="utf-8")
    assert "fcis_legacy_refinement" not in mounted
    assert "evaluate_refinement_v1" not in mounted


def test_p4b0_nomount_003_artifact_binds_all_frozen_mounted_sources() -> None:
    artifact = _clone_artifact()
    assert artifact["no_mount_source_hashes"] == verify_no_mount_sources_v1(REPO_ROOT)
    assert set(_mapping(artifact["no_mount_source_hashes"])) == {
        path.as_posix() for path, _expected_hash in NO_MOUNT_SOURCE_HASHES_V1
    }


@pytest.mark.parametrize(
    "mutated_path",
    tuple(path for path, _expected_hash in NO_MOUNT_SOURCE_HASHES_V1),
)
def test_p4b0_nomount_004_checker_rejects_post_evidence_source_mutation(
    tmp_path: Path,
    mutated_path: Path,
) -> None:
    """P4B0-NOMOUNT-001 and mandatory independent attack 12."""

    for relative_path, _expected_hash in NO_MOUNT_SOURCE_HASHES_V1:
        destination = tmp_path / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.symlink_to(REPO_ROOT / relative_path)
    target = tmp_path / mutated_path
    target.unlink()
    target.write_bytes((REPO_ROOT / mutated_path).read_bytes() + b"\n# mounted mutant\n")

    status, report = check_artifact_v1(
        tmp_path,
        ARTIFACT_PATH,
        require_all_refine=False,
    )

    assert status == 1
    assert report["code"] == f"no_mount_source_drift:{mutated_path.as_posix()}"
