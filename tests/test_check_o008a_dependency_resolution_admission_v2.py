from __future__ import annotations

import json
import subprocess
from copy import deepcopy
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import o008a_dependency_resolution_admission_v2 as admission

ROOT = Path(__file__).resolve().parents[1]


def _git(*arguments: str) -> str:
    result = subprocess.run(
        ("git", "-C", str(ROOT), *arguments),
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _stage_a() -> str:
    touches = _git("rev-list", "HEAD", "--", admission.ARTIFACT_PATH).splitlines()
    if not touches:
        return _git("rev-parse", "HEAD")
    parents = _git("show", "-s", "--format=%P", touches[0]).split()
    assert len(parents) == 1
    return parents[0]


@lru_cache(maxsize=1)
def _artifact() -> dict[str, Any]:
    return admission.build_artifact(ROOT, _stage_a())


def _mutated_bytes(mutator: Callable[[dict[str, Any]], None]) -> tuple[bytes, bytes]:
    expected_artifact = _artifact()
    expected = admission.canonical_json_bytes(expected_artifact)
    mutated = deepcopy(expected_artifact)
    mutator(mutated)
    return admission.canonical_json_bytes(mutated), expected


def _reject_code(raw: bytes, expected: bytes) -> str:
    with pytest.raises(admission.AdmissionReject) as captured:
        admission.validate_artifact_bytes(raw, expected)
    return captured.value.code


def test_bdd_selected_path_admits_only_controlled_local_research_execution() -> None:
    artifact = _artifact()

    assert artifact["schema"] == admission.SCHEMA
    assert artifact["status"] == admission.STATUS
    assert artifact["directive_premise"] == admission.DIRECTIVE_PREMISE
    assert artifact["resolution_selection"] == admission.SELECTION
    assert artifact["execution_admission"] == admission.EXECUTION_ADMISSION
    assert artifact["resource_observation"] == admission.RESOURCE_OBSERVATION
    assert artifact["superseded_candidate"] == admission.SUPERSEDED_CANDIDATE
    assert artifact["claim_ceiling"] == admission.CLAIM_CEILING
    assert artifact["claim_ceiling"]["authority"] == admission.NO_AUTHORITY


def test_protected_governance_inputs_are_exact_and_unchanged() -> None:
    manifest = {
        row["path"]: row for row in _artifact()["source_binding"]["source_manifest"]
    }

    for path, expected_sha256 in admission.PROTECTED_SHA256.items():
        assert admission.sha256_hex((ROOT / path).read_bytes()) == expected_sha256
        assert manifest[path]["sha256"] == expected_sha256
    assert _artifact()["governed_subjects"] == admission._expected_subjects()


def test_admission_keeps_dependency_and_qualification_claims_open() -> None:
    artifact = _artifact()
    claims = artifact["claim_ceiling"]
    controls = artifact["execution_admission"]["controls"]

    assert claims["resolution_option_selected"] is True
    assert claims["local_isolated_execution_scope_admitted"] is True
    assert claims["dependency_patch_or_fork_validated"] is False
    assert claims["dependency_policy_conflict_resolved"] is False
    assert claims["build_host_qualified"] is False
    assert claims["o008a_complete"] is False
    assert controls["network_access_authorized"] is False
    assert controls["tmpdir"] == "BENEATH_ISOLATED_ROOT_BACKED_BUILD_ROOT"
    assert controls["concurrency"] == "ONE_BUILD_AT_A_TIME"
    assert controls["build_storage"] == {
        "crucial_volume_use_authorized": False,
        "dev_shm_build_output_allowed": False,
        "removable_or_recovery_evidence_volume_use_authorized": False,
        "repository_worktree_allowed_as_build_output": False,
        "required_class": "ROOT_FILESYSTEM_BACKED_ISOLATED_DIRECTORY",
        "required_mountpoint": "/",
    }
    assert controls["preflight"] == {
        "fail_closed_if_any_threshold_unmet": True,
        "maximum_declared_build_budget_bytes": 8 * 1024**3,
        "measurement_required_immediately_before_each_run": True,
        "minimum_available_memory_bytes": 12 * 1024**3,
        "minimum_projected_root_free_bytes_after_build": 12 * 1024**3,
        "minimum_root_free_bytes": 20 * 1024**3,
        "minimum_root_free_inodes": 1_000_000,
    }


def test_resource_observation_selects_root_backed_storage_but_remains_volatile() -> None:
    observation = _artifact()["resource_observation"]

    assert observation["classification"] == (
        "VOLATILE_SINGLE_HOST_OBSERVATION_REQUIRES_FRESH_PREFLIGHT"
    )
    assert observation["observed_root_free_bytes"] > observation[
        "observed_dev_shm_free_bytes"
    ]
    assert observation["storage_ordering"] == (
        "ROOT_FREE_BYTES_GREATER_THAN_DEV_SHM_FREE_BYTES"
    )
    assert _artifact()["superseded_candidate"]["reason_code"] == (
        "STALE_TMPFS_BUILD_STORAGE_SELECTION"
    )


def test_mutation_external_directive_premise_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["directive_premise"].update(
            {"classification": "MACHINE_VERIFIED"}
        )
    )

    assert _reject_code(raw, expected) == "DIRECTIVE_PREMISE"


def test_mutation_governed_subject_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["governed_subjects"][
            "dependency_policy_blocker"
        ].update({"sha256": "0" * 64})
    )

    assert _reject_code(raw, expected) == "SUBJECT_BINDING"


def test_mutation_selected_option_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["resolution_selection"].update(
            {"selected_resolution_option": "EXPLICIT_RESEARCH_ONLY_WAIVER"}
        )
    )

    assert _reject_code(raw, expected) == "RESOLUTION_OPTION"


def test_mutation_authority_promotion_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["claim_ceiling"]["authority"].update(
            {"release_authority": "GRANTED"}
        )
    )

    assert _reject_code(raw, expected) == "AUTHORITY_PROMOTION"


def test_mutation_network_authorization_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["execution_admission"]["controls"].update(
            {"network_access_authorized": True}
        )
    )

    assert _reject_code(raw, expected) == "EXECUTION_SCOPE"


def test_mutation_tmpfs_build_storage_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["execution_admission"]["controls"][
            "build_storage"
        ].update({"dev_shm_build_output_allowed": True})
    )

    assert _reject_code(raw, expected) == "EXECUTION_SCOPE"


def test_mutation_crucial_volume_use_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["execution_admission"]["controls"][
            "build_storage"
        ].update({"crucial_volume_use_authorized": True})
    )

    assert _reject_code(raw, expected) == "EXECUTION_SCOPE"


def test_mutation_resource_preflight_understatement_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["execution_admission"]["controls"][
            "preflight"
        ].update({"minimum_root_free_bytes": 1})
    )

    assert _reject_code(raw, expected) == "EXECUTION_SCOPE"


def test_duplicate_json_key_is_a_typed_reject() -> None:
    with pytest.raises(admission.AdmissionReject) as captured:
        admission.decode_json(b'{"status":"a","status":"b"}', "fixture")

    assert captured.value.code == "JSON_DUPLICATE_KEY"


def test_stage_lifecycle_requires_artifact_only_stage_b() -> None:
    report = admission.check_admission(ROOT)
    artifact_exists = (ROOT / admission.ARTIFACT_PATH).exists()

    if artifact_exists:
        assert report["ok"] is True
        assert report["historical_valid"] is True
        assert report["current_applicable"] is True
        assert report["authority"] == admission.NO_AUTHORITY
        assert report["build_storage_class"] == (
            "ROOT_FILESYSTEM_BACKED_ISOLATED_DIRECTORY"
        )
        assert report["dev_shm_build_output_allowed"] is False
        assert report["crucial_volume_use_authorized"] is False
        assert report["o008a_complete"] is False
    else:
        assert report["ok"] is False
        assert report["finding"]["code"] == "ARTIFACT_HISTORY"


def test_canonical_projection_roundtrip_and_self_hashes() -> None:
    artifact = _artifact()
    raw = admission.canonical_json_bytes(artifact)

    decoded = admission.validate_artifact_bytes(raw, raw)
    payload = dict(decoded)
    recorded = payload.pop("artifact_payload_sha256")
    assert recorded == admission.sha256_hex(admission.canonical_json_bytes(payload))
    assert json.loads(raw)["certificate_root"] == artifact["certificate_root"]
