from __future__ import annotations

import json
import subprocess
from copy import deepcopy
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import o008a_dependency_policy_blocker_v1 as blocker

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
    touches = _git("rev-list", "HEAD", "--", blocker.ARTIFACT_PATH).splitlines()
    if not touches:
        return _git("rev-parse", "HEAD")
    parents = _git("show", "-s", "--format=%P", touches[0]).split()
    assert len(parents) == 1
    return parents[0]


@lru_cache(maxsize=1)
def _artifact() -> dict[str, Any]:
    return blocker.build_artifact(ROOT, _stage_a())


def _mutated_bytes(mutator: Callable[[dict[str, Any]], None]) -> tuple[bytes, bytes]:
    artifact = _artifact()
    expected = blocker.canonical_json_bytes(artifact)
    mutated = deepcopy(artifact)
    mutator(mutated)
    return blocker.canonical_json_bytes(mutated), expected


def _reject_code(raw: bytes, expected: bytes) -> str:
    with pytest.raises(blocker.BlockerReject) as captured:
        blocker.validate_artifact_bytes(raw, expected)
    return captured.value.code


def test_bdd_given_exact_stage_a_when_projected_then_o008a_remains_blocked() -> None:
    artifact = _artifact()

    assert artifact["schema"] == blocker.SCHEMA
    assert artifact["status"] == "BLOCKED_DEPENDENCY_POLICY_CONFLICT"
    assert artifact["plan_binding"]["exact_o008a_row"] == blocker.EXACT_PLAN_ROW
    assert artifact["claim_ceiling"] == {
        "authority": blocker.NO_AUTHORITY,
        "build_host_qualification_gap_closed": False,
        "build_host_qualified": False,
        "clean_build_receipt": "NOT_ACCEPTED",
        "dependency_safe": False,
        "proof_validity": "NOT_CLAIMED",
        "qualification_complete": False,
        "release_ready": False,
        "risc0_3_0_6_image_rebuild_receipt": "HISTORICAL_STALE_NOT_ACCEPTED",
    }


def test_lock_and_local_evidence_bind_both_incompatible_advisories() -> None:
    policy = _artifact()["dependency_policy"]

    assert policy["governed_lock_sha256"] == blocker.sha256_hex(
        (ROOT / blocker.LOCK_PATH).read_bytes()
    )
    assert policy["risc0_requirement"] == "=3.0.6"
    assert policy["dependency_chains"] == [list(chain) for chain in blocker.DEPENDENCY_CHAINS]
    assert [(row["advisory_id"], row["patched_versions"]) for row in policy["advisories"]] == [
        ("RUSTSEC-2023-0071", []),
        ("RUSTSEC-2025-0055", [">=0.3.20"]),
    ]
    assert policy["lock_only_resolution"] == "IMPOSSIBLE_FOR_BOTH_FINDINGS"
    assert policy["silent_vulnerability_exceptions_allowed"] is False


def test_stale_candidate_is_rejected_against_exact_current_closure() -> None:
    stale = _artifact()["stale_candidate_adjudication"]

    assert stale["adjudication"] == "STALE_REJECTED"
    assert stale["candidate_commit"] == blocker.STALE_CANDIDATE
    assert stale["candidate_write_set_count"] == 17
    assert stale["stage_e_artifact_at_candidate"] == "ABSENT"
    assert stale["current_source_closure_changed_path_count"] == 11
    assert stale["current_source_closure_changed_paths"] == [
        "zk/economic_initial_state_risc0/host/tests/real_proof.rs",
        "zk/economic_initial_state_risc0/host/tests/receipt_admission.rs",
        "zk/global_settlement_abi_v1/src/lib.rs",
        "zk/global_settlement_abi_v1/src/release.rs",
        "zk/global_settlement_abi_v1/src/zdex_buyback_shadow_composer_v2.rs",
        "zk/global_settlement_abi_v1/src/zdex_spot_buyback_transition_v2.rs",
        "zk/global_settlement_abi_v1/src/zdex_spot_buyback_transition_v2_rejection_fixture.rs",
        "zk/global_settlement_abi_v1/src/zdex_tokenomics_buyback_transition_v2.rs",
        "zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs",
        "zk/global_settlement_abi_v1/tests/zdex_buyback_v2_composition.rs",
        "zk/global_settlement_abi_v1/tests/zdex_spot_buyback_transition_v2.rs",
    ]


def test_resource_feasibility_uses_calibrated_exact_byte_arithmetic() -> None:
    resources = _artifact()["resource_feasibility"]

    assert resources["assessment"] == "FEASIBLE_ONLY_WITH_CALIBRATED_ISOLATED_BUDGET"
    assert resources["build_authorized"] is False
    assert resources["cache_reuse"] == {
        "calculated_incremental_bytes": 2717135970,
        "calculated_remaining_tmpfs_bytes": 12998867870,
        "governed_minimum_free_tmpfs_bytes": 4294967296,
        "observed_threshold_met": True,
    }
    assert resources["full_isolation"] == {
        "calculated_incremental_bytes": 6350979208,
        "calculated_remaining_tmpfs_bytes": 9365024632,
        "governed_minimum_free_tmpfs_bytes": 7516192768,
        "observed_threshold_met": True,
    }
    assert resources["memory"]["governed_minimum_available_bytes"] == 17179869184
    assert resources["memory"]["observed_headroom_over_historical_upper_bound_bytes"] == 14888140800
    assert resources["required_controls"]["required_tmpdir"] == "/dev/shm"
    assert resources["required_controls"]["root_filesystem_build_target_allowed"] is False


def test_source_manifest_covers_the_complete_governed_rust_closure() -> None:
    binding = _artifact()["source_binding"]
    closure = binding["governed_build_closure"]

    assert closure["selection"] == (
        "ALL_REGULAR_TRACKED_FILES_UNDER_GOVERNED_WORKSPACE_AND_PATH_DEPENDENCY"
    )
    assert [row["root"] for row in closure["roots"]] == list(blocker.SOURCE_ROOTS)
    assert sum(row["file_count"] for row in closure["roots"]) == 153
    assert {row["path"] for row in binding["source_manifest"]} == set(
        blocker.STATIC_INPUT_PATHS
    )


def test_mutation_advisory_removal_is_rejected() -> None:
    raw, expected = _mutated_bytes(
        lambda artifact: artifact["dependency_policy"]["advisories"].pop()
    )

    assert _reject_code(raw, expected) == "ADVISORY_REMOVAL"


def test_mutation_authority_promotion_is_rejected() -> None:
    def promote(artifact: dict[str, Any]) -> None:
        artifact["claim_ceiling"]["authority"]["release_authority"] = "GRANTED"

    raw, expected = _mutated_bytes(promote)
    assert _reject_code(raw, expected) == "AUTHORITY_PROMOTION"


def test_mutation_stale_candidate_acceptance_is_rejected() -> None:
    def accept_stale(artifact: dict[str, Any]) -> None:
        artifact["stale_candidate_adjudication"]["adjudication"] = "ACCEPTED"

    raw, expected = _mutated_bytes(accept_stale)
    assert _reject_code(raw, expected) == "STALE_CANDIDATE_ACCEPTANCE"


def test_mutation_resource_budget_understatement_is_rejected() -> None:
    def understate(artifact: dict[str, Any]) -> None:
        artifact["resource_feasibility"]["cache_reuse"][
            "governed_minimum_free_tmpfs_bytes"
        ] = 50 * 1024**2
        artifact["resource_feasibility"]["memory"][
            "governed_minimum_available_bytes"
        ] = 128 * 1024**2

    raw, expected = _mutated_bytes(understate)
    assert _reject_code(raw, expected) == "RESOURCE_BUDGET_UNDERSTATEMENT"


def test_duplicate_json_key_is_a_typed_reject() -> None:
    with pytest.raises(blocker.BlockerReject) as captured:
        blocker.decode_json(b'{"status":"a","status":"b"}', "fixture")

    assert captured.value.code == "JSON_DUPLICATE_KEY"


def test_stage_lifecycle_requires_artifact_only_stage_b() -> None:
    report = blocker.check_blocker(ROOT)
    artifact_exists = (ROOT / blocker.ARTIFACT_PATH).exists()

    if artifact_exists:
        assert report["ok"] is True
        assert report["status"] == blocker.STATUS
        assert report["authority"] == blocker.NO_AUTHORITY
        assert report["qualification_complete"] is False
        assert report["release_ready"] is False
    else:
        assert report["ok"] is False
        assert report["finding"]["code"] == "ARTIFACT_HISTORY"


def test_canonical_projection_roundtrip_and_payload_hash() -> None:
    artifact = _artifact()
    raw = blocker.canonical_json_bytes(artifact)

    decoded = blocker.validate_artifact_bytes(raw, raw)
    payload = dict(decoded)
    recorded = payload.pop("artifact_payload_sha256")
    assert recorded == blocker.sha256_hex(blocker.canonical_json_bytes(payload))
    assert json.loads(raw)["certificate_root"] == artifact["certificate_root"]
