from __future__ import annotations

import copy
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools import check_zrpf_v3_firecracker_replay_profile as checker


@dataclass(frozen=True)
class BoundaryMutation:
    case_id: str
    path: tuple[str, ...]
    replacement: Any
    expected_error: str


MUTATIONS = (
    BoundaryMutation(
        "claim_promotion",
        ("claims", "microvm_replay_verified"),
        True,
        "profile_claims_mismatch",
    ),
    BoundaryMutation(
        "integer_boolean",
        ("claims", "sandbox_escape_resistance"),
        0,
        "profile_claims_mismatch",
    ),
    BoundaryMutation(
        "nested_host",
        ("host_policy", "nested_virtualization_allowed"),
        True,
        "host_policy_mismatch",
    ),
    BoundaryMutation(
        "ksm_zero_page_enabled",
        ("host_policy", "ksm_use_zero_pages_required"),
        1,
        "host_policy_mismatch",
    ),
    BoundaryMutation(
        "seccomp_disabled",
        ("runner_policy", "built_in_default_seccomp_required"),
        False,
        "runner_policy_mismatch",
    ),
    BoundaryMutation(
        "nic_enabled",
        ("runner_policy", "guest_network_device_allowed"),
        True,
        "runner_policy_mismatch",
    ),
    BoundaryMutation(
        "stale_output_protocol",
        ("runner_policy", "output_validation"),
        "bounded_length_only",
        "runner_policy_mismatch",
    ),
    BoundaryMutation(
        "weak_teardown",
        ("runner_policy", "teardown_policy"),
        "kill_parent_only",
        "runner_policy_mismatch",
    ),
    BoundaryMutation(
        "vm_config_self_attested",
        ("runner_policy", "exact_vm_configuration_status"),
        "publisher_attested_complete",
        "runner_policy_mismatch",
    ),
    BoundaryMutation(
        "archive_extraction_self_attested",
        ("runner_policy", "archive_extraction_status"),
        "publisher_attested_complete",
        "runner_policy_mismatch",
    ),
    BoundaryMutation(
        "release_rebound",
        ("release", "tag_commit"),
        "00" * 20,
        "profile_release_mismatch",
    ),
    BoundaryMutation(
        "binary_rebound",
        ("artifacts", "firecracker_release_binary", "sha256"),
        "00" * 32,
        "profile_artifacts_mismatch",
    ),
)


def test_structure_preserving_boundary_atlas_rejects_every_mutation(
    tmp_path: Path,
) -> None:
    signatures: set[tuple[str, ...]] = set()
    for mutation in MUTATIONS:
        candidate = _profile()
        _replace(candidate, mutation.path, mutation.replacement)
        report = checker.validate_profile(
            _write(tmp_path / f"{mutation.case_id}.json", candidate)
        )

        assert report["profile_valid"] is False, mutation.case_id
        assert mutation.expected_error in report["errors"], mutation.case_id
        assert "profile_canonical_hash_mismatch" in report["errors"], mutation.case_id
        signatures.add(tuple(report["errors"]))

    assert len(signatures) >= 5


def test_depth_two_frontier_preserves_both_reject_families(tmp_path: Path) -> None:
    candidate = _profile()
    _replace(candidate, ("claims", "production_authority"), True)
    _replace(candidate, ("runner_policy", "metadata_service_allowed"), True)

    report = checker.validate_profile(_write(tmp_path / "depth-two.json", candidate))

    assert report["profile_valid"] is False
    assert report["errors"] == [
        "profile_claims_mismatch",
        "runner_policy_mismatch",
        "profile_canonical_hash_mismatch",
    ]


def _replace(candidate: dict[str, Any], path: tuple[str, ...], value: Any) -> None:
    cursor: dict[str, Any] = candidate
    for component in path[:-1]:
        child = cursor[component]
        assert isinstance(child, dict)
        cursor = child
    cursor[path[-1]] = value


def _profile() -> dict[str, Any]:
    value = checker.support.strict_json_loads(checker.PROFILE_PATH.read_bytes())
    assert isinstance(value, dict)
    return copy.deepcopy(value)


def _write(path: Path, value: dict[str, Any]) -> Path:
    path.write_bytes(checker._canonical_bytes(value))
    return path
