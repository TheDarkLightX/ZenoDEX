"""Adversarial tests for the authority-neutral supervisor candidate policy."""

from __future__ import annotations

import copy
import hashlib
import json
from collections.abc import Iterator
from typing import Any

import pytest

from tests.test_zrpf_spot_v7_release_candidate_manifest_v1 import (
    _body as release_candidate_body,
)
from tools import zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 as policy
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as release_candidate


def _digest(label: bytes) -> str:
    return hashlib.sha256(label).hexdigest()


def _canonical(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _contract_document(
    *,
    runtime_manifest_sha256: str | None = None,
    firecracker_profile_sha256: str | None = None,
) -> dict[str, Any]:
    return {
        "authority": {field: False for field in policy.CANDIDATE_POLICY_AUTHORITY_FIELDS_V1},
        "bindings": {
            "firecracker_profile_sha256": (
                firecracker_profile_sha256 or _digest(b"firecracker-profile")
            ),
            "runtime_manifest_sha256": (runtime_manifest_sha256 or _digest(b"runtime-manifest")),
        },
        "cgroup": {
            "cgroup_mount": "/sys/fs/cgroup",
            "limits": {
                "cpu_period_us": 100_000,
                "cpu_quota_us": 100_000,
                "cpuset_cpus": "0",
                "cpuset_mems": "0",
                "io_max": ("8:0 rbps=1048576 wbps=1048576 riops=1024 wiops=1024"),
                "memory_high_bytes": 256 * 1024 * 1024,
                "memory_max_bytes": 512 * 1024 * 1024,
                "memory_swap_max_bytes": 0,
                "pids_max": 64,
            },
            "mountinfo_path": "/proc/self/mountinfo",
            "parent_relative_path": "zenodex01/zrpf0001",
            "proc_root": "/proc",
            "trusted_uid": 0,
        },
        "format_flags": 1,
        "network_namespace": {
            "helper_sha256": _digest(b"netns-helper"),
            "root": "/run/netns",
        },
        "non_claims": list(policy.CANDIDATE_POLICY_NON_CLAIMS_V1),
        "reserved_u32": 0,
        "schema": policy.ROOT_SUPERVISOR_CANDIDATE_CONTRACT_SCHEMA_V1,
        "status": policy.ROOT_SUPERVISOR_CANDIDATE_CONTRACT_STATUS_V1,
        "timeouts": {
            "process_timeout_ns": 30_000_000_000,
            "teardown_timeout_ns": 5_000_000_000,
        },
    }


def _release_candidate_for_contract(
    contract: dict[str, Any],
    *,
    contract_digest_override: str | None = None,
    contract_size_override: int | None = None,
    artifact_set_id: str | None = None,
    machine_config_sha256: str | None = None,
    authority_input_profile_sha256: str | None = None,
) -> bytes:
    contract_bytes = _canonical(contract)
    contract_digest = contract_digest_override or hashlib.sha256(contract_bytes).hexdigest()
    body = copy.deepcopy(release_candidate_body())
    role_bindings = {
        "root_supervisor_contract": contract_digest,
        "runtime_manifest": contract["bindings"]["runtime_manifest_sha256"],
        "firecracker_profile": contract["bindings"]["firecracker_profile_sha256"],
        "runtime_artifact_manifest": (artifact_set_id or body["runtime"]["artifact_set_id"]),
        "machine_config": (machine_config_sha256 or body["runtime"]["machine_config_sha256"]),
        "authority_input_profile": (
            authority_input_profile_sha256 or body["runtime"]["authority_input_profile_sha256"]
        ),
    }
    for row in body["evidence_inventory"]:
        role = row["role"]
        if role not in role_bindings:
            continue
        digest = role_bindings[role]
        row["artifact_sha256"] = digest
        row["bound_identity"] = digest
        if role == "root_supervisor_contract":
            row["size_bytes"] = (
                contract_size_override
                if contract_size_override is not None
                else len(contract_bytes)
            )
    body["runtime"]["root_supervisor_contract_sha256"] = contract_digest
    body["runtime"]["runtime_manifest_sha256"] = role_bindings["runtime_manifest"]
    body["runtime"]["firecracker_profile_sha256"] = role_bindings["firecracker_profile"]
    body["runtime"]["artifact_set_id"] = role_bindings["runtime_artifact_manifest"]
    body["runtime"]["machine_config_sha256"] = role_bindings["machine_config"]
    body["runtime"]["authority_input_profile_sha256"] = role_bindings["authority_input_profile"]
    return release_candidate.recompose_spot_v7_release_candidate_manifest_v1(body)


def _prepared_policy(
    contract: dict[str, Any] | None = None,
) -> policy.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
    selected = _contract_document() if contract is None else contract
    candidate_bytes = _release_candidate_for_contract(selected)
    candidate = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    return policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
        exact_root_supervisor_contract_bytes=_canonical(selected),
        exact_release_candidate_bytes=candidate_bytes,
        expected_candidate_id=candidate.candidate_id,
    )


def test_exact_candidate_contract_binds_all_supervisor_controls() -> None:
    prepared = _prepared_policy()

    assert prepared.candidate_id
    assert prepared.evidence_inventory_root
    assert prepared.candidate_manifest_sha256
    assert prepared.artifact_set_id
    assert prepared.machine_config_sha256
    assert prepared.authority_input_profile_sha256
    assert prepared.cgroup_mount.as_posix() == "/sys/fs/cgroup"
    assert prepared.mountinfo_path.as_posix() == "/proc/self/mountinfo"
    assert prepared.proc_root.as_posix() == "/proc"
    assert prepared.cgroup_parent_relative_path == "zenodex01/zrpf0001"
    assert prepared.trusted_uid == 0
    assert prepared.cgroup_limits.cpu_quota_us == 100_000
    assert prepared.cgroup_limits.memory_max_bytes == 512 * 1024 * 1024
    assert prepared.network_namespace_root.as_posix() == "/run/netns"
    assert prepared.netns_helper_sha256 == _digest(b"netns-helper")
    assert prepared.process_timeout_ns == 30_000_000_000
    assert prepared.teardown_timeout_ns == 5_000_000_000
    assert prepared.runtime_manifest_sha256 == bytes.fromhex(_digest(b"runtime-manifest"))
    assert prepared.firecracker_profile_sha256 == bytes.fromhex(_digest(b"firecracker-profile"))
    assert prepared.candidate_selected is False
    assert prepared.live_execution_verified is False
    assert prepared.runtime_authority is False
    assert prepared.release_authority is False
    assert prepared.settlement_authority is False
    assert prepared.production_authority is False


def test_revalidation_is_type_sensitive_and_rejects_bool_for_zero_limit() -> None:
    prepared = _prepared_policy()
    object.__setattr__(
        prepared.cgroup_limits,
        "memory_swap_max_bytes",
        False,
    )

    with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1) as captured:
        policy._revalidate_prepared_policy(prepared)

    assert captured.value.code == "candidate_policy_prepared_policy_mutated"


def test_forged_prepared_policy_rejects_with_stable_boundary_code() -> None:
    forged = object.__new__(policy.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1)

    with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1) as captured:
        policy._revalidate_prepared_policy(forged)

    assert captured.value.code == "candidate_policy_prepared_policy"


def test_contract_inventory_digest_and_size_are_both_exact() -> None:
    contract = _contract_document()
    contract_bytes = _canonical(contract)
    wrong_digest_candidate = _release_candidate_for_contract(
        contract,
        contract_digest_override=_digest(b"wrong-contract"),
    )
    wrong_size_candidate = _release_candidate_for_contract(
        contract,
        contract_size_override=len(contract_bytes) + 1,
    )

    for candidate_bytes, expected_code in (
        (wrong_digest_candidate, "candidate_policy_contract_inventory_digest"),
        (wrong_size_candidate, "candidate_policy_contract_inventory_size"),
    ):
        parsed = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(
            candidate_bytes
        )
        with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1) as captured:
            policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
                exact_root_supervisor_contract_bytes=contract_bytes,
                exact_release_candidate_bytes=candidate_bytes,
                expected_candidate_id=parsed.candidate_id,
            )
        assert captured.value.code == expected_code


def test_coherent_candidate_substitution_rejects_independent_expected_id() -> None:
    original_contract = _contract_document()
    original_candidate_bytes = _release_candidate_for_contract(original_contract)
    original_candidate = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(
        original_candidate_bytes
    )
    substituted_contract = copy.deepcopy(original_contract)
    substituted_contract["timeouts"]["process_timeout_ns"] += 1
    substituted_candidate_bytes = _release_candidate_for_contract(substituted_contract)

    with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1) as captured:
        policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
            exact_root_supervisor_contract_bytes=_canonical(substituted_contract),
            exact_release_candidate_bytes=substituted_candidate_bytes,
            expected_candidate_id=original_candidate.candidate_id,
        )

    assert captured.value.code == "candidate_policy_release_candidate"


def test_contract_runtime_bindings_must_equal_release_candidate_runtime_section() -> None:
    contract = _contract_document()
    candidate_bytes = _release_candidate_for_contract(contract)
    parsed = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    substituted = copy.deepcopy(contract)
    substituted["bindings"]["runtime_manifest_sha256"] = _digest(b"substituted-runtime-manifest")
    substituted_bytes = _canonical(substituted)
    body = copy.deepcopy(release_candidate_body())
    original_document = json.loads(candidate_bytes)
    body = {key: original_document[key] for key in body}
    contract_digest = hashlib.sha256(substituted_bytes).hexdigest()
    for row in body["evidence_inventory"]:
        if row["role"] == "root_supervisor_contract":
            row["artifact_sha256"] = contract_digest
            row["bound_identity"] = contract_digest
            row["size_bytes"] = len(substituted_bytes)
    body["runtime"]["root_supervisor_contract_sha256"] = contract_digest
    rebound_candidate = release_candidate.recompose_spot_v7_release_candidate_manifest_v1(body)
    rebound = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(rebound_candidate)

    assert rebound.candidate_id != parsed.candidate_id
    with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1) as captured:
        policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
            exact_root_supervisor_contract_bytes=substituted_bytes,
            exact_release_candidate_bytes=rebound_candidate,
            expected_candidate_id=rebound.candidate_id,
        )
    assert captured.value.code == "candidate_policy_runtime_manifest_binding"


@pytest.mark.parametrize(
    ("mutate", "expected_code"),
    (
        (
            lambda value: value["authority"].__setitem__("release_authority", True),
            "candidate_policy_authority",
        ),
        (
            lambda value: value["cgroup"].__setitem__("cgroup_mount", "relative"),
            "candidate_policy_cgroup_path",
        ),
        (
            lambda value: value["cgroup"].__setitem__("trusted_uid", False),
            "candidate_policy_trusted_uid",
        ),
        (
            lambda value: value["cgroup"].__setitem__("trusted_uid", 1),
            "candidate_policy_trusted_uid",
        ),
        (
            lambda value: value["cgroup"]["limits"].__setitem__("pids_max", True),
            "candidate_policy_cgroup_limits",
        ),
        (
            lambda value: value["cgroup"]["limits"].__setitem__("memory_high_bytes", 1 << 40),
            "candidate_policy_cgroup_limits",
        ),
        (
            lambda value: value["network_namespace"].__setitem__("root", "/run/../netns"),
            "candidate_policy_network_namespace",
        ),
        (
            lambda value: value["network_namespace"].__setitem__("helper_sha256", "00" * 32),
            "candidate_policy_netns_helper",
        ),
        (
            lambda value: value["timeouts"].__setitem__("process_timeout_ns", True),
            "candidate_policy_process_timeout",
        ),
        (
            lambda value: value["timeouts"].__setitem__("teardown_timeout_ns", 30_000_000_001),
            "candidate_policy_teardown_timeout",
        ),
        (
            lambda value: value["non_claims"].append("invented claim"),
            "candidate_policy_non_claims",
        ),
    ),
)
def test_invalid_contract_fields_reject_even_in_a_coherently_rebound_candidate(
    mutate: Any,
    expected_code: str,
) -> None:
    contract = _contract_document()
    mutate(contract)
    candidate_bytes = _release_candidate_for_contract(contract)
    candidate = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)

    with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1) as captured:
        policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
            exact_root_supervisor_contract_bytes=_canonical(contract),
            exact_release_candidate_bytes=candidate_bytes,
            expected_candidate_id=candidate.candidate_id,
        )

    assert captured.value.code == expected_code


def _leaf_paths(
    value: object,
    prefix: tuple[object, ...] = (),
) -> Iterator[tuple[object, ...]]:
    if type(value) is dict:
        for key in sorted(value):
            yield from _leaf_paths(value[key], (*prefix, key))
    elif type(value) is list:
        for index, child in enumerate(value):
            yield from _leaf_paths(child, (*prefix, index))
    else:
        yield prefix


def _mutate_leaf(value: dict[str, Any], path: tuple[object, ...]) -> None:
    cursor: Any = value
    for component in path[:-1]:
        cursor = cursor[component]
    leaf = cursor[path[-1]]
    if type(leaf) is bool:
        cursor[path[-1]] = not leaf
    elif type(leaf) is int:
        cursor[path[-1]] = leaf + 1
    elif type(leaf) is str:
        cursor[path[-1]] = leaf + "x"
    else:
        raise AssertionError(f"unsupported leaf type at {path!r}")


@pytest.mark.parametrize(
    "path",
    tuple(_leaf_paths(_contract_document())),
    ids=lambda path: ".".join(str(component) for component in path),
)
def test_every_contract_leaf_mutation_breaks_the_candidate_inventory_binding(
    path: tuple[object, ...],
) -> None:
    contract = _contract_document()
    candidate_bytes = _release_candidate_for_contract(contract)
    candidate = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    _mutate_leaf(contract, path)

    with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1):
        policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
            exact_root_supervisor_contract_bytes=_canonical(contract),
            exact_release_candidate_bytes=candidate_bytes,
            expected_candidate_id=candidate.candidate_id,
        )


def test_contract_json_is_exact_bounded_and_duplicate_free() -> None:
    contract = _contract_document()
    candidate_bytes = _release_candidate_for_contract(contract)
    candidate = release_candidate.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    noncanonical = json.dumps(contract).encode("ascii")
    duplicate = _canonical(contract).replace(
        b'{"authority":',
        b'{"schema":"duplicate","authority":',
        1,
    )

    for raw in (noncanonical, duplicate, b" " * (policy.MAX_CANDIDATE_CONTRACT_BYTES_V1 + 1)):
        with pytest.raises(policy.SpotV7RootSupervisorCandidatePolicyRejectV1):
            policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
                exact_root_supervisor_contract_bytes=raw,
                exact_release_candidate_bytes=candidate_bytes,
                expected_candidate_id=candidate.candidate_id,
            )
