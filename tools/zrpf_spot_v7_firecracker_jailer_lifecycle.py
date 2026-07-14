"""Spot V7 binding layer over the shared data-only Jailer lifecycle.

This module carries exact authority-neutral prepare identities through natural
Firecracker completion.  It reuses the retained process, cgroup, namespace,
and teardown controls without changing their V3 behavior.  A completed value
is ordinary evidence data; it grants no execution, release, settlement, or
production authority.
"""

from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass
from typing import Any, Callable

from tools import zrpf_v3_firecracker_cgroup_v2 as cgroup_v2
from tools.zrpf_spot_v7_firecracker_jail_staging import PreparedSpotV7JailRootV1
from tools.zrpf_spot_v7_firecracker_runtime_binding import (
    SpotV7FirecrackerPrepareObservationV1,
)
from tools.zrpf_v3_firecracker_jailer_launcher import (
    CgroupLeafControl,
    NetworkNamespaceControl,
    PreparedJailerLaunchSpecV2,
    ProcessHandle,
    _finish_jailer_process_control_for_test,
    _JailerLaunchObservationV1,
    _launch_jailer_process_control_for_test,
)
from tools.zrpf_v3_firecracker_netns import PinnedNetworkNamespaceV1
from tools.zrpf_v3_firecracker_trusted_runtime import (
    JailerLauncherReject,
    PinnedExecutableV1,
)

__all__ = [
    "CompletedPreparedSpotV7JailerRunV1",
    "run_prepared_spot_v7_jailer_process_control_v1",
]


@dataclass(frozen=True, slots=True)
class CompletedPreparedSpotV7JailerRunV1:
    """Bound V7 lifecycle evidence and output bytes with no authority."""

    prepare_observation: dict[str, Any]
    launch_observation: dict[str, Any]
    finish_observation: dict[str, Any]
    output_device_bytes: bytes


def run_prepared_spot_v7_jailer_process_control_v1(
    *,
    spec: PreparedJailerLaunchSpecV2,
    prepared_jail: PreparedSpotV7JailRootV1,
    jailer: PinnedExecutableV1,
    firecracker: PinnedExecutableV1,
    cgroup_leaf: cgroup_v2.CgroupLeafV1,
    network_namespace: PinnedNetworkNamespaceV1,
    process_timeout_seconds: float,
) -> CompletedPreparedSpotV7JailerRunV1:
    """Run one exact V7-prepared jail and retain its identity chain."""

    _require_exact_root_owned_controls(
        spec=spec,
        prepared_jail=prepared_jail,
        jailer=jailer,
        firecracker=firecracker,
        cgroup_leaf=cgroup_leaf,
        network_namespace=network_namespace,
    )
    _require_prepared_jail_matches_launch(spec, prepared_jail, firecracker)
    return _complete_prepared_spot_v7_jailer_lifecycle_for_test(
        prepared_jail=prepared_jail,
        launch=lambda: _launch_jailer_process_control_for_test(
            spec=spec,
            jailer=jailer,
            firecracker=firecracker,
            cgroup_leaf=cgroup_leaf,
            network_namespace=network_namespace,
        ),
        finish=lambda process, observation, prepare: (
            _finish_spot_v7_jailer_process_control_for_test(
                process=process,
                cgroup_leaf=cgroup_leaf,
                network_namespace=network_namespace,
                observation=observation,
                prepare_observation=prepare,
                process_timeout_seconds=process_timeout_seconds,
            )
        ),
    )


def _require_exact_root_owned_controls(
    *,
    spec: PreparedJailerLaunchSpecV2,
    prepared_jail: PreparedSpotV7JailRootV1,
    jailer: PinnedExecutableV1,
    firecracker: PinnedExecutableV1,
    cgroup_leaf: cgroup_v2.CgroupLeafV1,
    network_namespace: PinnedNetworkNamespaceV1,
) -> None:
    if (
        type(spec) is not PreparedJailerLaunchSpecV2
        or type(prepared_jail) is not PreparedSpotV7JailRootV1
        or type(jailer) is not PinnedExecutableV1
        or type(firecracker) is not PinnedExecutableV1
        or type(cgroup_leaf) is not cgroup_v2.CgroupLeafV1
        or type(network_namespace) is not PinnedNetworkNamespaceV1
    ):
        raise JailerLauncherReject("jailer_prepared_spot_v7_control_type_invalid")
    if (
        os.geteuid() != 0
        or jailer.trusted_uid != 0
        or firecracker.trusted_uid != 0
        or cgroup_leaf.trusted_uid != 0
        or network_namespace.trusted_uid != 0
        or prepared_jail.spec.trusted_uid != 0
    ):
        raise JailerLauncherReject("jailer_prepared_spot_v7_control_not_root_owned")


def _require_prepared_jail_matches_launch(
    spec: PreparedJailerLaunchSpecV2,
    prepared_jail: PreparedSpotV7JailRootV1,
    firecracker: PinnedExecutableV1,
) -> None:
    staged = prepared_jail.spec
    if (
        staged.jail_id,
        staged.firecracker_file_name,
        staged.chroot_base_dir,
        staged.runtime_uid,
        staged.runtime_gid,
        staged.config_path_in_jail,
    ) != (
        spec.jail_id,
        firecracker.path.name,
        spec.chroot_base_dir,
        spec.uid,
        spec.gid,
        "/resources/config.json",
    ):
        raise JailerLauncherReject("jailer_prepared_stage_binding_mismatch")


def _complete_prepared_spot_v7_jailer_lifecycle_for_test(
    *,
    prepared_jail: PreparedSpotV7JailRootV1,
    launch: Callable[[], tuple[ProcessHandle, _JailerLaunchObservationV1]],
    finish: Callable[
        [
            ProcessHandle,
            _JailerLaunchObservationV1,
            SpotV7FirecrackerPrepareObservationV1,
        ],
        dict[str, Any],
    ],
) -> CompletedPreparedSpotV7JailerRunV1:
    """Complete one V7 lifecycle and always close its staged jail.

    The production ``launch`` and ``finish`` callbacks own cgroup teardown on
    every failure. Once either callback returns or raises, removing the staged
    jail is therefore safe and mandatory.
    """

    if type(prepared_jail) is not PreparedSpotV7JailRootV1:
        raise TypeError("prepared_jail must be exact PreparedSpotV7JailRootV1")
    try:
        prepare_observation = prepared_jail.prepare_observation()
    except BaseException:
        prepared_jail.abandon_before_launch()
        raise
    try:
        process, observation = launch()
        report = finish(process, observation, prepare_observation)
        output = prepared_jail.read_validated_output_after_exit()
        return CompletedPreparedSpotV7JailerRunV1(
            prepare_observation=prepare_observation.to_document(),
            launch_observation=observation.to_document(),
            finish_observation=report,
            output_device_bytes=output,
        )
    finally:
        prepared_jail.cleanup_after_teardown()


def _finish_spot_v7_jailer_process_control_for_test(
    *,
    process: ProcessHandle,
    cgroup_leaf: CgroupLeafControl,
    network_namespace: NetworkNamespaceControl,
    observation: _JailerLaunchObservationV1,
    prepare_observation: SpotV7FirecrackerPrepareObservationV1,
    process_timeout_seconds: float,
    teardown_timeout_ns: int = 5_000_000_000,
) -> dict[str, Any]:
    """Complete the shared lifecycle and bind its exact V7 prepare record."""

    if type(prepare_observation) is not SpotV7FirecrackerPrepareObservationV1:
        raise TypeError(
            "prepare_observation must be exact SpotV7FirecrackerPrepareObservationV1"
        )
    retained_finish = _finish_jailer_process_control_for_test(
        process=process,
        cgroup_leaf=cgroup_leaf,
        network_namespace=network_namespace,
        observation=observation,
        process_timeout_seconds=process_timeout_seconds,
        teardown_timeout_ns=teardown_timeout_ns,
    )
    return _spot_v7_finish_observation_document_v1(
        observation=observation,
        prepare_observation=prepare_observation,
        exit_code=retained_finish["exit_code"],
    )


def _spot_v7_finish_observation_document_v1(
    *,
    observation: _JailerLaunchObservationV1,
    prepare_observation: SpotV7FirecrackerPrepareObservationV1,
    exit_code: int,
) -> dict[str, Any]:
    """Bind natural completion to exact proposed V7 runtime identities."""

    if type(observation) is not _JailerLaunchObservationV1:
        raise TypeError("observation must be exact _JailerLaunchObservationV1")
    if type(prepare_observation) is not SpotV7FirecrackerPrepareObservationV1:
        raise TypeError(
            "prepare_observation must be exact SpotV7FirecrackerPrepareObservationV1"
        )
    if type(exit_code) is not int or exit_code != 0:
        raise JailerLauncherReject("jailer_exit_status_invalid")
    launch_document = observation.to_document()
    prepare_document = prepare_observation.to_document()
    authority = dict(launch_document["authority"])
    authority.update(prepare_document["authority"])
    return {
        "authority": authority,
        "cgroup_relative_path": observation.cgroup_relative_path,
        "control_facts": {
            "cgroup_kill_issued": False,
            "cgroup_removed_after_natural_completion": True,
            "firecracker_cgroup_naturally_empty_verified": True,
            "jailer_parent_exit_observed": True,
            "network_namespace_path_identity_preserved": True,
        },
        "exit_code": exit_code,
        "jailer_pid": observation.jailer_pid,
        "launch_observation_sha256": hashlib.sha256(
            _canonical_observation_bytes_v1(launch_document)
        ).hexdigest(),
        "observed_process_count": len(observation.process_set),
        "prepare_observation": prepare_document,
        "prepare_observation_sha256": hashlib.sha256(
            prepare_observation.canonical_bytes()
        ).hexdigest(),
        "schema": "zenodex/zrpf_spot_v7_firecracker_jailer_finish_observation/v1",
        "scope": "exact_proposed_runtime_and_natural_completion_authority_false",
    }


def _validate_exact_spot_v7_finish_observation_v1(
    raw: bytes,
    *,
    observation: _JailerLaunchObservationV1,
    prepare_observation: SpotV7FirecrackerPrepareObservationV1,
) -> dict[str, Any]:
    """Validate canonical finish data without promoting runtime authority."""

    if type(raw) is not bytes or not 0 < len(raw) <= 1024 * 1024:
        raise JailerLauncherReject("jailer_spot_v7_finish_invalid")
    try:
        document = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_json_object_v1,
            parse_constant=_reject_json_number_v1,
            parse_float=_reject_json_number_v1,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise JailerLauncherReject("jailer_spot_v7_finish_invalid") from exc
    expected = _spot_v7_finish_observation_document_v1(
        observation=observation,
        prepare_observation=prepare_observation,
        exit_code=0,
    )
    if type(document) is not dict or raw != _canonical_observation_bytes_v1(document):
        raise JailerLauncherReject("jailer_spot_v7_finish_noncanonical")
    if raw != _canonical_observation_bytes_v1(expected):
        raise JailerLauncherReject("jailer_spot_v7_finish_binding_mismatch")
    return document


def _unique_json_object_v1(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate key")
        output[key] = value
    return output


def _reject_json_number_v1(_value: str) -> None:
    raise ValueError("unsupported JSON number")


def _canonical_observation_bytes_v1(document: object) -> bytes:
    return (
        json.dumps(
            document,
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
        + "\n"
    ).encode("ascii")
