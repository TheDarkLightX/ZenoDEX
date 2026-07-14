"""One-shot descriptor-to-launch staging for the Spot V7 Firecracker lane.

The bridge consumes the six descriptors retained by the exact runtime-artifact
binding, copies their bytes into one fresh supervisor-owned snapshot, and
builds the jail and executable handles only from that snapshot. Caller artifact
paths are never reopened after descriptor binding. The result is launch
preparation only. It carries no runtime, release, settlement, or production
authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from tools import zrpf_v3_firecracker_jail_staging_io as staging_io
from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _LIFECYCLE_HANDOFF_REQUEST_SEAL_V1,
    _LaunchResourcesV1,
    _new_prepared_launch_v1,
    _PreparedDescriptorBoundSpotV7LaunchV1,
    _PreparedLaunchSealV1,
)
from tools._zrpf_spot_v7_firecracker_descriptor_snapshot import (
    SpotV7DescriptorStagingRejectV1,
    _create_snapshot_v1,
    _jail_artifacts_v1,
    _pin_snapshot_executable_v1,
    _RetainedSpotV7LaunchSnapshotV1,
    _SnapshotCreateInputsV1,
)
from tools.zrpf_spot_v7_firecracker_artifact_binding import (
    _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1,
    _OpenedRuntimeArtifactV1,
)
from tools.zrpf_spot_v7_firecracker_jail_staging import (
    PreparedSpotV7JailRootV1,
    prepare_root_owned_spot_v7_jail_v1,
)
from tools.zrpf_spot_v7_firecracker_runtime_binding import (
    ProposedSpotV7FirecrackerRuntimeBindingV1,
)
from tools.zrpf_spot_v7_firecracker_runtime_manifest import (
    SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1,
    CandidateSpotV7FirecrackerRuntimeManifestV1,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SpotV7FirecrackerProtocolRejectV1,
    decode_exact_request_v1,
)
from tools.zrpf_v3_firecracker_jail_staging import PreparedJailRootSpecV2
from tools.zrpf_v3_firecracker_jailer_launcher import PreparedJailerLaunchSpecV2
from tools.zrpf_v3_firecracker_trusted_runtime import (
    JailerLauncherReject,
    PinnedExecutableV1,
)

__all__ = [
    "SpotV7DescriptorStagingRejectV1",
    "_LIFECYCLE_HANDOFF_REQUEST_SEAL_V1",
    "_LaunchResourcesV1",
    "_PreparedDescriptorBoundSpotV7LaunchV1",
    "_PreparedLaunchSealV1",
    "_RetainedSpotV7LaunchSnapshotV1",
    "prepare_descriptor_bound_spot_v7_launch_v1",
    "staging_io",
]


@dataclass(frozen=True, slots=True)
class _PrepareInputsV1:
    proposal: ProposedSpotV7FirecrackerRuntimeBindingV1
    records: tuple[_OpenedRuntimeArtifactV1, ...]
    jail_spec: PreparedJailRootSpecV2
    request_bytes: bytes
    launch_snapshot_root: Path
    trusted_chroot_root: Path
    trusted_snapshot_root: Path


@dataclass(slots=True)
class _PartialPreparationV1:
    snapshot: _RetainedSpotV7LaunchSnapshotV1 | None = None
    prepared_jail: PreparedSpotV7JailRootV1 | None = None
    jailer: PinnedExecutableV1 | None = None
    firecracker: PinnedExecutableV1 | None = None


def prepare_descriptor_bound_spot_v7_launch_v1(
    *,
    descriptor_bound_runtime: _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1,
    jail_spec: PreparedJailRootSpecV2,
    request_bytes: bytes,
    launch_snapshot_root: Path,
    trusted_chroot_root: Path = Path("/"),
    trusted_snapshot_root: Path = Path("/"),
) -> _PreparedDescriptorBoundSpotV7LaunchV1:
    """Spend retained source descriptors and prepare one exact launch snapshot."""

    _require_exact_public_inputs(descriptor_bound_runtime, jail_spec)
    try:
        proposal, records = descriptor_bound_runtime._take_for_descriptor_staging_v1()
        inputs = _PrepareInputsV1(
            proposal=proposal,
            records=records,
            jail_spec=jail_spec,
            request_bytes=request_bytes,
            launch_snapshot_root=launch_snapshot_root,
            trusted_chroot_root=trusted_chroot_root,
            trusted_snapshot_root=trusted_snapshot_root,
        )
        return _prepare_consumed_descriptors(inputs)
    finally:
        descriptor_bound_runtime.close()


def _require_exact_public_inputs(
    descriptor_bound_runtime: _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1,
    jail_spec: PreparedJailRootSpecV2,
) -> None:
    if type(descriptor_bound_runtime) is not _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1:
        raise TypeError("descriptor_bound_runtime must be the exact private binding")
    if type(jail_spec) is not PreparedJailRootSpecV2:
        raise TypeError("jail_spec must be exact PreparedJailRootSpecV2")


def _prepare_consumed_descriptors(
    inputs: _PrepareInputsV1,
) -> _PreparedDescriptorBoundSpotV7LaunchV1:
    partial = _PartialPreparationV1()
    try:
        _require_exact_opened_inventory(inputs.records, inputs.proposal.runtime_manifest)
        _require_request_binding(inputs)
        partial.snapshot = _create_launch_snapshot(inputs)
        partial.prepared_jail = _prepare_jail(inputs, partial.snapshot)
        partial.jailer = _pin_executable(inputs, partial.snapshot, role="jailer")
        partial.firecracker = _pin_executable(
            inputs,
            partial.snapshot,
            role="firecracker",
        )
        return _finish_preparation(inputs, partial)
    except BaseException as exc:
        _cleanup_partial_preparation(partial)
        if isinstance(exc, (SpotV7DescriptorStagingRejectV1, TypeError)):
            raise
        if isinstance(exc, JailerLauncherReject):
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_launch_prepare"
            ) from exc
        raise


def _create_launch_snapshot(
    inputs: _PrepareInputsV1,
) -> _RetainedSpotV7LaunchSnapshotV1:
    return _create_snapshot_v1(
        _SnapshotCreateInputsV1(
            records=inputs.records,
            manifest=inputs.proposal.runtime_manifest,
            root=inputs.launch_snapshot_root,
            stage_name=inputs.jail_spec.jail_id,
            trusted_root=inputs.trusted_snapshot_root,
            trusted_uid=inputs.jail_spec.trusted_uid,
        )
    )


def _prepare_jail(
    inputs: _PrepareInputsV1,
    snapshot: _RetainedSpotV7LaunchSnapshotV1,
) -> PreparedSpotV7JailRootV1:
    return prepare_root_owned_spot_v7_jail_v1(
        spec=inputs.jail_spec,
        artifacts=_jail_artifacts_v1(snapshot, inputs.proposal.runtime_manifest),
        config_bytes=inputs.proposal.exact_machine_config_bytes,
        request_bytes=inputs.request_bytes,
        runtime_binding=inputs.proposal,
        trusted_chroot_root=inputs.trusted_chroot_root,
        trusted_source_root=inputs.trusted_snapshot_root,
    )


def _pin_executable(
    inputs: _PrepareInputsV1,
    snapshot: _RetainedSpotV7LaunchSnapshotV1,
    *,
    role: str,
) -> PinnedExecutableV1:
    return _pin_snapshot_executable_v1(
        snapshot,
        inputs.proposal.runtime_manifest,
        role=role,
        trusted_root=inputs.trusted_snapshot_root,
        trusted_uid=inputs.jail_spec.trusted_uid,
    )


def _finish_preparation(
    inputs: _PrepareInputsV1,
    partial: _PartialPreparationV1,
) -> _PreparedDescriptorBoundSpotV7LaunchV1:
    if (
        partial.snapshot is None
        or partial.prepared_jail is None
        or partial.jailer is None
        or partial.firecracker is None
    ):
        raise SpotV7DescriptorStagingRejectV1("descriptor_stage_launch_incomplete")
    return _new_prepared_launch_v1(
        _LaunchResourcesV1(
            prepared_jail=partial.prepared_jail,
            snapshot=partial.snapshot,
            jailer=partial.jailer,
            firecracker=partial.firecracker,
            launch_spec=PreparedJailerLaunchSpecV2(
                jail_id=inputs.jail_spec.jail_id,
                uid=inputs.jail_spec.runtime_uid,
                gid=inputs.jail_spec.runtime_gid,
                chroot_base_dir=inputs.jail_spec.chroot_base_dir,
            ),
            runtime_manifest=inputs.proposal.runtime_manifest,
            runtime_manifest_sha256=inputs.proposal.runtime_manifest_sha256,
        )
    )


def _require_exact_opened_inventory(
    records: tuple[_OpenedRuntimeArtifactV1, ...],
    manifest: CandidateSpotV7FirecrackerRuntimeManifestV1,
) -> None:
    if (
        type(records) is not tuple
        or len(records) != len(SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1)
        or any(type(row) is not _OpenedRuntimeArtifactV1 for row in records)
        or tuple(row.role for row in records) != SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1
    ):
        raise SpotV7DescriptorStagingRejectV1("descriptor_stage_artifact_inventory")
    expected_rows = zip(records, manifest.artifacts, strict=True)
    for record, expected in expected_rows:
        if (
            record.role != expected.role
            or record.source_path.name != expected.artifact_name
            or record.expected_sha256 != expected.sha256.hex()
            or record.expected_size != expected.size_bytes
        ):
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_artifact_inventory"
            )


def _require_request_binding(inputs: _PrepareInputsV1) -> None:
    try:
        request = decode_exact_request_v1(inputs.request_bytes)
    except (SpotV7FirecrackerProtocolRejectV1, TypeError, ValueError) as exc:
        raise SpotV7DescriptorStagingRejectV1("descriptor_stage_request") from exc
    input_identity = next(
        row for row in inputs.proposal.runtime_manifest.artifacts if row.role == "input"
    )
    if (
        request.encode() != inputs.request_bytes
        or request.runtime_manifest_sha256 != inputs.proposal.runtime_manifest_sha256
        or request.machine_config_sha256 != inputs.proposal.machine_config_sha256
        or request.input_drive_sha256 != input_identity.sha256
    ):
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_request_binding"
        )


def _cleanup_partial_preparation(partial: _PartialPreparationV1) -> None:
    if partial.prepared_jail is not None:
        try:
            partial.prepared_jail.abandon_before_launch()
        except BaseException:
            pass
    for executable in (partial.jailer, partial.firecracker):
        if executable is not None:
            try:
                executable.close()
            except BaseException:
                pass
    if partial.snapshot is not None:
        try:
            partial.snapshot.close_and_remove()
        except BaseException:
            pass
