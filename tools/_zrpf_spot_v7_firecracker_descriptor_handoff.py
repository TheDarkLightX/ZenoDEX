"""Private one-shot capability types for descriptor-sourced launch inputs."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn, SupportsIndex, final

from tools._zrpf_spot_v7_firecracker_descriptor_snapshot import (
    SpotV7DescriptorStagingRejectV1,
    _RetainedSpotV7LaunchSnapshotV1,
)
from tools.zrpf_spot_v7_firecracker_jail_staging import PreparedSpotV7JailRootV1
from tools.zrpf_spot_v7_firecracker_runtime_manifest import (
    CandidateSpotV7FirecrackerRuntimeManifestV1,
)
from tools.zrpf_v3_firecracker_jailer_launcher import PreparedJailerLaunchSpecV2
from tools.zrpf_v3_firecracker_trusted_runtime import PinnedExecutableV1


@dataclass(frozen=True, slots=True)
class _LaunchResourcesV1:
    prepared_jail: PreparedSpotV7JailRootV1
    snapshot: _RetainedSpotV7LaunchSnapshotV1
    jailer: PinnedExecutableV1
    firecracker: PinnedExecutableV1
    launch_spec: PreparedJailerLaunchSpecV2
    runtime_manifest: CandidateSpotV7FirecrackerRuntimeManifestV1
    runtime_manifest_sha256: bytes


class _PreparedLaunchSealV1:
    __slots__ = ()


_PREPARED_LAUNCH_SEAL_V1 = _PreparedLaunchSealV1()


class _LifecycleHandoffRequestSealV1:
    __slots__ = ()


_LIFECYCLE_HANDOFF_REQUEST_SEAL_V1 = _LifecycleHandoffRequestSealV1()


class _LifecycleHandoffSealV1:
    __slots__ = ()


_LIFECYCLE_HANDOFF_SEAL_V1 = _LifecycleHandoffSealV1()


@final
class _PreparedDescriptorBoundSpotV7LaunchV1:
    """One-shot launch preparation built exclusively from snapshot bytes."""

    __slots__ = ("_closed", "_resources", "_seal", "_spent")

    _closed: bool
    _resources: _LaunchResourcesV1
    _seal: _PreparedLaunchSealV1
    _spent: bool

    def __init__(
        self,
        *,
        resources: _LaunchResourcesV1,
        seal: _PreparedLaunchSealV1,
    ) -> None:
        if seal is not _PREPARED_LAUNCH_SEAL_V1:
            raise TypeError("prepared descriptor launch requires the module-private seal")
        _require_exact_resources(resources)
        object.__setattr__(self, "_resources", resources)
        object.__setattr__(self, "_seal", seal)
        object.__setattr__(self, "_closed", False)
        object.__setattr__(self, "_spent", False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("prepared descriptor launch cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("prepared descriptor launch cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("prepared descriptor launch cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("prepared descriptor launch cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("prepared descriptor launch cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("prepared descriptor launch cannot be serialized")

    @property
    def artifact_roles(self) -> tuple[str, ...]:
        return self._resources.snapshot.roles

    @property
    def artifact_set_id(self) -> bytes:
        return self._resources.runtime_manifest.artifact_set_id

    @property
    def runtime_manifest(self) -> CandidateSpotV7FirecrackerRuntimeManifestV1:
        return self._resources.runtime_manifest

    @property
    def runtime_manifest_sha256(self) -> bytes:
        return self._resources.runtime_manifest_sha256

    @property
    def launch_spec(self) -> PreparedJailerLaunchSpecV2:
        return self._resources.launch_spec

    @property
    def snapshot_root_path(self) -> Path:
        return self._resources.snapshot.root_path

    def snapshot_artifact_path(self, role: str) -> Path:
        return self._resources.snapshot.path_for_role(role)

    @property
    def governance_admission_verified(self) -> bool:
        return False

    @property
    def live_firecracker_execution_verified(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    def verify_prelaunch(self) -> None:
        self._require_usable()
        _verify_launch_resources(self._resources)

    def close_before_launch(self) -> None:
        if self._closed:
            return
        if self._spent:
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_launch_spent"
            )
        try:
            _abandon_unlaunched_resources(self._resources)
        finally:
            object.__setattr__(self, "_closed", True)

    def _take_for_lifecycle_v1(
        self,
        seal: _LifecycleHandoffRequestSealV1,
    ) -> _DescriptorBoundSpotV7LifecycleHandoffV1:
        if seal is not _LIFECYCLE_HANDOFF_REQUEST_SEAL_V1:
            raise TypeError("descriptor lifecycle handoff requires the private seal")
        self._require_usable()
        object.__setattr__(self, "_spent", True)
        try:
            _verify_launch_resources(self._resources)
        except BaseException:
            try:
                _abandon_unlaunched_resources(self._resources)
            except BaseException:
                pass
            object.__setattr__(self, "_closed", True)
            raise
        return _DescriptorBoundSpotV7LifecycleHandoffV1(
            resources=self._resources,
            seal=_LIFECYCLE_HANDOFF_SEAL_V1,
        )

    def _require_usable(self) -> None:
        if self._closed:
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_launch_closed"
            )
        if self._spent:
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_launch_spent"
            )
        if self._seal is not _PREPARED_LAUNCH_SEAL_V1:
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_launch_invalid"
            )


@final
class _DescriptorBoundSpotV7LifecycleHandoffV1:
    """Exact one-shot lifecycle inputs; still no runtime authority."""

    __slots__ = ("_closed", "_resources", "_seal")

    _closed: bool
    _resources: _LaunchResourcesV1
    _seal: _LifecycleHandoffSealV1

    def __init__(
        self,
        *,
        resources: _LaunchResourcesV1,
        seal: _LifecycleHandoffSealV1,
    ) -> None:
        if seal is not _LIFECYCLE_HANDOFF_SEAL_V1:
            raise TypeError("descriptor lifecycle handoff requires the module-private seal")
        _require_exact_resources(resources)
        object.__setattr__(self, "_resources", resources)
        object.__setattr__(self, "_seal", seal)
        object.__setattr__(self, "_closed", False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("descriptor lifecycle handoff cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("descriptor lifecycle handoff cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("descriptor lifecycle handoff cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("descriptor lifecycle handoff cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("descriptor lifecycle handoff cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("descriptor lifecycle handoff cannot be serialized")

    @property
    def prepared_jail(self) -> PreparedSpotV7JailRootV1:
        self._require_open()
        return self._resources.prepared_jail

    @property
    def jailer(self) -> PinnedExecutableV1:
        self._require_open()
        return self._resources.jailer

    @property
    def firecracker(self) -> PinnedExecutableV1:
        self._require_open()
        return self._resources.firecracker

    @property
    def launch_spec(self) -> PreparedJailerLaunchSpecV2:
        self._require_open()
        return self._resources.launch_spec

    def verify_prelaunch(self) -> None:
        self._require_open()
        _verify_launch_resources(self._resources)

    def _exact_request_bytes_for_supervisor_v1(self) -> bytes:
        """Return the already-staged request after rechecking every resource."""

        self.verify_prelaunch()
        return self._resources.prepared_jail._exact_request_bytes_for_supervisor_v1()

    def _close_after_completed_lifecycle_v1(self) -> None:
        """Close snapshot resources after the lifecycle removed its jail."""

        self._require_open()
        try:
            _close_executables_and_snapshot(self._resources)
        finally:
            object.__setattr__(self, "_closed", True)

    def _cleanup_after_forced_teardown_v1(self) -> None:
        """Remove staged files only after the supervisor proved process absence."""

        self._require_open()
        primary: BaseException | None = None
        try:
            self._resources.prepared_jail.cleanup_after_teardown()
        except BaseException as exc:
            primary = exc
        try:
            _close_executables_and_snapshot(self._resources)
        except BaseException as exc:
            if primary is None:
                primary = exc
        finally:
            object.__setattr__(self, "_closed", True)
        if primary is not None:
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_forced_cleanup_failed"
            ) from primary

    def _quarantine_after_uncertain_lifecycle_v1(self) -> None:
        """Spend the capability while retaining files for operator recovery."""

        self._require_open()
        object.__setattr__(self, "_closed", True)

    def abandon_before_launch(self) -> None:
        if self._closed:
            return
        try:
            _abandon_unlaunched_resources(self._resources)
        finally:
            object.__setattr__(self, "_closed", True)

    def _require_open(self) -> None:
        if self._closed or self._seal is not _LIFECYCLE_HANDOFF_SEAL_V1:
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_handoff_closed"
            )


def _new_prepared_launch_v1(
    resources: _LaunchResourcesV1,
) -> _PreparedDescriptorBoundSpotV7LaunchV1:
    result = _PreparedDescriptorBoundSpotV7LaunchV1(
        resources=resources,
        seal=_PREPARED_LAUNCH_SEAL_V1,
    )
    result.verify_prelaunch()
    return result


def _require_exact_resources(resources: _LaunchResourcesV1) -> None:
    if (
        type(resources) is not _LaunchResourcesV1
        or type(resources.prepared_jail) is not PreparedSpotV7JailRootV1
        or type(resources.snapshot) is not _RetainedSpotV7LaunchSnapshotV1
        or type(resources.jailer) is not PinnedExecutableV1
        or type(resources.firecracker) is not PinnedExecutableV1
        or type(resources.launch_spec) is not PreparedJailerLaunchSpecV2
        or type(resources.runtime_manifest) is not CandidateSpotV7FirecrackerRuntimeManifestV1
        or type(resources.runtime_manifest_sha256) is not bytes
        or len(resources.runtime_manifest_sha256) != 32
        or not any(resources.runtime_manifest_sha256)
    ):
        raise TypeError("prepared descriptor launch inputs have invalid types")


def _verify_launch_resources(resources: _LaunchResourcesV1) -> None:
    resources.snapshot.verify(resources.runtime_manifest)
    resources.jailer.reverify()
    resources.firecracker.reverify()
    resources.prepared_jail.verify_prelaunch()
    staged = resources.prepared_jail.spec
    launch = resources.launch_spec
    if (
        launch.jail_id,
        launch.uid,
        launch.gid,
        launch.chroot_base_dir,
        resources.firecracker.path.name,
    ) != (
        staged.jail_id,
        staged.runtime_uid,
        staged.runtime_gid,
        staged.chroot_base_dir,
        staged.firecracker_file_name,
    ):
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_launch_binding"
        )


def _abandon_unlaunched_resources(resources: _LaunchResourcesV1) -> None:
    primary: BaseException | None = None
    try:
        resources.prepared_jail.abandon_before_launch()
    except BaseException as exc:
        primary = exc
    for executable in (resources.jailer, resources.firecracker):
        try:
            executable.close()
        except BaseException as exc:
            if primary is None:
                primary = exc
    try:
        resources.snapshot.close_and_remove()
    except BaseException as exc:
        if primary is None:
            primary = exc
    if primary is not None:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_abandon_failed"
        ) from primary


def _close_executables_and_snapshot(resources: _LaunchResourcesV1) -> None:
    primary: BaseException | None = None
    for executable in (resources.jailer, resources.firecracker):
        try:
            executable.close()
        except BaseException as exc:
            if primary is None:
                primary = exc
    try:
        resources.snapshot.close_and_remove()
    except BaseException as exc:
        if primary is None:
            primary = exc
    if primary is not None:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_completed_cleanup_failed"
        ) from primary
