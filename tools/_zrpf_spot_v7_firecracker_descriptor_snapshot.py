"""Private immutable snapshot implementation for Spot V7 launch staging."""

from __future__ import annotations

import os
import shutil
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Final, NoReturn, final

from tools import zrpf_v3_firecracker_jail_staging_io as staging_io
from tools.zrpf_spot_v7_firecracker_artifact_binding import _OpenedRuntimeArtifactV1
from tools.zrpf_spot_v7_firecracker_runtime_manifest import (
    SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1,
    CandidateSpotV7FirecrackerRuntimeManifestV1,
    SpotV7RuntimeArtifactIdentityV1,
)
from tools.zrpf_v3_firecracker_jail_staging import RootOwnedStagedArtifactV2
from tools.zrpf_v3_firecracker_trusted_runtime import (
    ExecutableExpectationV1,
    JailerLauncherReject,
    PinnedExecutableV1,
    open_pinned_executable,
)

_EXECUTABLE_ROLES_V1: Final = frozenset({"firecracker", "guest_init", "jailer"})
_JAIL_RESOURCE_ROLES_V1: Final = ("input", "kernel", "rootfs")


class SpotV7DescriptorStagingRejectV1(ValueError):
    """Stable fail-closed rejection for the descriptor snapshot bridge."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@dataclass(frozen=True, slots=True)
class _SnapshotArtifactV1:
    role: str
    artifact_name: str
    path: Path
    descriptor: int
    version: staging_io.FileVersionV2
    sha256: str
    size_bytes: int


@dataclass(frozen=True, slots=True)
class _SnapshotStateV1:
    root_path: Path
    stage_name: str
    parent_fd: int
    directory_fd: int
    artifacts: tuple[_SnapshotArtifactV1, ...]
    trusted_uid: int


@dataclass(frozen=True, slots=True)
class _SnapshotCreateInputsV1:
    records: tuple[_OpenedRuntimeArtifactV1, ...]
    manifest: CandidateSpotV7FirecrackerRuntimeManifestV1
    root: Path
    stage_name: str
    trusted_root: Path
    trusted_uid: int


class _SnapshotSealV1:
    __slots__ = ()


_SNAPSHOT_SEAL_V1 = _SnapshotSealV1()


@final
class _RetainedSpotV7LaunchSnapshotV1:
    """Fresh immutable copies plus retained descriptors for all six roles."""

    __slots__ = ("_closed", "_seal", "_state")

    _closed: bool
    _seal: _SnapshotSealV1
    _state: _SnapshotStateV1

    def __init__(self, *, state: _SnapshotStateV1, seal: _SnapshotSealV1) -> None:
        if seal is not _SNAPSHOT_SEAL_V1:
            raise TypeError("descriptor snapshot requires the module-private seal")
        if tuple(row.role for row in state.artifacts) != SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1:
            raise TypeError("descriptor snapshot requires the exact role inventory")
        object.__setattr__(self, "_state", state)
        object.__setattr__(self, "_seal", seal)
        object.__setattr__(self, "_closed", False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("descriptor snapshot cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("descriptor snapshot cannot be mutated")

    @property
    def root_path(self) -> Path:
        return self._state.root_path

    @property
    def roles(self) -> tuple[str, ...]:
        return tuple(row.role for row in self._state.artifacts)

    def path_for_role(self, role: str) -> Path:
        if type(role) is not str or role not in SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1:
            raise SpotV7DescriptorStagingRejectV1("descriptor_stage_artifact_role")
        return next(row.path for row in self._state.artifacts if row.role == role)

    def verify(self, manifest: CandidateSpotV7FirecrackerRuntimeManifestV1) -> None:
        self._require_open()
        if type(manifest) is not CandidateSpotV7FirecrackerRuntimeManifestV1:
            raise TypeError("descriptor snapshot requires an exact manifest")
        _verify_snapshot_directory(self._state, manifest)
        expected_by_role = {row.role: row for row in manifest.artifacts}
        for row in self._state.artifacts:
            _verify_snapshot_artifact(
                row,
                expected_by_role[row.role],
                self._state.directory_fd,
            )

    def close_and_remove(self) -> None:
        if self._closed:
            return
        try:
            _close_and_remove_snapshot(self._state)
        finally:
            object.__setattr__(self, "_closed", True)

    def _require_open(self) -> None:
        if self._closed or self._seal is not _SNAPSHOT_SEAL_V1:
            raise SpotV7DescriptorStagingRejectV1(
                "descriptor_stage_snapshot_closed"
            )


def _create_snapshot_v1(
    inputs: _SnapshotCreateInputsV1,
) -> _RetainedSpotV7LaunchSnapshotV1:
    parent_fd = _open_snapshot_parent(inputs)
    directory_fd = -1
    artifacts: tuple[_SnapshotArtifactV1, ...] = ()
    try:
        directory_fd = _create_snapshot_directory(inputs, parent_fd)
        artifacts = _copy_snapshot_artifacts(inputs, directory_fd)
        os.fchmod(directory_fd, 0o555)
        os.fsync(directory_fd)
        state = _SnapshotStateV1(
            root_path=inputs.root / inputs.stage_name,
            stage_name=inputs.stage_name,
            parent_fd=parent_fd,
            directory_fd=directory_fd,
            artifacts=artifacts,
            trusted_uid=inputs.trusted_uid,
        )
        result = _RetainedSpotV7LaunchSnapshotV1(
            state=state,
            seal=_SNAPSHOT_SEAL_V1,
        )
        result.verify(inputs.manifest)
        return result
    except BaseException:
        _cleanup_partial_snapshot(
            stage_name=inputs.stage_name,
            parent_fd=parent_fd,
            directory_fd=directory_fd,
            artifacts=artifacts,
        )
        raise


def _jail_artifacts_v1(
    snapshot: _RetainedSpotV7LaunchSnapshotV1,
    manifest: CandidateSpotV7FirecrackerRuntimeManifestV1,
) -> tuple[RootOwnedStagedArtifactV2, ...]:
    expected = {row.role: row for row in manifest.artifacts}
    return tuple(
        RootOwnedStagedArtifactV2(
            role=role,
            source_path=snapshot.path_for_role(role),
            sha256=expected[role].sha256.hex(),
            size_bytes=expected[role].size_bytes,
        )
        for role in _JAIL_RESOURCE_ROLES_V1
    )


def _pin_snapshot_executable_v1(
    snapshot: _RetainedSpotV7LaunchSnapshotV1,
    manifest: CandidateSpotV7FirecrackerRuntimeManifestV1,
    *,
    role: str,
    trusted_root: Path,
    trusted_uid: int,
) -> PinnedExecutableV1:
    expected = next(row for row in manifest.artifacts if row.role == role)
    try:
        return open_pinned_executable(
            path=snapshot.path_for_role(role),
            expectation=ExecutableExpectationV1(
                sha256=expected.sha256.hex(),
                size_bytes=expected.size_bytes,
            ),
            trusted_root=trusted_root,
            trusted_uid=trusted_uid,
        )
    except JailerLauncherReject as exc:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_executable_prepare"
        ) from exc


def _open_snapshot_parent(inputs: _SnapshotCreateInputsV1) -> int:
    try:
        return staging_io._open_trusted_directory_path(
            inputs.root,
            trusted_root=inputs.trusted_root,
            trusted_uid=inputs.trusted_uid,
        )
    except (JailerLauncherReject, OSError) as exc:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_root"
        ) from exc


def _create_snapshot_directory(inputs: _SnapshotCreateInputsV1, parent_fd: int) -> int:
    try:
        os.mkdir(inputs.stage_name, 0o700, dir_fd=parent_fd)
        return staging_io.open_directory_at(
            parent_fd,
            inputs.stage_name,
            inputs.trusted_uid,
        )
    except (JailerLauncherReject, OSError) as exc:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_not_fresh"
        ) from exc


def _copy_snapshot_artifacts(
    inputs: _SnapshotCreateInputsV1,
    directory_fd: int,
) -> tuple[_SnapshotArtifactV1, ...]:
    rows: list[_SnapshotArtifactV1] = []
    try:
        for record, expected in zip(
            inputs.records,
            inputs.manifest.artifacts,
            strict=True,
        ):
            descriptor = _copy_one_snapshot_artifact(
                record,
                expected,
                directory_fd=directory_fd,
                trusted_uid=inputs.trusted_uid,
            )
            rows.append(
                _snapshot_row(
                    descriptor,
                    expected,
                    root=inputs.root / inputs.stage_name,
                )
            )
    except BaseException:
        for row in rows:
            _close_fd(row.descriptor)
        raise
    return tuple(rows)


def _copy_one_snapshot_artifact(
    record: _OpenedRuntimeArtifactV1,
    expected: SpotV7RuntimeArtifactIdentityV1,
    *,
    directory_fd: int,
    trusted_uid: int,
) -> int:
    descriptor = -1
    try:
        descriptor = staging_io.copy_exact_artifact(
            source_fd=record.descriptor,
            destination_dir_fd=directory_fd,
            role=expected.artifact_name,
            expected_sha256=expected.sha256.hex(),
            expected_size=expected.size_bytes,
            trusted_uid=trusted_uid,
        )
        if expected.role in _EXECUTABLE_ROLES_V1:
            os.fchmod(descriptor, 0o555)
            os.fsync(descriptor)
        return descriptor
    except (JailerLauncherReject, OSError) as exc:
        _close_fd(descriptor)
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_copy"
        ) from exc


def _snapshot_row(
    descriptor: int,
    expected: SpotV7RuntimeArtifactIdentityV1,
    *,
    root: Path,
) -> _SnapshotArtifactV1:
    try:
        version = staging_io.file_version(os.fstat(descriptor))
    except OSError as exc:
        _close_fd(descriptor)
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_copy"
        ) from exc
    return _SnapshotArtifactV1(
        role=expected.role,
        artifact_name=expected.artifact_name,
        path=root / expected.artifact_name,
        descriptor=descriptor,
        version=version,
        sha256=expected.sha256.hex(),
        size_bytes=expected.size_bytes,
    )


def _verify_snapshot_directory(
    state: _SnapshotStateV1,
    manifest: CandidateSpotV7FirecrackerRuntimeManifestV1,
) -> None:
    try:
        current = os.stat(
            state.stage_name,
            dir_fd=state.parent_fd,
            follow_symlinks=False,
        )
        opened = os.fstat(state.directory_fd)
        names = set(os.listdir(state.directory_fd))
    except OSError as exc:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_identity"
        ) from exc
    expected_names = {row.artifact_name for row in manifest.artifacts}
    if (
        (current.st_dev, current.st_ino) != (opened.st_dev, opened.st_ino)
        or not stat.S_ISDIR(opened.st_mode)
        or opened.st_uid != state.trusted_uid
        or stat.S_IMODE(opened.st_mode) & 0o022
        or names != expected_names
    ):
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_identity"
        )


def _verify_snapshot_artifact(
    row: _SnapshotArtifactV1,
    expected: SpotV7RuntimeArtifactIdentityV1,
    directory_fd: int,
) -> None:
    try:
        current = os.stat(
            row.artifact_name,
            dir_fd=directory_fd,
            follow_symlinks=False,
        )
        opened = os.fstat(row.descriptor)
    except OSError as exc:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_artifact_identity"
        ) from exc
    version = staging_io.file_version(opened)
    expected_mode = 0o555 if row.role in _EXECUTABLE_ROLES_V1 else 0o444
    if (
        row.role != expected.role
        or row.artifact_name != expected.artifact_name
        or row.sha256 != expected.sha256.hex()
        or row.size_bytes != expected.size_bytes
        or (current.st_dev, current.st_ino) != (opened.st_dev, opened.st_ino)
        or not stat.S_ISREG(opened.st_mode)
        or opened.st_nlink != 1
        or stat.S_IMODE(opened.st_mode) != expected_mode
        or version != row.version
    ):
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_artifact_identity"
        )
    try:
        digest = staging_io.sha256_fd(row.descriptor, row.size_bytes)
    except (JailerLauncherReject, OSError) as exc:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_artifact_changed"
        ) from exc
    if digest != row.sha256:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_artifact_changed"
        )


def _close_and_remove_snapshot(state: _SnapshotStateV1) -> None:
    identity_ok, permission_error = _prepare_snapshot_removal(state)
    for row in state.artifacts:
        _close_fd(row.descriptor)
    _close_fd(state.directory_fd)
    removal_error: OSError | None = None
    if identity_ok:
        try:
            shutil.rmtree(state.stage_name, dir_fd=state.parent_fd)
        except OSError as exc:
            removal_error = exc
    _close_fd(state.parent_fd)
    if permission_error is not None or removal_error is not None:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_cleanup"
        ) from (permission_error if permission_error is not None else removal_error)
    if not identity_ok:
        raise SpotV7DescriptorStagingRejectV1(
            "descriptor_stage_snapshot_identity"
        )


def _prepare_snapshot_removal(
    state: _SnapshotStateV1,
) -> tuple[bool, OSError | None]:
    try:
        current = os.stat(
            state.stage_name,
            dir_fd=state.parent_fd,
            follow_symlinks=False,
        )
        opened = os.fstat(state.directory_fd)
        identity_ok = (current.st_dev, current.st_ino) == (
            opened.st_dev,
            opened.st_ino,
        )
        if identity_ok:
            os.fchmod(state.directory_fd, 0o700)
        return identity_ok, None
    except OSError as exc:
        return False, exc


def _cleanup_partial_snapshot(
    *,
    stage_name: str,
    parent_fd: int,
    directory_fd: int,
    artifacts: tuple[_SnapshotArtifactV1, ...],
) -> None:
    for row in artifacts:
        _close_fd(row.descriptor)
    if directory_fd >= 0:
        try:
            os.fchmod(directory_fd, 0o700)
        except OSError:
            pass
    _close_fd(directory_fd)
    try:
        shutil.rmtree(stage_name, dir_fd=parent_fd)
    except OSError:
        pass
    _close_fd(parent_fd)


def _close_fd(descriptor: int) -> None:
    if descriptor < 0:
        return
    try:
        os.close(descriptor)
    except OSError:
        pass
