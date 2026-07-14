"""Root-owned, descriptor-retained staging for one Firecracker jail.

The Firecracker jailer requires every configuration and block-device resource
to already exist below the jail root.  This module lets the supervising root
process create that exact, unique root before Jailer starts while retaining
descriptors for every authority-relevant file.  A pre-existing jail ID always
rejects.  Successful staging is still not VM, proof, release, or settlement
authority.
"""

from __future__ import annotations

import os
import shutil
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Final, NoReturn, SupportsIndex, final

from tools import zrpf_v3_firecracker_jail_staging_io as staging_io
from tools.zrpf_v3_firecracker_output_protocol import (
    OUTPUT_BYTES_V1,
    REQUEST_BYTES_V1,
    decode_request,
    validate_committed_output,
)
from tools.zrpf_v3_firecracker_trusted_runtime import JailerLauncherReject

_RESOURCE_DIRECTORY_NAME: Final = "resources"
_RESOURCE_NAMES: Final = ("config.json", "input", "kernel", "output", "rootfs")
_READ_ONLY_ARTIFACT_ROLES: Final = ("input", "kernel", "rootfs")


@dataclass(frozen=True, slots=True)
class RootOwnedStagedArtifactV2:
    """One governed source artifact copied into the private jail."""

    role: str
    source_path: Path
    sha256: str
    size_bytes: int

    def __post_init__(self) -> None:
        if self.role not in _READ_ONLY_ARTIFACT_ROLES:
            raise JailerLauncherReject("jail_stage_artifact_role_invalid")
        if not self.source_path.is_absolute():
            raise JailerLauncherReject("jail_stage_artifact_path_invalid")
        if (
            type(self.sha256) is not str
            or len(self.sha256) != 64
            or any(character not in "0123456789abcdef" for character in self.sha256)
            or self.sha256 == "0" * 64
            or type(self.size_bytes) is not int
            or not 0 < self.size_bytes <= 4 * 1024 * 1024 * 1024
        ):
            raise JailerLauncherReject("jail_stage_artifact_expectation_invalid")


@dataclass(frozen=True, slots=True)
class PreparedJailRootSpecV2:
    """Exact path and ownership allocation for one supervisor-created jail."""

    jail_id: str
    firecracker_file_name: str
    chroot_base_dir: Path
    runtime_uid: int
    runtime_gid: int
    trusted_uid: int = 0

    def __post_init__(self) -> None:
        if (
            not 8 <= len(self.jail_id) <= 64
            or not self.jail_id.isascii()
            or not self.jail_id[0].isalnum()
            or any(
                not (character.islower() or character.isdigit() or character == "-")
                for character in self.jail_id
            )
        ):
            raise JailerLauncherReject("jail_stage_id_invalid")
        if (
            not self.firecracker_file_name
            or "/" in self.firecracker_file_name
            or self.firecracker_file_name in {".", ".."}
        ):
            raise JailerLauncherReject("jail_stage_executable_name_invalid")
        if not self.chroot_base_dir.is_absolute():
            raise JailerLauncherReject("jail_stage_base_path_invalid")
        for value in (self.runtime_uid, self.runtime_gid):
            if type(value) is not int or not 1 <= value <= (1 << 31) - 1:
                raise JailerLauncherReject("jail_stage_runtime_identity_invalid")
        if type(self.trusted_uid) is not int or not 0 <= self.trusted_uid <= (1 << 31) - 1:
            raise JailerLauncherReject("jail_stage_trusted_uid_invalid")

    @property
    def jail_root_path(self) -> Path:
        return self.chroot_base_dir / self.firecracker_file_name / self.jail_id / "root"

    @property
    def config_path_in_jail(self) -> str:
        return "/resources/config.json"


class _PreparedJailRootSealV2:
    __slots__ = ()


_PREPARED_JAIL_ROOT_SEAL_V2 = _PreparedJailRootSealV2()


@final
class PreparedJailRootV2:
    """One-shot staged jail whose exact resource descriptors remain open."""

    __slots__ = (
        "_closed",
        "_exec_dir_fd",
        "_file_fds",
        "_file_versions",
        "_jail_dir_fd",
        "_request_bytes",
        "_resources_dir_fd",
        "_root_dir_fd",
        "_seal",
        "_spec",
    )

    _closed: bool
    _exec_dir_fd: int
    _file_fds: dict[str, int]
    _file_versions: dict[str, staging_io.FileVersionV2]
    _jail_dir_fd: int
    _request_bytes: bytes
    _resources_dir_fd: int
    _root_dir_fd: int
    _seal: _PreparedJailRootSealV2
    _spec: PreparedJailRootSpecV2

    def __init__(
        self,
        *,
        spec: PreparedJailRootSpecV2,
        exec_dir_fd: int,
        jail_dir_fd: int,
        root_dir_fd: int,
        resources_dir_fd: int,
        file_fds: dict[str, int],
        file_versions: dict[str, staging_io.FileVersionV2],
        request_bytes: bytes,
        seal: _PreparedJailRootSealV2,
    ) -> None:
        if seal is not _PREPARED_JAIL_ROOT_SEAL_V2:
            raise TypeError("prepared jail root requires the module-private seal")
        object.__setattr__(self, "_spec", spec)
        object.__setattr__(self, "_exec_dir_fd", exec_dir_fd)
        object.__setattr__(self, "_jail_dir_fd", jail_dir_fd)
        object.__setattr__(self, "_root_dir_fd", root_dir_fd)
        object.__setattr__(self, "_resources_dir_fd", resources_dir_fd)
        object.__setattr__(self, "_file_fds", file_fds)
        object.__setattr__(self, "_file_versions", file_versions)
        object.__setattr__(self, "_request_bytes", request_bytes)
        object.__setattr__(self, "_seal", seal)
        object.__setattr__(self, "_closed", False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PreparedJailRootV2 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("prepared jail root cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("prepared jail root cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("prepared jail root cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("prepared jail root cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("prepared jail root cannot be serialized")

    @property
    def spec(self) -> PreparedJailRootSpecV2:
        return self._spec

    @property
    def jail_root_path(self) -> Path:
        return self._spec.jail_root_path

    def verify_prelaunch(self) -> None:
        """Require the exact initial inventory and request-bearing output."""

        self._require_open()
        self._require_directory_identities(prelaunch=True)
        if set(os.listdir(self._root_dir_fd)) != {_RESOURCE_DIRECTORY_NAME}:
            raise JailerLauncherReject("jail_stage_root_inventory_changed")
        if set(os.listdir(self._resources_dir_fd)) != set(_RESOURCE_NAMES):
            raise JailerLauncherReject("jail_stage_resource_inventory_changed")
        self._reverify_immutable_resources()
        output = self._reverify_file("output", mutable=True)
        if output.size != OUTPUT_BYTES_V1:
            raise JailerLauncherReject("jail_stage_output_size_changed")
        if (
            staging_io.pread_exact(self._file_fds["output"], REQUEST_BYTES_V1, 0)
            != self._request_bytes
        ):
            raise JailerLauncherReject("jail_stage_request_changed")
        if staging_io.region_has_nonzero(
            self._file_fds["output"],
            start=REQUEST_BYTES_V1,
            size=OUTPUT_BYTES_V1 - REQUEST_BYTES_V1,
        ):
            raise JailerLauncherReject("jail_stage_output_not_fresh")

    def read_output_after_exit(self) -> bytes:
        """Read one stable output through the descriptor retained since creation."""

        self._require_open()
        self._require_directory_identities(prelaunch=False)
        self._reverify_immutable_resources()
        before = self._reverify_file("output", mutable=True)
        if before.size != OUTPUT_BYTES_V1:
            raise JailerLauncherReject("jail_stage_output_size_changed")
        raw = staging_io.pread_exact(self._file_fds["output"], OUTPUT_BYTES_V1, 0)
        after = self._reverify_file("output", mutable=True)
        if before != after:
            raise JailerLauncherReject("jail_stage_output_changed_while_reading")
        return raw

    def read_validated_output_after_exit(self) -> bytes:
        """Require the exact request-bound committed outer output protocol."""

        raw = self.read_output_after_exit()
        try:
            validate_committed_output(raw, decode_request(self._request_bytes))
        except ValueError as exc:
            raise JailerLauncherReject("jail_stage_output_protocol_rejected") from exc
        return raw

    def cleanup_after_teardown(self) -> None:
        """Remove the unique jail tree after the caller has emptied the cgroup."""

        self._require_open()
        self._require_directory_identities(prelaunch=False)
        try:
            os.fchmod(self._resources_dir_fd, 0o700)
        except OSError as exc:
            raise JailerLauncherReject("jail_stage_cleanup_permissions_failed") from exc
        self._close_inner_descriptors()
        try:
            current = os.stat(
                self._spec.jail_id,
                dir_fd=self._exec_dir_fd,
                follow_symlinks=False,
            )
            opened = os.fstat(self._jail_dir_fd)
            if (current.st_dev, current.st_ino) != (opened.st_dev, opened.st_ino):
                raise JailerLauncherReject("jail_stage_jail_identity_changed")
            os.close(self._jail_dir_fd)
            object.__setattr__(self, "_jail_dir_fd", -1)
            shutil.rmtree(self._spec.jail_id, dir_fd=self._exec_dir_fd)
            try:
                os.stat(
                    self._spec.jail_id,
                    dir_fd=self._exec_dir_fd,
                    follow_symlinks=False,
                )
            except FileNotFoundError:
                pass
            else:
                raise JailerLauncherReject("jail_stage_cleanup_incomplete")
        except OSError as exc:
            raise JailerLauncherReject("jail_stage_cleanup_failed") from exc
        finally:
            if self._exec_dir_fd >= 0:
                os.close(self._exec_dir_fd)
                object.__setattr__(self, "_exec_dir_fd", -1)
            object.__setattr__(self, "_closed", True)

    def abandon_before_launch(self) -> None:
        """Remove a prepared jail that was never handed to Jailer."""

        self.cleanup_after_teardown()

    def _require_open(self) -> None:
        if self._closed or self._seal is not _PREPARED_JAIL_ROOT_SEAL_V2:
            raise JailerLauncherReject("jail_stage_closed")

    def _require_directory_identities(self, *, prelaunch: bool) -> None:
        jail_current = os.stat(
            self._spec.jail_id,
            dir_fd=self._exec_dir_fd,
            follow_symlinks=False,
        )
        jail_opened = os.fstat(self._jail_dir_fd)
        root_current = os.stat("root", dir_fd=self._jail_dir_fd, follow_symlinks=False)
        root_opened = os.fstat(self._root_dir_fd)
        resources_current = os.stat(
            _RESOURCE_DIRECTORY_NAME,
            dir_fd=self._root_dir_fd,
            follow_symlinks=False,
        )
        resources_opened = os.fstat(self._resources_dir_fd)
        for current, opened, code in (
            (jail_current, jail_opened, "jail_stage_jail_identity_changed"),
            (root_current, root_opened, "jail_stage_root_identity_changed"),
            (
                resources_current,
                resources_opened,
                "jail_stage_resources_identity_changed",
            ),
        ):
            if (current.st_dev, current.st_ino) != (
                opened.st_dev,
                opened.st_ino,
            ) or not stat.S_ISDIR(opened.st_mode):
                raise JailerLauncherReject(code)
        for metadata, code in (
            (jail_opened, "jail_stage_jail_permissions_changed"),
            (resources_opened, "jail_stage_resources_permissions_changed"),
        ):
            if metadata.st_uid != self._spec.trusted_uid or stat.S_IMODE(metadata.st_mode) & 0o022:
                raise JailerLauncherReject(code)
        if prelaunch and (
            root_opened.st_uid != self._spec.trusted_uid
            or stat.S_IMODE(root_opened.st_mode) & 0o022
        ):
            raise JailerLauncherReject("jail_stage_root_permissions_changed")

    def _reverify_immutable_resources(self) -> None:
        for name in ("config.json", "input", "kernel", "rootfs"):
            current = self._reverify_file(name, mutable=False)
            if current != self._file_versions[name]:
                raise JailerLauncherReject("jail_stage_immutable_resource_changed")

    def _reverify_file(
        self,
        name: str,
        *,
        mutable: bool,
    ) -> staging_io.FileVersionV2:
        try:
            current = os.stat(name, dir_fd=self._resources_dir_fd, follow_symlinks=False)
            opened = os.fstat(self._file_fds[name])
        except OSError as exc:
            raise JailerLauncherReject("jail_stage_resource_identity_changed") from exc
        if (
            (current.st_dev, current.st_ino) != (opened.st_dev, opened.st_ino)
            or not stat.S_ISREG(opened.st_mode)
            or opened.st_nlink != 1
        ):
            raise JailerLauncherReject("jail_stage_resource_identity_changed")
        version = staging_io.file_version(opened)
        expected = self._file_versions[name]
        if mutable:
            if (
                version.device,
                version.inode,
                version.mode,
                version.uid,
                version.gid,
                version.links,
            ) != (
                expected.device,
                expected.inode,
                expected.mode,
                expected.uid,
                expected.gid,
                expected.links,
            ):
                raise JailerLauncherReject("jail_stage_output_identity_changed")
        return version

    def _close_inner_descriptors(self) -> None:
        for descriptor in self._file_fds.values():
            if descriptor >= 0:
                os.close(descriptor)
        self._file_fds.clear()
        for name in ("_resources_dir_fd", "_root_dir_fd"):
            descriptor = getattr(self, name)
            if descriptor >= 0:
                os.close(descriptor)
                object.__setattr__(self, name, -1)


def prepare_root_owned_jail_v2(
    *,
    spec: PreparedJailRootSpecV2,
    artifacts: tuple[RootOwnedStagedArtifactV2, ...],
    config_bytes: bytes,
    request_bytes: bytes,
    trusted_chroot_root: Path = Path("/"),
    trusted_source_root: Path = Path("/"),
) -> PreparedJailRootV2:
    """Create a unique staged jail and retain every authority-relevant fd."""

    _validate_prepare_inputs(spec, artifacts, config_bytes, request_bytes)
    exec_dir_fd = staging_io.open_exec_directory(
        chroot_base_dir=spec.chroot_base_dir,
        firecracker_file_name=spec.firecracker_file_name,
        trusted_root=trusted_chroot_root,
        trusted_uid=spec.trusted_uid,
    )
    try:
        jail_dir_fd, root_dir_fd, resources_dir_fd = _create_staging_directories(
            exec_dir_fd,
            spec,
        )
    except BaseException:
        os.close(exec_dir_fd)
        raise
    file_fds: dict[str, int] = {}
    try:
        file_fds = _stage_resource_files(
            resources_dir_fd,
            artifacts=artifacts,
            config_bytes=config_bytes,
            request_bytes=request_bytes,
            spec=spec,
            trusted_source_root=trusted_source_root,
        )
        prepared = PreparedJailRootV2(
            spec=spec,
            exec_dir_fd=exec_dir_fd,
            jail_dir_fd=jail_dir_fd,
            root_dir_fd=root_dir_fd,
            resources_dir_fd=resources_dir_fd,
            file_fds=file_fds,
            file_versions=_capture_file_versions(file_fds),
            request_bytes=request_bytes,
            seal=_PREPARED_JAIL_ROOT_SEAL_V2,
        )
        prepared.verify_prelaunch()
        return prepared
    except BaseException:
        _cleanup_failed_preparation(
            exec_dir_fd=exec_dir_fd,
            jail_dir_fd=jail_dir_fd,
            root_dir_fd=root_dir_fd,
            resources_dir_fd=resources_dir_fd,
            file_fds=file_fds,
            jail_id=spec.jail_id,
        )
        raise


def _validate_prepare_inputs(
    spec: PreparedJailRootSpecV2,
    artifacts: tuple[RootOwnedStagedArtifactV2, ...],
    config_bytes: bytes,
    request_bytes: bytes,
) -> None:
    if type(spec) is not PreparedJailRootSpecV2:
        raise TypeError("spec must be exact PreparedJailRootSpecV2")
    if tuple(sorted(artifact.role for artifact in artifacts)) != _READ_ONLY_ARTIFACT_ROLES:
        raise JailerLauncherReject("jail_stage_artifact_inventory_invalid")
    if any(type(artifact) is not RootOwnedStagedArtifactV2 for artifact in artifacts):
        raise TypeError("artifacts must contain exact RootOwnedStagedArtifactV2 values")
    staging_io.validate_config_bytes(config_bytes)
    if type(request_bytes) is not bytes or len(request_bytes) != REQUEST_BYTES_V1:
        raise JailerLauncherReject("jail_stage_request_invalid")
    try:
        decoded_request = decode_request(request_bytes)
    except ValueError as exc:
        raise JailerLauncherReject("jail_stage_request_invalid") from exc
    if decoded_request.encode() != request_bytes:
        raise JailerLauncherReject("jail_stage_request_noncanonical")


def _create_staging_directories(
    exec_dir_fd: int,
    spec: PreparedJailRootSpecV2,
) -> tuple[int, int, int]:
    os.mkdir(spec.jail_id, 0o700, dir_fd=exec_dir_fd)
    jail_dir_fd = root_dir_fd = resources_dir_fd = -1
    try:
        jail_dir_fd = staging_io.open_directory_at(
            exec_dir_fd,
            spec.jail_id,
            spec.trusted_uid,
        )
        os.mkdir("root", 0o700, dir_fd=jail_dir_fd)
        root_dir_fd = staging_io.open_directory_at(
            jail_dir_fd,
            "root",
            spec.trusted_uid,
        )
        os.mkdir(_RESOURCE_DIRECTORY_NAME, 0o700, dir_fd=root_dir_fd)
        resources_dir_fd = staging_io.open_directory_at(
            root_dir_fd,
            _RESOURCE_DIRECTORY_NAME,
            spec.trusted_uid,
        )
        return jail_dir_fd, root_dir_fd, resources_dir_fd
    except BaseException:
        for descriptor in (resources_dir_fd, root_dir_fd, jail_dir_fd):
            if descriptor >= 0:
                os.close(descriptor)
        try:
            shutil.rmtree(spec.jail_id, dir_fd=exec_dir_fd)
        except OSError:
            pass
        raise


def _stage_resource_files(
    resources_dir_fd: int,
    *,
    artifacts: tuple[RootOwnedStagedArtifactV2, ...],
    config_bytes: bytes,
    request_bytes: bytes,
    spec: PreparedJailRootSpecV2,
    trusted_source_root: Path,
) -> dict[str, int]:
    file_fds: dict[str, int] = {}
    try:
        for artifact in artifacts:
            source_fd = staging_io.open_trusted_source(
                artifact.source_path,
                trusted_root=trusted_source_root,
                trusted_uid=spec.trusted_uid,
            )
            try:
                file_fds[artifact.role] = staging_io.copy_exact_artifact(
                    source_fd=source_fd,
                    destination_dir_fd=resources_dir_fd,
                    role=artifact.role,
                    expected_sha256=artifact.sha256,
                    expected_size=artifact.size_bytes,
                    trusted_uid=spec.trusted_uid,
                )
            finally:
                os.close(source_fd)
        file_fds["config.json"] = staging_io.create_exact_file(
            resources_dir_fd,
            "config.json",
            config_bytes,
            uid=spec.trusted_uid,
            gid=0 if spec.trusted_uid == 0 else os.getgid(),
            mode=0o444,
        )
        file_fds["output"] = staging_io.create_fresh_output(
            resources_dir_fd,
            request_bytes,
            uid=spec.runtime_uid,
            gid=spec.runtime_gid,
        )
        os.fchmod(resources_dir_fd, 0o555)
        os.fsync(resources_dir_fd)
        return file_fds
    except BaseException:
        for descriptor in file_fds.values():
            try:
                os.close(descriptor)
            except OSError:
                pass
        raise


def _capture_file_versions(
    file_fds: dict[str, int],
) -> dict[str, staging_io.FileVersionV2]:
    return {
        name: staging_io.file_version(os.fstat(descriptor)) for name, descriptor in file_fds.items()
    }


def _cleanup_failed_preparation(
    *,
    exec_dir_fd: int,
    jail_dir_fd: int,
    root_dir_fd: int,
    resources_dir_fd: int,
    file_fds: dict[str, int],
    jail_id: str,
) -> None:
    if resources_dir_fd >= 0:
        try:
            os.fchmod(resources_dir_fd, 0o700)
        except OSError:
            pass
    for descriptor in file_fds.values():
        try:
            os.close(descriptor)
        except OSError:
            pass
    for descriptor in (resources_dir_fd, root_dir_fd, jail_dir_fd):
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass
    try:
        shutil.rmtree(jail_id, dir_fd=exec_dir_fd)
    except OSError:
        pass
    os.close(exec_dir_fd)
