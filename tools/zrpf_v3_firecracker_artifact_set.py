"""Stable local byte binding for candidate ZRPF Firecracker artifacts.

The returned identity object deliberately contains no path or open descriptor.
It records a completed local comparison and cannot authorize later path reuse.
"""

from __future__ import annotations

import hashlib
import importlib
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from tools.zrpf_v3_firecracker_runtime_manifest import (
        ArtifactIdentityV1,
        PinnedRuntimeManifestV1,
    )

_MODULE_PREFIX = "tools." if __package__ else ""
runtime = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_runtime_manifest")


class ArtifactSetError(ValueError):
    """Stable fail-closed error raised at the artifact byte boundary."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class BoundArtifactIdentityV1:
    role: str
    sha256: str
    size_bytes: int

    def to_document(self) -> dict[str, Any]:
        return {
            "role": self.role,
            "sha256": self.sha256,
            "size_bytes": self.size_bytes,
        }


@dataclass(frozen=True, slots=True, init=False)
class LocallyBoundRuntimeArtifactSetV1:
    """Exact local bytes matched a manifest; source and runtime remain untrusted."""

    artifact_set_id: str
    guest_kernel: BoundArtifactIdentityV1
    input_image: BoundArtifactIdentityV1
    rootfs: BoundArtifactIdentityV1

    def __new__(cls) -> LocallyBoundRuntimeArtifactSetV1:
        raise TypeError("LocallyBoundRuntimeArtifactSetV1 requires verified construction")

    @classmethod
    def _from_verified(
        cls,
        *,
        artifact_set_id: str,
        guest_kernel: BoundArtifactIdentityV1,
        input_image: BoundArtifactIdentityV1,
        rootfs: BoundArtifactIdentityV1,
    ) -> LocallyBoundRuntimeArtifactSetV1:
        value = object.__new__(cls)
        object.__setattr__(value, "artifact_set_id", artifact_set_id)
        object.__setattr__(value, "guest_kernel", guest_kernel)
        object.__setattr__(value, "input_image", input_image)
        object.__setattr__(value, "rootfs", rootfs)
        return value

    def to_document(self) -> dict[str, Any]:
        return {
            "artifact_set_id": self.artifact_set_id,
            "authority": {
                "artifact_source_authenticated": False,
                "microvm_replay_verified": False,
                "root_launcher_ready": False,
                "runtime_path_reuse_authorized": False,
            },
            "guest_kernel": self.guest_kernel.to_document(),
            "input_image": self.input_image.to_document(),
            "rootfs": self.rootfs.to_document(),
            "schema": "zenodex/zrpf_firecracker_locally_bound_artifact_set/v1",
            "status": "exact_local_bytes_matched_non_authoritative",
        }


def verify_artifact_set(
    root: Path,
    manifest: PinnedRuntimeManifestV1,
) -> LocallyBoundRuntimeArtifactSetV1:
    """Hash the exact three-file inventory through descriptor-relative reads."""

    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    try:
        root_descriptor = os.open(root, flags)
    except OSError as exc:
        raise ArtifactSetError("artifact_directory_rejected") from exc
    try:
        before = os.fstat(root_descriptor)
        if not stat.S_ISDIR(before.st_mode):
            raise ArtifactSetError("artifact_directory_rejected")
        expected = {
            manifest.guest_kernel.artifact.artifact_name,
            manifest.input_image.artifact.artifact_name,
            manifest.rootfs.artifact.artifact_name,
        }
        try:
            inventory = os.listdir(root_descriptor)
        except OSError as exc:
            raise ArtifactSetError("artifact_inventory_rejected") from exc
        if len(inventory) != 3 or set(inventory) != expected:
            raise ArtifactSetError("artifact_inventory_rejected")
        kernel = _bind_artifact(
            root_descriptor,
            role="guest_kernel",
            identity=manifest.guest_kernel.artifact,
        )
        input_image = _bind_artifact(
            root_descriptor,
            role="input_image",
            identity=manifest.input_image.artifact,
        )
        rootfs = _bind_artifact(
            root_descriptor,
            role="rootfs",
            identity=manifest.rootfs.artifact,
        )
        after = os.fstat(root_descriptor)
        if _directory_identity(before) != _directory_identity(after):
            raise ArtifactSetError("artifact_directory_changed")
    except OSError as exc:
        raise ArtifactSetError("artifact_input_rejected") from exc
    finally:
        os.close(root_descriptor)
    return LocallyBoundRuntimeArtifactSetV1._from_verified(
        artifact_set_id=manifest.artifact_set_id,
        guest_kernel=kernel,
        input_image=input_image,
        rootfs=rootfs,
    )


def _bind_artifact(
    root_descriptor: int,
    *,
    role: str,
    identity: ArtifactIdentityV1,
) -> BoundArtifactIdentityV1:
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        descriptor = os.open(identity.artifact_name, flags, dir_fd=root_descriptor)
    except OSError as exc:
        raise ArtifactSetError("artifact_input_rejected") from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
            raise ArtifactSetError("artifact_input_rejected")
        if before.st_size != identity.size_bytes:
            raise ArtifactSetError("artifact_size_mismatch")
        digest = hashlib.sha256()
        remaining = before.st_size
        while remaining:
            try:
                chunk = os.read(descriptor, min(1024 * 1024, remaining))
            except OSError as exc:
                raise ArtifactSetError("artifact_input_rejected") from exc
            if not chunk:
                raise ArtifactSetError("artifact_changed_while_reading")
            digest.update(chunk)
            remaining -= len(chunk)
        try:
            if os.read(descriptor, 1):
                raise ArtifactSetError("artifact_changed_while_reading")
            after = os.fstat(descriptor)
        except OSError as exc:
            raise ArtifactSetError("artifact_input_rejected") from exc
        if _file_identity(before) != _file_identity(after):
            raise ArtifactSetError("artifact_changed_while_reading")
        actual_digest = digest.hexdigest()
        if actual_digest != identity.sha256:
            raise ArtifactSetError("artifact_sha256_mismatch")
        return BoundArtifactIdentityV1(role, actual_digest, before.st_size)
    finally:
        os.close(descriptor)


def _directory_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _file_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_nlink,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )
