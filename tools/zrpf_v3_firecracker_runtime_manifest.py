"""Typed, non-authoritative runtime identities for a future ZRPF microVM.

This module validates identity records only.  It does not download, mount,
execute, or authorize any artifact.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any
from urllib.parse import urlsplit

SCHEMA = "zenodex/zrpf_firecracker_runtime_artifact_manifest/v1"
STATUS = "candidate_frozen_identity_non_authoritative"
ARCHITECTURE = "x86_64"
PROFILE_CANONICAL_SHA256 = "3be22c7d06bc3c4a7f0d83065fe2cadbb7b284830a70797165e32e229a1bdd0f"
INPUT_PROTOCOL_ID = "zenodex/zrpf_firecracker_input_squashfs/v1"
REQUEST_PROTOCOL_ID = "zenodex/zrpf_firecracker_request/v1"
OUTPUT_PROTOCOL_ID = "zenodex/zrpf_firecracker_output/v1"
OUTPUT_SIZE_BYTES = 16_777_216
PAYLOAD_CAP_BYTES = 65_536

MAX_MANIFEST_BYTES = 256 * 1024
MAX_KERNEL_BYTES = 256 * 1024 * 1024
MAX_ROOTFS_BYTES = 4 * 1024 * 1024 * 1024
MAX_INPUT_IMAGE_BYTES = 16 * 1024 * 1024
MAX_PAYLOAD_FILE_BYTES = 256 * 1024 * 1024
SQUASHFS_BLOCK_SIZE_BYTES = 131_072
SQUASHFS_BUILD_EPOCH = 1_780_396_050

AUTHORITY_FIELDS = (
    "artifact_format_verified",
    "guest_boot_verified",
    "microvm_replay_verified",
    "production_authority",
    "release_authority",
    "root_launcher_ready",
    "runtime_artifacts_locally_verified",
    "sandbox_escape_resistance",
    "settlement_authority",
    "witness_privacy",
    "zero_knowledge_privacy",
)
NON_CLAIMS = (
    "no artifact source authenticity or reproducible-build claim",
    "no root-owned launcher, sandbox, microVM replay, or escape-resistance claim",
    "no release, settlement, ledger-admission, production, privacy, or zero-knowledge claim",
)

_ROOT_FIELDS = {
    "architecture",
    "artifact_set_id",
    "authority",
    "boot_contract",
    "firecracker_profile_canonical_sha256",
    "guest_kernel",
    "guest_payload",
    "input_image",
    "non_claims",
    "provenance",
    "rootfs",
    "schema",
    "status",
}
_KERNEL_FIELDS = {
    "artifact_name",
    "base_config_sha256",
    "build_container_image_id",
    "build_recipe_sha256",
    "byte_identical_local_rebuild",
    "ci_config_sha256",
    "hardening_fragment_sha256",
    "image_format",
    "kernel_config_sha256",
    "kernel_release",
    "sha256",
    "size_bytes",
    "source_commit",
    "source_repository",
    "source_tag",
    "source_tag_object",
    "source_tree",
    "support_minimum_end_date",
}
_ROOTFS_FIELDS = {
    "artifact_name",
    "compression",
    "filesystem_block_size_bytes",
    "filesystem_inventory_root",
    "guest_payload_manifest_sha256",
    "image_format",
    "mkfs_epoch",
    "sha256",
    "size_bytes",
}
_INPUT_IMAGE_FIELDS = {
    "artifact_name",
    "compression",
    "filesystem_block_size_bytes",
    "filesystem_inventory_root",
    "image_format",
    "input_bundle_root",
    "mkfs_epoch",
    "receipt_count",
    "sha256",
    "size_bytes",
}
_PAYLOAD_FIELDS = {
    "entrypoint_guest_path",
    "files",
    "input_protocol_id",
    "output_protocol_id",
    "output_size_bytes",
    "payload_cap_bytes",
    "request_protocol_id",
    "runtime_linkage",
}
_PAYLOAD_FILE_FIELDS = {"guest_path", "mode", "role", "sha256", "size_bytes"}
_BOOT_FIELDS = {
    "init_guest_path",
    "kernel_cmdline",
    "panic_policy",
    "root_device",
    "rootfs_read_only",
    "serial_policy",
}
_PROVENANCE_FIELDS = {
    "guest_payload_source_commit",
    "input_build_recipe_sha256",
    "kernel_source_repository",
    "mksquashfs_binary_sha256",
    "mksquashfs_version",
    "rootfs_build_recipe_sha256",
    "status",
}


class RuntimeManifestError(ValueError):
    """Stable fail-closed error raised at the runtime-manifest boundary."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class ArtifactIdentityV1:
    artifact_name: str
    sha256: str
    size_bytes: int


@dataclass(frozen=True, slots=True)
class GuestKernelIdentityV1:
    artifact: ArtifactIdentityV1
    base_config_sha256: str
    build_container_image_id: str
    build_recipe_sha256: str
    byte_identical_local_rebuild: bool
    ci_config_sha256: str
    hardening_fragment_sha256: str
    image_format: str
    kernel_config_sha256: str
    kernel_release: str
    source_commit: str
    source_repository: str
    source_tag: str
    source_tag_object: str
    source_tree: str
    support_minimum_end_date: str


@dataclass(frozen=True, slots=True)
class RootfsIdentityV1:
    artifact: ArtifactIdentityV1
    compression: str
    filesystem_block_size_bytes: int
    filesystem_inventory_root: str
    guest_payload_manifest_sha256: str
    image_format: str
    mkfs_epoch: int


@dataclass(frozen=True, slots=True)
class InputImageIdentityV1:
    artifact: ArtifactIdentityV1
    compression: str
    filesystem_block_size_bytes: int
    filesystem_inventory_root: str
    image_format: str
    input_bundle_root: str
    mkfs_epoch: int
    receipt_count: int


@dataclass(frozen=True, slots=True)
class GuestPayloadFileV1:
    guest_path: str
    mode: str
    role: str
    sha256: str
    size_bytes: int

    def to_document(self) -> dict[str, Any]:
        return {
            "guest_path": self.guest_path,
            "mode": self.mode,
            "role": self.role,
            "sha256": self.sha256,
            "size_bytes": self.size_bytes,
        }


@dataclass(frozen=True, slots=True)
class GuestPayloadV1:
    files: tuple[GuestPayloadFileV1, ...]
    entrypoint_guest_path: str

    def to_document(self) -> dict[str, Any]:
        return {
            "entrypoint_guest_path": self.entrypoint_guest_path,
            "files": [row.to_document() for row in self.files],
            "input_protocol_id": INPUT_PROTOCOL_ID,
            "output_protocol_id": OUTPUT_PROTOCOL_ID,
            "output_size_bytes": OUTPUT_SIZE_BYTES,
            "payload_cap_bytes": PAYLOAD_CAP_BYTES,
            "request_protocol_id": REQUEST_PROTOCOL_ID,
            "runtime_linkage": "static_pie_glibc_no_pt_interp_no_dt_needed",
        }


@dataclass(frozen=True, slots=True)
class BootContractV1:
    init_guest_path: str
    kernel_cmdline: str

    def to_document(self) -> dict[str, Any]:
        return {
            "init_guest_path": self.init_guest_path,
            "kernel_cmdline": self.kernel_cmdline,
            "panic_policy": "panic=0_host_watchdog_reboot=k",
            "root_device": "/dev/vda",
            "rootfs_read_only": True,
            "serial_policy": "8250_disabled",
        }


@dataclass(frozen=True, slots=True)
class ProvenanceRecordV1:
    guest_payload_source_commit: str
    input_build_recipe_sha256: str
    kernel_source_repository: str
    mksquashfs_binary_sha256: str
    mksquashfs_version: str
    rootfs_build_recipe_sha256: str

    def to_document(self) -> dict[str, Any]:
        return {
            "guest_payload_source_commit": self.guest_payload_source_commit,
            "input_build_recipe_sha256": self.input_build_recipe_sha256,
            "kernel_source_repository": self.kernel_source_repository,
            "mksquashfs_binary_sha256": self.mksquashfs_binary_sha256,
            "mksquashfs_version": self.mksquashfs_version,
            "rootfs_build_recipe_sha256": self.rootfs_build_recipe_sha256,
            "status": "identity_pinned_source_build_not_reproduced",
        }


@dataclass(frozen=True, slots=True, init=False)
class PinnedRuntimeManifestV1:
    """Canonical identity contract; this type carries no execution authority."""

    artifact_set_id: str
    canonical_sha256: str
    guest_kernel: GuestKernelIdentityV1
    guest_payload: GuestPayloadV1
    input_image: InputImageIdentityV1
    rootfs: RootfsIdentityV1
    boot_contract: BootContractV1
    provenance: ProvenanceRecordV1

    def __new__(cls) -> PinnedRuntimeManifestV1:
        raise TypeError("PinnedRuntimeManifestV1 requires validated construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        artifact_set_id: str,
        canonical_sha256: str,
        guest_kernel: GuestKernelIdentityV1,
        guest_payload: GuestPayloadV1,
        input_image: InputImageIdentityV1,
        rootfs: RootfsIdentityV1,
        boot_contract: BootContractV1,
        provenance: ProvenanceRecordV1,
    ) -> PinnedRuntimeManifestV1:
        value = object.__new__(cls)
        object.__setattr__(value, "artifact_set_id", artifact_set_id)
        object.__setattr__(value, "canonical_sha256", canonical_sha256)
        object.__setattr__(value, "guest_kernel", guest_kernel)
        object.__setattr__(value, "guest_payload", guest_payload)
        object.__setattr__(value, "input_image", input_image)
        object.__setattr__(value, "rootfs", rootfs)
        object.__setattr__(value, "boot_contract", boot_contract)
        object.__setattr__(value, "provenance", provenance)
        return value

    def to_document(self) -> dict[str, Any]:
        kernel = {
            "artifact_name": self.guest_kernel.artifact.artifact_name,
            "base_config_sha256": self.guest_kernel.base_config_sha256,
            "build_container_image_id": self.guest_kernel.build_container_image_id,
            "build_recipe_sha256": self.guest_kernel.build_recipe_sha256,
            "byte_identical_local_rebuild": self.guest_kernel.byte_identical_local_rebuild,
            "ci_config_sha256": self.guest_kernel.ci_config_sha256,
            "hardening_fragment_sha256": self.guest_kernel.hardening_fragment_sha256,
            "image_format": self.guest_kernel.image_format,
            "kernel_config_sha256": self.guest_kernel.kernel_config_sha256,
            "kernel_release": self.guest_kernel.kernel_release,
            "sha256": self.guest_kernel.artifact.sha256,
            "size_bytes": self.guest_kernel.artifact.size_bytes,
            "source_commit": self.guest_kernel.source_commit,
            "source_repository": self.guest_kernel.source_repository,
            "source_tag": self.guest_kernel.source_tag,
            "source_tag_object": self.guest_kernel.source_tag_object,
            "source_tree": self.guest_kernel.source_tree,
            "support_minimum_end_date": self.guest_kernel.support_minimum_end_date,
        }
        rootfs = {
            "artifact_name": self.rootfs.artifact.artifact_name,
            "compression": self.rootfs.compression,
            "filesystem_block_size_bytes": self.rootfs.filesystem_block_size_bytes,
            "filesystem_inventory_root": self.rootfs.filesystem_inventory_root,
            "guest_payload_manifest_sha256": (self.rootfs.guest_payload_manifest_sha256),
            "image_format": self.rootfs.image_format,
            "mkfs_epoch": self.rootfs.mkfs_epoch,
            "sha256": self.rootfs.artifact.sha256,
            "size_bytes": self.rootfs.artifact.size_bytes,
        }
        input_image = {
            "artifact_name": self.input_image.artifact.artifact_name,
            "compression": self.input_image.compression,
            "filesystem_block_size_bytes": self.input_image.filesystem_block_size_bytes,
            "filesystem_inventory_root": self.input_image.filesystem_inventory_root,
            "image_format": self.input_image.image_format,
            "input_bundle_root": self.input_image.input_bundle_root,
            "mkfs_epoch": self.input_image.mkfs_epoch,
            "receipt_count": self.input_image.receipt_count,
            "sha256": self.input_image.artifact.sha256,
            "size_bytes": self.input_image.artifact.size_bytes,
        }
        return {
            "architecture": ARCHITECTURE,
            "artifact_set_id": self.artifact_set_id,
            "authority": {name: False for name in AUTHORITY_FIELDS},
            "boot_contract": self.boot_contract.to_document(),
            "firecracker_profile_canonical_sha256": PROFILE_CANONICAL_SHA256,
            "guest_kernel": kernel,
            "guest_payload": self.guest_payload.to_document(),
            "input_image": input_image,
            "non_claims": list(NON_CLAIMS),
            "provenance": self.provenance.to_document(),
            "rootfs": rootfs,
            "schema": SCHEMA,
            "status": STATUS,
        }


def parse_runtime_manifest_bytes(
    raw: bytes,
    *,
    expected_canonical_sha256: str | None = None,
) -> PinnedRuntimeManifestV1:
    """Strictly decode one canonical manifest and verify all derived bindings."""

    if not 0 < len(raw) <= MAX_MANIFEST_BYTES:
        raise RuntimeManifestError("runtime_manifest_input_rejected")
    try:
        document = _strict_json_loads(raw)
    except (RecursionError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise RuntimeManifestError("runtime_manifest_input_rejected") from exc
    if not isinstance(document, dict):
        raise RuntimeManifestError("runtime_manifest_root_not_object")
    if raw != canonical_document_bytes(document):
        raise RuntimeManifestError("runtime_manifest_noncanonical")
    _require_fields(document, _ROOT_FIELDS, "runtime_manifest_fields_mismatch")
    if document["schema"] != SCHEMA or document["status"] != STATUS:
        raise RuntimeManifestError("runtime_manifest_version_mismatch")
    if document["architecture"] != ARCHITECTURE:
        raise RuntimeManifestError("runtime_manifest_architecture_mismatch")
    if document["firecracker_profile_canonical_sha256"] != PROFILE_CANONICAL_SHA256:
        raise RuntimeManifestError("runtime_manifest_profile_binding_mismatch")
    _validate_authority(document["authority"])
    if document["non_claims"] != list(NON_CLAIMS):
        raise RuntimeManifestError("runtime_manifest_non_claims_mismatch")

    payload = _parse_payload(document["guest_payload"])
    kernel = _parse_kernel(document["guest_kernel"])
    rootfs = _parse_rootfs(document["rootfs"], payload)
    input_image = _parse_input_image(document["input_image"])
    boot = _parse_boot_contract(document["boot_contract"], payload)
    provenance = _parse_provenance(document["provenance"])
    artifact_set_id = derive_artifact_set_id(
        architecture=ARCHITECTURE,
        profile_canonical_sha256=PROFILE_CANONICAL_SHA256,
        guest_kernel=document["guest_kernel"],
        rootfs=document["rootfs"],
        input_image=document["input_image"],
        guest_payload=document["guest_payload"],
        boot_contract=document["boot_contract"],
    )
    if document["artifact_set_id"] != artifact_set_id:
        raise RuntimeManifestError("runtime_manifest_artifact_set_id_mismatch")
    canonical_sha256 = canonical_sha256_hex(document)
    if expected_canonical_sha256 is not None:
        _require_sha256(expected_canonical_sha256)
        if canonical_sha256 != expected_canonical_sha256:
            raise RuntimeManifestError("runtime_manifest_governed_hash_mismatch")
    return PinnedRuntimeManifestV1._from_validated(
        artifact_set_id=artifact_set_id,
        canonical_sha256=canonical_sha256,
        guest_kernel=kernel,
        guest_payload=payload,
        input_image=input_image,
        rootfs=rootfs,
        boot_contract=boot,
        provenance=provenance,
    )


def load_runtime_manifest(
    path: Path,
    *,
    expected_canonical_sha256: str,
) -> PinnedRuntimeManifestV1:
    raw = read_bounded_regular(path, maximum=MAX_MANIFEST_BYTES)
    return parse_runtime_manifest_bytes(
        raw,
        expected_canonical_sha256=expected_canonical_sha256,
    )


def derive_artifact_set_id(
    *,
    architecture: str,
    profile_canonical_sha256: str,
    guest_kernel: dict[str, Any],
    rootfs: dict[str, Any],
    input_image: dict[str, Any],
    guest_payload: dict[str, Any],
    boot_contract: dict[str, Any],
) -> str:
    return canonical_sha256_hex(
        {
            "architecture": architecture,
            "boot_contract": boot_contract,
            "domain": "zenodex/zrpf_firecracker_artifact_set/v1",
            "guest_kernel": guest_kernel,
            "guest_payload": guest_payload,
            "input_image": input_image,
            "profile_canonical_sha256": profile_canonical_sha256,
            "rootfs": rootfs,
        }
    )


def canonical_document_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("ascii")


def canonical_sha256_hex(value: Any) -> str:
    raw = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    return hashlib.sha256(raw).hexdigest()


def read_bounded_regular(path: Path, *, maximum: int) -> bytes:
    """Read a stable, single-linked regular file without following a symlink."""

    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise RuntimeManifestError("runtime_manifest_input_rejected") from exc
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or not 0 < before.st_size <= maximum
            or before.st_nlink != 1
        ):
            raise RuntimeManifestError("runtime_manifest_input_rejected")
        output = bytearray()
        while len(output) < before.st_size:
            chunk = os.read(descriptor, min(65_536, before.st_size - len(output)))
            if not chunk:
                raise RuntimeManifestError("runtime_manifest_input_changed")
            output.extend(chunk)
        if os.read(descriptor, 1):
            raise RuntimeManifestError("runtime_manifest_input_changed")
        after = os.fstat(descriptor)
    except OSError as exc:
        raise RuntimeManifestError("runtime_manifest_input_rejected") from exc
    finally:
        os.close(descriptor)
    if _stable_identity(before) != _stable_identity(after):
        raise RuntimeManifestError("runtime_manifest_input_changed")
    return bytes(output)


def _parse_kernel(value: Any) -> GuestKernelIdentityV1:
    _require_fields(value, _KERNEL_FIELDS, "runtime_manifest_kernel_fields_mismatch")
    artifact = _artifact_identity(value, maximum=MAX_KERNEL_BYTES)
    if value["image_format"] != "linux_uncompressed_vmlinux_x86_64":
        raise RuntimeManifestError("runtime_manifest_kernel_format_mismatch")
    kernel_release = _require_ascii(value["kernel_release"], maximum=128)
    source_commit = _require_hex(value["source_commit"], length=40)
    source_repository = _require_https_repository(value["source_repository"])
    if value["byte_identical_local_rebuild"] is not True:
        raise RuntimeManifestError("runtime_manifest_kernel_rebuild_status_mismatch")
    if value["support_minimum_end_date"] != "2026-09-02":
        raise RuntimeManifestError("runtime_manifest_kernel_support_date_mismatch")
    return GuestKernelIdentityV1(
        artifact=artifact,
        base_config_sha256=_require_sha256(value["base_config_sha256"]),
        build_container_image_id=_require_sha256_identifier(value["build_container_image_id"]),
        build_recipe_sha256=_require_sha256(value["build_recipe_sha256"]),
        byte_identical_local_rebuild=True,
        ci_config_sha256=_require_sha256(value["ci_config_sha256"]),
        hardening_fragment_sha256=_require_sha256(value["hardening_fragment_sha256"]),
        image_format=value["image_format"],
        kernel_config_sha256=_require_sha256(value["kernel_config_sha256"]),
        kernel_release=kernel_release,
        source_commit=source_commit,
        source_repository=source_repository,
        source_tag=_require_ascii(value["source_tag"], maximum=128),
        source_tag_object=_require_hex(value["source_tag_object"], length=40),
        source_tree=_require_hex(value["source_tree"], length=40),
        support_minimum_end_date="2026-09-02",
    )


def _parse_rootfs(value: Any, payload: GuestPayloadV1) -> RootfsIdentityV1:
    _require_fields(value, _ROOTFS_FIELDS, "runtime_manifest_rootfs_fields_mismatch")
    artifact = _artifact_identity(value, maximum=MAX_ROOTFS_BYTES)
    if value["image_format"] != "squashfs_v4_zstd":
        raise RuntimeManifestError("runtime_manifest_rootfs_format_mismatch")
    if (
        type(value["filesystem_block_size_bytes"]) is not int
        or value["filesystem_block_size_bytes"] != SQUASHFS_BLOCK_SIZE_BYTES
    ):
        raise RuntimeManifestError("runtime_manifest_rootfs_geometry_mismatch")
    if value["compression"] != "zstd" or value["mkfs_epoch"] != SQUASHFS_BUILD_EPOCH:
        raise RuntimeManifestError("runtime_manifest_rootfs_geometry_mismatch")
    expected_payload_hash = canonical_sha256_hex(payload.to_document())
    if value["guest_payload_manifest_sha256"] != expected_payload_hash:
        raise RuntimeManifestError("runtime_manifest_payload_binding_mismatch")
    return RootfsIdentityV1(
        artifact=artifact,
        compression="zstd",
        filesystem_block_size_bytes=SQUASHFS_BLOCK_SIZE_BYTES,
        filesystem_inventory_root=_require_sha256(value["filesystem_inventory_root"]),
        guest_payload_manifest_sha256=expected_payload_hash,
        image_format=value["image_format"],
        mkfs_epoch=SQUASHFS_BUILD_EPOCH,
    )


def _parse_input_image(value: Any) -> InputImageIdentityV1:
    _require_fields(
        value,
        _INPUT_IMAGE_FIELDS,
        "runtime_manifest_input_image_fields_mismatch",
    )
    artifact = _artifact_identity(value, maximum=MAX_INPUT_IMAGE_BYTES)
    if value["image_format"] != "squashfs_v4_zstd":
        raise RuntimeManifestError("runtime_manifest_input_image_format_mismatch")
    if (
        type(value["filesystem_block_size_bytes"]) is not int
        or value["filesystem_block_size_bytes"] != SQUASHFS_BLOCK_SIZE_BYTES
        or value["compression"] != "zstd"
        or value["mkfs_epoch"] != SQUASHFS_BUILD_EPOCH
    ):
        raise RuntimeManifestError("runtime_manifest_input_image_geometry_mismatch")
    if type(value["receipt_count"]) is not int or value["receipt_count"] != 8:
        raise RuntimeManifestError("runtime_manifest_input_image_inventory_invalid")
    return InputImageIdentityV1(
        artifact=artifact,
        compression="zstd",
        filesystem_block_size_bytes=SQUASHFS_BLOCK_SIZE_BYTES,
        filesystem_inventory_root=_require_sha256(value["filesystem_inventory_root"]),
        image_format=value["image_format"],
        input_bundle_root=_require_sha256(value["input_bundle_root"]),
        mkfs_epoch=SQUASHFS_BUILD_EPOCH,
        receipt_count=8,
    )


def _parse_payload(value: Any) -> GuestPayloadV1:
    _require_fields(value, _PAYLOAD_FIELDS, "runtime_manifest_payload_fields_mismatch")
    expected_scalars = {
        "input_protocol_id": INPUT_PROTOCOL_ID,
        "output_protocol_id": OUTPUT_PROTOCOL_ID,
        "output_size_bytes": OUTPUT_SIZE_BYTES,
        "payload_cap_bytes": PAYLOAD_CAP_BYTES,
        "request_protocol_id": REQUEST_PROTOCOL_ID,
        "runtime_linkage": "static_pie_glibc_no_pt_interp_no_dt_needed",
    }
    for field, expected in expected_scalars.items():
        if type(value[field]) is not type(expected) or value[field] != expected:
            raise RuntimeManifestError("runtime_manifest_payload_contract_mismatch")
    entrypoint_path = _require_guest_path(value["entrypoint_guest_path"])
    rows = value["files"]
    if not isinstance(rows, list) or len(rows) != 1:
        raise RuntimeManifestError("runtime_manifest_payload_inventory_invalid")
    parsed: list[GuestPayloadFileV1] = []
    for row in rows:
        _require_fields(
            row,
            _PAYLOAD_FILE_FIELDS,
            "runtime_manifest_payload_inventory_invalid",
        )
        parsed.append(
            GuestPayloadFileV1(
                guest_path=_require_guest_path(row["guest_path"]),
                mode=_require_payload_mode(row["mode"]),
                role=_require_ascii(row["role"], maximum=32),
                sha256=_require_sha256(row["sha256"]),
                size_bytes=_require_positive_int(row["size_bytes"], maximum=MAX_PAYLOAD_FILE_BYTES),
            )
        )
    paths = [row.guest_path for row in parsed]
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        raise RuntimeManifestError("runtime_manifest_payload_inventory_invalid")
    role_names = [row.role for row in parsed]
    if role_names != ["pid1_replay_verifier"]:
        raise RuntimeManifestError("runtime_manifest_payload_inventory_invalid")
    roles = {row.role: row.guest_path for row in parsed}
    if roles.get("pid1_replay_verifier") != entrypoint_path:
        raise RuntimeManifestError("runtime_manifest_payload_inventory_invalid")
    return GuestPayloadV1(tuple(parsed), entrypoint_path)


def _parse_boot_contract(value: Any, payload: GuestPayloadV1) -> BootContractV1:
    _require_fields(value, _BOOT_FIELDS, "runtime_manifest_boot_fields_mismatch")
    expected = {
        "panic_policy": "panic=0_host_watchdog_reboot=k",
        "root_device": "/dev/vda",
        "rootfs_read_only": True,
        "serial_policy": "8250_disabled",
    }
    for field, expected_value in expected.items():
        if type(value[field]) is not type(expected_value) or value[field] != expected_value:
            raise RuntimeManifestError("runtime_manifest_boot_contract_mismatch")
    init_path = _require_guest_path(value["init_guest_path"])
    if init_path != payload.entrypoint_guest_path:
        raise RuntimeManifestError("runtime_manifest_boot_payload_mismatch")
    command_line = _require_ascii(value["kernel_cmdline"], maximum=4_096)
    expected_command_line = (
        "reboot=k panic=0 nomodule 8250.nr_uarts=0 i8042.noaux i8042.nomux "
        f"i8042.dumbkbd swiotlb=noforce init={init_path} rootfstype=squashfs "
        "quiet loglevel=0 oops=panic panic_on_oops=1"
    )
    if command_line != expected_command_line:
        raise RuntimeManifestError("runtime_manifest_boot_contract_mismatch")
    return BootContractV1(init_path, command_line)


def _parse_provenance(value: Any) -> ProvenanceRecordV1:
    _require_fields(
        value,
        _PROVENANCE_FIELDS,
        "runtime_manifest_provenance_fields_mismatch",
    )
    if value["status"] != "identity_pinned_source_build_not_reproduced":
        raise RuntimeManifestError("runtime_manifest_provenance_status_mismatch")
    repository = _require_https_repository(value["kernel_source_repository"])
    return ProvenanceRecordV1(
        guest_payload_source_commit=_require_hex(value["guest_payload_source_commit"], length=40),
        input_build_recipe_sha256=_require_sha256(value["input_build_recipe_sha256"]),
        kernel_source_repository=repository,
        mksquashfs_binary_sha256=_require_sha256(value["mksquashfs_binary_sha256"]),
        mksquashfs_version=_require_ascii(value["mksquashfs_version"], maximum=64),
        rootfs_build_recipe_sha256=_require_sha256(value["rootfs_build_recipe_sha256"]),
    )


def _artifact_identity(value: dict[str, Any], *, maximum: int) -> ArtifactIdentityV1:
    return ArtifactIdentityV1(
        artifact_name=_require_safe_basename(value["artifact_name"]),
        sha256=_require_sha256(value["sha256"]),
        size_bytes=_require_positive_int(value["size_bytes"], maximum=maximum),
    )


def _validate_authority(value: Any) -> None:
    if not isinstance(value, dict) or set(value) != set(AUTHORITY_FIELDS):
        raise RuntimeManifestError("runtime_manifest_authority_mismatch")
    if any(type(value[name]) is not bool or value[name] is not False for name in AUTHORITY_FIELDS):
        raise RuntimeManifestError("runtime_manifest_authority_mismatch")


def _require_fields(value: Any, fields: set[str], code: str) -> None:
    if not isinstance(value, dict) or set(value) != fields:
        raise RuntimeManifestError(code)


def _require_safe_basename(value: Any) -> str:
    if not isinstance(value, str) or not _bounded_ascii(value, maximum=255):
        raise RuntimeManifestError("runtime_manifest_artifact_name_invalid")
    path = PurePosixPath(value)
    if path.name != value or value in {".", ".."} or "/" in value or "\\" in value:
        raise RuntimeManifestError("runtime_manifest_artifact_name_invalid")
    return value


def _require_guest_path(value: Any) -> str:
    if not isinstance(value, str) or not _bounded_ascii(value, maximum=512):
        raise RuntimeManifestError("runtime_manifest_guest_path_invalid")
    path = PurePosixPath(value)
    if (
        len(path.parts) <= 1
        or not path.is_absolute()
        or str(path) != value
        or any(part in {"", ".", ".."} for part in path.parts[1:])
    ):
        raise RuntimeManifestError("runtime_manifest_guest_path_invalid")
    return value


def _require_payload_mode(value: Any) -> str:
    if not isinstance(value, str) or value != "0555":
        raise RuntimeManifestError("runtime_manifest_payload_mode_invalid")
    return value


def _require_sha256(value: Any) -> str:
    return _require_hex(value, length=64)


def _require_sha256_identifier(value: Any) -> str:
    if not isinstance(value, str) or not value.startswith("sha256:"):
        raise RuntimeManifestError("runtime_manifest_digest_invalid")
    _require_sha256(value.removeprefix("sha256:"))
    return value


def _require_https_repository(value: Any) -> str:
    repository = _require_ascii(value, maximum=512)
    parsed_repository = urlsplit(repository)
    if any(
        (
            parsed_repository.scheme != "https",
            not parsed_repository.hostname,
            parsed_repository.username is not None,
            parsed_repository.password is not None,
            bool(parsed_repository.query),
            bool(parsed_repository.fragment),
        )
    ):
        raise RuntimeManifestError("runtime_manifest_provenance_source_invalid")
    return repository


def _require_hex(value: Any, *, length: int) -> str:
    if (
        not isinstance(value, str)
        or len(value) != length
        or value == "0" * length
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise RuntimeManifestError("runtime_manifest_digest_invalid")
    return value


def _require_positive_int(value: Any, *, maximum: int) -> int:
    if type(value) is not int or not 0 < value <= maximum:
        raise RuntimeManifestError("runtime_manifest_size_invalid")
    return value


def _require_ascii(value: Any, *, maximum: int) -> str:
    if not isinstance(value, str) or not _bounded_ascii(value, maximum=maximum):
        raise RuntimeManifestError("runtime_manifest_string_invalid")
    return value


def _bounded_ascii(value: str, *, maximum: int) -> bool:
    return bool(
        value
        and len(value) <= maximum
        and value.isascii()
        and all(32 <= ord(character) <= 126 for character in value)
    )


def _canonical_uuid(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != 36:
        return False
    return all(
        character == "-" if index in {8, 13, 18, 23} else character in "0123456789abcdef"
        for index, character in enumerate(value)
    )


def _strict_json_loads(raw: bytes) -> Any:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise ValueError("duplicate key")
            output[key] = value
        return output

    def reject_constant(_value: str) -> None:
        raise ValueError("non-finite number")

    return json.loads(
        raw.decode("ascii"),
        object_pairs_hook=unique_object,
        parse_constant=reject_constant,
    )


def _stable_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_nlink,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )
