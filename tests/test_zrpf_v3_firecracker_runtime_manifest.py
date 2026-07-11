from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from typing import Any

import pytest

from tools import zrpf_v3_firecracker_runtime_manifest as runtime


def build_manifest_document(
    kernel_bytes: bytes = b"test-kernel",
    rootfs_bytes: bytes = b"test-rootfs",
) -> dict[str, Any]:
    payload = {
        "entrypoint_guest_path": "/sbin/zrpf-replay-init",
        "files": [
            {
                "guest_path": "/sbin/zrpf-replay-init",
                "mode": "0555",
                "role": "pid1_replay_verifier",
                "sha256": _hash(b"init"),
                "size_bytes": 4,
            },
        ],
        "input_protocol_id": runtime.INPUT_PROTOCOL_ID,
        "output_protocol_id": runtime.OUTPUT_PROTOCOL_ID,
        "output_size_bytes": runtime.OUTPUT_SIZE_BYTES,
        "payload_cap_bytes": runtime.PAYLOAD_CAP_BYTES,
        "request_protocol_id": runtime.REQUEST_PROTOCOL_ID,
        "runtime_linkage": "static_pie_glibc_no_pt_interp_no_dt_needed",
    }
    kernel = {
        "artifact_name": "zrpf-vmlinux",
        "base_config_sha256": _hash(b"base-config"),
        "build_container_image_id": f"sha256:{_hash(b'kernel-builder')}",
        "build_recipe_sha256": _hash(b"kernel-recipe"),
        "byte_identical_local_rebuild": True,
        "ci_config_sha256": _hash(b"ci-config"),
        "hardening_fragment_sha256": _hash(b"hardening-fragment"),
        "image_format": "linux_uncompressed_vmlinux_x86_64",
        "kernel_config_sha256": _hash(b"kernel-config"),
        "kernel_release": "6.18.2-zrpf",
        "sha256": _hash(kernel_bytes),
        "size_bytes": len(kernel_bytes),
        "source_commit": "12" * 20,
        "source_repository": "https://example.invalid/linux",
        "source_tag": "microvm-kernel-test",
        "source_tag_object": "56" * 20,
        "source_tree": "78" * 20,
        "support_minimum_end_date": "2026-09-02",
    }
    rootfs = {
        "artifact_name": "zrpf-replay-rootfs.squashfs",
        "compression": "zstd",
        "filesystem_block_size_bytes": runtime.SQUASHFS_BLOCK_SIZE_BYTES,
        "filesystem_inventory_root": _hash(b"rootfs-inventory"),
        "guest_payload_manifest_sha256": runtime.canonical_sha256_hex(payload),
        "image_format": "squashfs_v4_zstd",
        "mkfs_epoch": runtime.SQUASHFS_BUILD_EPOCH,
        "sha256": _hash(rootfs_bytes),
        "size_bytes": len(rootfs_bytes),
    }
    input_image = {
        "artifact_name": "zrpf-replay-input.squashfs",
        "compression": "zstd",
        "filesystem_block_size_bytes": runtime.SQUASHFS_BLOCK_SIZE_BYTES,
        "filesystem_inventory_root": _hash(b"input-inventory"),
        "image_format": "squashfs_v4_zstd",
        "input_bundle_root": _hash(b"input-bundle"),
        "mkfs_epoch": runtime.SQUASHFS_BUILD_EPOCH,
        "receipt_count": 8,
        "sha256": _hash(b"input-image"),
        "size_bytes": len(b"input-image"),
    }
    boot = {
        "init_guest_path": "/sbin/zrpf-replay-init",
        "kernel_cmdline": (
            "reboot=k panic=0 nomodule 8250.nr_uarts=0 i8042.noaux "
            "i8042.nomux i8042.dumbkbd swiotlb=noforce "
            "init=/sbin/zrpf-replay-init rootfstype=squashfs quiet loglevel=0 "
            "oops=panic panic_on_oops=1"
        ),
        "panic_policy": "panic=0_host_watchdog_reboot=k",
        "root_device": "/dev/vda",
        "rootfs_read_only": True,
        "serial_policy": "8250_disabled",
    }
    artifact_set_id = runtime.derive_artifact_set_id(
        architecture=runtime.ARCHITECTURE,
        profile_canonical_sha256=runtime.PROFILE_CANONICAL_SHA256,
        guest_kernel=kernel,
        rootfs=rootfs,
        input_image=input_image,
        guest_payload=payload,
        boot_contract=boot,
    )
    return {
        "architecture": runtime.ARCHITECTURE,
        "artifact_set_id": artifact_set_id,
        "authority": {name: False for name in runtime.AUTHORITY_FIELDS},
        "boot_contract": boot,
        "firecracker_profile_canonical_sha256": (runtime.PROFILE_CANONICAL_SHA256),
        "guest_kernel": kernel,
        "guest_payload": payload,
        "input_image": input_image,
        "non_claims": list(runtime.NON_CLAIMS),
        "provenance": {
            "guest_elf_checker_schema": "zenodex/zrpf_firecracker_guest_elf_check/v1",
            "guest_elf_checker_sha256": _hash(b"guest-elf-checker"),
            "guest_payload_source_commit": "34" * 20,
            "input_build_recipe_sha256": _hash(b"input-recipe"),
            "kernel_source_repository": "https://example.invalid/linux",
            "mksquashfs_binary_sha256": _hash(b"mksquashfs"),
            "mksquashfs_version": "mksquashfs_4.6.1",
            "python_binary_sha256": _hash(b"python"),
            "python_version": "Python_3.12.3",
            "rootfs_build_recipe_sha256": _hash(b"rootfs-recipe"),
            "status": "identity_pinned_source_build_not_reproduced",
        },
        "rootfs": rootfs,
        "schema": runtime.SCHEMA,
        "status": runtime.STATUS,
    }


def manifest_bytes(document: dict[str, Any]) -> bytes:
    return runtime.canonical_document_bytes(document)


def parse_manifest(document: dict[str, Any]) -> runtime.PinnedRuntimeManifestV1:
    raw = manifest_bytes(document)
    return runtime.parse_runtime_manifest_bytes(
        raw,
        expected_canonical_sha256=runtime.canonical_sha256_hex(document),
    )


def test_valid_manifest_round_trips_without_authority() -> None:
    document = build_manifest_document()
    manifest = parse_manifest(document)

    assert manifest.to_document() == document
    assert manifest.canonical_sha256 == runtime.canonical_sha256_hex(document)
    assert all(value is False for value in document["authority"].values())
    with pytest.raises(TypeError):
        runtime.PinnedRuntimeManifestV1()


def test_manifest_rejects_duplicate_noncanonical_and_unknown_fields() -> None:
    with pytest.raises(runtime.RuntimeManifestError) as duplicate:
        runtime.parse_runtime_manifest_bytes(b'{"schema":"a","schema":"b"}\n')
    assert duplicate.value.code == "runtime_manifest_input_rejected"

    document = build_manifest_document()
    with pytest.raises(runtime.RuntimeManifestError) as noncanonical:
        runtime.parse_runtime_manifest_bytes(json.dumps(document).encode("ascii"))
    assert noncanonical.value.code == "runtime_manifest_noncanonical"

    document["unexpected"] = False
    with pytest.raises(runtime.RuntimeManifestError) as unknown:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(document))
    assert unknown.value.code == "runtime_manifest_fields_mismatch"

    with pytest.raises(runtime.RuntimeManifestError) as oversized:
        runtime.parse_runtime_manifest_bytes(b" " * (runtime.MAX_MANIFEST_BYTES + 1))
    assert oversized.value.code == "runtime_manifest_input_rejected"


def test_manifest_rejects_integer_boolean_and_authority_promotion() -> None:
    integer = build_manifest_document()
    integer["boot_contract"]["rootfs_read_only"] = 1
    with pytest.raises(runtime.RuntimeManifestError) as wrong_type:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(integer))
    assert wrong_type.value.code == "runtime_manifest_boot_contract_mismatch"

    promoted = build_manifest_document()
    promoted["authority"]["root_launcher_ready"] = True
    with pytest.raises(runtime.RuntimeManifestError) as authority:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(promoted))
    assert authority.value.code == "runtime_manifest_authority_mismatch"


def test_manifest_rejects_profile_payload_and_artifact_set_drift() -> None:
    profile = build_manifest_document()
    profile["firecracker_profile_canonical_sha256"] = "ab" * 32
    with pytest.raises(runtime.RuntimeManifestError) as profile_error:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(profile))
    assert profile_error.value.code == "runtime_manifest_profile_binding_mismatch"

    payload = build_manifest_document()
    payload["rootfs"]["guest_payload_manifest_sha256"] = "cd" * 32
    with pytest.raises(runtime.RuntimeManifestError) as payload_error:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(payload))
    assert payload_error.value.code == "runtime_manifest_payload_binding_mismatch"

    artifact_set = build_manifest_document()
    artifact_set["artifact_set_id"] = "ef" * 32
    with pytest.raises(runtime.RuntimeManifestError) as set_error:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(artifact_set))
    assert set_error.value.code == "runtime_manifest_artifact_set_id_mismatch"


def test_manifest_rejects_unsafe_and_ambiguous_payload_inventory() -> None:
    unsafe = build_manifest_document()
    unsafe["guest_kernel"]["artifact_name"] = "../vmlinux"
    _refresh_artifact_set_id(unsafe)
    with pytest.raises(runtime.RuntimeManifestError) as unsafe_name:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(unsafe))
    assert unsafe_name.value.code == "runtime_manifest_artifact_name_invalid"

    duplicate = build_manifest_document()
    duplicate["guest_payload"]["files"].append(dict(duplicate["guest_payload"]["files"][0]))
    duplicate["rootfs"]["guest_payload_manifest_sha256"] = runtime.canonical_sha256_hex(
        duplicate["guest_payload"]
    )
    _refresh_artifact_set_id(duplicate)
    with pytest.raises(runtime.RuntimeManifestError) as duplicate_path:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(duplicate))
    assert duplicate_path.value.code == "runtime_manifest_payload_inventory_invalid"

    wrong_role = build_manifest_document()
    wrong_role["guest_payload"]["files"][0]["role"] = "verifier"
    wrong_role["rootfs"]["guest_payload_manifest_sha256"] = runtime.canonical_sha256_hex(
        wrong_role["guest_payload"]
    )
    _refresh_artifact_set_id(wrong_role)
    with pytest.raises(runtime.RuntimeManifestError) as wrong_role_error:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(wrong_role))
    assert wrong_role_error.value.code == "runtime_manifest_payload_inventory_invalid"

    writable = build_manifest_document()
    writable["guest_payload"]["files"][0]["mode"] = "0755"
    writable["rootfs"]["guest_payload_manifest_sha256"] = runtime.canonical_sha256_hex(
        writable["guest_payload"]
    )
    _refresh_artifact_set_id(writable)
    with pytest.raises(runtime.RuntimeManifestError) as writable_error:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(writable))
    assert writable_error.value.code == "runtime_manifest_payload_mode_invalid"

    ambiguous_boot = build_manifest_document()
    ambiguous_boot["boot_contract"]["kernel_cmdline"] += " rw init=/bin/sh"
    _refresh_artifact_set_id(ambiguous_boot)
    with pytest.raises(runtime.RuntimeManifestError) as boot_error:
        runtime.parse_runtime_manifest_bytes(manifest_bytes(ambiguous_boot))
    assert boot_error.value.code == "runtime_manifest_boot_contract_mismatch"


def test_manifest_file_reader_rejects_symlink_fifo_and_empty_file(
    tmp_path: Path,
) -> None:
    target = tmp_path / "target"
    target.write_bytes(manifest_bytes(build_manifest_document()))
    link = tmp_path / "link"
    link.symlink_to(target)
    with pytest.raises(runtime.RuntimeManifestError) as symlink:
        runtime.read_bounded_regular(link, maximum=runtime.MAX_MANIFEST_BYTES)
    assert symlink.value.code == "runtime_manifest_input_rejected"

    fifo = tmp_path / "fifo"
    os.mkfifo(fifo)
    with pytest.raises(runtime.RuntimeManifestError) as fifo_error:
        runtime.read_bounded_regular(fifo, maximum=runtime.MAX_MANIFEST_BYTES)
    assert fifo_error.value.code == "runtime_manifest_input_rejected"

    empty = tmp_path / "empty"
    empty.write_bytes(b"")
    with pytest.raises(runtime.RuntimeManifestError) as empty_error:
        runtime.read_bounded_regular(empty, maximum=runtime.MAX_MANIFEST_BYTES)
    assert empty_error.value.code == "runtime_manifest_input_rejected"


def _refresh_artifact_set_id(document: dict[str, Any]) -> None:
    document["artifact_set_id"] = runtime.derive_artifact_set_id(
        architecture=document["architecture"],
        profile_canonical_sha256=document["firecracker_profile_canonical_sha256"],
        guest_kernel=document["guest_kernel"],
        rootfs=document["rootfs"],
        input_image=document["input_image"],
        guest_payload=document["guest_payload"],
        boot_contract=document["boot_contract"],
    )


def _hash(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()
