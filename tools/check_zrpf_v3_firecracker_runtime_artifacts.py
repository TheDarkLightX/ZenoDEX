#!/usr/bin/env python3
"""Validate the governed, non-authoritative ZRPF Firecracker artifact identities."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import sys
from datetime import date
from pathlib import Path
from typing import Any, Mapping

if __package__:
    _MODULE_PREFIX = "tools."
else:
    sys.path.insert(0, Path(__file__).resolve().parent.as_posix())
    _MODULE_PREFIX = ""

candidate_plan = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_candidate_plan")
runtime = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_runtime_manifest")
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")

REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = (
    REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v1.json"
)
KERNEL_RECORD_PATH = (
    REPO_ROOT / "config/proof_profiles/zrpf_firecracker_guest_kernel_build_record_v1.json"
)
IMAGE_RECORD_PATH = (
    REPO_ROOT / "config/proof_profiles/zrpf_firecracker_runtime_image_build_record_v1.json"
)
IMAGE_RECIPE_PATH = REPO_ROOT / "tools/build_zrpf_v3_firecracker_guest_images.sh"
PROFILE_PATH = REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json"

EXPECTED_MANIFEST_CANONICAL_SHA256 = (
    "cb19138eb6bb7dd404c860382e0c0f2b765d12ea8e734e9afb99caae381ff312"
)
EXPECTED_KERNEL_RECORD_SHA256 = "c2d007adbde38855a24fbd80d574097d8892086ec5924051d977b0c08bc5c373"
EXPECTED_IMAGE_RECORD_SHA256 = "85168dd8db9bacc921377d1fc0d39736199058c323fd92612a333429f8a73961"
EXPECTED_IMAGE_RECIPE_SHA256 = "b3363c124fe40cd22e36e7943cb3cfe92e78c8739d935155d8e55b0eb59c0bbd"
RECORDED_EVIDENCE_DATE = date(2026, 7, 11)
REPORT_SCHEMA = "zenodex/zrpf_firecracker_runtime_artifact_check/v2"


def build_report(*, current_release_date: date | None = None) -> dict[str, Any]:
    errors: list[str] = []
    try:
        manifest = runtime.load_runtime_manifest(
            MANIFEST_PATH,
            expected_canonical_sha256=EXPECTED_MANIFEST_CANONICAL_SHA256,
        )
        kernel_raw, kernel_record = _load_record(
            KERNEL_RECORD_PATH,
            expected_sha256=EXPECTED_KERNEL_RECORD_SHA256,
        )
        image_raw, image_record = _load_record(
            IMAGE_RECORD_PATH,
            expected_sha256=EXPECTED_IMAGE_RECORD_SHA256,
        )
        recipe_raw = runtime.read_bounded_regular(
            IMAGE_RECIPE_PATH,
            maximum=128 * 1024,
        )
        if hashlib.sha256(recipe_raw).hexdigest() != EXPECTED_IMAGE_RECIPE_SHA256:
            errors.append("image_recipe_hash_mismatch")
        profile_raw = runtime.read_bounded_regular(PROFILE_PATH, maximum=128 * 1024)
        profile = support.strict_json_loads(profile_raw)
        if not isinstance(profile, dict):
            raise ValueError("profile root is not an object")
        if profile_raw != runtime.canonical_document_bytes(profile):
            errors.append("profile_noncanonical")
        if runtime.canonical_sha256_hex(profile) != runtime.PROFILE_CANONICAL_SHA256:
            errors.append("profile_canonical_hash_mismatch")
        errors.extend(
            _cross_check(
                manifest,
                kernel_record=kernel_record,
                kernel_record_sha256=hashlib.sha256(kernel_raw).hexdigest(),
                image_record=image_record,
                image_recipe_sha256=hashlib.sha256(recipe_raw).hexdigest(),
                profile=profile,
            )
        )
    except (OSError, RecursionError, UnicodeDecodeError, ValueError):
        manifest = None
        errors.append("runtime_artifact_package_rejected")

    support_end = (
        date.fromisoformat(manifest.guest_kernel.support_minimum_end_date)
        if manifest is not None
        else None
    )
    historical_supported = bool(
        support_end is not None and RECORDED_EVIDENCE_DATE <= support_end
    )
    if not historical_supported:
        errors.append("guest_kernel_support_expired_for_recorded_evidence_date")
    current_checked = current_release_date is not None
    current_eligible = bool(
        current_checked
        and support_end is not None
        and current_release_date is not None
        and current_release_date <= support_end
    )
    if current_checked and not current_eligible:
        errors.append("guest_kernel_support_expired_for_current_release_date")
    return {
        "authority": {
            "cross_host_reproducible_build": False,
            "microvm_replay_verified": False,
            "production_authority": False,
            "release_authority": False,
            "root_launcher_ready": False,
            "settlement_authority": False,
        },
        "current_release_date": (
            current_release_date.isoformat() if current_release_date is not None else None
        ),
        "current_runtime_eligibility_checked": current_checked,
        "current_runtime_eligible": current_eligible,
        "errors": errors,
        "guest_kernel_support_minimum_end_date": (
            support_end.isoformat() if support_end is not None else None
        ),
        "historical_evidence_supported_on_recorded_date": historical_supported,
        "manifest_canonical_sha256": (manifest.canonical_sha256 if manifest is not None else None),
        "ok": not errors,
        "recorded_evidence_date": RECORDED_EVIDENCE_DATE.isoformat(),
        "schema": REPORT_SCHEMA,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--current-release-date")
    parser.add_argument("--require-current-runtime-eligible", action="store_true")
    arguments = parser.parse_args(argv)
    try:
        current_release_date = (
            date.fromisoformat(arguments.current_release_date)
            if arguments.current_release_date is not None
            else None
        )
    except ValueError:
        return 2
    report = build_report(current_release_date=current_release_date)
    print(json.dumps(report, indent=2, sort_keys=True))
    current_requirement_met = (
        not arguments.require_current_runtime_eligible
        or report["current_runtime_eligible"] is True
    )
    return 0 if report["ok"] and current_requirement_met else 1


def _load_record(path: Path, *, expected_sha256: str) -> tuple[bytes, dict[str, Any]]:
    raw = runtime.read_bounded_regular(path, maximum=512 * 1024)
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("record hash mismatch")
    value = support.strict_json_loads(raw)
    if not isinstance(value, dict):
        raise ValueError("record root is not an object")
    return raw, value


def _cross_check(
    manifest,
    *,
    kernel_record: dict[str, Any],
    kernel_record_sha256: str,
    image_record: dict[str, Any],
    image_recipe_sha256: str,
    profile: dict[str, Any],
) -> list[str]:
    errors = _check_kernel_record(
        manifest,
        kernel_record=kernel_record,
        kernel_record_sha256=kernel_record_sha256,
    )
    errors.extend(
        _check_image_record(
            manifest,
            image_record=image_record,
            image_recipe_sha256=image_recipe_sha256,
        )
    )
    runner_policy = profile.get("runner_policy")
    expected_configuration = (
        runner_policy.get("exact_vm_configuration_template")
        if isinstance(runner_policy, dict)
        else None
    )
    if candidate_plan.candidate_microvm_configuration(manifest) != expected_configuration:
        errors.append("microvm_configuration_binding_mismatch")
    return errors


def _check_kernel_record(
    manifest,
    *,
    kernel_record: Mapping[str, Any],
    kernel_record_sha256: str,
) -> list[str]:
    errors: list[str] = []
    if kernel_record.get("schema") != "zenodex/zrpf_firecracker_guest_kernel_build_record/v1":
        errors.append("kernel_record_schema_mismatch")
    if (
        kernel_record.get("status")
        != "local_byte_identical_candidate_kernel_build_non_authoritative"
    ):
        errors.append("kernel_record_status_mismatch")
    authority = kernel_record.get("authority")
    if (
        not isinstance(authority, dict)
        or not authority
        or any(type(value) is not bool or value is not False for value in authority.values())
    ):
        errors.append("kernel_record_authority_mismatch")
    if manifest.guest_kernel.build_recipe_sha256 != kernel_record_sha256:
        errors.append("kernel_recipe_binding_mismatch")
    if kernel_record.get("outputs") != {
        "kernel_config_sha256": manifest.guest_kernel.kernel_config_sha256,
        "kernel_release": manifest.guest_kernel.kernel_release,
        "support_minimum_end_date": manifest.guest_kernel.support_minimum_end_date,
        "vmlinux_sha256": manifest.guest_kernel.artifact.sha256,
        "vmlinux_size_bytes": manifest.guest_kernel.artifact.size_bytes,
    }:
        errors.append("kernel_output_binding_mismatch")
    inputs = kernel_record.get("inputs")
    source = inputs.get("kernel_source") if isinstance(inputs, dict) else None
    expected_source = {
        "repository": manifest.guest_kernel.source_repository,
        "source_commit": manifest.guest_kernel.source_commit,
        "source_tag": manifest.guest_kernel.source_tag,
        "source_tag_object": manifest.guest_kernel.source_tag_object,
        "source_tree": manifest.guest_kernel.source_tree,
        "tag_signature_verified": False,
    }
    if not isinstance(inputs, dict) or (
        inputs.get("firecracker_ci_config_sha256"),
        inputs.get("firecracker_x86_64_6_1_config_sha256"),
        inputs.get("zrpf_hardening_fragment_sha256"),
    ) != (
        manifest.guest_kernel.ci_config_sha256,
        manifest.guest_kernel.base_config_sha256,
        manifest.guest_kernel.hardening_fragment_sha256,
    ):
        errors.append("kernel_input_binding_mismatch")
    if source != expected_source:
        errors.append("kernel_source_binding_mismatch")
    builder = kernel_record.get("builder")
    if not isinstance(builder, dict) or builder.get("local_builder_image_id") != (
        manifest.guest_kernel.build_container_image_id
    ):
        errors.append("kernel_builder_binding_mismatch")
    rebuild = kernel_record.get("local_rebuild_evidence")
    if not isinstance(rebuild, dict) or rebuild != {
        "build_a_config_sha256": manifest.guest_kernel.kernel_config_sha256,
        "build_a_vmlinux_sha256": manifest.guest_kernel.artifact.sha256,
        "build_b_config_sha256": manifest.guest_kernel.kernel_config_sha256,
        "build_b_vmlinux_sha256": manifest.guest_kernel.artifact.sha256,
        "byte_identical": True,
        "scope": "same_host_same_container_image_two_clean_output_directories",
    }:
        errors.append("kernel_rebuild_binding_mismatch")
    if manifest.provenance.kernel_source_repository != manifest.guest_kernel.source_repository:
        errors.append("kernel_repository_binding_mismatch")
    return errors


def _check_image_record(
    manifest,
    *,
    image_record: Mapping[str, Any],
    image_recipe_sha256: str,
) -> list[str]:
    errors: list[str] = []
    if image_record.get("schema") != "zenodex/zrpf_firecracker_runtime_image_build_record/v1":
        errors.append("image_record_schema_mismatch")
    if image_record.get("status") != "same_host_byte_identical_candidate_images_non_authoritative":
        errors.append("image_record_status_mismatch")
    authority = image_record.get("authority")
    if (
        not isinstance(authority, dict)
        or not authority
        or any(type(value) is not bool or value is not False for value in authority.values())
    ):
        errors.append("image_record_authority_mismatch")
    if manifest.provenance.rootfs_build_recipe_sha256 != image_recipe_sha256:
        errors.append("rootfs_recipe_binding_mismatch")
    if manifest.provenance.input_build_recipe_sha256 != image_recipe_sha256:
        errors.append("input_recipe_binding_mismatch")
    if image_record.get("build_recipe") != {
        "path": "tools/build_zrpf_v3_firecracker_guest_images.sh",
        "sha256": image_recipe_sha256,
    }:
        errors.append("image_recipe_record_mismatch")

    payload_file = manifest.guest_payload.files[0]
    guest_binary = image_record.get("guest_binary")
    if not isinstance(guest_binary, dict) or (
        guest_binary.get("sha256"),
        guest_binary.get("size_bytes"),
        guest_binary.get("guest_source_commit"),
        guest_binary.get("image_format"),
        guest_binary.get("direct_non_pid1_exit_code"),
        guest_binary.get("pt_interp_present"),
        guest_binary.get("dt_needed_present"),
    ) != (
        payload_file.sha256,
        payload_file.size_bytes,
        manifest.provenance.guest_payload_source_commit,
        "static_pie_glibc_no_pt_interp_no_dt_needed",
        125,
        False,
        False,
    ):
        errors.append("guest_binary_binding_mismatch")

    builder = image_record.get("image_builder")
    if not isinstance(builder, dict) or builder != {
        "mksquashfs_binary_sha256": manifest.provenance.mksquashfs_binary_sha256,
        "mksquashfs_version": "4.6.1",
        "readelf_binary_sha256": manifest.provenance.readelf_binary_sha256,
        "readelf_version": "GNU_readelf_2.42",
        "squashfs_block_size_bytes": manifest.rootfs.filesystem_block_size_bytes,
        "squashfs_compression": manifest.rootfs.compression,
        "squashfs_epoch": manifest.rootfs.mkfs_epoch,
    }:
        errors.append("image_builder_binding_mismatch")
    if manifest.provenance.mksquashfs_version != "mksquashfs_4.6.1":
        errors.append("image_builder_version_binding_mismatch")
    if manifest.provenance.readelf_version != "GNU_readelf_2.42":
        errors.append("image_builder_version_binding_mismatch")

    rootfs_record = image_record.get("rootfs")
    input_record = image_record.get("input_image")
    if not isinstance(rootfs_record, dict) or not isinstance(input_record, dict):
        return [*errors, "image_record_shape_mismatch"]
    if runtime.canonical_sha256_hex(rootfs_record.get("filesystem_inventory")) != (
        manifest.rootfs.filesystem_inventory_root
    ):
        errors.append("rootfs_inventory_root_mismatch")
    if runtime.canonical_sha256_hex(input_record.get("filesystem_inventory")) != (
        manifest.input_image.filesystem_inventory_root
    ):
        errors.append("input_inventory_root_mismatch")
    if (
        rootfs_record.get("sha256"),
        rootfs_record.get("size_bytes"),
    ) != (
        manifest.rootfs.artifact.sha256,
        manifest.rootfs.artifact.size_bytes,
    ):
        errors.append("rootfs_artifact_binding_mismatch")
    if (
        input_record.get("sha256"),
        input_record.get("size_bytes"),
        input_record.get("receipt_set_root"),
    ) != (
        manifest.input_image.artifact.sha256,
        manifest.input_image.artifact.size_bytes,
        manifest.input_image.input_bundle_root,
    ):
        errors.append("input_artifact_binding_mismatch")
    if rootfs_record.get("byte_identical_two_builds") is not True:
        errors.append("rootfs_rebuild_status_mismatch")
    if input_record.get("byte_identical_two_builds") is not True:
        errors.append("input_rebuild_status_mismatch")
    if _receipt_set_root(input_record.get("filesystem_inventory")) != (
        manifest.input_image.input_bundle_root
    ):
        errors.append("receipt_set_root_mismatch")
    return errors


def _receipt_set_root(value: Any) -> str | None:
    if not isinstance(value, dict) or set(value) != {"domain", "entries"}:
        return None
    if value["domain"] != "zenodex/zrpf_squashfs_inventory/v1":
        return None
    entries = value["entries"]
    if not isinstance(entries, list):
        return None
    receipt_rows: list[tuple[str, int, str]] = []
    for row in entries:
        if not isinstance(row, dict) or row.get("kind") != "file":
            continue
        path = row.get("path")
        size = row.get("size_bytes")
        digest = row.get("sha256")
        if (
            not isinstance(path, str)
            or not path.startswith("/receipts/")
            or "/" in path.removeprefix("/receipts/")
            or "\x00" in path
            or "\n" in path
            or "\r" in path
            or type(size) is not int
            or size <= 0
            or not isinstance(digest, str)
            or len(digest) != 64
            or any(character not in "0123456789abcdef" for character in digest)
        ):
            return None
        receipt_rows.append((path.removeprefix("/receipts/"), size, digest))
    if len(receipt_rows) != 8 or receipt_rows != sorted(receipt_rows):
        return None
    encoded = b"".join(
        name.encode("ascii")
        + b"\0"
        + str(size).encode("ascii")
        + b"\0"
        + digest.encode("ascii")
        + b"\n"
        for name, size, digest in receipt_rows
    )
    return hashlib.sha256(encoded).hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())
