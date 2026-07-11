#!/usr/bin/env python3
"""Validate the incomplete, non-authoritative ZRPF Firecracker candidate profile."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
from pathlib import Path
from typing import Any

if __package__:
    from tools import zrpf_v3_firecracker_host_probe as host_probe
    from tools import zrpf_v3_replay_evidence_support as support
else:
    trusted_tools = Path(__file__).resolve().parent.as_posix()
    sys.path.insert(0, trusted_tools)
    import zrpf_v3_firecracker_host_probe as host_probe  # type: ignore[no-redef]
    import zrpf_v3_replay_evidence_support as support  # type: ignore[no-redef]

REPO_ROOT = Path(__file__).resolve().parents[1]
PROFILE_PATH = (
    REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json"
)
MAX_PROFILE_BYTES = 64 * 1024
EXPECTED_PROFILE_CANONICAL_SHA256 = (
    "433d251ea949f9a4bdb8b9bbd521a83c4fd7ffcd583ee6256f2ce148d1455a38"
)

EXPECTED_CLAIMS = {
    "cgroup_limits_installed": False,
    "complete_build_input_closure_verified": False,
    "constant_time_execution": False,
    "covert_channel_freedom": False,
    "cross_host_reproducible_build": False,
    "data_availability_verified": False,
    "durable_atomic_admission_verified": False,
    "guest_image_ids_recomputed": False,
    "guest_kernel_identity_authenticated": False,
    "hardware_side_channel_resistance": False,
    "host_baseline_verified": False,
    "host_filesystem_isolated": False,
    "host_secret_absence_verified": False,
    "host_secret_isolation": False,
    "ledger_admission_authority": False,
    "microvm_replay_verified": False,
    "network_egress_denied_by_runtime": False,
    "privacy_or_zero_knowledge": False,
    "process_namespace_isolated": False,
    "production_authority": False,
    "proofs_regenerated": False,
    "public_replay_promoted": False,
    "release_authority": False,
    "release_tag_signature_verified": False,
    "rootfs_identity_authenticated": False,
    "runtime_artifacts_locally_verified": False,
    "runtime_rootfs_identity_authenticated": False,
    "sandbox_escape_controls_passed": False,
    "sandbox_escape_resistance": False,
    "sandbox_isolation_verified": False,
    "seccomp_policy_installed": False,
    "semantic_composition_verified": False,
    "settlement_authority": False,
    "witness_privacy": False,
    "zero_knowledge_privacy": False,
}
EXPECTED_RELEASE = {
    "architecture": "x86_64",
    "binary_flavor": "release_musl_with_embedded_default_seccomp",
    "repository": "https://github.com/firecracker-microvm/firecracker",
    "tag": "v1.16.1",
    "tag_commit": "2038188f145fb81b8d098147a10e9d9f392fd22f",
    "tag_object": "e527ccfc54495dabac96f1835db61a40afa15115",
}
EXPECTED_ARTIFACTS = {
    "firecracker_release_binary": {
        "archive_path": "release-v1.16.1-x86_64/firecracker-v1.16.1-x86_64",
        "sha256": "2fd0171309af7e24cf8dafc8a6f921c1434c49b5f9349bb996b7ed0a4deb8aa7",
        "size_bytes": 3_527_456,
    },
    "guest_kernel": {
        "identity_authenticated": False,
        "selection_status": "pending_governed_selection",
    },
    "jailer_release_binary": {
        "archive_path": "release-v1.16.1-x86_64/jailer-v1.16.1-x86_64",
        "sha256": "1f3a0c1fe86212d0001819bfe0819071c01208b3ccc9398c3b3bc1b84cf21edd",
        "size_bytes": 2_181_264,
    },
    "openapi_spec": {
        "archive_path": "release-v1.16.1-x86_64/firecracker_spec-v1.16.1.yaml",
        "sha256": "a514abec7b29700c5ca8bdaebbb960e4ffb46fe1fd4869094c6c63630a6fa41c",
        "size_bytes": 60_748,
    },
    "release_archive": {
        "name": "firecracker-v1.16.1-x86_64.tgz",
        "sha256": "382a02a869e4d6d5cb14c40577f9545e8458021ea8b0b2d3fc10ec14d9c242e6",
        "size_bytes": 7_486_686,
        "url": "https://github.com/firecracker-microvm/firecracker/releases/download/v1.16.1/firecracker-v1.16.1-x86_64.tgz",
    },
    "release_sha256s": {
        "archive_path": "release-v1.16.1-x86_64/SHA256SUMS",
        "sha256": "3a1f96bf847c561604f62f632f63ed40f28325dafbef8b2eb0cb6625aa51ff86",
        "size_bytes": 2_140,
    },
    "rootfs": {
        "identity_authenticated": False,
        "selection_status": "pending_governed_selection",
    },
    "seccomp_source_policy": {
        "archive_path": (
            "release-v1.16.1-x86_64/seccomp-filter-v1.16.1-x86_64.json"
        ),
        "sha256": "1b683d5c9fc51174ab1926b84aaf10dc2164678f6c2fe7c38a910556d7b5dc39",
        "size_bytes": 50_351,
    },
}
EXPECTED_HOST_POLICY = {
    "architecture": "x86_64",
    "candidate_host_kernel_major_minor_allowlist": ["6.18"],
    "cpu_platform_allowlist_status": "pending_governed_selection",
    "ksm_counters_required_zero": [
        "ksm_zero_pages",
        "pages_shared",
        "pages_sharing",
    ],
    "ksm_run_required": 0,
    "ksm_use_zero_pages_required": 0,
    "page_size_bytes": 4_096,
    "require_cgroup_v2": True,
    "require_kvm_read_write": True,
    "require_swap_disabled": True,
    "required_cgroup_controllers": ["cpu", "cpuset", "io", "memory", "pids"],
    "smt_policy": "must_be_disabled_for_tenant_separation",
}
EXPECTED_RUNNER_POLICY = {
    "allowed_inherited_file_descriptors": [0, 1, 2],
    "api_mode": "no_api_with_canonical_config_file",
    "archive_extraction_policy": [
        "absolute_and_parent_paths_rejected",
        "duplicate_member_paths_rejected",
        "links_devices_fifos_and_sockets_rejected",
        "member_inventory_exact",
        "ownership_and_timestamps_not_preserved",
        "selected_regular_files_only",
        "stable_archive_descriptor_size_and_sha256_verified_before_member_enumeration_or_extraction",
        "stable_descriptor_outputs_rehashed",
    ],
    "archive_extraction_status": "pending_root_owned_launcher",
    "block_device_rate_limits_required": True,
    "boot_timer_allowed": False,
    "built_in_default_seccomp_required": True,
    "cgroup_and_netns_path_symlinks_allowed": False,
    "cgroup_io_max_required": True,
    "cgroup_v2_numeric_limits_status": "pending_measured_replay_envelope",
    "configurable_virtio_device_allowlist": ["virtio-block"],
    "config_file_validation_requirements": [
        "bounded_canonical_json_bytes",
        "duplicate_keys_rejected",
        "exact_drive_count_ids_order_and_backing_types",
        "exact_equality_to_governed_config",
        "exact_root_field_set",
        "unknown_fields_rejected",
    ],
    "core_dump_rlimit_bytes": 0,
    "cpu_affinity_status": "pending_governed_dedicated_cpuset",
    "daemonize": False,
    "dedicated_uid_gid_required": True,
    "drive_profile": [
        {
            "backend": "file",
            "cache_type": "Writeback",
            "drive_id": "rootfs",
            "io_engine": "Sync",
            "is_read_only": True,
            "is_root_device": True,
            "position": 0,
            "rate_limiter_required": True,
        },
        {
            "backend": "file",
            "cache_type": "Writeback",
            "drive_id": "input",
            "io_engine": "Sync",
            "is_read_only": True,
            "is_root_device": False,
            "position": 1,
            "rate_limiter_required": True,
        },
        {
            "backend": "file",
            "cache_type": "Writeback",
            "drive_id": "output",
            "fixed_preallocated_bytes": 16_777_216,
            "io_engine": "Sync",
            "is_read_only": False,
            "is_root_device": False,
            "position": 2,
            "rate_limiter_required": True,
        },
    ],
    "empty_network_namespace_required": True,
    "exact_vm_configuration_required_fields": [
        "boot_args",
        "cpu_template_or_custom_cpu_config",
        "drive_cache_types",
        "drive_count",
        "drive_ids_and_order",
        "drive_io_engines",
        "drive_is_root_device",
        "drive_partuuid",
        "drive_rate_limiters",
        "drive_read_only_flags",
        "huge_pages",
        "mem_size_mib",
        "smt",
        "track_dirty_pages",
        "vcpu_count",
    ],
    "exact_vm_configuration_status": "pending_governed_selection",
    "firecracker_cli_allowed_options": [
        "--config-file",
        "--id",
        "--no-api",
        "--parent-cpu-time-us",
        "--start-time-cpu-us",
        "--start-time-us",
    ],
    "firecracker_cli_forbidden_options": [
        "--boot-timer",
        "--describe-snapshot",
        "--enable-pci",
        "--http-api-max-payload-size",
        "--level",
        "--log-path",
        "--metadata",
        "--metrics-path",
        "--mmds-size-limit",
        "--no-seccomp",
        "--seccomp-filter",
        "--show-level",
        "--show-log-origin",
        "--snapshot-version",
        "--version",
    ],
    "guest_network_device_allowed": False,
    "guest_nested_virtualization_allowed": False,
    "host_network_egress_policy": "deny_all_independent_of_guest_devices",
    "unexpected_inherited_file_descriptors_allowed": False,
    "jail_device_inventory": [
        "dev_kvm",
        "dev_net_tun",
        "dev_urandom",
        "dev_userfaultfd_when_registered",
    ],
    "jail_storage_allowed_backends": [
        "project_quota",
        "size_bounded_one_shot_tmpfs",
    ],
    "jail_storage_numeric_limit_status": "pending_measured_replay_envelope",
    "jail_storage_selected_backend": "pending_governed_selection",
    "jailer_cgroup_membership_postcheck_required": True,
    "jailer_cli_forbidden_options": ["--daemonize"],
    "jailer_cli_required_options": [
        "--cgroup",
        "--cgroup-version=2",
        "--chroot-base-dir",
        "--exec-file",
        "--gid",
        "--id",
        "--netns",
        "--new-pid-ns",
        "--parent-cgroup",
        "--resource-limit",
        "--uid",
    ],
    "jail_id_policy": "fresh_unique_never_reused",
    "jailer_required": True,
    "jailer_injected_timing_values_authority_relevant": False,
    "log_sink_mode": "disabled",
    "metadata_service_allowed": False,
    "metrics_sink_mode": "disabled",
    "netns_identity_verification": "stable_type_and_inode_before_and_after_join",
    "network_namespace_policy": (
        "fresh_per_replay_exclusive_root_owned_fd_held_until_teardown"
    ),
    "network_namespace_lifecycle": {
        "active": [
            "exact_expected_firecracker_process_set",
            "loopback_down",
            "no_addresses",
            "no_non_loopback_links",
            "no_routes",
            "no_rules",
            "same_namespace_inode",
        ],
        "post_teardown": ["same_namespace_inode", "zero_processes"],
        "pre_join": ["same_namespace_inode", "zero_processes"],
    },
    "new_pid_namespace_required": True,
    "output_negative_controls_required": [
        "different_input_root_or_nonce",
        "forged_length_or_payload_hash",
        "missing_commit_marker",
        "partial_header_or_payload",
        "prior_run_valid_output",
        "valid_looking_output_followed_by_timeout_or_crash",
    ],
    "output_protocol_requirements": [
        "commit_marker_written_last_then_fdatasync",
        "exact_fixed_size_fresh_object_created_with_o_excl",
        "firecracker_exit_status_never_authorizes_acceptance",
        "input_bundle_root_bound",
        "payload_length_and_sha256_bound",
        "request_sha256_bound",
        "run_nonce_256_bound",
        "stable_descriptor_read_only_after_vm_exit",
        "trailing_bytes_canonical_zero",
    ],
    "output_transport": "fixed_size_raw_block_device",
    "output_validation": "zrpf_firecracker_raw_output_v1_strict_commit_protocol",
    "pci_enabled": False,
    "post_privilege_drop_dumpability_status": (
        "pending_enforced_launcher_or_runtime_mechanism"
    ),
    "preexisting_jail_root_allowed": False,
    "read_only_input_drive_required": True,
    "read_only_rootfs_required": True,
    "resource_limits_required": [
        "cpu",
        "memory",
        "pids",
        "io",
        "core",
        "fsize",
        "nofile",
        "wall_clock",
    ],
    "secrets_permitted": False,
    "serial_boot_argument": "8250.nr_uarts=0",
    "serial_sink_must_equal_stdout": True,
    "serial_transport": "firecracker_stdout_under_no_api",
    "signing_inside_sandbox": False,
    "snapshots_allowed": False,
    "stdin_source": "dev_null",
    "stdout_stderr_sink_allowed_modes": ["dev_null", "fixed_size"],
    "stdout_stderr_sink_selected_mode": "pending_governed_selection",
    "teardown_policy": "whole_cgroup_reaped_then_unique_jail_removed",
    "trusted_path_policy": (
        "root_owned_non_writable_full_parent_chain_with_stable_descriptor_identity"
    ),
    "unknown_firecracker_cli_options_allowed": False,
    "unknown_jailer_cli_options_allowed": False,
    "userfaultfd_registration_allowed": False,
    "vm_forbidden_configuration_sections": [
        "balloon",
        "entropy",
        "logger",
        "memory_hotplug",
        "metrics",
        "network_interfaces",
        "pmem",
        "serial_override",
        "vsock",
    ],
    "vhost_user_block_allowed": False,
    "vsock_allowed": False,
    "watchdog_policy": "prelaunched_monotonic_deadline_sigkill_whole_cgroup",
    "watchdog_timeout_numeric_status": "pending_measured_replay_envelope",
    "writable_output_max_bytes": 16_777_216,
    "x86_platform_device_inventory": [
        "8250_serial",
        "acpi_ged",
        "i8042_partial_keyboard_controller",
        "ioapic",
        "kvm_clock",
        "lapic",
        "pic",
        "pit",
        "tsc",
        "vmclock",
        "vmgenid",
    ],
}
EXPECTED_SOURCES = [
    "https://github.com/firecracker-microvm/firecracker/releases/tag/v1.16.1",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/docs/design.md",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/docs/jailer.md",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/docs/kernel-policy.md",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/docs/prod-host-setup.md",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/docs/seccomp.md",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/src/jailer/src/env.rs",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/src/firecracker/src/main.rs",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/src/vmm/src/arch/x86_64/mod.rs",
    "https://github.com/firecracker-microvm/firecracker/blob/2038188f145fb81b8d098147a10e9d9f392fd22f/src/vmm/src/builder.rs",
]
EXPECTED_ROOT_FIELDS = {
    "artifacts",
    "claims",
    "host_policy",
    "release",
    "runner_policy",
    "schema",
    "sources",
    "status",
}


def validate_profile(profile_path: Path = PROFILE_PATH) -> dict[str, Any]:
    validation, _ = _validate_profile_document(profile_path)
    return validation


def _validate_profile_document(
    profile_path: Path,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    errors: list[str] = []
    raw: bytes | None = None
    profile: Any = None
    try:
        raw = _read_bounded_regular(profile_path)
        profile = support.strict_json_loads(raw)
    except (
        OSError,
        RecursionError,
        UnicodeDecodeError,
        json.JSONDecodeError,
        ValueError,
    ):
        errors.append("profile_input_rejected")
    try:
        if isinstance(profile, dict):
            if set(profile) != EXPECTED_ROOT_FIELDS:
                errors.append("profile_root_fields_mismatch")
            if raw != _canonical_bytes(profile):
                errors.append("profile_noncanonical")
            if (
                profile.get("schema")
                != "zenodex/zrpf_v3_firecracker_replay_profile/v1"
            ):
                errors.append("profile_schema_mismatch")
            if profile.get("status") != "candidate_incomplete_non_authoritative":
                errors.append("profile_status_mismatch")
            if not _exact_equal(profile.get("claims"), EXPECTED_CLAIMS):
                errors.append("profile_claims_mismatch")
            if not _exact_equal(profile.get("release"), EXPECTED_RELEASE):
                errors.append("profile_release_mismatch")
            if not _exact_equal(profile.get("artifacts"), EXPECTED_ARTIFACTS):
                errors.append("profile_artifacts_mismatch")
            errors.extend(_validate_policy(profile))
            if _canonical_sha256(profile) != EXPECTED_PROFILE_CANONICAL_SHA256:
                errors.append("profile_canonical_hash_mismatch")
        elif profile is not None:
            errors.append("profile_root_not_object")
    except (RecursionError, TypeError, ValueError):
        errors = ["profile_input_rejected"]
        profile = None
    validation = {
        "errors": errors,
        "profile_complete": False,
        "profile_raw_sha256": hashlib.sha256(raw).hexdigest() if raw else None,
        "profile_valid": not errors,
        "schema": "zenodex/zrpf_v3_firecracker_replay_profile_check/v1",
    }
    governed_profile = profile if not errors and isinstance(profile, dict) else None
    return validation, governed_profile


def build_report(*, include_host_probe: bool) -> dict[str, Any]:
    validation, profile = _validate_profile_document(PROFILE_PATH)
    probe: dict[str, Any] | None = None
    if include_host_probe and profile is not None:
        probe = host_probe.evaluate_host_facts(
            profile["host_policy"], host_probe.collect_host_facts()
        )
    return {
        "authority": {
            "covert_channel_freedom": False,
            "hardware_side_channel_resistance": False,
            "host_secret_absence_verified": False,
            "privacy_or_zero_knowledge": False,
            "production_authority": False,
            "release_authority": False,
            "settlement_authority": False,
            "zero_knowledge_privacy": False,
        },
        "host_probe": probe,
        "ok": bool(
            validation["profile_valid"]
            and (
                probe is None
                or probe["candidate_host_policy_checks_passed"]
            )
        ),
        "profile": validation,
        "replay_runner_ready": False,
        "schema": "zenodex/zrpf_v3_firecracker_replay_profile_report/v1",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--probe-host", action="store_true")
    arguments = parser.parse_args(argv)
    try:
        report = build_report(include_host_probe=arguments.probe_host)
    except (OSError, RecursionError, ValueError):
        print("error: Firecracker profile check failed closed", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def _validate_policy(profile: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if not _exact_equal(profile.get("host_policy"), EXPECTED_HOST_POLICY):
        errors.append("host_policy_mismatch")
    if not _exact_equal(profile.get("runner_policy"), EXPECTED_RUNNER_POLICY):
        errors.append("runner_policy_mismatch")
    if not _exact_equal(profile.get("sources"), EXPECTED_SOURCES):
        errors.append("profile_sources_mismatch")
    return errors


def _read_bounded_regular(path: Path) -> bytes:
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or not 0 < before.st_size <= MAX_PROFILE_BYTES
            or before.st_nlink != 1
        ):
            raise ValueError("profile is not a bounded regular file")
        output = bytearray()
        while len(output) < before.st_size:
            chunk = os.read(descriptor, min(65_536, before.st_size - len(output)))
            if not chunk:
                raise ValueError("profile changed while reading")
            output.extend(chunk)
        if os.read(descriptor, 1):
            raise ValueError("profile changed while reading")
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if _identity(before) != _identity(after):
        raise ValueError("profile changed while reading")
    return bytes(output)


def _identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_nlink,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode(
        "ascii"
    )


def _canonical_sha256(value: Any) -> str:
    raw = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return hashlib.sha256(raw).hexdigest()


def _exact_equal(actual: Any, expected: Any) -> bool:
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(
            _exact_equal(actual[key], expected[key]) for key in expected
        )
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            _exact_equal(left, right)
            for left, right in zip(actual, expected, strict=True)
        )
    return bool(actual == expected)


if __name__ == "__main__":
    raise SystemExit(main())
