"""Typed, non-authoritative host facts for a future Firecracker replay lane."""

from __future__ import annotations

import fcntl
import os
import platform
import re
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

MAX_HOST_FACT_BYTES = 1024 * 1024
KVM_API_VERSION = 12
KVM_GET_API_VERSION = 0xAE00
REQUIRED_STRONG_CHECKS = (
    "architecture_matches",
    "cgroup_v2_mounted",
    "host_kernel_version_listed",
    "hypervisor_cpuid_flag_absent",
    "ksm_disabled_and_clean",
    "kvm_character_device",
    "kvm_api_version_supported",
    "kvm_read_write",
    "page_size_matches",
    "required_cgroup_controllers_present",
    "smt_disabled",
    "swap_disabled",
)
REQUIRED_KVM_CHECKS = (
    "architecture_matches",
    "cgroup_v2_mounted",
    "kvm_character_device",
    "kvm_api_version_supported",
    "kvm_read_write",
    "page_size_matches",
    "required_cgroup_controllers_present",
)
AUTHORITY_NONCLAIMS = (
    "covert_channel_freedom",
    "hardware_side_channel_resistance",
    "host_secret_absence_verified",
    "host_secret_isolation",
    "microvm_replay_verified",
    "production_authority",
    "release_authority",
    "sandbox_escape_resistance",
    "settlement_authority",
    "witness_privacy",
    "zero_knowledge_privacy",
)
UNVERIFIED_REQUIREMENTS = (
    "artifact_and_input_path_immutability",
    "bare_metal_attestation_beyond_cpuid_flag",
    "cgroup_delegation_limits_and_membership",
    "cpu_platform_and_microcode_allowlist",
    "dedicated_uid_gid_allocation",
    "default_seccomp_active",
    "firmware_microcode_and_host_vulnerability_posture",
    "fresh_empty_netns_and_deny_all_egress",
    "guest_cpu_template_and_nested_virtualization",
    "guest_kernel_rootfs_and_config_identity",
    "host_posture_enforced_for_runner_lifetime",
    "jail_storage_quota",
    "kvm_pit_thread_containment",
    "logger_metrics_and_serial_runtime_bounds",
    "output_extraction_and_canonical_validation",
    "runtime_artifact_identity_and_version",
    "whole_cgroup_teardown_and_jail_cleanup",
)


@dataclass(frozen=True)
class HostProbePaths:
    cgroup_controllers: Path = Path("/sys/fs/cgroup/cgroup.controllers")
    cpuinfo: Path = Path("/proc/cpuinfo")
    ksm_pages_shared: Path = Path("/sys/kernel/mm/ksm/pages_shared")
    ksm_pages_sharing: Path = Path("/sys/kernel/mm/ksm/pages_sharing")
    ksm_run: Path = Path("/sys/kernel/mm/ksm/run")
    ksm_use_zero_pages: Path = Path("/sys/kernel/mm/ksm/use_zero_pages")
    ksm_zero_pages: Path = Path("/sys/kernel/mm/ksm/ksm_zero_pages")
    kvm: Path = Path("/dev/kvm")
    mountinfo: Path = Path("/proc/self/mountinfo")
    smt_active: Path = Path("/sys/devices/system/cpu/smt/active")
    swaps: Path = Path("/proc/swaps")


@dataclass(frozen=True)
class HostFacts:
    architecture: str
    cgroup_controllers: frozenset[str]
    cgroup_v2_mounted: bool
    cpu_family: str | None
    cpu_microcode: str | None
    cpu_model: str | None
    cpu_vendor: str | None
    host_kernel_release: str
    hypervisor_present: bool | None
    ksm_pages_shared: int | None
    ksm_pages_sharing: int | None
    ksm_run: int | None
    ksm_use_zero_pages: int | None
    ksm_zero_pages: int | None
    kvm_api_version: int | None
    kvm_character_device: bool
    kvm_read_write: bool
    page_size_bytes: int
    smt_active: bool | None
    swap_active: bool | None


def collect_host_facts(paths: HostProbePaths | None = None) -> HostFacts:
    """Collect bounded public posture facts without emitting host paths or names."""

    paths = HostProbePaths() if paths is None else paths
    controllers = _read_text(paths.cgroup_controllers)
    cpu_identity = _parse_cpuinfo(_read_text(paths.cpuinfo))
    mountinfo = _read_text(paths.mountinfo)
    kvm_character_device, kvm_read_write, kvm_api_version = _probe_kvm(paths.kvm)
    return HostFacts(
        architecture=platform.machine(),
        cgroup_controllers=frozenset(controllers.split()) if controllers else frozenset(),
        cgroup_v2_mounted=_has_cgroup_v2_mount(mountinfo),
        cpu_family=cpu_identity[1],
        cpu_microcode=cpu_identity[3],
        cpu_model=cpu_identity[2],
        cpu_vendor=cpu_identity[0],
        host_kernel_release=platform.release(),
        hypervisor_present=cpu_identity[4],
        ksm_pages_shared=_parse_integer(_read_text(paths.ksm_pages_shared)),
        ksm_pages_sharing=_parse_integer(_read_text(paths.ksm_pages_sharing)),
        ksm_run=_parse_integer(_read_text(paths.ksm_run)),
        ksm_use_zero_pages=_parse_integer(_read_text(paths.ksm_use_zero_pages)),
        ksm_zero_pages=_parse_integer(_read_text(paths.ksm_zero_pages)),
        kvm_api_version=kvm_api_version,
        kvm_character_device=kvm_character_device,
        kvm_read_write=kvm_read_write,
        page_size_bytes=int(os.sysconf("SC_PAGE_SIZE")),
        smt_active=_parse_binary(_read_text(paths.smt_active)),
        swap_active=_parse_swaps(_read_text(paths.swaps)),
    )


def evaluate_host_facts(policy: Mapping[str, Any], facts: HostFacts) -> dict[str, Any]:
    """Evaluate typed observations against the governed candidate host policy."""

    checks = _evaluate_checks(policy, facts)
    failed_checks = [name for name in REQUIRED_STRONG_CHECKS if not checks[name]]
    return {
        "authority": {name: False for name in AUTHORITY_NONCLAIMS},
        "checks": checks,
        "failed_checks": failed_checks,
        "base_host_prerequisite_checks_passed": all(
            checks[name] for name in REQUIRED_KVM_CHECKS
        ),
        "observations": _host_observations(facts),
        "replay_runner_ready": False,
        "schema": "zenodex/zrpf_v3_firecracker_host_probe/v1",
        "candidate_host_prerequisites_passed": not failed_checks,
        "representative_unverified_requirements": list(UNVERIFIED_REQUIREMENTS),
    }


def _evaluate_checks(
    policy: Mapping[str, Any], facts: HostFacts
) -> dict[str, bool]:
    required_controllers = frozenset(policy["required_cgroup_controllers"])
    listed_kernels = frozenset(
        policy["candidate_host_kernel_major_minor_allowlist"]
    )
    return {
        "architecture_matches": facts.architecture == policy["architecture"],
        "cgroup_v2_mounted": facts.cgroup_v2_mounted,
        "host_kernel_version_listed": (
            _kernel_major_minor(facts.host_kernel_release) in listed_kernels
        ),
        "hypervisor_cpuid_flag_absent": (
            policy["nested_virtualization_allowed"] is False
            and facts.hypervisor_present is False
        ),
        "ksm_disabled_and_clean": (
            facts.ksm_run == policy["ksm_run_required"]
            and facts.ksm_use_zero_pages
            == policy["ksm_use_zero_pages_required"]
            and facts.ksm_pages_shared == 0
            and facts.ksm_pages_sharing == 0
            and facts.ksm_zero_pages == 0
        ),
        "kvm_character_device": facts.kvm_character_device,
        "kvm_api_version_supported": facts.kvm_api_version == KVM_API_VERSION,
        "kvm_read_write": facts.kvm_read_write,
        "page_size_matches": facts.page_size_bytes == policy["page_size_bytes"],
        "required_cgroup_controllers_present": required_controllers.issubset(
            facts.cgroup_controllers
        ),
        "smt_disabled": facts.smt_active is False,
        "swap_disabled": facts.swap_active is False,
    }


def _host_observations(facts: HostFacts) -> dict[str, Any]:
    return {
        "architecture": facts.architecture,
        "cgroup_controller_count": len(facts.cgroup_controllers),
        "cpu_family": facts.cpu_family,
        "cpu_microcode": facts.cpu_microcode,
        "cpu_model": facts.cpu_model,
        "cpu_vendor": facts.cpu_vendor,
        "host_kernel_major_minor": _kernel_major_minor(facts.host_kernel_release),
        "hypervisor_present": facts.hypervisor_present,
        "ksm_pages_shared": facts.ksm_pages_shared,
        "ksm_pages_sharing": facts.ksm_pages_sharing,
        "ksm_run": facts.ksm_run,
        "ksm_use_zero_pages": facts.ksm_use_zero_pages,
        "ksm_zero_pages": facts.ksm_zero_pages,
        "kvm_api_version": facts.kvm_api_version,
        "page_size_bytes": facts.page_size_bytes,
        "smt_active": facts.smt_active,
        "swap_active": facts.swap_active,
    }


def _probe_kvm(path: Path) -> tuple[bool, bool, int | None]:
    try:
        metadata = path.lstat()
    except OSError:
        return False, False, None
    if path.is_symlink() or not stat.S_ISCHR(metadata.st_mode):
        return False, False, None
    flags = os.O_RDWR | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError:
        return True, False, None
    try:
        opened = os.fstat(descriptor)
        character_device = stat.S_ISCHR(opened.st_mode) and _same_device(
            metadata, opened
        )
        if not character_device:
            return False, False, None
        try:
            api_version = int(fcntl.ioctl(descriptor, KVM_GET_API_VERSION))
        except OSError:
            api_version = None
        return True, True, api_version
    finally:
        os.close(descriptor)


def _same_device(before: os.stat_result, after: os.stat_result) -> bool:
    return (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_rdev,
    ) == (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_rdev,
    )


def _read_text(path: Path) -> str | None:
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        descriptor = os.open(path, flags)
    except OSError:
        return None
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            return None
        output = bytearray()
        while len(output) <= MAX_HOST_FACT_BYTES:
            chunk = os.read(descriptor, min(65_536, MAX_HOST_FACT_BYTES + 1 - len(output)))
            if not chunk:
                break
            output.extend(chunk)
        after = os.fstat(descriptor)
        if len(output) > MAX_HOST_FACT_BYTES or _stable_identity(before) != _stable_identity(after):
            return None
        return bytes(output).decode("ascii", errors="strict")
    except (OSError, UnicodeDecodeError):
        return None
    finally:
        os.close(descriptor)


def _stable_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _has_cgroup_v2_mount(raw: str | None) -> bool:
    if raw is None:
        return False
    for line in raw.splitlines():
        fields = line.split()
        if "-" not in fields:
            continue
        separator = fields.index("-")
        if separator + 1 >= len(fields) or len(fields) < 5:
            continue
        if fields[4] == "/sys/fs/cgroup" and fields[separator + 1] == "cgroup2":
            return True
    return False


def _kernel_major_minor(release: str) -> str | None:
    match = re.fullmatch(r"([0-9]+)\.([0-9]+)(?:[.-].*)?", release)
    return f"{match.group(1)}.{match.group(2)}" if match else None


def _parse_cpuinfo(
    raw: str | None,
) -> tuple[str | None, str | None, str | None, str | None, bool | None]:
    empty: tuple[str | None, str | None, str | None, str | None, bool | None]
    empty = (None, None, None, None, None)
    if raw is None:
        return empty
    processor_blocks = [
        block for block in re.split(r"\n\s*\n", raw.strip()) if block.strip()
    ]
    if not processor_blocks:
        return empty
    parsed_blocks = [_parse_cpuinfo_block(block) for block in processor_blocks]
    if any(block is None for block in parsed_blocks):
        return empty
    complete_blocks = [block for block in parsed_blocks if block is not None]
    identities = {
        (
            block["vendor_id"],
            block["cpu family"],
            block["model"],
            block["microcode"],
        )
        for block in complete_blocks
    }
    if len(identities) != 1:
        return empty
    identity = next(iter(identities))
    return (*identity, any("hypervisor" in block["flags"].split() for block in complete_blocks))


def _parse_cpuinfo_block(raw: str) -> dict[str, str] | None:
    selected: dict[str, str] = {}
    field_limits = {
        "cpu family": 128,
        "flags": 16 * 1024,
        "microcode": 128,
        "model": 128,
        "vendor_id": 128,
    }
    for line in raw.splitlines():
        if ":" not in line:
            continue
        name, value = (part.strip() for part in line.split(":", 1))
        if name not in field_limits:
            continue
        if name in selected or not _bounded_printable_ascii(value, field_limits[name]):
            return None
        selected[name] = value
    return selected if selected.keys() == field_limits.keys() else None


def _bounded_printable_ascii(value: str, maximum: int) -> bool:
    return bool(
        value
        and len(value) <= maximum
        and value.isascii()
        and all(32 <= ord(character) <= 126 for character in value)
    )


def _parse_binary(raw: str | None) -> bool | None:
    if raw is None:
        return None
    value = raw.strip()
    if value == "0":
        return False
    if value == "1":
        return True
    return None


def _parse_integer(raw: str | None) -> int | None:
    if raw is None:
        return None
    value = raw.strip()
    if not value or not value.isascii() or not value.isdecimal():
        return None
    return int(value)


def _parse_swaps(raw: str | None) -> bool | None:
    if raw is None:
        return None
    lines = [line for line in raw.splitlines() if line.strip()]
    if not lines or not lines[0].split()[:2] == ["Filename", "Type"]:
        return None
    return len(lines) > 1
