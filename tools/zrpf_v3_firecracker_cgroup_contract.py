"""Pure finite-resource and jailer-attachment contract for ZRPF cgroup v2."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import Mapping

REQUIRED_CONTROLLERS = frozenset({"cpu", "cpuset", "io", "memory", "pids"})
LIMIT_FILE_ORDER = (
    "cpu.max",
    "cpuset.cpus",
    "cpuset.mems",
    "io.max",
    "memory.high",
    "memory.max",
    "memory.oom.group",
    "memory.swap.max",
    "pids.max",
)
_COMPONENT = re.compile(r"[a-z0-9][a-z0-9-]{7,63}\Z")
_IO_MAX = re.compile(
    r"(?P<major>[0-9]+):(?P<minor>[0-9]+) "
    r"rbps=(?P<rbps>[1-9][0-9]*) wbps=(?P<wbps>[1-9][0-9]*) "
    r"riops=(?P<riops>[1-9][0-9]*) wiops=(?P<wiops>[1-9][0-9]*)\Z"
)


class CgroupV2Reject(RuntimeError):
    """Stable fail-closed rejection at the cgroup lifecycle boundary."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class CgroupLimitsV1:
    """Exact finite limits installed before the jailer is started."""

    cpu_quota_us: int
    cpu_period_us: int
    cpuset_cpus: str
    cpuset_mems: str
    io_max: str
    memory_high_bytes: int
    memory_max_bytes: int
    memory_swap_max_bytes: int
    pids_max: int

    def __post_init__(self) -> None:
        integer_limits = (
            self.cpu_quota_us,
            self.cpu_period_us,
            self.memory_high_bytes,
            self.memory_max_bytes,
            self.memory_swap_max_bytes,
            self.pids_max,
        )
        if any(type(value) is not int for value in integer_limits):
            raise CgroupV2Reject("cgroup_numeric_limit_type_invalid")
        if not 1_000 <= self.cpu_period_us <= 1_000_000:
            raise CgroupV2Reject("cgroup_cpu_period_invalid")
        if not 1_000 <= self.cpu_quota_us <= self.cpu_period_us * 64:
            raise CgroupV2Reject("cgroup_cpu_quota_invalid")
        parse_cpu_set(self.cpuset_cpus, "cgroup_cpuset_cpus_invalid")
        parse_cpu_set(self.cpuset_mems, "cgroup_cpuset_mems_invalid")
        match = _IO_MAX.fullmatch(self.io_max)
        if match is None or any(int(value) > (1 << 63) - 1 for value in match.groupdict().values()):
            raise CgroupV2Reject("cgroup_io_max_invalid")
        if not 256 * 1024 * 1024 <= self.memory_high_bytes <= self.memory_max_bytes:
            raise CgroupV2Reject("cgroup_memory_high_invalid")
        if not self.memory_high_bytes <= self.memory_max_bytes <= 64 * 1024**3:
            raise CgroupV2Reject("cgroup_memory_max_invalid")
        if not 0 <= self.memory_swap_max_bytes <= self.memory_max_bytes:
            raise CgroupV2Reject("cgroup_memory_swap_invalid")
        if not 2 <= self.pids_max <= 4096:
            raise CgroupV2Reject("cgroup_pids_max_invalid")

    def file_values(self) -> dict[str, str]:
        return {
            "cpu.max": f"{self.cpu_quota_us} {self.cpu_period_us}",
            "cpuset.cpus": self.cpuset_cpus,
            "cpuset.mems": self.cpuset_mems,
            "io.max": self.io_max,
            "memory.high": str(self.memory_high_bytes),
            "memory.max": str(self.memory_max_bytes),
            "memory.oom.group": "1",
            "memory.swap.max": str(self.memory_swap_max_bytes),
            "pids.max": str(self.pids_max),
        }


def parse_cpu_set(value: str, code: str) -> frozenset[int]:
    if not value or any(character not in "0123456789,-" for character in value):
        raise CgroupV2Reject(code)
    output: set[int] = set()
    for part in value.split(","):
        fields = part.split("-")
        if len(fields) == 1 and fields[0].isdigit():
            lower = upper = int(fields[0])
        elif len(fields) == 2 and all(field.isdigit() for field in fields):
            lower, upper = (int(field) for field in fields)
        else:
            raise CgroupV2Reject(code)
        if lower > upper or upper > 4095:
            raise CgroupV2Reject(code)
        for item in range(lower, upper + 1):
            if item in output:
                raise CgroupV2Reject(code)
            output.add(item)
    if not output or _format_cpu_set(output) != value:
        raise CgroupV2Reject(code)
    return frozenset(output)


def relative_components(value: str) -> tuple[str, ...]:
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or len(path.parts) > 8:
        raise CgroupV2Reject("cgroup_parent_path_invalid")
    if any(
        part in {"", ".", ".."} or len(part) > 64 or _COMPONENT.fullmatch(part) is None
        for part in path.parts
    ):
        raise CgroupV2Reject("cgroup_parent_path_invalid")
    return tuple(path.parts)


def require_leaf_name(value: str) -> None:
    if not isinstance(value, str) or _COMPONENT.fullmatch(value) is None:
        raise CgroupV2Reject("cgroup_leaf_name_invalid")


def validate_jailer_cgroup_arguments(arguments: list[str]) -> None:
    """Reject every jailer cgroup-property form and require exact v2 attachment."""

    if any(argument == "--cgroup" or argument.startswith("--cgroup=") for argument in arguments):
        raise CgroupV2Reject("jailer_cgroup_property_forbidden")
    versions = [argument for argument in arguments if argument.startswith("--cgroup-version")]
    parents = [argument for argument in arguments if argument.startswith("--parent-cgroup")]
    if versions != ["--cgroup-version=2"] or parents != ["--parent-cgroup"]:
        raise CgroupV2Reject("jailer_cgroup_attachment_arguments_invalid")


def authority_nonclaims() -> Mapping[str, bool]:
    """Granular claims intentionally left false without a live privileged replay."""

    return {
        "chroot_base_live_verified": False,
        "cgroup_limits_live_verified": False,
        "cgroup_membership_live_verified": False,
        "descriptor_bound_exec_handoff_verified": False,
        "external_watchdog_live_verified": False,
        "firecracker_jailer_live_verified": False,
        "io_backing_device_binding_live_verified": False,
        "network_namespace_exclusive_live_verified": False,
        "network_namespace_live_verified": False,
        "production_authority": False,
        "root_owned_launcher_live_verified": False,
        "sandbox_escape_resistance": False,
        "settlement_authority": False,
    }


def _format_cpu_set(values: set[int]) -> str:
    ordered = sorted(values)
    ranges: list[str] = []
    start = previous = ordered[0]
    for value in ordered[1:]:
        if value == previous + 1:
            previous = value
            continue
        ranges.append(str(start) if start == previous else f"{start}-{previous}")
        start = previous = value
    ranges.append(str(start) if start == previous else f"{start}-{previous}")
    return ",".join(ranges)
