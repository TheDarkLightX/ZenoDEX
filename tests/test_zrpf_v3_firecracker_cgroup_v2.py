from __future__ import annotations

import os
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest

from tools import zrpf_v3_firecracker_cgroup_v2 as cgroup


def _valid_limits() -> cgroup.CgroupLimitsV1:
    return cgroup.CgroupLimitsV1(
        cpu_quota_us=100_000,
        cpu_period_us=100_000,
        cpuset_cpus="0",
        cpuset_mems="0",
        io_max="8:0 rbps=1048576 wbps=1048576 riops=1024 wiops=1024",
        memory_high_bytes=256 * 1024 * 1024,
        memory_max_bytes=512 * 1024 * 1024,
        memory_swap_max_bytes=0,
        pids_max=64,
    )


@pytest.mark.parametrize(
    ("field", "value", "code"),
    (
        ("cgroup_mount", Path("relative/cgroup"), "cgroup_request_path_invalid"),
        ("cgroup_mount", Path("/sys/fs/../cgroup"), "cgroup_request_path_invalid"),
        ("cgroup_mount", Path("/sys/fs/unsafe path"), "cgroup_request_path_invalid"),
        ("cgroup_mount", Path("/sys/fs/unsafe\npath"), "cgroup_request_path_invalid"),
        ("cgroup_mount", "/sys/fs/cgroup", "cgroup_request_path_invalid"),
        ("mountinfo_path", Path("relative/mountinfo"), "cgroup_request_path_invalid"),
        ("proc_root", Path("relative/proc"), "cgroup_request_path_invalid"),
        ("parent_relative_path", 7, "cgroup_parent_path_invalid"),
        ("leaf_name", 7, "cgroup_leaf_name_invalid"),
        ("limits", object(), "cgroup_request_limits_invalid"),
        ("trusted_uid", False, "cgroup_request_trusted_uid_invalid"),
        ("trusted_uid", -1, "cgroup_request_trusted_uid_invalid"),
        ("trusted_uid", 1 << 31, "cgroup_request_trusted_uid_invalid"),
    ),
)
def test_create_request_rejects_ambiguous_or_noncanonical_fields(
    field: str,
    value: object,
    code: str,
) -> None:
    kwargs: dict[str, object] = {
        "cgroup_mount": Path("/sys/fs/cgroup"),
        "parent_relative_path": "zenodex01/zrpf0001",
        "leaf_name": "run00001",
        "limits": _valid_limits(),
        "mountinfo_path": Path("/proc/self/mountinfo"),
        "proc_root": Path("/proc"),
        "trusted_uid": 0,
    }
    kwargs[field] = value

    with pytest.raises(cgroup.CgroupV2Reject) as captured:
        cgroup.CgroupCreateRequestV1(**kwargs)  # type: ignore[arg-type]

    assert captured.value.code == code


def test_mutated_request_rejects_before_any_cgroup_path_is_opened(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = cgroup.CgroupCreateRequestV1(
        cgroup_mount=Path("/sys/fs/cgroup"),
        parent_relative_path="zenodex01/zrpf0001",
        leaf_name="run00001",
        limits=_valid_limits(),
    )
    object.__setattr__(request, "trusted_uid", False)
    monkeypatch.setattr(
        cgroup.cgroup_io,
        "open_trusted_directory",
        lambda *_args, **_kwargs: pytest.fail("invalid request reached filesystem effects"),
    )

    with pytest.raises(cgroup.CgroupV2Reject) as captured:
        cgroup.create_cgroup_leaf_from_request(request)

    assert captured.value.code == "cgroup_request_trusted_uid_invalid"


def test_mutated_nested_limits_reject_before_any_cgroup_path_is_opened(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = cgroup.CgroupCreateRequestV1(
        cgroup_mount=Path("/sys/fs/cgroup"),
        parent_relative_path="zenodex01/zrpf0001",
        leaf_name="run00001",
        limits=_valid_limits(),
    )
    object.__setattr__(request.limits, "pids_max", False)
    monkeypatch.setattr(
        cgroup.cgroup_io,
        "open_trusted_directory",
        lambda *_args, **_kwargs: pytest.fail("invalid limits reached filesystem effects"),
    )

    with pytest.raises(cgroup.CgroupV2Reject) as captured:
        cgroup.create_cgroup_leaf_from_request(request)

    assert captured.value.code == "cgroup_numeric_limit_type_invalid"


def test_fresh_leaf_installs_and_rechecks_exact_finite_limits(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)

    leaf = fixture.create_leaf()

    leaf.verify_prelaunch()
    assert leaf.identity.relative_path == "/zenodex01/zrpf0001/run00001"
    for name, value in fixture.limits.file_values().items():
        assert (fixture.leaf_path / name).read_text(encoding="ascii") == f"{value}\n"
    leaf.close_without_removal()


def test_existing_leaf_rejects_instead_of_inheriting_stale_state(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    fixture.leaf_path.mkdir()

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_leaf_not_fresh"):
        fixture.create_leaf()


def test_descriptor_safe_absence_accepts_only_removed_exact_leaf(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    request = cgroup.CgroupCreateRequestV1(
        cgroup_mount=fixture.mount,
        parent_relative_path="zenodex01/zrpf0001",
        leaf_name="run00001",
        limits=fixture.limits,
        mountinfo_path=fixture.mountinfo,
        proc_root=fixture.proc_root,
        trusted_uid=os.getuid(),
    )

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_leaf_still_exists"):
        cgroup.require_cgroup_leaf_absent_from_request(request)

    leaf.close_without_removal()
    for control_file in fixture.leaf_path.iterdir():
        control_file.unlink()
    fixture.leaf_path.rmdir()
    cgroup.require_cgroup_leaf_absent_from_request(request)


def test_absence_check_rejects_replaced_leaf_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    leaf.close_without_removal()
    fixture.leaf_path.rename(fixture.parent / "old-run00001")
    fixture.leaf_path.mkdir()
    request = cgroup.CgroupCreateRequestV1(
        cgroup_mount=fixture.mount,
        parent_relative_path="zenodex01/zrpf0001",
        leaf_name="run00001",
        limits=fixture.limits,
        mountinfo_path=fixture.mountinfo,
        proc_root=fixture.proc_root,
        trusted_uid=os.getuid(),
    )

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_leaf_still_exists"):
        cgroup.require_cgroup_leaf_absent_from_request(request)


def test_limit_mutation_rejects_before_jailer_membership_is_trusted(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    (fixture.leaf_path / "memory.max").write_text("999999999\n", encoding="ascii")

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_numeric_limit_mismatch"):
        leaf.verify_prelaunch()
    leaf.close_without_removal()


def test_control_file_symlink_rejects_without_following_external_target(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    external = tmp_path / "external-limit"
    external.write_text(str(fixture.limits.memory_max_bytes), encoding="ascii")
    (fixture.leaf_path / "memory.max").unlink()
    (fixture.leaf_path / "memory.max").symlink_to(external)

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_control_open_failed"):
        leaf.verify_prelaunch()
    leaf.close_without_removal()


def test_path_replacement_rejects_even_while_original_leaf_descriptor_is_open(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    moved = fixture.parent / "run-moved"
    fixture.leaf_path.rename(moved)
    fixture.leaf_path.mkdir()

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_leaf_path_identity_changed"):
        leaf.verify_prelaunch()
    leaf.close_without_removal()


def test_exact_active_process_set_and_proc_membership_are_both_required(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123, 124})

    leaf.verify_active_membership(frozenset({123, 124}))
    (fixture.proc_root / "124" / "cgroup").write_text("0::/attacker\n", encoding="ascii")

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_process_membership_mismatch"):
        leaf.verify_active_membership(frozenset({123, 124}))
    leaf.close_without_removal()


def test_unexpected_process_in_leaf_rejects_exact_membership(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123, 124})

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_active_process_set_mismatch"):
        leaf.verify_active_membership(frozenset({123}))
    leaf.close_without_removal()


def test_active_processes_must_form_one_descendant_tree_from_spawned_jailer(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123, 124}, parents={123: 1, 124: 123})

    assert leaf.verify_active_descendant_set(123) == frozenset({123, 124})
    (fixture.proc_root / "124" / "stat").write_text(
        _proc_stat(124, parent=999),
        encoding="ascii",
    )

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_active_non_descendant_process"):
        leaf.verify_active_descendant_set(123)
    leaf.close_without_removal()


def test_active_leaf_rejects_hidden_descendant_cgroup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123}, parents={123: 1})
    (fixture.leaf_path / "cgroup.stat").write_text("nr_descendants 1\n", encoding="ascii")

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_active_descendants_present"):
        leaf.verify_active_descendant_set(123)
    leaf.close_without_removal()


def test_active_leaf_rejects_pid_reuse_between_identity_snapshots(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123}, parents={123: 1})
    real_read = cgroup.cgroup_io.read_process_identities
    call_count = 0

    def unstable_read(proc_root: Path, pids: frozenset[int]) -> dict[int, tuple[int, int]]:
        nonlocal call_count
        call_count += 1
        observed = real_read(proc_root, pids)
        if call_count == 2:
            parent, start_time = observed[123]
            observed[123] = (parent, start_time + 1)
        return observed

    monkeypatch.setattr(cgroup.cgroup_io, "read_process_identities", unstable_read)

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_active_process_identity_unstable"):
        leaf.verify_active_descendant_set(123)
    leaf.close_without_removal()


def test_teardown_writes_literal_kill_waits_for_empty_and_removes_leaf(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123})
    observed_kill: list[bytes] = []
    real_rmdir = os.rmdir

    def finish_processes() -> None:
        (fixture.leaf_path / "cgroup.events").write_text("populated 0\n", encoding="ascii")
        (fixture.leaf_path / "cgroup.procs").write_text("", encoding="ascii")

    def remove_fake_leaf(path: str, *, dir_fd: int | None = None) -> None:
        if path == fixture.leaf_path.name and dir_fd is not None:
            observed_kill.append((fixture.leaf_path / "cgroup.kill").read_bytes())
            for child in fixture.leaf_path.iterdir():
                child.unlink()
        real_rmdir(path, dir_fd=dir_fd)

    monkeypatch.setattr(os, "rmdir", remove_fake_leaf)
    clock = iter((10, 11, 12, 13))

    leaf.terminate_and_remove(
        timeout_ns=1_000_000,
        monotonic_ns=lambda: next(clock),
        wait_once=finish_processes,
    )

    assert observed_kill == [b"1\n"]
    assert not fixture.leaf_path.exists()


def test_teardown_timeout_preserves_leaf_for_supervisor_recovery(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123})
    clock = iter((0, 2_000_000))

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_teardown_timeout"):
        leaf.terminate_and_remove(
            timeout_ns=1_000_000,
            monotonic_ns=lambda: next(clock),
            wait_once=lambda: None,
        )

    assert fixture.leaf_path.exists()
    leaf.close_without_removal()


def test_natural_completion_waits_for_empty_and_removes_without_kill(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123})
    real_rmdir = os.rmdir
    observed_kill: list[bytes] = []

    def finish_processes() -> None:
        (fixture.leaf_path / "cgroup.events").write_text("populated 0\n", encoding="ascii")
        (fixture.leaf_path / "cgroup.procs").write_text("", encoding="ascii")

    def remove_fake_leaf(path: str, *, dir_fd: int | None = None) -> None:
        if path == fixture.leaf_path.name and dir_fd is not None:
            observed_kill.append((fixture.leaf_path / "cgroup.kill").read_bytes())
            for child in fixture.leaf_path.iterdir():
                child.unlink()
        real_rmdir(path, dir_fd=dir_fd)

    monkeypatch.setattr(os, "rmdir", remove_fake_leaf)
    clock = iter((10, 11, 12, 13))

    leaf.wait_until_empty_and_remove(
        timeout_ns=1_000_000,
        monotonic_ns=lambda: next(clock),
        wait_once=finish_processes,
    )

    assert observed_kill == [b""]
    assert not fixture.leaf_path.exists()


def test_natural_completion_timeout_preserves_live_leaf_without_kill(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _FakeCgroupV2(tmp_path, monkeypatch)
    leaf = fixture.create_leaf()
    fixture.activate({123})
    clock = iter((0, 2_000_000))

    with pytest.raises(cgroup.CgroupV2Reject, match="cgroup_natural_completion_timeout"):
        leaf.wait_until_empty_and_remove(
            timeout_ns=1_000_000,
            monotonic_ns=lambda: next(clock),
            wait_once=lambda: None,
        )

    assert (fixture.leaf_path / "cgroup.kill").read_bytes() == b""
    assert fixture.leaf_path.exists()
    leaf.close_without_removal()


@pytest.mark.parametrize(
    "arguments",
    (
        ["--cgroup-version=2", "--parent-cgroup", "--cgroup", "memory.max=1"],
        ["--cgroup-version=2", "--parent-cgroup", "--cgroup=memory.max=1"],
        ["--cgroup-version=1", "--parent-cgroup"],
        ["--cgroup-version=2", "--parent-cgroup=attacker"],
    ),
)
def test_jailer_attachment_rejects_property_or_ambiguous_forms(arguments: list[str]) -> None:
    with pytest.raises(cgroup.CgroupV2Reject):
        cgroup.validate_jailer_cgroup_arguments(arguments)


def test_jailer_attachment_accepts_only_exact_precreated_leaf_mode() -> None:
    cgroup.validate_jailer_cgroup_arguments(
        ["--cgroup-version=2", "--parent-cgroup", "zenodex01/zrpf0001/run00001"]
    )


def test_all_launcher_authority_claims_remain_false_without_live_replay() -> None:
    assert all(value is False for value in cgroup.authority_nonclaims().values())


@pytest.mark.parametrize(
    ("changes", "reject_code"),
    (
        ({"cpu_quota_us": True}, "cgroup_numeric_limit_type_invalid"),
        ({"cpu_period_us": 999}, "cgroup_cpu_period_invalid"),
        ({"cpu_quota_us": 999}, "cgroup_cpu_quota_invalid"),
        ({"cpuset_cpus": "0,1"}, "cgroup_cpuset_cpus_invalid"),
        ({"io_max": "8:0 rbps=0 wbps=1 riops=1 wiops=1"}, "cgroup_io_max_invalid"),
        ({"memory_high_bytes": 1}, "cgroup_memory_high_invalid"),
        ({"memory_max_bytes": 65 * 1024**3}, "cgroup_memory_max_invalid"),
        ({"memory_swap_max_bytes": 769 * 1024**2}, "cgroup_memory_swap_invalid"),
        ({"pids_max": 1}, "cgroup_pids_max_invalid"),
    ),
)
def test_finite_limit_boundary_atlas_rejects_one_predicate_flip(
    changes: dict[str, object],
    reject_code: str,
) -> None:
    with pytest.raises(cgroup.CgroupV2Reject, match=reject_code):
        _replace_one_limit_for_negative_test(changes)


def _replace_one_limit_for_negative_test(
    changes: dict[str, object],
) -> cgroup.CgroupLimitsV1:
    if len(changes) != 1:
        raise ValueError("negative limit test requires exactly one changed field")
    name, value = next(iter(changes.items()))
    limits = _limits()
    if name == "cpu_quota_us":
        return replace(limits, cpu_quota_us=cast(int, value))
    if name == "cpu_period_us":
        return replace(limits, cpu_period_us=cast(int, value))
    if name == "cpuset_cpus":
        return replace(limits, cpuset_cpus=cast(str, value))
    if name == "io_max":
        return replace(limits, io_max=cast(str, value))
    if name == "memory_high_bytes":
        return replace(limits, memory_high_bytes=cast(int, value))
    if name == "memory_max_bytes":
        return replace(limits, memory_max_bytes=cast(int, value))
    if name == "memory_swap_max_bytes":
        return replace(limits, memory_swap_max_bytes=cast(int, value))
    if name == "pids_max":
        return replace(limits, pids_max=cast(int, value))
    raise ValueError(f"unsupported negative limit field: {name}")


class _FakeCgroupV2:
    def __init__(self, root: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        self.mount = root / "cgroup2"
        self.parent = self.mount / "zenodex01" / "zrpf0001"
        self.leaf_path = self.parent / "run00001"
        self.proc_root = root / "proc"
        self.mount.mkdir(mode=0o700)
        (self.mount / "zenodex01").mkdir(mode=0o700)
        self.parent.mkdir(mode=0o700)
        self.proc_root.mkdir(mode=0o700)
        self.mountinfo = root / "mountinfo"
        device = self.mount.stat().st_dev
        self.mountinfo.write_text(
            f"10 9 {os.major(device)}:{os.minor(device)} / {self.mount.as_posix()} rw - "
            "cgroup2 cgroup2 rw\n",
            encoding="ascii",
        )
        _write(self.parent / "cgroup.controllers", "cpu cpuset io memory pids\n")
        _write(self.parent / "cgroup.subtree_control", "cpu cpuset io memory pids\n")
        _write(self.parent / "cpuset.cpus.effective", "0-3\n")
        _write(self.parent / "cpuset.mems.effective", "0\n")
        self.limits = _limits()
        real_mkdir = os.mkdir

        def mkdir_with_kernel_files(
            path: str,
            mode: int = 0o777,
            *,
            dir_fd: int | None = None,
        ) -> None:
            real_mkdir(path, mode, dir_fd=dir_fd)
            if path == "run00001" and dir_fd is not None:
                leaf = Path(os.readlink(f"/proc/self/fd/{dir_fd}")) / path
                self._populate_leaf(leaf)

        monkeypatch.setattr(os, "mkdir", mkdir_with_kernel_files)

    def create_leaf(self) -> cgroup.CgroupLeafV1:
        return cgroup.create_cgroup_leaf(
            cgroup_mount=self.mount,
            parent_relative_path="zenodex01/zrpf0001",
            leaf_name="run00001",
            limits=self.limits,
            mountinfo_path=self.mountinfo,
            proc_root=self.proc_root,
            trusted_uid=os.getuid(),
        )

    def activate(self, pids: set[int], *, parents: dict[int, int] | None = None) -> None:
        _write(self.leaf_path / "cgroup.procs", "".join(f"{pid}\n" for pid in sorted(pids)))
        _write(self.leaf_path / "cgroup.events", "populated 1\n")
        parents = {} if parents is None else parents
        for pid in pids:
            process = self.proc_root / str(pid)
            process.mkdir()
            _write(process / "cgroup", "0::/zenodex01/zrpf0001/run00001\n")
            _write(process / "stat", _proc_stat(pid, parent=parents.get(pid, 1)))

    @staticmethod
    def _populate_leaf(leaf: Path) -> None:
        values = {
            "cgroup.events": "populated 0\n",
            "cgroup.kill": "",
            "cgroup.procs": "",
            "cgroup.stat": "nr_descendants 0\n",
            "cgroup.subtree_control": "\n",
            "cgroup.type": "domain\n",
        }
        values.update({name: "\n" for name in cgroup.LIMIT_FILE_ORDER})
        for name, value in values.items():
            _write(leaf / name, value)


def _write(path: Path, value: str) -> None:
    path.write_text(value, encoding="ascii")


def _proc_stat(pid: int, *, parent: int) -> str:
    tail = ["S", str(parent), *("0" for _ in range(17)), str(pid * 100)]
    return f"{pid} (process {pid}) {' '.join(tail)}\n"


def _limits() -> cgroup.CgroupLimitsV1:
    return cgroup.CgroupLimitsV1(
        cpu_quota_us=100_000,
        cpu_period_us=100_000,
        cpuset_cpus="0-1",
        cpuset_mems="0",
        io_max="8:0 rbps=67108864 wbps=67108864 riops=4096 wiops=4096",
        memory_high_bytes=512 * 1024 * 1024,
        memory_max_bytes=768 * 1024 * 1024,
        memory_swap_max_bytes=0,
        pids_max=32,
    )
