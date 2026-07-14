from __future__ import annotations

import hashlib
import inspect
import json
import os
import subprocess
from pathlib import Path
from types import SimpleNamespace
from typing import cast

import pytest

from tools import zrpf_v3_firecracker_cgroup_v2 as cgroup_v2
from tools import zrpf_v3_firecracker_jailer_launcher as launcher


def test_pinned_executable_rejects_path_replacement_after_open(tmp_path: Path) -> None:
    binary = tmp_path / "bin" / "jailer"
    binary.parent.mkdir(mode=0o700)
    raw = b"pinned executable"
    binary.write_bytes(raw)
    binary.chmod(0o500)
    pinned = launcher.open_pinned_executable(
        path=binary,
        expectation=launcher.ExecutableExpectationV1(
            sha256=hashlib.sha256(raw).hexdigest(),
            size_bytes=len(raw),
        ),
        trusted_root=tmp_path,
        trusted_uid=os.getuid(),
    )
    moved = binary.with_name("jailer-opened")
    binary.rename(moved)
    binary.write_bytes(raw)
    binary.chmod(0o500)

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_executable_identity_changed"):
        pinned.reverify()
    pinned.close()


def test_pinned_executable_rejects_mutated_open_inode(tmp_path: Path) -> None:
    binary = tmp_path / "bin" / "firecracker"
    binary.parent.mkdir(mode=0o700)
    original = b"firecracker"
    binary.write_bytes(original)
    binary.chmod(0o500)
    pinned = launcher.open_pinned_executable(
        path=binary,
        expectation=launcher.ExecutableExpectationV1(
            sha256=hashlib.sha256(original).hexdigest(),
            size_bytes=len(original),
        ),
        trusted_root=tmp_path,
        trusted_uid=os.getuid(),
    )
    binary.chmod(0o700)
    binary.write_bytes(b"attacker!!")
    binary.chmod(0o500)

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_executable_identity_changed"):
        pinned.reverify()
    pinned.close()


def test_network_namespace_binds_nsfs_path_and_every_active_process(
    tmp_path: Path,
) -> None:
    namespace = tmp_path / "netns" / "run00001"
    namespace.parent.mkdir(mode=0o700)
    namespace.write_bytes(b"namespace handle")
    namespace.chmod(0o400)
    mountinfo = tmp_path / "mountinfo"
    device = namespace.stat().st_dev
    mountinfo.write_text(
        f"11 10 {os.major(device)}:{os.minor(device)} net:[1] {namespace.as_posix()} rw - "
        "nsfs nsfs rw\n",
        encoding="ascii",
    )
    proc_root = tmp_path / "proc"
    process_net = proc_root / "123" / "ns" / "net"
    process_net.parent.mkdir(parents=True)
    process_net.symlink_to(namespace)
    pinned = launcher.open_pinned_network_namespace(
        path=namespace,
        mountinfo_path=mountinfo,
        proc_root=proc_root,
        trusted_root=tmp_path,
        trusted_uid=os.getuid(),
    )

    pinned.verify_process_membership(frozenset({123}))
    process_net.unlink()
    replacement = tmp_path / "other-netns"
    replacement.write_bytes(b"other")
    process_net.symlink_to(replacement)

    with pytest.raises(
        launcher.JailerLauncherReject,
        match="jailer_netns_process_identity_mismatch",
    ):
        pinned.verify_process_membership(frozenset({123}))
    pinned.close()


def test_network_namespace_rejects_unexpected_resident_process(tmp_path: Path) -> None:
    namespace = tmp_path / "netns" / "run00001"
    namespace.parent.mkdir(mode=0o700)
    namespace.write_bytes(b"namespace handle")
    namespace.chmod(0o400)
    proc_root = tmp_path / "proc"
    for pid in (123, 999):
        process_net = proc_root / str(pid) / "ns" / "net"
        process_net.parent.mkdir(parents=True)
        process_net.symlink_to(namespace)
    pinned = launcher.open_pinned_network_namespace(
        path=namespace,
        mountinfo_path=_mountinfo_for(tmp_path, namespace),
        proc_root=proc_root,
        trusted_root=tmp_path,
        trusted_uid=os.getuid(),
    )

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_netns_process_set_mismatch"):
        pinned.verify_exact_process_set(frozenset({123}))
    pinned.close()


def test_exact_jailer_argv_uses_precreated_leaf_without_cgroup_properties() -> None:
    spec = _spec()
    arguments = spec.argv(
        jailer=_PathPinned("/trusted/jailer"),
        firecracker=_PathPinned("/trusted/firecracker"),
        cgroup_leaf=_Leaf(),
        network_namespace=_Netns("/run/netns/run00001"),
    )

    assert "--cgroup-version=2" in arguments
    assert arguments[arguments.index("--parent-cgroup") + 1] == ("zenodex01/zrpf0001/run00001")
    assert not any(
        argument == "--cgroup" or argument.startswith("--cgroup=") for argument in arguments
    )
    assert "--daemonize" not in arguments
    assert "--new-pid-ns" in arguments
    assert "--netns" in arguments
    assert arguments[-4:] == ("--", "--no-api", "--config-file", "/config.json")


def test_prepared_jailer_v2_uses_immutable_resource_config_path() -> None:
    spec = launcher.PreparedJailerLaunchSpecV2(
        jail_id="run00001",
        uid=20001,
        gid=20001,
        chroot_base_dir=Path("/srv/zenodex-jailer"),
    )

    arguments = spec.argv(
        jailer=_PathPinned("/trusted/jailer"),
        firecracker=_PathPinned("/trusted/firecracker"),
        cgroup_leaf=_Leaf(),
        network_namespace=_Netns("/run/netns/run00001"),
    )

    assert arguments[-4:] == (
        "--",
        "--no-api",
        "--config-file",
        "/resources/config.json",
    )
    assert not any(
        argument == "--cgroup" or argument.startswith("--cgroup=")
        for argument in arguments
    )


def test_public_candidate_entry_rejects_injected_test_controls() -> None:
    with pytest.raises(
        launcher.JailerLauncherReject,
        match="jailer_candidate_control_type_invalid",
    ):
        launcher.run_candidate_jailer_process_control(
            spec=_spec(),
            jailer=cast(launcher.PinnedExecutableV1, _PathPinned("/trusted/jailer")),
            firecracker=cast(
                launcher.PinnedExecutableV1,
                _PathPinned("/trusted/firecracker"),
            ),
            cgroup_leaf=cast(cgroup_v2.CgroupLeafV1, _Leaf()),
            network_namespace=cast(
                launcher.PinnedNetworkNamespaceV1,
                _Netns("/run/netns/run00001"),
            ),
            process_timeout_seconds=5.0,
        )


def test_public_prepared_entry_rejects_test_double_before_spawn() -> None:
    with pytest.raises(
        launcher.JailerLauncherReject,
        match="jailer_prepared_control_type_invalid",
    ):
        launcher.run_prepared_jailer_process_control_v2(
            spec=launcher.PreparedJailerLaunchSpecV2(
                jail_id="run00001",
                uid=20001,
                gid=20001,
                chroot_base_dir=Path("/srv/zenodex-jailer"),
            ),
            prepared_jail=cast(launcher.PreparedJailRootV2, _PreparedJail()),
            jailer=cast(launcher.PinnedExecutableV1, _PathPinned("/trusted/jailer")),
            firecracker=cast(
                launcher.PinnedExecutableV1,
                _PathPinned("/trusted/firecracker"),
            ),
            cgroup_leaf=cast(cgroup_v2.CgroupLeafV1, _Leaf()),
            network_namespace=cast(
                launcher.PinnedNetworkNamespaceV1,
                _Netns("/run/netns/run00001"),
            ),
            process_timeout_seconds=5.0,
        )


def test_prepared_runner_has_no_spot_v7_authority_mint_or_integration_import() -> None:
    source = inspect.getsource(launcher)

    assert "_GovernedJailedFirecrackerExecutionV1" not in source
    assert "_GovernedFirecrackerSpotV7SettlementV1" not in source
    assert "_GOVERNED_RUNTIME_SEAL_V1" not in source
    assert "src.integration" not in source


def test_prepared_lifecycle_reads_only_after_finish_and_then_cleans() -> None:
    prepared = _PreparedJail()
    process = _Process(321)
    observation = launcher._JailerLaunchObservationV1(
        jailer_pid=321,
        process_set=frozenset({321}),
        cgroup_relative_path="/zenodex01/zrpf0001/run00001",
    )
    events: list[str] = []

    def launch() -> tuple[_Process, launcher._JailerLaunchObservationV1]:
        events.append("launch")
        return process, observation

    def finish(
        actual_process: launcher.ProcessHandle,
        actual_observation: launcher._JailerLaunchObservationV1,
    ) -> dict[str, object]:
        assert actual_process is process
        assert actual_observation is observation
        events.append("finish")
        prepared.finish_seen = True
        return {"status": "finished"}

    result = launcher._complete_prepared_jailer_lifecycle_for_test(
        prepared_jail=prepared,
        launch=launch,
        finish=finish,
    )

    assert events == ["launch", "finish"]
    assert prepared.calls == ["verify", "read", "cleanup"]
    assert result.output_device_bytes == b"committed-output"


def test_prepared_lifecycle_quarantines_stage_when_launch_is_uncertain() -> None:
    prepared = _PreparedJail()

    with pytest.raises(RuntimeError, match="uncertain launch"):
        launcher._complete_prepared_jailer_lifecycle_for_test(
            prepared_jail=prepared,
            launch=lambda: (_ for _ in ()).throw(RuntimeError("uncertain launch")),
            finish=lambda _process, _observation: {},
        )

    assert prepared.calls == ["verify"]


def test_prepared_lifecycle_abandons_only_when_prelaunch_rejects() -> None:
    prepared = _PreparedJail(reject_prelaunch=True)

    with pytest.raises(RuntimeError, match="prelaunch reject"):
        launcher._complete_prepared_jailer_lifecycle_for_test(
            prepared_jail=prepared,
            launch=lambda: (_ for _ in ()).throw(AssertionError("must not launch")),
            finish=lambda _process, _observation: {},
        )

    assert prepared.calls == ["verify", "abandon"]


@pytest.mark.parametrize(
    ("overrides", "reject_code"),
    (
        ({"jail_id": "short"}, "jailer_id_invalid"),
        ({"uid": True}, "jailer_uid_gid_invalid"),
        ({"gid": 0}, "jailer_uid_gid_invalid"),
        ({"chroot_base_dir": Path("relative")}, "jailer_chroot_base_not_absolute"),
        ({"config_path_in_jail": "/other.json"}, "jailer_config_path_invalid"),
        ({"nofile_limit": 31}, "jailer_nofile_limit_invalid"),
    ),
)
def test_jailer_spec_boundary_atlas_rejects_one_predicate_flip(
    overrides: dict[str, object],
    reject_code: str,
) -> None:
    values: dict[str, object] = {
        "jail_id": "run00001",
        "uid": 20001,
        "gid": 20001,
        "chroot_base_dir": Path("/srv/zenodex-jailer"),
        "config_path_in_jail": "/config.json",
        "nofile_limit": 64,
    }
    values.update(overrides)
    with pytest.raises(launcher.JailerLauncherReject, match=reject_code):
        launcher.JailerLaunchSpecV1(**values)  # type: ignore[arg-type]


def test_launch_control_rechecks_boundaries_and_reports_only_process_placement() -> None:
    jailer = _PathPinned("/trusted/jailer")
    firecracker = _PathPinned("/trusted/firecracker")
    leaf = _Leaf()
    netns = _Netns("/run/netns/run00001")
    process = _Process(321)
    spawned: list[tuple[str, ...]] = []

    def spawn(arguments: tuple[str, ...]) -> _Process:
        spawned.append(arguments)
        return process

    observed_process, observation = launcher._launch_jailer_process_control_for_test(
        spec=_spec(),
        jailer=jailer,
        firecracker=firecracker,
        cgroup_leaf=leaf,
        network_namespace=netns,
        spawn=spawn,
        monotonic_ns=lambda: 0,
        wait_once=lambda: None,
    )

    assert observed_process is process
    assert len(spawned) == 1
    assert jailer.reverify_count == 2
    assert firecracker.reverify_count == 2
    assert leaf.prelaunch_count == 1
    assert leaf.supervisor_pids == [321]
    assert netns.empty_check_count == 1
    assert netns.verified_process_sets == [frozenset({321, 322})]
    document = observation.to_document()
    assert document["scope"] == "live_process_placement_control_only"
    assert all(value is False for value in document["authority"].values())


def test_launch_control_rejects_non_descendant_or_missing_cgroup_membership() -> None:
    leaf = _Leaf(reject_membership=True)
    process = _Process(321, exit_code=1)

    with pytest.raises(
        launcher.JailerLauncherReject,
        match="jailer_cgroup_membership_not_established",
    ):
        launcher._launch_jailer_process_control_for_test(
            spec=_spec(),
            jailer=_PathPinned("/trusted/jailer"),
            firecracker=_PathPinned("/trusted/firecracker"),
            cgroup_leaf=leaf,
            network_namespace=_Netns("/run/netns/run00001"),
            spawn=lambda _arguments: process,
            monotonic_ns=lambda: 0,
            wait_once=lambda: None,
        )
    assert leaf.teardown_count == 1
    assert process.wait_count == 1


def test_finish_control_reaps_process_and_verifies_whole_cgroup_teardown() -> None:
    leaf = _Leaf()
    netns = _Netns("/run/netns/run00001")
    process = _Process(321, exit_code=0)
    observation = launcher._JailerLaunchObservationV1(
        jailer_pid=321,
        process_set=frozenset({321}),
        cgroup_relative_path=leaf.identity.relative_path,
    )

    report = launcher._finish_jailer_process_control_for_test(
        process=process,
        cgroup_leaf=leaf,
        network_namespace=netns,
        observation=observation,
        process_timeout_seconds=5.0,
    )

    assert report["exit_code"] == 0
    assert report["cgroup_relative_path"] == observation.cgroup_relative_path
    assert report["jailer_pid"] == observation.jailer_pid
    assert report["observed_process_count"] == len(observation.process_set)
    launch_bytes = (
        json.dumps(
            observation.to_document(),
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
        + "\n"
    ).encode("ascii")
    assert report["launch_observation_sha256"] == hashlib.sha256(
        launch_bytes
    ).hexdigest()
    assert report["schema"] == (
        "zenodex/zrpf_firecracker_jailer_finish_observation/v2"
    )
    assert report["control_facts"] == {
        "cgroup_populated_zero_verified": True,
        "cgroup_removed_after_kill": True,
        "network_namespace_path_identity_preserved": True,
        "process_exit_observed": True,
    }
    assert all(value is False for value in report["authority"].values())
    assert leaf.teardown_count == 1
    assert netns.empty_check_count == 1


def test_finish_report_binding_changes_with_launch_lifecycle() -> None:
    first = launcher._JailerLaunchObservationV1(
        jailer_pid=321,
        process_set=frozenset({321}),
        cgroup_relative_path="/zenodex01/zrpf0001/run00001",
    )
    second = launcher._JailerLaunchObservationV1(
        jailer_pid=322,
        process_set=frozenset({322}),
        cgroup_relative_path="/zenodex01/zrpf0001/run00002",
    )

    first_report = launcher._finish_jailer_process_control_for_test(
        process=_Process(321, exit_code=0),
        cgroup_leaf=_Leaf(relative_path=first.cgroup_relative_path),
        network_namespace=_Netns("/run/netns/run00001"),
        observation=first,
        process_timeout_seconds=5.0,
    )
    second_report = launcher._finish_jailer_process_control_for_test(
        process=_Process(322, exit_code=0),
        cgroup_leaf=_Leaf(relative_path=second.cgroup_relative_path),
        network_namespace=_Netns("/run/netns/run00002"),
        observation=second,
        process_timeout_seconds=5.0,
    )

    assert first_report["launch_observation_sha256"] != (
        second_report["launch_observation_sha256"]
    )
    assert first_report["cgroup_relative_path"] != second_report[
        "cgroup_relative_path"
    ]


def test_finish_rejects_observation_substituted_from_other_lifecycle() -> None:
    leaf = _Leaf()
    substituted = launcher._JailerLaunchObservationV1(
        jailer_pid=999,
        process_set=frozenset({999}),
        cgroup_relative_path="/zenodex01/zrpf0001/run99999",
    )

    with pytest.raises(
        launcher.JailerLauncherReject,
        match="jailer_finish_launch_observation_mismatch",
    ):
        launcher._finish_jailer_process_control_for_test(
            process=_Process(321, exit_code=0),
            cgroup_leaf=leaf,
            network_namespace=_Netns("/run/netns/run00001"),
            observation=substituted,
            process_timeout_seconds=5.0,
        )

    assert leaf.teardown_count == 1


def test_spawn_failure_still_removes_fresh_cgroup_leaf() -> None:
    leaf = _Leaf()

    def fail_spawn(_arguments: tuple[str, ...]) -> _Process:
        raise launcher.JailerLauncherReject("jailer_spawn_failed")

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_spawn_failed"):
        launcher._launch_jailer_process_control_for_test(
            spec=_spec(),
            jailer=_PathPinned("/trusted/jailer"),
            firecracker=_PathPinned("/trusted/firecracker"),
            cgroup_leaf=leaf,
            network_namespace=_Netns("/run/netns/run00001"),
            spawn=fail_spawn,
        )
    assert leaf.teardown_count == 1


def test_watchdog_timeout_kills_complete_cgroup_before_reporting_reject() -> None:
    leaf = _Leaf()
    observation = launcher._JailerLaunchObservationV1(
        jailer_pid=321,
        process_set=frozenset({321}),
        cgroup_relative_path=leaf.identity.relative_path,
    )

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_process_timeout"):
        launcher._finish_jailer_process_control_for_test(
            process=_TimeoutProcess(321),
            cgroup_leaf=leaf,
            network_namespace=_Netns("/run/netns/run00001"),
            observation=observation,
            process_timeout_seconds=0.1,
        )

    assert leaf.teardown_count == 1


def test_teardown_failure_falls_back_to_parent_kill_and_reap() -> None:
    leaf = _Leaf(reject_teardown=True)
    process = _TimeoutProcess(321)
    observation = launcher._JailerLaunchObservationV1(
        jailer_pid=321,
        process_set=frozenset({321}),
        cgroup_relative_path=leaf.identity.relative_path,
    )

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_cgroup_teardown_failed"):
        launcher._finish_jailer_process_control_for_test(
            process=process,
            cgroup_leaf=leaf,
            network_namespace=_Netns("/run/netns/run00001"),
            observation=observation,
            process_timeout_seconds=0.1,
        )

    assert leaf.teardown_count == 1
    assert process.kill_count == 1
    assert process.wait_count == 2


def test_network_namespace_path_replacement_rejects_before_process_use(
    tmp_path: Path,
) -> None:
    namespace = tmp_path / "netns" / "run00001"
    namespace.parent.mkdir(mode=0o700)
    namespace.write_bytes(b"namespace")
    namespace.chmod(0o400)
    mountinfo = _mountinfo_for(tmp_path, namespace)
    pinned = launcher.open_pinned_network_namespace(
        path=namespace,
        mountinfo_path=mountinfo,
        proc_root=tmp_path / "proc",
        trusted_root=tmp_path,
        trusted_uid=os.getuid(),
    )
    namespace.rename(namespace.with_name("old"))
    namespace.write_bytes(b"namespace")
    namespace.chmod(0o400)

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_netns_identity_changed"):
        pinned.reverify_path()
    pinned.close()


def test_untrusted_writable_executable_rejects(tmp_path: Path) -> None:
    binary = tmp_path / "jailer"
    raw = b"jailer"
    binary.write_bytes(raw)
    binary.chmod(0o777)

    with pytest.raises(launcher.JailerLauncherReject, match="jailer_trusted_file_invalid"):
        launcher.open_pinned_executable(
            path=binary,
            expectation=launcher.ExecutableExpectationV1(
                sha256=hashlib.sha256(raw).hexdigest(),
                size_bytes=len(raw),
            ),
            trusted_root=tmp_path,
            trusted_uid=os.getuid(),
        )


def test_chroot_base_rejects_exact_stale_jailer_target(tmp_path: Path) -> None:
    chroot_base = tmp_path / "jailer"
    chroot_base.mkdir(mode=0o700)
    firecracker = tmp_path / "bin" / "firecracker"

    launcher.verify_fresh_chroot_target(
        chroot_base_dir=chroot_base,
        exec_file_path=firecracker,
        jail_id="run00001",
        trusted_root=tmp_path,
        trusted_uid=os.getuid(),
    )
    stale = chroot_base / firecracker.name / "run00001"
    stale.mkdir(parents=True)
    stale.parent.chmod(0o700)

    with pytest.raises(
        launcher.JailerLauncherReject,
        match="jailer_chroot_target_not_fresh",
    ):
        launcher.verify_fresh_chroot_target(
            chroot_base_dir=chroot_base,
            exec_file_path=firecracker,
            jail_id="run00001",
            trusted_root=tmp_path,
            trusted_uid=os.getuid(),
        )


def _spec() -> launcher.JailerLaunchSpecV1:
    return launcher.JailerLaunchSpecV1(
        jail_id="run00001",
        uid=20001,
        gid=20001,
        chroot_base_dir=Path("/srv/zenodex-jailer"),
    )


class _PathPinned:
    def __init__(self, path: str) -> None:
        self.path = Path(path)
        self.reverify_count = 0

    def reverify(self) -> None:
        self.reverify_count += 1


class _Leaf:
    def __init__(
        self,
        *,
        relative_path: str = "/zenodex01/zrpf0001/run00001",
        reject_membership: bool = False,
        reject_teardown: bool = False,
    ) -> None:
        self.identity = SimpleNamespace(relative_path=relative_path)
        self.prelaunch_count = 0
        self.supervisor_pids: list[int] = []
        self.reject_membership = reject_membership
        self.reject_teardown = reject_teardown
        self.teardown_count = 0

    def verify_prelaunch(self) -> None:
        self.prelaunch_count += 1

    def verify_active_descendant_set(self, pid: int) -> frozenset[int]:
        self.supervisor_pids.append(pid)
        if self.reject_membership:
            raise cgroup_v2.CgroupV2Reject("cgroup_active_process_set_mismatch")
        return frozenset({pid, pid + 1})

    def terminate_and_remove(self, *, timeout_ns: int) -> None:
        assert timeout_ns > 0
        self.teardown_count += 1
        if self.reject_teardown:
            raise cgroup_v2.CgroupV2Reject("cgroup_leaf_remove_failed")


class _Netns:
    def __init__(self, path: str) -> None:
        self.path = Path(path)
        self.reverify_count = 0
        self.verified_process_sets: list[frozenset[int]] = []
        self.empty_check_count = 0

    def reverify_path(self) -> None:
        self.reverify_count += 1

    def verify_empty(self) -> None:
        self.empty_check_count += 1

    def verify_exact_process_set(self, pids: frozenset[int]) -> None:
        self.verified_process_sets.append(pids)


class _Process:
    def __init__(self, pid: int, *, exit_code: int | None = None) -> None:
        self.pid = pid
        self.exit_code = exit_code
        self.wait_count = 0
        self.kill_count = 0

    def poll(self) -> int | None:
        return self.exit_code

    def wait(self, timeout: float | None = None) -> int:
        del timeout
        self.wait_count += 1
        return 0 if self.exit_code is None else self.exit_code

    def kill(self) -> None:
        self.kill_count += 1
        self.exit_code = -9


class _PreparedJail:
    def __init__(self, *, reject_prelaunch: bool = False) -> None:
        self.reject_prelaunch = reject_prelaunch
        self.finish_seen = False
        self.calls: list[str] = []

    def verify_prelaunch(self) -> None:
        self.calls.append("verify")
        if self.reject_prelaunch:
            raise RuntimeError("prelaunch reject")

    def read_validated_output_after_exit(self) -> bytes:
        assert self.finish_seen
        self.calls.append("read")
        return b"committed-output"

    def cleanup_after_teardown(self) -> None:
        self.calls.append("cleanup")

    def abandon_before_launch(self) -> None:
        self.calls.append("abandon")


class _TimeoutProcess(_Process):
    def __init__(self, pid: int) -> None:
        super().__init__(pid)

    def wait(self, timeout: float | None = None) -> int:
        self.wait_count += 1
        if self.wait_count == 1:
            raise subprocess.TimeoutExpired("jailer", 0.0 if timeout is None else timeout)
        return -9


def _mountinfo_for(root: Path, path: Path) -> Path:
    mountinfo = root / "mountinfo"
    device = path.stat().st_dev
    mountinfo.write_text(
        f"11 10 {os.major(device)}:{os.minor(device)} net:[1] {path.as_posix()} rw - "
        "nsfs nsfs rw\n",
        encoding="ascii",
    )
    return mountinfo
