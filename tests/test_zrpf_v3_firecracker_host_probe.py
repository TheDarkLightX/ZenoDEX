from __future__ import annotations

from dataclasses import replace
import os
from pathlib import Path

from tools import check_zrpf_v3_firecracker_replay_profile as checker
from tools import zrpf_v3_firecracker_host_probe as probe


def test_strong_host_requires_every_governed_posture_check() -> None:
    report = probe.evaluate_host_facts(_policy(), _healthy_facts())

    assert report["candidate_host_policy_checks_passed"] is True
    assert report["base_host_prerequisite_checks_passed"] is True
    assert report["replay_runner_ready"] is False
    assert report["failed_checks"] == []
    assert all(value is False for value in report["authority"].values())


def test_kvm_capability_does_not_promote_an_unsupported_host() -> None:
    facts = replace(
        _healthy_facts(),
        host_kernel_release="6.17.0-35-generic",
        smt_active=True,
        swap_active=True,
    )

    report = probe.evaluate_host_facts(_policy(), facts)

    assert report["base_host_prerequisite_checks_passed"] is True
    assert report["candidate_host_policy_checks_passed"] is False
    assert report["failed_checks"] == [
        "host_kernel_version_listed",
        "smt_disabled",
        "swap_disabled",
    ]


def test_older_firecracker_kernel_family_is_outside_stricter_ksm_gate() -> None:
    facts = replace(
        _healthy_facts(),
        host_kernel_release="6.1.150",
        ksm_zero_pages=None,
    )

    report = probe.evaluate_host_facts(_policy(), facts)

    assert report["candidate_host_policy_checks_passed"] is False
    assert report["failed_checks"] == [
        "host_kernel_version_listed",
        "ksm_disabled_and_clean",
    ]


def test_ksm_zero_page_configuration_must_be_disabled() -> None:
    report = probe.evaluate_host_facts(
        _policy(),
        replace(_healthy_facts(), ksm_use_zero_pages=1),
    )

    assert report["candidate_host_policy_checks_passed"] is False
    assert report["failed_checks"] == ["ksm_disabled_and_clean"]


def test_missing_kvm_and_controller_fail_closed_with_stable_checks() -> None:
    facts = replace(
        _healthy_facts(),
        cgroup_controllers=frozenset({"cpu", "memory", "pids"}),
        kvm_character_device=False,
        kvm_read_write=False,
    )

    report = probe.evaluate_host_facts(_policy(), facts)

    assert report["base_host_prerequisite_checks_passed"] is False
    assert report["candidate_host_policy_checks_passed"] is False
    assert report["failed_checks"] == [
        "kvm_character_device",
        "kvm_read_write",
        "required_cgroup_controllers_present",
    ]


def test_unknown_ksm_smt_and_swap_posture_rejects_strong_profile() -> None:
    facts = replace(
        _healthy_facts(),
        ksm_pages_shared=None,
        ksm_pages_sharing=None,
        ksm_run=None,
        ksm_use_zero_pages=None,
        ksm_zero_pages=None,
        smt_active=None,
        swap_active=None,
    )

    report = probe.evaluate_host_facts(_policy(), facts)

    assert report["candidate_host_policy_checks_passed"] is False
    assert report["failed_checks"] == [
        "ksm_disabled_and_clean",
        "smt_disabled",
        "swap_disabled",
    ]


def test_read_write_character_device_does_not_substitute_for_kvm() -> None:
    character_device, read_write, api_version = probe._probe_kvm(Path("/dev/null"))

    assert character_device is True
    assert read_write is True
    assert api_version is None


def test_host_fact_reader_rejects_fifo_without_blocking(tmp_path: Path) -> None:
    fifo = tmp_path / "host-fact.fifo"
    os.mkfifo(fifo)

    assert probe._read_text(fifo) is None


def test_host_observations_exclude_machine_paths_and_names() -> None:
    report = probe.evaluate_host_facts(_policy(), _healthy_facts())

    assert set(report["observations"]) == {
        "architecture",
        "cgroup_controller_count",
        "host_kernel_major_minor",
        "ksm_pages_shared",
        "ksm_pages_sharing",
        "ksm_run",
        "ksm_use_zero_pages",
        "ksm_zero_pages",
        "kvm_api_version",
        "page_size_bytes",
        "smt_active",
        "swap_active",
    }


def _policy() -> dict:
    profile = checker.support.strict_json_loads(checker.PROFILE_PATH.read_bytes())
    return profile["host_policy"]


def _healthy_facts() -> probe.HostFacts:
    return probe.HostFacts(
        architecture="x86_64",
        cgroup_controllers=frozenset({"cpu", "cpuset", "io", "memory", "pids"}),
        cgroup_v2_mounted=True,
        host_kernel_release="6.18.2-secure",
        ksm_pages_shared=0,
        ksm_pages_sharing=0,
        ksm_run=0,
        ksm_use_zero_pages=0,
        ksm_zero_pages=0,
        kvm_api_version=probe.KVM_API_VERSION,
        kvm_character_device=True,
        kvm_read_write=True,
        page_size_bytes=4096,
        smt_active=False,
        swap_active=False,
    )
