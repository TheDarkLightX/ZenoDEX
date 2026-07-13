from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from tools import check_zrpf_v3_firecracker_replay_profile as checker
from tools import zrpf_v3_firecracker_host_probe as host_probe


def test_committed_candidate_profile_is_canonical_and_incomplete() -> None:
    report = checker.validate_profile()
    profile = _profile()

    assert report["profile_valid"] is True
    assert report["profile_complete"] is False
    assert profile["status"] == "candidate_incomplete_non_authoritative"
    assert profile["artifacts"]["guest_kernel"]["identity_authenticated"] is False
    assert profile["artifacts"]["rootfs"]["identity_authenticated"] is False
    assert all(value is False for value in profile["claims"].values())


def test_static_report_cannot_claim_runner_or_authority() -> None:
    report = checker.build_report(include_host_probe=False)

    assert report["ok"] is True
    assert report["candidate_profile_integrity_ok"] is True
    assert report["decision"] == ("candidate_profile_integrity_valid_runner_unavailable")
    assert report["host_probe"] is None
    assert report["replay_runner_ready"] is False
    assert all(value is False for value in report["authority"].values())


def test_runner_joins_one_precreated_domain_leaf_without_cgroup_properties() -> None:
    runner = _profile()["runner_policy"]

    assert runner["jailer_cgroup_property_arguments_allowed"] is False
    assert "--cgroup" not in runner["jailer_cli_required_options"]
    assert "--cgroup" in runner["jailer_cli_forbidden_options"]
    assert runner["jailer_parent_cgroup_value_policy"] == (
        "verified_relative_path_to_exact_precreated_leaf_under_cgroup2_mount"
    )
    assert runner["cgroup_leaf_prelaunch_requirements"] == [
        "cgroup_path_exists",
        "cgroup_path_is_cgroup_v2_directory",
        "cgroup_path_stable_device_and_inode",
        "cgroup_type_exact_domain",
        "cgroup_subtree_control_empty",
        "cgroup_procs_empty",
        "cgroup_events_populated_zero",
        "cgroup_stat_nr_descendants_zero",
        "required_controller_files_present",
        "numeric_limits_exactly_match_governed_policy",
    ]
    assert runner["cgroup_leaf_active_requirements"] == [
        "exact_expected_firecracker_process_set",
        "proc_pid_cgroup_resolves_to_expected_relative_path",
        "cgroup_path_stable_device_and_inode",
        "numeric_limits_unchanged",
    ]


def test_runner_requires_whole_cgroup_teardown_completion() -> None:
    runner = _profile()["runner_policy"]
    contract = runner["cgroup_termination_contract"]

    assert contract == {
        "cgroup_kill_unavailable_or_populated_nonzero": "reject",
        "cgroup_type_readback_required": "domain",
        "process_group_kill": "supplemental_only_never_authoritative",
        "teardown_completion_file": "cgroup.events",
        "teardown_completion_predicate": "parsed_populated_equals_zero",
        "teardown_method": "cgroup_v2_cgroup_kill",
        "teardown_owner": "privileged_host_supervisor",
        "teardown_write_bytes_hex": "310a",
        "teardown_write_file": "cgroup.kill",
    }
    assert runner["teardown_policy"] == (
        "cgroup_kill_literal_one_then_cgroup_events_populated_zero_then_unique_jail_removed"
    )
    assert runner["watchdog_policy"] == (
        "prelaunched_host_monotonic_deadline_cgroup_kill_literal_one_and_populated_zero"
    )


def test_profile_rejects_cgroup_property_even_after_expected_data_refresh(
    tmp_path: Path,
    monkeypatch,
) -> None:
    weakened = _profile()
    runner = weakened["runner_policy"]
    runner["jailer_cgroup_property_arguments_allowed"] = True
    runner["jailer_cli_forbidden_options"].remove("--cgroup")
    runner["jailer_cli_required_options"].append("--cgroup")
    monkeypatch.setattr(checker, "EXPECTED_RUNNER_POLICY", runner)
    monkeypatch.setattr(
        checker,
        "EXPECTED_PROFILE_CANONICAL_SHA256",
        checker._canonical_sha256(weakened),
    )

    report = checker.validate_profile(_write(tmp_path / "cgroup-property.json", weakened))

    assert "runner_policy_mismatch" not in report["errors"]
    assert "runner_v1_cgroup_security_boundary_mismatch" in report["errors"]


def test_jailer_argument_guard_rejects_every_cgroup_property_spelling() -> None:
    assert checker.jailer_argv_contains_cgroup_property(["--cgroup", "memory.max=268435456"])
    assert checker.jailer_argv_contains_cgroup_property(["--cgroup=memory.max=268435456"])
    assert not checker.jailer_argv_contains_cgroup_property(
        ["--cgroup-version=2", "--parent-cgroup", "zenodex/zrpf/run-1"]
    )


def test_profile_rejects_equals_form_cgroup_property_after_expected_data_refresh(
    tmp_path: Path,
    monkeypatch,
) -> None:
    weakened = _profile()
    runner = weakened["runner_policy"]
    runner["jailer_cli_required_options"].append("--cgroup=io.max=8:0 rbps=1048576")
    monkeypatch.setattr(checker, "EXPECTED_RUNNER_POLICY", runner)
    monkeypatch.setattr(
        checker,
        "EXPECTED_PROFILE_CANONICAL_SHA256",
        checker._canonical_sha256(weakened),
    )

    report = checker.validate_profile(_write(tmp_path / "cgroup-equals.json", weakened))

    assert "runner_policy_mismatch" not in report["errors"]
    assert "runner_v1_cgroup_security_boundary_mismatch" in report["errors"]


@pytest.mark.parametrize(
    "mutation",
    [
        "remove_cgroup_version",
        "remove_parent_cgroup",
        "remove_prelaunch_checks",
        "remove_active_checks",
        "accept_missing_cgroup_kill",
        "disable_cgroup_kill",
        "disable_membership_postcheck",
        "allow_path_symlinks",
        "disable_jailer",
        "allow_unknown_jailer_options",
        "allow_preexisting_jail",
        "allow_daemonize",
        "add_cgroup_v1_selector",
        "add_bare_cgroup_version",
        "add_concrete_parent_cgroup",
    ],
)
def test_literal_cgroup_floor_survives_coherent_runner_data_refresh(
    tmp_path: Path,
    monkeypatch,
    mutation: str,
) -> None:
    weakened = _profile()
    runner = weakened["runner_policy"]
    _weaken_cgroup_contract(runner, mutation)
    monkeypatch.setattr(checker, "EXPECTED_RUNNER_POLICY", runner)
    monkeypatch.setattr(
        checker,
        "EXPECTED_PROFILE_CANONICAL_SHA256",
        checker._canonical_sha256(weakened),
    )

    report = checker.validate_profile(_write(tmp_path / f"{mutation}.json", weakened))

    assert "runner_policy_mismatch" not in report["errors"]
    assert "runner_v1_cgroup_security_boundary_mismatch" in report["errors"]


def test_literal_host_cgroup_floor_survives_coherent_policy_refresh(
    tmp_path: Path,
    monkeypatch,
) -> None:
    weakened = _profile()
    host = weakened["host_policy"]
    host["require_cgroup_v2"] = False
    host["required_cgroup_controllers"] = []
    monkeypatch.setattr(checker, "EXPECTED_HOST_POLICY", host)
    monkeypatch.setattr(
        checker,
        "EXPECTED_PROFILE_CANONICAL_SHA256",
        checker._canonical_sha256(weakened),
    )

    report = checker.validate_profile(_write(tmp_path / "host-cgroup.json", weakened))

    assert "host_policy_mismatch" not in report["errors"]
    assert "host_v1_cgroup_security_boundary_mismatch" in report["errors"]


def test_profile_rejects_claim_promotion_and_integer_boolean(tmp_path: Path) -> None:
    promoted = _profile()
    promoted["claims"]["release_authority"] = True
    assert (
        "profile_claims_mismatch"
        in checker.validate_profile(_write(tmp_path / "promoted.json", promoted))["errors"]
    )

    integer = _profile()
    integer["claims"]["release_authority"] = 0
    assert (
        "profile_claims_mismatch"
        in checker.validate_profile(_write(tmp_path / "integer.json", integer))["errors"]
    )


def test_profile_rejects_artifact_identity_and_release_drift(tmp_path: Path) -> None:
    artifact = _profile()
    artifact["artifacts"]["firecracker_release_binary"]["sha256"] = "00" * 32
    assert (
        "profile_artifacts_mismatch"
        in checker.validate_profile(_write(tmp_path / "artifact.json", artifact))["errors"]
    )


def test_profile_rejects_runner_and_host_security_policy_weakening(
    tmp_path: Path,
) -> None:
    runner = _profile()
    runner["runner_policy"]["built_in_default_seccomp_required"] = False
    assert (
        "runner_policy_mismatch"
        in checker.validate_profile(_write(tmp_path / "runner.json", runner))["errors"]
    )

    network = _profile()
    network["runner_policy"]["guest_network_device_allowed"] = True
    assert (
        "runner_policy_mismatch"
        in checker.validate_profile(_write(tmp_path / "network.json", network))["errors"]
    )

    host = _profile()
    host["host_policy"]["require_swap_disabled"] = False
    assert (
        "host_policy_mismatch"
        in checker.validate_profile(_write(tmp_path / "host.json", host))["errors"]
    )

    release = _profile()
    release["release"]["tag_commit"] = "00" * 20
    assert (
        "profile_release_mismatch"
        in checker.validate_profile(_write(tmp_path / "release.json", release))["errors"]
    )


def test_profile_rejects_unknown_missing_and_noncanonical_fields(tmp_path: Path) -> None:
    unknown = _profile()
    unknown["unexpected"] = False
    assert (
        "profile_root_fields_mismatch"
        in checker.validate_profile(_write(tmp_path / "unknown.json", unknown))["errors"]
    )

    missing = _profile()
    del missing["runner_policy"]
    assert (
        "profile_root_fields_mismatch"
        in checker.validate_profile(_write(tmp_path / "missing.json", missing))["errors"]
    )

    noncanonical = tmp_path / "noncanonical.json"
    noncanonical.write_text(json.dumps(_profile()), encoding="ascii")
    assert "profile_noncanonical" in checker.validate_profile(noncanonical)["errors"]


def test_profile_rejects_duplicate_keys_symlink_and_empty_file(tmp_path: Path) -> None:
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_bytes(b'{"schema":"a","schema":"b"}\n')
    assert checker.validate_profile(duplicate)["errors"] == ["profile_input_rejected"]

    target = _write(tmp_path / "target.json", _profile())
    symlink = tmp_path / "profile-link.json"
    symlink.symlink_to(target)
    assert checker.validate_profile(symlink)["errors"] == ["profile_input_rejected"]

    empty = tmp_path / "empty.json"
    empty.write_bytes(b"")
    assert checker.validate_profile(empty)["errors"] == ["profile_input_rejected"]

    fifo = tmp_path / "profile.fifo"
    os.mkfifo(fifo)
    assert checker.validate_profile(fifo)["errors"] == ["profile_input_rejected"]


def test_deep_json_rejects_without_cli_traceback(
    tmp_path: Path,
    monkeypatch,
    capsys,
) -> None:
    deep = tmp_path / "deep.json"
    deep.write_bytes(b'{"x":' + b"[" * 1_200 + b"0" + b"]" * 1_200 + b"}\n")
    monkeypatch.setattr(checker, "PROFILE_PATH", deep)

    exit_code = checker.main([])
    captured = capsys.readouterr()

    assert exit_code == 1
    assert "profile_input_rejected" in captured.out
    assert captured.err == ""
    assert deep.as_posix() not in captured.out


def test_cli_rejects_unknown_arguments() -> None:
    try:
        checker.main(["--profile", "attacker.json"])
    except SystemExit as exc:
        assert exc.code == 2
    else:
        raise AssertionError("argparse must reject profile overrides")


def test_require_ready_rejects_integrity_valid_candidate(capsys) -> None:
    exit_code = checker.main(["--require-ready"])
    report = json.loads(capsys.readouterr().out)

    assert exit_code == 1
    assert report["ok"] is True
    assert report["candidate_profile_integrity_ok"] is True
    assert report["replay_runner_ready"] is False


def test_isolated_cli_loads_only_trusted_sibling_modules(tmp_path: Path) -> None:
    completed = subprocess.run(
        [sys.executable, "-I", checker.__file__],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        env={"PATH": "/usr/bin:/bin", "PYTHONPATH": tmp_path.as_posix()},
        timeout=10,
    )

    assert completed.returncode == 0
    assert completed.stderr == b""
    report = json.loads(completed.stdout)
    assert report["profile"]["profile_valid"] is True
    assert report["replay_runner_ready"] is False


def test_host_probe_uses_the_single_validated_profile_snapshot(monkeypatch) -> None:
    raw = checker.PROFILE_PATH.read_bytes()
    reads = 0

    def read_once(_path: Path) -> bytes:
        nonlocal reads
        reads += 1
        if reads != 1:
            raise AssertionError("profile was reopened after validation")
        return raw

    monkeypatch.setattr(checker, "_read_bounded_regular", read_once)
    monkeypatch.setattr(host_probe, "collect_host_facts", lambda: object())
    monkeypatch.setattr(
        host_probe,
        "evaluate_host_facts",
        lambda _policy, _facts: {"candidate_host_prerequisites_passed": True},
    )

    report = checker.build_report(include_host_probe=True)

    assert report["ok"] is True
    assert reads == 1


def _profile() -> dict:
    return copy.deepcopy(checker.support.strict_json_loads(checker.PROFILE_PATH.read_bytes()))


def _write(path: Path, value: dict) -> Path:
    path.write_bytes(checker._canonical_bytes(value))
    return path


def _weaken_cgroup_contract(runner: dict, mutation: str) -> None:
    if mutation == "remove_cgroup_version":
        runner["jailer_cli_required_options"].remove("--cgroup-version=2")
    elif mutation == "remove_parent_cgroup":
        runner["jailer_cli_required_options"].remove("--parent-cgroup")
    elif mutation == "remove_prelaunch_checks":
        runner["cgroup_leaf_prelaunch_requirements"] = []
    elif mutation == "remove_active_checks":
        runner["cgroup_leaf_active_requirements"] = []
    elif mutation == "accept_missing_cgroup_kill":
        runner["cgroup_termination_contract"][
            "cgroup_kill_unavailable_or_populated_nonzero"
        ] = "accept"
    elif mutation == "disable_cgroup_kill":
        runner["cgroup_termination_contract"]["teardown_method"] = "none"
    elif mutation == "disable_membership_postcheck":
        runner["jailer_cgroup_membership_postcheck_required"] = False
    elif mutation == "allow_path_symlinks":
        runner["cgroup_and_netns_path_symlinks_allowed"] = True
    elif mutation == "disable_jailer":
        runner["jailer_required"] = False
    elif mutation == "allow_unknown_jailer_options":
        runner["unknown_jailer_cli_options_allowed"] = True
    elif mutation == "allow_preexisting_jail":
        runner["preexisting_jail_root_allowed"] = True
    elif mutation == "allow_daemonize":
        runner["jailer_cli_forbidden_options"].remove("--daemonize")
    elif mutation == "add_cgroup_v1_selector":
        runner["jailer_cli_required_options"].append("--cgroup-version=1")
    elif mutation == "add_bare_cgroup_version":
        runner["jailer_cli_required_options"].append("--cgroup-version")
    elif mutation == "add_concrete_parent_cgroup":
        runner["jailer_cli_required_options"].append("--parent-cgroup=attacker")
    else:
        raise AssertionError(f"unknown mutation: {mutation}")
