from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
from pathlib import Path

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
    assert report["decision"] == (
        "candidate_profile_integrity_valid_runner_unavailable"
    )
    assert report["host_probe"] is None
    assert report["replay_runner_ready"] is False
    assert all(value is False for value in report["authority"].values())


def test_profile_rejects_claim_promotion_and_integer_boolean(tmp_path: Path) -> None:
    promoted = _profile()
    promoted["claims"]["release_authority"] = True
    assert "profile_claims_mismatch" in checker.validate_profile(
        _write(tmp_path / "promoted.json", promoted)
    )["errors"]

    integer = _profile()
    integer["claims"]["release_authority"] = 0
    assert "profile_claims_mismatch" in checker.validate_profile(
        _write(tmp_path / "integer.json", integer)
    )["errors"]


def test_profile_rejects_artifact_identity_and_release_drift(tmp_path: Path) -> None:
    artifact = _profile()
    artifact["artifacts"]["firecracker_release_binary"]["sha256"] = "00" * 32
    assert "profile_artifacts_mismatch" in checker.validate_profile(
        _write(tmp_path / "artifact.json", artifact)
    )["errors"]


def test_profile_rejects_runner_and_host_security_policy_weakening(
    tmp_path: Path,
) -> None:
    runner = _profile()
    runner["runner_policy"]["built_in_default_seccomp_required"] = False
    assert "runner_policy_mismatch" in checker.validate_profile(
        _write(tmp_path / "runner.json", runner)
    )["errors"]

    network = _profile()
    network["runner_policy"]["guest_network_device_allowed"] = True
    assert "runner_policy_mismatch" in checker.validate_profile(
        _write(tmp_path / "network.json", network)
    )["errors"]

    host = _profile()
    host["host_policy"]["require_swap_disabled"] = False
    assert "host_policy_mismatch" in checker.validate_profile(
        _write(tmp_path / "host.json", host)
    )["errors"]

    release = _profile()
    release["release"]["tag_commit"] = "00" * 20
    assert "profile_release_mismatch" in checker.validate_profile(
        _write(tmp_path / "release.json", release)
    )["errors"]


def test_profile_rejects_unknown_missing_and_noncanonical_fields(tmp_path: Path) -> None:
    unknown = _profile()
    unknown["unexpected"] = False
    assert "profile_root_fields_mismatch" in checker.validate_profile(
        _write(tmp_path / "unknown.json", unknown)
    )["errors"]

    missing = _profile()
    del missing["runner_policy"]
    assert "profile_root_fields_mismatch" in checker.validate_profile(
        _write(tmp_path / "missing.json", missing)
    )["errors"]

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
