from __future__ import annotations

import copy
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from tools import check_zrpf_v3_replay_verifier_evidence as checker
from tools import zrpf_v3_replay_environment as replay_environment
from tools import zrpf_v3_replay_evidence_support as support
from tools import zrpf_v3_replay_live_controls as replay_controls
from tools import zrpf_v3_replay_process as replay_process
from tools import zrpf_v3_replay_record_writer as record_writer
from tools import zrpf_v3_replay_sealed_executable as sealed_executable
from tools import zrpf_v3_replay_source_snapshot as replay_snapshot
from tools import zrpf_v3_replay_toolchain as replay_toolchain

TEST_EXECUTION_IDENTITY = {
    "binary_sha256": "0e71d8f4ebb6e15d531bc367244e0ede33d0a9e76ba1c38be855cda30788e78f",
    "binary_size_bytes": 2_821_648,
    "binary_transport": support.EXPECTED_BINARY_TRANSPORT,
    "dependency_graph_package_count": 127,
    "dependency_graph_sha256": "419b73b822f65d326f3221b57f47e7ae1936c71323fe85b45d5181affc7d4b59",
}


def test_expected_evidence_pins_source_receipts_and_authority_boundary() -> None:
    evidence = _expected_evidence()

    assert evidence["schema"] == support.SCHEMA
    assert evidence["source_anchor"] == {
        "commit": support.SOURCE_COMMIT,
        "tree": support.SOURCE_TREE,
    }
    assert evidence["replay_source_closure"]["file_count"] == 44
    assert evidence["retained_receipt_set"]["artifact_count"] == 8
    assert evidence["retained_receipt_set"]["total_bytes"] == 4_746_064
    assert evidence["recorded_execution"]["stdout_sha256"] == (support.EXPECTED_STDOUT_SHA256)
    assert evidence["claims"]["same_host_source_built_host_verifier_replay"] is True
    assert evidence["claims"]["executing_binary_identity_authenticated"] is True
    assert evidence["claims"]["network_disabled"] is False
    assert evidence["claims"]["covert_channel_freedom"] is False
    assert evidence["claims"]["public_replay_promoted"] is False
    assert evidence["claims"]["production_authority"] is False
    assert evidence["recorded_build"]["dependency_graph_canonical_source_root"] == (
        support.DEPENDENCY_GRAPH_CANONICAL_SOURCE_ROOT
    )
    assert evidence["recorded_build"]["dependency_graph_normalization"] == (
        support.DEPENDENCY_GRAPH_NORMALIZATION
    )
    assert support.sha256_bytes(support.canonical_evidence_bytes(evidence)) == (
        support.EXPECTED_EVIDENCE_SHA256
    )


def test_expected_evidence_reads_the_governed_anchor_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def reject_current_checkout(_root: Path) -> dict:
        raise AssertionError("current checkout source must not define anchored evidence")

    monkeypatch.setattr(support, "source_closure", reject_current_checkout)

    assert _expected_evidence()["replay_source_closure"]["sha256"] == (
        support.EXPECTED_SOURCE_CLOSURE_SHA256
    )


def test_anchor_inventory_rejects_an_unexpected_compiler_visible_file(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = support._run_git_read

    def add_build_script(
        repo_root: Path,
        arguments: tuple[str, ...],
        output_limit: int,
    ) -> bytes:
        raw = original(repo_root, arguments, output_limit)
        if arguments[0] != "ls-tree":
            return raw
        return raw + (b"100644 blob " + b"0" * 40 + b"\tzk/zrpf_risc0/replay_verifier/build.rs\0")

    monkeypatch.setattr(support, "_run_git_read", add_build_script)

    with pytest.raises(ValueError, match="anchor replay source inventory mismatch"):
        support.anchored_source_closure(support.REPO_ROOT)


def test_verified_live_record_creation_passes_static_check_and_refuses_overwrite(
    tmp_path: Path,
) -> None:
    evidence_path = tmp_path / "evidence.json"
    record_writer.write_after_verified_live(
        evidence_path,
        {"live": _synthetic_live_facts(), "ok": True},
    )

    report = checker.validate_static(evidence_path)

    assert report["ok"] is True
    assert report["facts"]["source_files_checked"] == 44
    assert report["facts"]["receipt_artifacts_checked"] == 8
    with pytest.raises(FileExistsError):
        record_writer.write_after_verified_live(
            evidence_path,
            {"live": _synthetic_live_facts(), "ok": True},
        )


def test_record_creation_requires_verified_live_facts(tmp_path: Path) -> None:
    evidence_path = tmp_path / "evidence.json"

    with pytest.raises(RuntimeError, match="verified live replay facts are required"):
        record_writer.write_after_verified_live(evidence_path, {})

    assert not evidence_path.exists()

    rebound = _synthetic_live_facts()
    rebound["binary_sha256"] = "00"
    with pytest.raises(RuntimeError, match="live execution identity is malformed"):
        record_writer.write_after_verified_live(
            evidence_path,
            {"live": rebound, "ok": True},
        )

    assert not evidence_path.exists()


def test_static_check_rejects_claim_mutation_and_unknown_field(tmp_path: Path) -> None:
    evidence = _expected_evidence()
    evidence["claims"]["production_authority"] = True
    evidence["unknown"] = True
    path = tmp_path / "evidence.json"
    path.write_text(json.dumps(evidence), encoding="utf-8")

    report = checker.validate_static(path)

    assert report["ok"] is False
    assert "evidence SHA-256 differs from governed anchor" in report["errors"]
    assert "evidence root field set mismatch" in report["errors"]
    assert "evidence field mismatch: claims" in report["errors"]


def test_static_check_rejects_noncanonical_equivalent_bytes(tmp_path: Path) -> None:
    path = tmp_path / "evidence.json"
    path.write_text(json.dumps(_expected_evidence()), encoding="ascii")

    report = checker.validate_static(path)

    assert report["ok"] is False
    assert "evidence SHA-256 differs from governed anchor" in report["errors"]
    assert "evidence bytes are not canonical" in report["errors"]


def test_static_check_rejects_coordinated_execution_identity_rebind(
    tmp_path: Path,
) -> None:
    evidence = _expected_evidence()
    rebound = "00" * 32
    evidence["recorded_build"]["verifier_binary_sha256"] = rebound
    evidence["recorded_execution"]["executing_binary_sha256"] = rebound
    path = tmp_path / "evidence.json"
    path.write_bytes(support.canonical_evidence_bytes(evidence))

    report = checker.validate_static(path)

    assert report["ok"] is False
    assert report["errors"] == ["evidence SHA-256 differs from governed anchor"]


def test_live_cli_threads_selected_evidence_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    selected = tmp_path / "selected.json"
    observed: list[Path] = []

    def fake_live(_home: Path, _target: Path, evidence: Path) -> dict:
        observed.append(evidence)
        return {"live": {"verified": True}, "ok": True}

    monkeypatch.setattr(checker, "live_check", fake_live)
    exit_code = checker.main(
        [
            "--live",
            "--evidence",
            str(selected),
            "--risc0-home",
            str(tmp_path / "risc0"),
            "--target-dir",
            str(tmp_path / "target"),
        ]
    )

    assert exit_code == 0
    assert observed == [selected]


def test_build_environment_drops_parent_authority_and_secret_inputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    poisoned = {
        "ZRPF_TEST_SECRET": "secret",
        "CARGO_ENCODED_RUSTFLAGS": "poison",
        "LD_PRELOAD": "/tmp/poison.so",
        "RUSTC_WRAPPER": "/tmp/poison",
        "RUSTFLAGS": "-C linker=/tmp/poison",
    }
    for name, value in poisoned.items():
        monkeypatch.setenv(name, value)
    tool_paths = {
        "cargo": tmp_path / "tools/cargo",
        "rustc": tmp_path / "tools/rustc",
        "rustdoc": tmp_path / "tools/rustdoc",
    }
    (tmp_path / "target").mkdir()

    env = replay_environment.build_environment(tool_paths, tmp_path / "target")

    assert {key for key in poisoned if key != "CARGO_ENCODED_RUSTFLAGS"}.isdisjoint(env)
    assert env["CARGO_ENCODED_RUSTFLAGS"] == "\x1f".join(
        (
            "--remap-path-prefix",
            f"{tmp_path / 'target'}=/zrpf/build",
        )
    )
    assert env["CARGO_ENCODED_RUSTFLAGS"] != poisoned["CARGO_ENCODED_RUSTFLAGS"]
    assert env["HOME"] == str(tmp_path / "target/home")
    assert env["CARGO_HOME"] == str(tmp_path / "target/cargo-home")
    assert env["PATH"] == replay_environment.SYSTEM_PATH


def test_live_target_must_not_preexist(tmp_path: Path) -> None:
    target = tmp_path / "target"
    target.mkdir(mode=0o777)

    with pytest.raises(RuntimeError, match="must not pre-exist"):
        checker._prepare_target_directory(target, support.REPO_ROOT)


def test_inside_repo_target_rejection_creates_nothing(tmp_path: Path) -> None:
    target = tmp_path / "inside"

    with pytest.raises(RuntimeError, match="outside the repository"):
        checker._prepare_target_directory(target, tmp_path)

    assert not target.exists()


def test_ancestor_cargo_config_is_rejected(tmp_path: Path) -> None:
    workspace = tmp_path / "source/zk/zrpf_risc0"
    (workspace / ".cargo").mkdir(parents=True)
    (workspace / ".cargo/config.toml").write_text("[net]\noffline=true\n")
    (tmp_path / ".cargo").mkdir()
    (tmp_path / ".cargo/config.toml").write_text("[build]\nrustc-wrapper='x'\n")

    with pytest.raises(RuntimeError, match="unpinned Cargo config"):
        replay_environment.validate_cargo_config_ancestors(workspace)


def test_source_snapshot_disables_post_checkout_hook(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.name", "ZRPF Test")
    _git(repo, "config", "user.email", "zrpf@example.invalid")
    (repo / "tracked").write_text("bound\n", encoding="ascii")
    _git(repo, "add", "tracked")
    _git(repo, "commit", "-q", "-m", "source")
    commit = _git(repo, "rev-parse", "HEAD").strip()
    tree = _git(repo, "show", "-s", "--format=%T", "HEAD").strip()
    hook = repo / ".git/hooks/post-checkout"
    hook.write_text("#!/bin/sh\nmkdir -p .cargo\ntouch .cargo/config.toml\n")
    hook.chmod(0o755)
    target = tmp_path / "target"
    target.mkdir(mode=0o700)

    with replay_snapshot.SourceSnapshot(repo, target, commit, tree) as snapshot:
        assert not (snapshot / ".cargo/config.toml").exists()


def test_bounded_process_rejects_output_before_unbounded_buffering(
    tmp_path: Path,
) -> None:
    request = replay_process.ProcessRequest(
        command=(sys.executable, "-c", "import os; os.write(1, b'x' * 4096)"),
        cwd=tmp_path,
        env={"PATH": replay_environment.SYSTEM_PATH},
        timeout_seconds=5,
        output_limit_bytes=32,
        profile=replay_process.ProcessProfile.TOOL,
    )

    with pytest.raises(RuntimeError, match="output exceeded cap"):
        replay_process.run_bounded(request)


def test_bounded_process_supplies_exact_bounded_stdin(tmp_path: Path) -> None:
    request = replay_process.ProcessRequest(
        command=(
            sys.executable,
            "-c",
            "import sys; sys.stdout.buffer.write(sys.stdin.buffer.read())",
        ),
        cwd=tmp_path,
        env={"PATH": replay_environment.SYSTEM_PATH},
        timeout_seconds=5,
        output_limit_bytes=1_024,
        profile=replay_process.ProcessProfile.TOOL,
        stdin_bytes=b"governed replay request",
        input_limit_bytes=1_024,
    )

    process = replay_process.run_bounded(request)

    assert process.returncode == 0
    assert process.stdout == b"governed replay request"
    assert process.stderr == b""


def test_bounded_process_kills_spawned_child_when_parent_stdin_close_fails(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    descriptor = os.memfd_create("close-failure-test", os.MFD_CLOEXEC)
    real_close = replay_process.os.close
    real_popen = replay_process.subprocess.Popen
    real_kill = replay_process._kill_process_group
    spawned: list[subprocess.Popen[bytes]] = []
    killed: list[int] = []
    close_failed = False

    def record_popen(*args: Any, **kwargs: Any) -> subprocess.Popen[bytes]:
        process = real_popen(*args, **kwargs)
        spawned.append(process)
        return process

    def close_then_fail_once(target: int) -> None:
        nonlocal close_failed
        real_close(target)
        if target == descriptor and not close_failed:
            close_failed = True
            raise OSError("injected stdin close failure")

    def record_kill(process: subprocess.Popen[bytes]) -> None:
        killed.append(process.pid)
        real_kill(process)

    monkeypatch.setattr(replay_process, "_sealed_stdin", lambda _raw: descriptor)
    monkeypatch.setattr(replay_process.subprocess, "Popen", record_popen)
    monkeypatch.setattr(replay_process.os, "close", close_then_fail_once)
    monkeypatch.setattr(replay_process, "_kill_process_group", record_kill)

    request = replay_process.ProcessRequest(
        command=(sys.executable, "-c", "import time; time.sleep(30)"),
        cwd=tmp_path,
        env={"PATH": replay_environment.SYSTEM_PATH},
        timeout_seconds=5,
        output_limit_bytes=1_024,
        profile=replay_process.ProcessProfile.TOOL,
        stdin_bytes=b"governed",
    )

    with pytest.raises(RuntimeError, match="sealed stdin close failed"):
        replay_process.run_bounded(request)

    assert len(spawned) == 1
    assert killed == [spawned[0].pid]
    assert spawned[0].poll() is not None


def test_sealed_stdin_cleanup_failure_preserves_primary_write_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    real_close = replay_process.os.close

    def reject_write(_descriptor: int, _raw: object) -> int:
        raise RuntimeError("primary sealed stdin write failure")

    def close_then_reject(descriptor: int) -> None:
        real_close(descriptor)
        raise OSError("injected cleanup close failure")

    monkeypatch.setattr(replay_process.os, "write", reject_write)
    monkeypatch.setattr(replay_process.os, "close", close_then_reject)

    with pytest.raises(RuntimeError, match="primary sealed stdin write failure") as rejected:
        replay_process._sealed_stdin(b"governed")

    assert rejected.value.__notes__ == ["cleanup_failure=SEALED_STDIN_CLOSE_FAILED"]


def test_bounded_process_child_observes_fully_sealed_stdin(tmp_path: Path) -> None:
    script = (
        "import fcntl,sys\n"
        f"assert fcntl.fcntl(0, fcntl.F_GET_SEALS) == {replay_process.STDIN_SEALS}\n"
        "sys.stdout.buffer.write(sys.stdin.buffer.read())\n"
    )
    request = replay_process.ProcessRequest(
        command=(sys.executable, "-c", script),
        cwd=tmp_path,
        env={"PATH": replay_environment.SYSTEM_PATH},
        timeout_seconds=5,
        output_limit_bytes=1_024,
        profile=replay_process.ProcessProfile.TOOL,
        stdin_bytes=b"sealed request",
        input_limit_bytes=1_024,
    )

    process = replay_process.run_bounded(request)

    assert process.returncode == 0
    assert process.stdout == b"sealed request"
    assert process.stderr == b""


def test_bounded_process_rejects_oversized_stdin_before_spawn(tmp_path: Path) -> None:
    marker = tmp_path / "spawned"
    request = replay_process.ProcessRequest(
        command=(sys.executable, "-c", f"open({str(marker)!r}, 'wb').close()"),
        cwd=tmp_path,
        env={"PATH": replay_environment.SYSTEM_PATH},
        timeout_seconds=5,
        output_limit_bytes=1_024,
        profile=replay_process.ProcessProfile.TOOL,
        stdin_bytes=b"12345",
        input_limit_bytes=4,
    )

    with pytest.raises(ValueError, match="stdin exceeded cap"):
        replay_process.run_bounded(request)

    assert not marker.exists()


def _git(repo: Path, *arguments: str) -> str:
    process = subprocess.run(
        ["/usr/bin/git", *arguments],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    return process.stdout


def test_loader_rejects_duplicate_key_and_symlink(tmp_path: Path) -> None:
    target = tmp_path / "target.json"
    target.write_text('{"claims":{"x":false,"x":true}}', encoding="utf-8")
    document, errors = checker.load_evidence(target)
    assert document is None
    assert errors == ["evidence JSON rejected: duplicate JSON key: x"]

    link = tmp_path / "link.json"
    link.symlink_to(target)
    document, errors = checker.load_evidence(link)
    assert document is None
    assert errors == ["evidence file read failed"]


def test_source_closure_rejects_symlinked_component(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    real = tmp_path / "real"
    real.mkdir()
    (real / "source.rs").write_text("fn main() {}\n", encoding="utf-8")
    (tmp_path / "linked").symlink_to(real, target_is_directory=True)
    with pytest.raises(ValueError, match="unavailable or symlinked"):
        support._regular_file_bytes(tmp_path, "linked/source.rs", 1_024)

    for unsafe in (".", "linked//source.rs", "nul\0source.rs"):
        with pytest.raises(ValueError, match="unsafe relative path"):
            support._regular_file_bytes(tmp_path, unsafe, 1_024)


def test_source_closure_rejects_undeclared_build_script(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package = tmp_path / "package"
    (package / "src").mkdir(parents=True)
    (package / "Cargo.toml").write_text("[package]\nname='x'\nversion='0.1.0'\n")
    (package / "src/lib.rs").write_text("pub fn x() {}\n")
    monkeypatch.setattr(
        support,
        "SOURCE_FILES",
        (
            ("manifest", "package/Cargo.toml"),
            ("source", "package/src/lib.rs"),
        ),
    )
    monkeypatch.setattr(support, "SOURCE_INVENTORY_PACKAGE_ROOTS", ("package",))
    monkeypatch.setattr(support, "SOURCE_INVENTORY_EXACT_FILES", ())
    support.source_closure(tmp_path)

    (package / "build.rs").write_text("fn main() {}\n")

    with pytest.raises(ValueError, match="source inventory mismatch"):
        support.source_closure(tmp_path)


def test_sealed_executable_runs_original_bytes_after_path_replacement(
    tmp_path: Path,
) -> None:
    source = tmp_path / "verifier"
    shutil.copyfile("/usr/bin/true", source)

    with sealed_executable.SealedExecutable(source) as executable:
        shutil.copyfile("/usr/bin/false", source)
        process = replay_process.run_bounded(
            replay_process.ProcessRequest(
                command=(executable.command_path,),
                cwd=tmp_path,
                env=replay_environment.clean_environment(),
                timeout_seconds=5,
                output_limit_bytes=1_024,
                profile=replay_process.ProcessProfile.REPLAY,
                pass_fds=executable.pass_fds,
            )
        )

        assert process.returncode == 0
        assert executable.identity.transport == "linux_memfd_full_seals_v1"
        assert executable.identity.size_bytes > 0


def test_replay_profile_installs_no_new_privileges_and_blocks_fork(
    tmp_path: Path,
) -> None:
    script = (
        "import os,sys\n"
        "status=open('/proc/self/status', encoding='ascii').read()\n"
        "assert 'NoNewPrivs:\\t1' in status\n"
        "try:\n"
        " os.fork()\n"
        "except OSError:\n"
        " sys.stdout.buffer.write(b'bounded')\n"
        "else:\n"
        " os._exit(17)\n"
    )
    process = replay_process.run_bounded(
        replay_process.ProcessRequest(
            command=(sys.executable, "-c", script),
            cwd=tmp_path,
            env=replay_environment.clean_environment(),
            timeout_seconds=5,
            output_limit_bytes=1_024,
            profile=replay_process.ProcessProfile.REPLAY,
        )
    )

    assert process.returncode == 0
    assert process.stdout == b"bounded"
    assert process.stderr == b""


def test_live_replay_rejects_privileged_execution_context(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(checker.os, "geteuid", lambda: 0)

    with pytest.raises(RuntimeError, match="unprivileged Linux"):
        checker._require_unprivileged_execution_context()

    monkeypatch.setattr(checker.os, "geteuid", lambda: 1_000)
    monkeypatch.setattr(
        checker.Path,
        "read_text",
        lambda *_args, **_kwargs: (
            "Uid:\t1000\t1000\t1000\t1000\n"
            "Gid:\t1000\t1000\t1000\t1000\n"
            "CapInh:\t0000000000000000\n"
            "CapPrm:\t0000000000000000\n"
            "CapEff:\t0000000000000001\n"
            "CapAmb:\t0000000000000000\n"
        ),
    )
    with pytest.raises(RuntimeError, match="zero inherited, permitted, effective"):
        checker._require_unprivileged_execution_context()

    monkeypatch.setattr(
        checker.Path,
        "read_text",
        lambda *_args, **_kwargs: (
            "Uid:\t1000\t1000\t0\t1000\n"
            "Gid:\t1000\t1000\t1000\t1000\n"
            "CapInh:\t0000000000000000\n"
            "CapPrm:\t0000000000000000\n"
            "CapEff:\t0000000000000000\n"
            "CapAmb:\t0000000000000000\n"
        ),
    )
    with pytest.raises(RuntimeError, match="one unprivileged UID and GID"):
        checker._require_unprivileged_execution_context()


def test_live_facts_distinguish_fresh_binary_from_recorded_parity(
    tmp_path: Path,
) -> None:
    graph = ("package-a v1.0.0",)
    graph_sha256 = support.sha256_bytes((graph[0] + "\n").encode("utf-8"))
    recorded = {
        "binary_sha256": "11" * 32,
        "binary_size_bytes": 10,
        "binary_transport": support.EXPECTED_BINARY_TRANSPORT,
        "dependency_graph_package_count": 1,
        "dependency_graph_sha256": graph_sha256,
    }
    context = checker.LiveContext(
        repo_root=tmp_path,
        workspace=tmp_path,
        source_root=tmp_path,
        target_directory=tmp_path,
        cargo="cargo",
        env={},
        toolchain_versions={},
    )
    replay = checker.LiveReplay(
        binary_sha256="22" * 32,
        binary_size_bytes=11,
        binary_transport=support.EXPECTED_BINARY_TRANSPORT,
        dependency_graph=graph,
        negative_controls=[],
        stdout=b"report",
    )

    facts = checker._live_facts(context, replay, recorded)

    assert facts["verified"] is True
    assert facts["source_built_structural_replay_verified"] is True
    assert facts["recorded_dependency_graph_identity_match"] is True
    assert facts["recorded_execution_identity_match"] is False
    assert facts["recorded_evidence_parity"] is False
    assert facts["status"] == ("source_built_structural_replay_with_fresh_measured_identity")


def test_dependency_graph_identity_is_private_snapshot_path_independent(
    tmp_path: Path,
) -> None:
    source_a = tmp_path / "first" / "source-snapshot"
    source_b = tmp_path / "second" / "source-snapshot"
    source_a.mkdir(parents=True)
    source_b.mkdir(parents=True)
    rows_a = (
        f"serde v1.0.228\nzenodex-zrpf-protocol-v3 v0.1.0 ({source_a}/zk/zrpf_protocol/protocol)\n"
    ).encode()
    rows_b = (
        f"zenodex-zrpf-protocol-v3 v0.1.0 ({source_b}/zk/zrpf_protocol/protocol)\nserde v1.0.228\n"
    ).encode()

    first = checker._canonical_dependency_graph(rows_a, source_a)
    second = checker._canonical_dependency_graph(rows_b, source_b)

    assert first == second
    assert str(tmp_path) not in "\n".join(first)
    assert support.DEPENDENCY_GRAPH_CANONICAL_SOURCE_ROOT in first[1]


def test_dependency_graph_identity_rejects_unbound_absolute_path(
    tmp_path: Path,
) -> None:
    source = tmp_path / "source-snapshot"
    source.mkdir()

    with pytest.raises(RuntimeError, match="contains an unbound path"):
        checker._canonical_dependency_graph(
            b"foreign v0.1.0 (/untrusted/" + b"workspace/foreign)\n",
            source,
        )


def test_negative_control_rejects_unknown_output_fields() -> None:
    script = (
        "import json,sys\n"
        "record={'context':'replay','error_code':'usage','extra':'leak',"
        "'ok':False,'schema':'zenodex/zrpf_v3_retained_structural_replay/v1',"
        "'status':'rejected','verifier_code':None}\n"
        "sys.stderr.write(json.dumps(record,sort_keys=True,separators=(',',':'))+'\\n')\n"
        "raise SystemExit(1)\n"
    )

    with pytest.raises(RuntimeError, match="rejection mismatch"):
        replay_controls._reject(
            sys.executable,
            (),
            ["-c", script],
            replay_environment.clean_environment(),
            replay_controls.ExpectedReject("extra", "usage", "replay"),
        )


def test_receipt_set_rejects_byte_mutation_and_symlink(tmp_path: Path) -> None:
    receipt_dir = tmp_path / "receipts"
    shutil.copytree(support.RECEIPT_DIRECTORY, receipt_dir)
    first = receipt_dir / support.RECEIPTS[0][0]
    raw = bytearray(first.read_bytes())
    raw[0] ^= 1
    first.write_bytes(raw)
    with pytest.raises(ValueError, match="retained receipt binding mismatch"):
        support.retained_receipt_set(receipt_dir)

    first.unlink()
    first.symlink_to(support.RECEIPT_DIRECTORY / support.RECEIPTS[0][0])
    with pytest.raises(ValueError, match="unavailable or symlinked"):
        support.retained_receipt_set(receipt_dir)


def test_replay_report_exact_shape_accepts_and_root_mutation_rejects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = _synthetic_exact_report()
    raw = _report_bytes(report)
    _bind_report_bytes(monkeypatch, raw)

    parsed, errors = support.validate_replay_report(raw)

    assert parsed == report
    assert errors == []

    mutated = copy.deepcopy(report)
    mutated["root"]["journal_hash"] = "00" * 32
    mutated_raw = _report_bytes(mutated)
    _bind_report_bytes(monkeypatch, mutated_raw)
    _, errors = support.validate_replay_report(mutated_raw)
    assert errors == ["root report mismatch"]

    malformed = copy.deepcopy(report)
    malformed["leaf_receipts"] = {}
    malformed["level_one_receipts"] = [None]
    malformed_raw = _report_bytes(malformed)
    _bind_report_bytes(monkeypatch, malformed_raw)
    _, errors = support.validate_replay_report(malformed_raw)
    assert "leaf receipt report mismatch" in errors
    assert "level-one receipt report mismatch" in errors


def test_manifest_features_and_governed_source_anchor_snapshot_match() -> None:
    replay_toolchain.validate_manifest_features()
    assert checker.verify_source_anchor(support.REPO_ROOT) == []
    closure = support.anchored_source_closure(support.REPO_ROOT)
    assert closure["file_count"] == support.EXPECTED_SOURCE_CLOSURE_FILES
    assert closure["total_bytes"] == support.EXPECTED_SOURCE_CLOSURE_BYTES
    assert closure["sha256"] == support.EXPECTED_SOURCE_CLOSURE_SHA256


def test_toolchain_binding_rejects_symlinked_artifact(tmp_path: Path) -> None:
    toolchain_home = tmp_path / "toolchain"
    binary = toolchain_home / "bin/cargo"
    binary.parent.mkdir(parents=True)
    binary.write_bytes(b"pinned-tool")
    row = {
        "relative_path": "bin/cargo",
        "sha256": support.sha256_bytes(b"pinned-tool"),
        "size_bytes": len(b"pinned-tool"),
    }

    assert replay_toolchain._bound_artifact(toolchain_home, row) == binary
    binary.unlink()
    replacement = tmp_path / "replacement"
    replacement.write_bytes(b"pinned-tool")
    binary.symlink_to(replacement)

    with pytest.raises(RuntimeError, match="toolchain artifact binding mismatch"):
        replay_toolchain._bound_artifact(toolchain_home, row)


def _synthetic_exact_report() -> dict:
    return {
        "authority": dict(support.EXPECTED_REPORT_AUTHORITY),
        "expected_images": dict(support.EXPECTED_REPORT_IMAGES),
        "leaf_receipts": [{"receipt_sha256": digest} for _, _, digest in support.RECEIPTS[:4]],
        "level_one_receipts": [
            {"receipt_sha256": digest} for _, _, digest in support.RECEIPTS[4:6]
        ],
        "mutation_control": {
            "candidate_accepted": False,
            "mutated_receipt_sha256": support.MUTATION_RECEIPT_SHA256,
            "reject_code": "receipt_verification_failed",
            "source_receipt_sha256": support.ROOT_RECEIPT_SHA256,
        },
        "ok": True,
        "receipt_security_profile": dict(support.EXPECTED_REPORT_PROFILE),
        "root": {
            "count_unit": {"label": "source_transition_receipt_v3"},
            "journal_hash": support.ROOT_JOURNAL_HASH,
            "leaf_count": 4,
            "operation_count": 4,
            "receipt_sha256": support.ROOT_RECEIPT_SHA256,
            "subtree_node_count": 7,
        },
        "schema": support.REPORT_SCHEMA,
        "status": "retained_exact_four_leaf_two_level_receipts_verified",
    }


def _synthetic_live_facts() -> dict:
    recorded = _expected_evidence()["recorded_execution"]
    build = _expected_evidence()["recorded_build"]
    return {
        **TEST_EXECUTION_IDENTITY,
        "executed": True,
        "negative_controls": [row | {"passed": True} for row in recorded["negative_controls"]],
        "normal_and_dev_stdout_identical": True,
        "stdout_sha256": recorded["stdout_sha256"],
        "stdout_size_bytes": recorded["stdout_size_bytes"],
        "toolchain_versions": {
            "cargo": build["cargo_version"],
            "rustc": build["rustc_version"],
            "rustdoc": build["rustdoc_version"],
        },
        "verified": True,
    }


def _expected_evidence() -> dict:
    return support.expected_evidence(TEST_EXECUTION_IDENTITY)


def _report_bytes(report: dict) -> bytes:
    return (json.dumps(report, sort_keys=True, separators=(",", ":")) + "\n").encode()


def _bind_report_bytes(monkeypatch: pytest.MonkeyPatch, raw: bytes) -> None:
    monkeypatch.setattr(support, "EXPECTED_STDOUT_SIZE", len(raw))
    monkeypatch.setattr(support, "EXPECTED_STDOUT_SHA256", support.sha256_bytes(raw))
