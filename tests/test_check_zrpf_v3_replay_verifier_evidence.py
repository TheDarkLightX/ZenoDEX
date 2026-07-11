from __future__ import annotations

import copy
import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from tools import check_zrpf_v3_replay_verifier_evidence as checker
from tools import zrpf_v3_replay_environment as replay_environment
from tools import zrpf_v3_replay_evidence_support as support
from tools import zrpf_v3_replay_process as replay_process
from tools import zrpf_v3_replay_record_writer as record_writer
from tools import zrpf_v3_replay_sealed_executable as sealed_executable
from tools import zrpf_v3_replay_source_snapshot as replay_snapshot
from tools import zrpf_v3_replay_toolchain as replay_toolchain


def test_expected_evidence_pins_source_receipts_and_authority_boundary() -> None:
    evidence = support.expected_evidence()

    assert evidence["schema"] == support.SCHEMA
    assert evidence["source_anchor"] == {
        "commit": support.SOURCE_COMMIT,
        "tree": support.SOURCE_TREE,
    }
    assert evidence["replay_source_closure"]["file_count"] == 32
    assert evidence["retained_receipt_set"]["artifact_count"] == 8
    assert evidence["retained_receipt_set"]["total_bytes"] == 4_746_064
    assert evidence["recorded_execution"]["stdout_sha256"] == (
        support.EXPECTED_STDOUT_SHA256
    )
    assert evidence["claims"]["same_host_source_built_host_verifier_replay"] is True
    assert evidence["claims"]["public_replay_promoted"] is False
    assert evidence["claims"]["production_authority"] is False


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
    assert report["facts"]["source_files_checked"] == 32
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


def test_static_check_rejects_claim_mutation_and_unknown_field(tmp_path: Path) -> None:
    evidence = support.expected_evidence()
    evidence["claims"]["production_authority"] = True
    evidence["unknown"] = True
    path = tmp_path / "evidence.json"
    path.write_text(json.dumps(evidence), encoding="utf-8")

    report = checker.validate_static(path)

    assert report["ok"] is False
    assert "evidence root field set mismatch" in report["errors"]
    assert "evidence field mismatch: claims" in report["errors"]


def test_static_check_rejects_noncanonical_equivalent_bytes(tmp_path: Path) -> None:
    path = tmp_path / "evidence.json"
    path.write_text(json.dumps(support.expected_evidence()), encoding="ascii")

    report = checker.validate_static(path)

    assert report["ok"] is False
    assert "evidence bytes are not canonical" in report["errors"]


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

    assert poisoned.keys().isdisjoint(env)
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
    assert errors == ["evidence file is not a bounded regular file"]


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


def test_manifest_features_and_source_anchor_match_current_boundary() -> None:
    replay_toolchain.validate_manifest_features()
    assert checker.verify_source_anchor(support.REPO_ROOT) == []


def _synthetic_exact_report() -> dict:
    return {
        "authority": dict(support.EXPECTED_REPORT_AUTHORITY),
        "expected_images": dict(support.EXPECTED_REPORT_IMAGES),
        "leaf_receipts": [
            {"receipt_sha256": digest} for _, _, digest in support.RECEIPTS[:4]
        ],
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
    recorded = support.expected_evidence()["recorded_execution"]
    build = support.expected_evidence()["recorded_build"]
    return {
        "binary_sha256": "11" * 32,
        "binary_size_bytes": 1,
        "dependency_graph_package_count": 1,
        "dependency_graph_sha256": "22" * 32,
        "executed": True,
        "negative_controls": [
            row | {"passed": True} for row in recorded["negative_controls"]
        ],
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


def _report_bytes(report: dict) -> bytes:
    return (json.dumps(report, sort_keys=True, separators=(",", ":")) + "\n").encode()


def _bind_report_bytes(monkeypatch: pytest.MonkeyPatch, raw: bytes) -> None:
    monkeypatch.setattr(support, "EXPECTED_STDOUT_SIZE", len(raw))
    monkeypatch.setattr(support, "EXPECTED_STDOUT_SHA256", support.sha256_bytes(raw))
