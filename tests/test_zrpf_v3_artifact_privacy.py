from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from tools.zrpf_v3_artifact_privacy import (
    DEFAULT_ARTIFACTS,
    FIRECRACKER_RUNTIME_PUBLIC_ARTIFACTS,
    REPO_ROOT,
    ArtifactSpec,
    main,
    scan_artifacts,
    scan_candidate_bytes,
    scan_default_artifacts,
)


def test_committed_zrpf_artifact_inventory_is_clean() -> None:
    report = scan_default_artifacts()

    assert report["ok"] is True
    assert report["artifact_count_expected"] == len(DEFAULT_ARTIFACTS) == 35
    assert report["artifact_count_scanned"] == 35
    assert report["complete_artifact_privacy_verified"] is False
    assert report["finding_count"] == 0
    assert report["error_count"] == 0


def test_firecracker_runtime_public_artifacts_are_governed() -> None:
    expected_paths = {
        "config/proof_profiles/zrpf_firecracker_guest_kernel_build_record_v1.json",
        "config/proof_profiles/zrpf_firecracker_runtime_image_build_record_v1.json",
        "config/proof_profiles/zrpf_v3_firecracker_replay_intent_v1.json",
        "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v1.json",
        "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v2.json",
        "docs/research/ZRPF_V3_FIRECRACKER_GOVERNED_DIRECT_REPLAY_EVIDENCE_20260712.json",
        "docs/research/ZRPF_V3_FIRECRACKER_RUNTIME_CONTRACT_20260711.md",
        "evidence/zrpf-v3-retained-structural-replay-v1/firecracker-governed-output-payload.json",
        "evidence/zrpf-v3-retained-structural-replay-v1/firecracker-direct-v2/config.json",
        "evidence/zrpf-v3-retained-structural-replay-v1/firecracker-direct-v2/firecracker.stdout",
        "evidence/zrpf-v3-retained-structural-replay-v1/firecracker-direct-v2/local-report.json",
        "tools/build_zrpf_v3_firecracker_guest_images.sh",
        "tools/check_zrpf_v3_firecracker_guest_elf.py",
    }

    assert {
        artifact.relative_path for artifact in FIRECRACKER_RUNTIME_PUBLIC_ARTIFACTS
    } == expected_paths
    report = scan_default_artifacts()
    scanned_paths = {artifact["path"] for artifact in report["artifacts"]}
    assert expected_paths <= scanned_paths


def test_firecracker_runtime_records_preserve_complete_privacy_nonclaim() -> None:
    image_record = json.loads(
        (
            REPO_ROOT / "config/proof_profiles/zrpf_firecracker_runtime_image_build_record_v1.json"
        ).read_text(encoding="utf-8")
    )
    runtime_manifest = json.loads(
        (
            REPO_ROOT
            / "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v2.json"
        ).read_text(encoding="utf-8")
    )
    replay_evidence = json.loads(
        (
            REPO_ROOT / "docs/research/"
            "ZRPF_V3_FIRECRACKER_GOVERNED_DIRECT_REPLAY_EVIDENCE_20260712.json"
        ).read_text(encoding="utf-8")
    )

    assert image_record["authority"]["artifact_privacy_scan_passed"] is False
    assert image_record["guest_binary"]["artifact_privacy"] == {
        "complete_guest_binary_path_privacy_verified": False,
        "confidential_name_policy_evaluated": False,
        "public_privacy_rule_scan_applied_to_guest_binary": False,
    }
    assert runtime_manifest["authority"]["witness_privacy"] is False
    assert runtime_manifest["authority"]["zero_knowledge_privacy"] is False
    assert (
        replay_evidence["privacy_scan"]["guest_binary_complete_path_privacy_scan_passed"] is False
    )


def test_in_memory_candidate_scan_rejects_before_publication() -> None:
    artifact = ArtifactSpec("docs/research/candidate.json", "candidate")

    clean = scan_candidate_bytes(artifact, b'{"public":true}\n')
    rejected = scan_candidate_bytes(
        artifact,
        b'{"credential":"ghp_' + b"A" * 36 + b'"}\n',
    )

    assert clean["ok"] is True
    assert clean["complete_artifact_privacy_verified"] is False
    assert rejected["ok"] is False
    assert rejected["complete_artifact_privacy_verified"] is False
    assert rejected["finding_count"] == 1
    assert rejected["findings"][0]["rule_id"] == "github_legacy_token"


@pytest.mark.parametrize(
    ("rule_id", "payload"),
    [
        (
            "posix_home_path",
            b"build=/" + b"home/researcher/project/target",
        ),
        (
            "posix_workspace_path",
            b"source=/" + b"workspace/project/src/lib.rs",
        ),
        ("posix_temporary_build_path", b"target=/tmp/project-build/output"),
        (
            "windows_home_or_workspace_path",
            rb"source=C:\Users\Researcher\project\src\lib.rs",
        ),
        ("email_address", b"contact=researcher@example.invalid"),
        ("private_key_pem", b"-----BEGIN OPENSSH PRIVATE KEY-----"),
        ("url_basic_credentials", b"https://builder:credential@example.invalid/repo"),
        (
            "url_long_userinfo_credential",
            b"https://abcdefghijklmnopqrstuvwx@example.invalid/repo",
        ),
        ("url_secret_query", b"https://example.invalid/api?access_token=credential"),
        ("aws_access_key_id", b"AK" + b"IA" + b"ABCDEFGHIJKLMNOP"),
        (
            "aws_secret_access_key_assignment",
            b"aws_secret_" + b"access_key=" + b"abcdefghijklmnopqrst" + b"uvwxyzABCDEFGHIJKLMN",
        ),
        ("google_api_key", b"AIza" + b"A" * 35),
        ("azure_storage_account_key", b"AccountKey=" + b"A" * 44),
        ("github_legacy_token", b"ghp_" + b"A" * 36),
        ("github_fine_grained_token", b"github_pat_" + b"A" * 24),
        ("bearer_token", b"Authorization: Bearer " + b"A" * 24),
    ],
)
def test_representative_public_leakage_pattern_rejects(
    tmp_path: Path,
    rule_id: str,
    payload: bytes,
) -> None:
    artifact = tmp_path / "artifact.bin"
    artifact.write_bytes(b"public-prefix\n" + payload + b"\npublic-suffix")

    report = scan_artifacts(tmp_path, [ArtifactSpec("artifact.bin", "test_artifact")])

    assert report["ok"] is False
    assert report["error_count"] == 0
    assert rule_id in {finding["rule_id"] for finding in report["findings"]}
    finding = next(row for row in report["findings"] if row["rule_id"] == rule_id)
    assert payload not in json.dumps(finding).encode("utf-8")
    assert set(finding) == {
        "byte_offset",
        "match_length",
        "match_sha256",
        "path",
        "role",
        "rule_id",
    }


def test_findings_are_deterministic_and_sorted_without_secret_echo(tmp_path: Path) -> None:
    (tmp_path / "z.bin").write_bytes(b"researcher@example.invalid")
    (tmp_path / "a.bin").write_bytes(b"-----BEGIN PRIVATE KEY-----")
    artifacts = [ArtifactSpec("z.bin", "z"), ArtifactSpec("a.bin", "a")]

    first = scan_artifacts(tmp_path, artifacts)
    second = scan_artifacts(tmp_path, list(reversed(artifacts)))

    assert first == second
    assert [row["path"] for row in first["findings"]] == ["a.bin", "z.bin"]
    encoded = json.dumps(first, sort_keys=True)
    assert "researcher@example.invalid" not in encoded
    assert "BEGIN PRIVATE KEY" not in encoded


def test_missing_symlink_fifo_and_oversized_artifacts_fail_closed(tmp_path: Path) -> None:
    real = tmp_path / "real.bin"
    real.write_bytes(b"clean")
    (tmp_path / "link.bin").symlink_to(real)
    os.mkfifo(tmp_path / "fifo.bin")
    (tmp_path / "oversized.bin").write_bytes(b"x" * 17 * 1024 * 1024)
    artifacts = [
        ArtifactSpec("missing.bin", "test"),
        ArtifactSpec("link.bin", "test"),
        ArtifactSpec("fifo.bin", "test"),
        ArtifactSpec("oversized.bin", "test"),
    ]

    report = scan_artifacts(tmp_path, artifacts)

    assert report["ok"] is False
    assert report["artifact_count_scanned"] == 0
    assert report["finding_count"] == 0
    assert {row["code"] for row in report["errors"]} == {
        "artifact_not_regular",
        "artifact_size_out_of_bounds",
        "artifact_unavailable",
    }


def test_symlinked_parent_and_invalid_or_duplicate_paths_fail_closed(tmp_path: Path) -> None:
    real = tmp_path / "real"
    real.mkdir()
    (real / "artifact.bin").write_bytes(b"clean")
    (tmp_path / "linked").symlink_to(real, target_is_directory=True)
    artifacts = [
        ArtifactSpec("linked/artifact.bin", "test"),
        ArtifactSpec(".", "test"),
        ArtifactSpec("nul\0artifact.bin", "test"),
        ArtifactSpec("../escape.bin", "test"),
        ArtifactSpec("real/artifact.bin", "test"),
        ArtifactSpec("real/artifact.bin", "duplicate"),
    ]

    report = scan_artifacts(tmp_path, artifacts)

    assert report["ok"] is False
    assert report["artifact_count_scanned"] == 1
    assert {row["code"] for row in report["errors"]} == {
        "artifact_parent_unavailable",
        "duplicate_artifact",
        "invalid_artifact_spec",
    }


def test_cli_prints_canonical_report_and_returns_one_on_finding(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    (tmp_path / "artifact.bin").write_bytes(b"ghp_" + b"A" * 36)

    exit_code = main(["--root", str(tmp_path), "--artifact", "artifact.bin"])
    stdout = capsys.readouterr().out
    report = json.loads(stdout)

    assert exit_code == 1
    assert report["ok"] is False
    assert stdout == json.dumps(report, sort_keys=True, separators=(",", ":")) + "\n"
