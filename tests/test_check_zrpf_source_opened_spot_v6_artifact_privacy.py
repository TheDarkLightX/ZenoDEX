from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import check_zrpf_source_opened_spot_v6_artifact_privacy as checker
from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence


def _populate_clean_inventory(root: Path) -> None:
    kinds = {
        path: kind for _artifact_id, path, kind in evidence.ARTIFACT_SPECS
    }
    for artifact in checker.FINAL_ARTIFACTS:
        if kinds[artifact.relative_path] in {"canonical_json", "canonical_receipt_json"}:
            raw = b'{"bounded_public_fixture":true}\n'
        else:
            raw = b"\x00\x01\x02ZRPF-V6-public-binary\xff"
        (root / artifact.relative_path).write_bytes(raw)


def test_governed_inventory_matches_the_fourteen_evidence_artifacts() -> None:
    assert len(checker.FINAL_ARTIFACTS) == 14
    assert [artifact.relative_path for artifact in checker.FINAL_ARTIFACTS] == [
        path for _artifact_id, path, _kind in evidence.ARTIFACT_SPECS
    ]
    assert [artifact.role for artifact in checker.FINAL_ARTIFACTS] == [
        artifact_id for artifact_id, _path, _kind in evidence.ARTIFACT_SPECS
    ]


def test_clean_binary_and_json_inventory_has_deterministic_hashes(
    tmp_path: Path,
) -> None:
    _populate_clean_inventory(tmp_path)

    first = checker.scan_artifact_directory(tmp_path)
    second = checker.scan_artifact_directory(tmp_path)

    assert first == second
    assert first["ok"] is True
    assert first["artifact_count_expected"] == 14
    assert first["artifact_count_observed"] == 14
    assert first["artifact_count_scanned"] == 14
    assert first["finding_count"] == 0
    assert first["error_count"] == 0
    assert first["complete_artifact_privacy_verified"] is False
    assert len(first["artifact_set_sha256"]) == 64
    assert len(first["inventory_names_sha256"]) == 64
    assert all(len(row["sha256"]) == 64 for row in first["artifacts"])


@pytest.mark.parametrize(
    ("rule_id", "payload"),
    [
        ("posix_home_path", b"source=/home/researcher/private/build.rs"),
        ("posix_workspace_path", b"source=/workspace/private-project/src/lib.rs"),
        ("email_address", b"author=researcher@example.invalid"),
        ("github_legacy_token", b"token=ghp_" + b"A" * 36),
        ("private_key_pem", b"-----BEGIN OPENSSH PRIVATE KEY-----"),
    ],
)
def test_named_sensitive_patterns_reject_without_secret_echo(
    tmp_path: Path,
    rule_id: str,
    payload: bytes,
) -> None:
    _populate_clean_inventory(tmp_path)
    target = tmp_path / checker.FINAL_ARTIFACTS[0].relative_path
    target.write_bytes(b"public-prefix\n" + payload + b"\npublic-suffix")

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["error_count"] == 0
    assert rule_id in {finding["rule_id"] for finding in report["findings"]}
    assert payload not in json.dumps(report, sort_keys=True).encode()
    assert report["complete_artifact_privacy_verified"] is False


def test_symlinked_governed_artifact_fails_closed(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    link = tmp_path / checker.FINAL_ARTIFACTS[0].relative_path
    target = checker.FINAL_ARTIFACTS[1].relative_path
    link.unlink()
    link.symlink_to(target)

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["artifact_count_observed"] == 14
    assert report["artifact_count_scanned"] == 13
    assert "artifact_unavailable" in {row["code"] for row in report["errors"]}


def test_missing_governed_artifact_fails_inventory_and_scan(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    missing = checker.FINAL_ARTIFACTS[0].relative_path
    (tmp_path / missing).unlink()

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["artifact_count_observed"] == 13
    assert report["artifact_count_scanned"] == 13
    assert {row["code"] for row in report["errors"]} >= {
        "artifact_unavailable",
        "governed_artifact_missing",
    }


def test_extra_inventory_fails_without_echoing_the_extra_name(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    private_name = "private-project-secret-name.txt"
    (tmp_path / private_name).write_bytes(b"clean")

    report = checker.scan_artifact_directory(tmp_path)
    encoded = json.dumps(report, sort_keys=True)

    assert report["ok"] is False
    assert report["artifact_count_observed"] == 15
    assert "extra_governed_inventory" in {
        row["code"] for row in report["errors"]
    }
    assert private_name not in encoded


def test_cli_emits_canonical_report_and_rejects_finding(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    _populate_clean_inventory(tmp_path)
    target = tmp_path / checker.FINAL_ARTIFACTS[0].relative_path
    target.write_bytes(b"researcher@example.invalid")

    exit_code = checker.main(["--artifact-directory", str(tmp_path)])
    stdout = capsys.readouterr().out
    report = json.loads(stdout)

    assert exit_code == 1
    assert report["ok"] is False
    assert stdout == json.dumps(report, sort_keys=True, separators=(",", ":")) + "\n"
