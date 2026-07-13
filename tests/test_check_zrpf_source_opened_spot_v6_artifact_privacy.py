from __future__ import annotations

import hashlib
import json
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path

import pytest

from tools import check_zrpf_source_opened_spot_v6_artifact_privacy as checker
from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
from tools import zrpf_v3_artifact_privacy as privacy


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


def _artifact_for_role(role: str) -> privacy.ArtifactSpec:
    return next(artifact for artifact in checker.FINAL_ARTIFACTS if artifact.role == role)


def test_governed_inventory_matches_the_evidence_artifacts() -> None:
    assert len(checker.FINAL_ARTIFACTS) == len(evidence.ARTIFACT_SPECS)
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
    assert first["artifact_count_expected"] == len(evidence.ARTIFACT_SPECS)
    assert first["artifact_count_observed"] == len(evidence.ARTIFACT_SPECS)
    assert first["artifact_count_scanned"] == len(evidence.ARTIFACT_SPECS)
    assert first["finding_count"] == 0
    assert first["error_count"] == 0
    assert first["complete_artifact_privacy_verified"] is False
    assert first["allowed_upstream_path_exception_count"] == 0
    assert first["allowed_upstream_path_exceptions"] == []
    assert len(first["artifact_set_sha256"]) == 64
    assert len(first["inventory_names_sha256"]) == 64
    assert len(first["upstream_path_exception_policy_sha256"]) == 64
    assert all(len(row["sha256"]) == 64 for row in first["artifacts"])


@pytest.mark.parametrize("exception", checker.UPSTREAM_PATH_EXCEPTIONS)
def test_exact_pinned_upstream_path_is_allowed_once_only_in_r0bf_program(
    tmp_path: Path,
    exception: checker.UpstreamPathException,
) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    (tmp_path / target.relative_path).write_bytes(
        b"R0BF\x01\x00public-prefix\x00" + exception.exact_path + b"\x00public-suffix"
    )

    report = checker.scan_artifact_directory(tmp_path)
    encoded = json.dumps(report, sort_keys=True).encode()

    assert report["ok"] is True
    assert report["finding_count"] == 0
    assert report["allowed_upstream_path_exception_count"] == 1
    assert report["complete_artifact_privacy_verified"] is False
    assert report["allowed_upstream_path_exceptions"] == [
        {
            "artifact_path": target.relative_path,
            "artifact_role": target.role,
            "byte_offset": len(b"R0BF\x01\x00public-prefix\x00"),
            "component_id": exception.component_id,
            "governed_source_artifact_sha256": (
                exception.governed_source_artifact_sha256
            ),
            "path_sha256": hashlib.sha256(exception.exact_path).hexdigest(),
            "rule_id": exception.rule_id,
        }
    ]
    assert exception.exact_path not in encoded


@pytest.mark.parametrize(
    ("exception_index", "mutate"),
    [
        (0, lambda raw: raw.replace(b"/home/remi/", b"/home/remix/", 1)),
        (0, lambda raw: raw.replace(b"no_std_strings-0.1.3", b"no_std_strings-0.1.4", 1)),
        (0, lambda raw: b"coherent-prefix" + raw),
        (0, lambda raw: raw + b".bak"),
        (1, lambda raw: raw.replace(b"/root/", b"/rootx/", 1)),
        (1, lambda raw: raw.replace(b"rustc-demangle-0.1.26", b"rustc-demangle-0.1.27", 1)),
        (1, lambda raw: b"coherent-prefix" + raw),
        (1, lambda raw: raw + b".bak"),
    ],
)
def test_nearby_upstream_path_variant_rejects(
    tmp_path: Path,
    exception_index: int,
    mutate: Callable[[bytes], bytes],
) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    exception = checker.UPSTREAM_PATH_EXCEPTIONS[exception_index]
    changed = mutate(exception.exact_path)
    (tmp_path / target.relative_path).write_bytes(b"R0BF\x01\x00" + changed + b"\x00")

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert exception.rule_id in {row["rule_id"] for row in report["findings"]}


@pytest.mark.parametrize("exception", checker.UPSTREAM_PATH_EXCEPTIONS)
def test_exact_upstream_path_rejects_in_non_program_role(
    tmp_path: Path,
    exception: checker.UpstreamPathException,
) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("source_request")
    (tmp_path / target.relative_path).write_bytes(exception.exact_path + b"\n")

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert exception.rule_id in {row["rule_id"] for row in report["findings"]}


def test_exact_upstream_path_rejects_without_r0bf_magic(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    exception = checker.UPSTREAM_PATH_EXCEPTIONS[0]
    (tmp_path / target.relative_path).write_bytes(
        b"ELF-not-r0bf\x00" + exception.exact_path + b"\x00"
    )

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert exception.rule_id in {row["rule_id"] for row in report["findings"]}


def test_second_exact_upstream_path_occurrence_rejects(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    exception = checker.UPSTREAM_PATH_EXCEPTIONS[0]
    (tmp_path / target.relative_path).write_bytes(
        b"R0BF\x01\x00"
        + exception.exact_path
        + b"\x00"
        + exception.exact_path
        + b"\x00"
    )

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 1
    assert report["finding_count"] == 1
    assert report["findings"][0]["rule_id"] == "posix_home_path"


@pytest.mark.parametrize("exception_index", [0, 1])
def test_changed_governed_upstream_artifact_hash_rejects_policy(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    exception_index: int,
) -> None:
    _populate_clean_inventory(tmp_path)
    exceptions = list(checker.UPSTREAM_PATH_EXCEPTIONS)
    selected = exceptions[exception_index]
    exceptions[exception_index] = replace(
        selected,
        governed_source_artifact_sha256="0" * 64,
    )
    monkeypatch.setattr(checker, "UPSTREAM_PATH_EXCEPTIONS", tuple(exceptions))
    target = _artifact_for_role("leaf_program_binary")
    (tmp_path / target.relative_path).write_bytes(
        b"R0BF\x01\x00" + selected.exact_path + b"\x00"
    )

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert "invalid_exception_binding" in {row["code"] for row in report["errors"]}
    assert selected.rule_id in {row["rule_id"] for row in report["findings"]}


@pytest.mark.parametrize(
    ("payload", "rule_id"),
    [
        (b"/home/private user/source.rs", "posix_home_path"),
        (b"/root/private user/source.rs", "posix_root_path"),
    ],
)
def test_arbitrary_home_or_root_path_is_detected_for_v6(
    tmp_path: Path,
    payload: bytes,
    rule_id: str,
) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    (tmp_path / target.relative_path).write_bytes(b"R0BF\x01\x00" + payload + b"\x00")

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert rule_id in {row["rule_id"] for row in report["findings"]}


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
    assert report["artifact_count_observed"] == len(evidence.ARTIFACT_SPECS)
    assert report["artifact_count_scanned"] == len(evidence.ARTIFACT_SPECS) - 1
    assert "artifact_unavailable" in {row["code"] for row in report["errors"]}


def test_missing_governed_artifact_fails_inventory_and_scan(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    missing = checker.FINAL_ARTIFACTS[0].relative_path
    (tmp_path / missing).unlink()

    report = checker.scan_artifact_directory(tmp_path)

    assert report["ok"] is False
    assert report["artifact_count_observed"] == len(evidence.ARTIFACT_SPECS) - 1
    assert report["artifact_count_scanned"] == len(evidence.ARTIFACT_SPECS) - 1
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
    assert report["artifact_count_observed"] == len(evidence.ARTIFACT_SPECS) + 1
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
