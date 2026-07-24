from __future__ import annotations

import hashlib
import json
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path

import pytest

from tools import check_zrpf_source_opened_spot_v6_artifact_privacy as checker
from tools import check_zrpf_source_opened_spot_v6_build_record as build_checker
from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
from tools import zrpf_v3_artifact_privacy as privacy


def _posix_path(*parts: bytes) -> bytes:
    return b"/".join((b"", *parts))


def _populate_clean_inventory(root: Path) -> None:
    kinds = {
        path: kind for _artifact_id, path, kind in evidence.ARTIFACT_SPECS
    }
    for artifact in checker.FINAL_ARTIFACTS:
        kind = kinds[artifact.relative_path]
        if kind == "canonical_json_line":
            raw = b'{"bounded_public_fixture":true}\n'
        elif kind in {"canonical_compact_json", "canonical_receipt_json"}:
            raw = b'{"bounded_public_fixture":true}'
        else:
            raw = b"\x00\x01\x02ZRPF-V6-public-binary\xff"
        (root / artifact.relative_path).write_bytes(raw)


def _artifact_for_role(role: str) -> privacy.ArtifactSpec:
    return next(artifact for artifact in checker.FINAL_ARTIFACTS if artifact.role == role)


def _write_candidate_build_record(path: Path, artifact_root: Path) -> None:
    programs = []
    for artifact in checker.FINAL_ARTIFACTS:
        if artifact.role not in checker.RISC0_PROGRAM_BINARY_ROLES:
            continue
        raw = (artifact_root / artifact.relative_path).read_bytes()
        programs.append(
            {
                "stage": artifact.role,
                "package": f"fixture-{artifact.role}",
                "artifact_file": artifact.relative_path,
                "program_binary_bytes": len(raw),
                "program_binary_sha256": hashlib.sha256(raw).hexdigest(),
                "image_id_hex": "1" * 64,
                "image_id_words_le": [1] * 8,
                "verified_child_stage": "fixture-child",
                "verified_child_image_id": "2" * 64,
            }
        )
    record = {
        "schema": checker.BUILD_RECORD_SCHEMA,
        "recorded_at": "2026-07-12",
        "source_observation": {},
        "toolchain": {},
        "programs": programs,
        "publisher_reported_observations": {},
        "claims": {
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        },
    }
    path.write_text(json.dumps(record, indent=2, sort_keys=False) + "\n")


def _candidate_build_record_path(artifact_root: Path) -> Path:
    return artifact_root.parent / f"{artifact_root.name}.candidate-build-record.json"


def test_governed_inventory_matches_the_evidence_artifacts() -> None:
    assert len(checker.FINAL_ARTIFACTS) == len(evidence.ARTIFACT_SPECS)
    assert [artifact.relative_path for artifact in checker.FINAL_ARTIFACTS] == [
        path for _artifact_id, path, _kind in evidence.ARTIFACT_SPECS
    ]
    assert [artifact.role for artifact in checker.FINAL_ARTIFACTS] == [
        artifact_id for artifact_id, _path, _kind in evidence.ARTIFACT_SPECS
    ]


def test_candidate_build_record_schema_tracks_v3_checker() -> None:
    assert checker.BUILD_RECORD_SCHEMA == build_checker.RECORD_SCHEMA
    assert checker.BUILD_RECORD_SCHEMA.endswith("/v3")


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
    assert first["snapshot_root_identity_verified"] is True
    assert first["build_record_anchor_checked"] is False
    assert first["build_record_sha256"] is None
    assert first["allowed_upstream_path_exception_count"] == 0
    assert first["allowed_upstream_path_exceptions"] == []
    assert len(first["artifact_set_sha256"]) == 64
    assert len(first["inventory_names_sha256"]) == 64
    assert len(first["upstream_path_exception_policy_sha256"]) == 64
    assert first["upstream_path_exception_policy_anchored"] is False
    assert first["upstream_path_exception_policy_authority"] is False
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
    build_record = _candidate_build_record_path(tmp_path)
    _write_candidate_build_record(build_record, tmp_path)

    report = checker.scan_artifact_directory(
        tmp_path,
        build_record_path=build_record,
    )
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
            "governed_program_binary_sha256": hashlib.sha256(
                (tmp_path / target.relative_path).read_bytes()
            ).hexdigest(),
            "path_sha256": hashlib.sha256(exception.exact_path).hexdigest(),
            "rule_id": exception.rule_id,
        }
    ]
    assert report["build_record_anchor_checked"] is False
    assert len(report["build_record_sha256"]) == 64
    assert report["upstream_path_exception_policy_authority"] is False
    assert exception.exact_path not in encoded


@pytest.mark.parametrize(
    ("exception_index", "mutate"),
    [
        (
            0,
            lambda raw: raw.replace(
                _posix_path(b"home", b"remi", b""),
                _posix_path(b"home", b"remix", b""),
                1,
            ),
        ),
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
    build_record = _candidate_build_record_path(tmp_path)
    _write_candidate_build_record(build_record, tmp_path)

    report = checker.scan_artifact_directory(
        tmp_path,
        build_record_path=build_record,
    )

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 1
    assert report["finding_count"] == 1
    assert report["findings"][0]["rule_id"] == "posix_home_path"


def test_modified_r0bf_with_exact_path_rejects_build_record_binding(
    tmp_path: Path,
) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    exception = checker.UPSTREAM_PATH_EXCEPTIONS[0]
    governed = b"R0BF\x01\x00governed\x00" + exception.exact_path + b"\x00"
    target_path = tmp_path / target.relative_path
    target_path.write_bytes(governed)
    build_record = _candidate_build_record_path(tmp_path)
    _write_candidate_build_record(build_record, tmp_path)
    target_path.write_bytes(governed + b"modified-after-build-record")

    report = checker.scan_artifact_directory(
        tmp_path,
        build_record_path=build_record,
    )

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert exception.rule_id in {row["rule_id"] for row in report["findings"]}
    assert report["build_record_anchor_checked"] is False
    assert report["upstream_path_exception_policy_authority"] is False


def test_candidate_build_record_cannot_promote_authority(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    exception = checker.UPSTREAM_PATH_EXCEPTIONS[0]
    (tmp_path / target.relative_path).write_bytes(
        b"R0BF\x01\x00" + exception.exact_path + b"\x00"
    )
    build_record = _candidate_build_record_path(tmp_path)
    _write_candidate_build_record(build_record, tmp_path)
    document = json.loads(build_record.read_bytes())
    document["claims"]["release_authority"] = True
    build_record.write_text(json.dumps(document, indent=2, sort_keys=False) + "\n")

    report = checker.scan_artifact_directory(
        tmp_path,
        build_record_path=build_record,
    )

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert report["build_record_anchor_checked"] is False
    assert report["build_record_sha256"] is None
    assert report["upstream_path_exception_policy_anchored"] is False
    assert report["upstream_path_exception_policy_authority"] is False
    assert "build_record_binding_rejected" in {
        row["code"] for row in report["errors"]
    }


def test_legacy_v2_candidate_build_record_is_rejected(tmp_path: Path) -> None:
    _populate_clean_inventory(tmp_path)
    target = _artifact_for_role("leaf_program_binary")
    exception = checker.UPSTREAM_PATH_EXCEPTIONS[0]
    (tmp_path / target.relative_path).write_bytes(
        b"R0BF\x01\x00" + exception.exact_path + b"\x00"
    )
    build_record = _candidate_build_record_path(tmp_path)
    _write_candidate_build_record(build_record, tmp_path)
    document = json.loads(build_record.read_bytes())
    document["schema"] = "zenodex/zrpf_source_opened_spot_v6_build_record/v2"
    build_record.write_text(json.dumps(document, indent=2, sort_keys=False) + "\n")

    report = checker.scan_artifact_directory(
        tmp_path,
        build_record_path=build_record,
    )

    assert report["ok"] is False
    assert report["allowed_upstream_path_exception_count"] == 0
    assert report["build_record_sha256"] is None
    assert "build_record_binding_rejected" in {
        row["code"] for row in report["errors"]
    }


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
        (_posix_path(b"home", b"private user", b"source.rs"), "posix_home_path"),
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
        (
            "posix_home_path",
            b"source=" + _posix_path(b"home", b"researcher", b"private", b"build.rs"),
        ),
        (
            "posix_workspace_path",
            b"source=" + _posix_path(b"workspace", b"private-project", b"src", b"lib.rs"),
        ),
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


def test_same_uid_root_directory_swap_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / "artifacts"
    replacement = tmp_path / "replacement"
    displaced = tmp_path / "displaced"
    root.mkdir()
    replacement.mkdir()
    _populate_clean_inventory(root)
    _populate_clean_inventory(replacement)
    private_name = "private-project-hidden-after-inventory.txt"
    (replacement / private_name).write_bytes(b"researcher@example.invalid")
    original_read = checker._read_and_hold_regular_bounded
    swapped = False

    def swap_then_read(
        descriptor: int,
        artifact: privacy.ArtifactSpec,
        maximum: int,
    ) -> tuple[bytes, checker._HeldArtifactDescriptor]:
        nonlocal swapped
        if not swapped:
            root.rename(displaced)
            replacement.rename(root)
            swapped = True
        return original_read(descriptor, artifact, maximum)

    monkeypatch.setattr(checker, "_read_and_hold_regular_bounded", swap_then_read)

    report = checker.scan_artifact_directory(root)
    encoded = json.dumps(report, sort_keys=True)

    assert report["ok"] is False
    assert report["snapshot_root_identity_verified"] is False
    assert "root_path_replaced_during_snapshot" in {
        row["code"] for row in report["errors"]
    }
    assert private_name not in encoded


def test_same_uid_post_read_artifact_mutation_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _populate_clean_inventory(tmp_path)
    target = checker.FINAL_ARTIFACTS[0]
    target_path = tmp_path / target.relative_path
    private_payload = b"researcher@example.invalid"
    original_read = checker._read_and_hold_regular_bounded
    mutated = False

    def read_then_mutate(
        descriptor: int,
        artifact: privacy.ArtifactSpec,
        maximum: int,
    ) -> tuple[bytes, checker._HeldArtifactDescriptor]:
        nonlocal mutated
        result = original_read(descriptor, artifact, maximum)
        if artifact == target and not mutated:
            target_path.write_bytes(private_payload)
            mutated = True
        return result

    monkeypatch.setattr(checker, "_read_and_hold_regular_bounded", read_then_mutate)

    report = checker.scan_artifact_directory(tmp_path)
    encoded = json.dumps(report, sort_keys=True).encode()

    assert mutated is True
    assert target_path.read_bytes() == private_payload
    assert report["ok"] is False
    assert report["snapshot_root_identity_verified"] is False
    assert "artifact_changed_after_read" in {
        row["code"] for row in report["errors"]
    }
    assert private_payload not in encoded


def test_same_uid_post_read_artifact_name_rebind_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _populate_clean_inventory(tmp_path)
    target = checker.FINAL_ARTIFACTS[0]
    target_path = tmp_path / target.relative_path
    displaced_path = tmp_path.parent / f"{tmp_path.name}-displaced-artifact"
    private_payload = b"researcher@example.invalid"
    original_read = checker._read_and_hold_regular_bounded
    rebound = False

    def read_then_rebind(
        descriptor: int,
        artifact: privacy.ArtifactSpec,
        maximum: int,
    ) -> tuple[bytes, checker._HeldArtifactDescriptor]:
        nonlocal rebound
        result = original_read(descriptor, artifact, maximum)
        if artifact == target and not rebound:
            target_path.rename(displaced_path)
            target_path.write_bytes(private_payload)
            rebound = True
        return result

    monkeypatch.setattr(checker, "_read_and_hold_regular_bounded", read_then_rebind)

    report = checker.scan_artifact_directory(tmp_path)
    encoded = json.dumps(report, sort_keys=True).encode()

    assert rebound is True
    assert target_path.read_bytes() == private_payload
    assert report["ok"] is False
    assert report["snapshot_root_identity_verified"] is False
    assert "artifact_name_rebound" in {row["code"] for row in report["errors"]}
    assert private_payload not in encoded


def test_cli_emits_canonical_report_and_rejects_finding(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    _populate_clean_inventory(tmp_path)
    target = tmp_path / checker.FINAL_ARTIFACTS[0].relative_path
    target.write_bytes(b"researcher@example.invalid")
    build_record = _candidate_build_record_path(tmp_path)
    _write_candidate_build_record(build_record, tmp_path)

    exit_code = checker.main(
        [
            "--artifact-directory",
            str(tmp_path),
            "--build-record",
            str(build_record),
        ]
    )
    stdout = capsys.readouterr().out
    report = json.loads(stdout)

    assert exit_code == 1
    assert report["ok"] is False
    assert stdout == json.dumps(report, sort_keys=True, separators=(",", ":")) + "\n"
