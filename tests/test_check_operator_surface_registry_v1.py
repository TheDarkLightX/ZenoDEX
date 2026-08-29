from __future__ import annotations

import shlex
import subprocess
import time
from copy import deepcopy
from pathlib import Path

import pytest

from tools import operator_surface_registry_v1 as registry_module
from tools.build_operator_surface_registry_v1 import build_operator_surface_registry_v1
from tools.check_operator_surface_registry_v1 import check_operator_surface_registry_v1
from tools.operator_surface_registry_v1 import (
    ARTIFACT_RELATIVE_PATH_V1,
    CHECK_SCHEMA_V1,
    CHECKOUT_DRAFT_V1,
    CHECKOUT_REPLAYABLE_V1,
    OperatorSurfaceRegistryRejectV1,
    canonical_json_bytes_v1,
    classify_evidence_checkout_v1,
    decode_json_object_v1,
)

ROOT = Path(__file__).resolve().parents[1]


def _artifact() -> dict[str, object]:
    return decode_json_object_v1(
        (ROOT / ARTIFACT_RELATIVE_PATH_V1).read_bytes(),
        "checked-in operator registry",
    )


def _write(tmp_path: Path, value: object) -> Path:
    path = tmp_path / "operator-surface-registry.json"
    path.write_bytes(canonical_json_bytes_v1(value))
    return path


def _assert_no_authority(report: dict[str, object]) -> None:
    assert report["mounted_routes"] == []
    assert report["runtime_receipts"] == []
    assert report["liveness_execution_verified"] is False
    assert report["mount_authority"] == "NONE"
    assert report["production_authority"] == "NONE"
    assert report["release_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"
    assert report["vm_gates_closed"] == []


def _finding_code(report: dict[str, object]) -> object:
    findings = report["findings"]
    assert isinstance(findings, list)
    assert findings and isinstance(findings[0], dict)
    return findings[0]["code"]


def _git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _commit(root: Path, message: str) -> str:
    _git(root, "add", ".")
    _git(
        root,
        "-c",
        "user.name=O004 Test",
        "-c",
        "user.email=o004@example.invalid",
        "commit",
        "-m",
        message,
    )
    return _git(root, "rev-parse", "HEAD")


def _create_gitlink(root: Path, name: str) -> Path:
    nested = root / name
    nested.mkdir()
    _git(nested, "init", "-q")
    (nested / "nested.txt").write_text("nested\n", encoding="utf-8")
    _commit(nested, "nested subject")
    return nested


def test_git_boundary_ignores_replacement_refs(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    source = repo / "source.txt"
    source.write_text("trusted\n", encoding="utf-8")
    subject = _commit(repo, "trusted subject")
    source.write_text("replacement\n", encoding="utf-8")
    replacement = _commit(repo, "replacement subject")
    _git(repo, "replace", subject, replacement)

    # Act
    observed = registry_module._git_blob_v1(repo, subject, "source.txt")

    # Assert
    assert observed.raw == b"trusted\n"


def test_git_boundary_rejects_legacy_graft_ancestry(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    (repo / ".git" / "info" / "grafts").write_text(f"{subject}\n", encoding="ascii")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "GIT_GRAFTS_PRESENT"


def test_git_boundary_pins_supplied_root_against_core_worktree_redirect(
    tmp_path: Path,
) -> None:
    # Arrange a clean decoy that would hide the unexpected file in the supplied root.
    repo = tmp_path / "repo"
    decoy = tmp_path / "decoy"
    repo.mkdir()
    decoy.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    for root in (repo, decoy):
        (root / "implementation.txt").write_text("p\n", encoding="utf-8")
        (root / "evidence.txt").write_text("e\n", encoding="utf-8")
    (repo / "unexpected.txt").write_text("must be observed\n", encoding="utf-8")
    _git(repo, "config", "core.worktree", str(decoy))

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_DRAFT_SCOPE"


@pytest.mark.parametrize("index_flag", ("--skip-worktree", "--assume-unchanged"))
def test_git_boundary_rejects_index_flags_that_hide_tracked_changes(
    tmp_path: Path,
    index_flag: str,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    (repo / "outside.txt").write_text("trusted\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    _git(repo, "update-index", index_flag, "outside.txt")
    (repo / "outside.txt").write_text("hidden mutation\n", encoding="utf-8")
    (repo / "evidence.txt").write_text("e\n", encoding="utf-8")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_INDEX_SUPPRESSION"


def test_git_boundary_overrides_core_filemode_to_observe_mode_changes(
    tmp_path: Path,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    (repo / "outside.txt").write_text("trusted\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    (repo / "outside.txt").chmod(0o755)
    (repo / "evidence.txt").write_text("e\n", encoding="utf-8")
    _git(repo, "config", "core.fileMode", "false")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_DRAFT_SCOPE"


def test_git_boundary_disables_repository_fsmonitor(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "tracked.txt").write_text("value\n", encoding="utf-8")
    _commit(repo, "subject")
    marker = tmp_path / "fsmonitor-ran"
    monitor = tmp_path / "fsmonitor.sh"
    monitor.write_text(
        f"#!/bin/sh\nprintf invoked > '{marker}'\nprintf '\\n'\n",
        encoding="utf-8",
    )
    monitor.chmod(0o700)
    _git(repo, "config", "core.fsmonitor", str(monitor))

    # Act
    registry_module._git_v1(
        repo,
        ("status", "--porcelain=v1"),
        max_stdout_bytes=1024,
    )

    # Assert
    assert not marker.exists()


def test_git_boundary_disables_external_diff_and_textconv(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    (repo / "evidence.txt").write_text("e\n", encoding="utf-8")
    _commit(repo, "evidence")
    marker = tmp_path / "diff-helper-ran"
    helper = tmp_path / "diff-helper.sh"
    helper.write_text(
        f"#!/bin/sh\nprintf invoked > '{marker}'\nexit 0\n",
        encoding="utf-8",
    )
    helper.chmod(0o700)
    _git(repo, "config", "diff.external", str(helper))
    info_attributes = repo / ".git" / "info" / "attributes"
    info_attributes.write_text("* diff=hostile\n", encoding="utf-8")
    _git(repo, "config", "diff.hostile.textconv", str(helper))

    # Act
    result = classify_evidence_checkout_v1(
        repo,
        implementation_subject=subject,
        expected_changed_paths=("evidence.txt",),
    )

    # Assert
    assert result["status"] == CHECKOUT_REPLAYABLE_V1
    assert not marker.exists()


def test_git_timeout_kills_descendant_process_group(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    marker = tmp_path / "escaped-descendant"
    hostile_git = tmp_path / "hostile-git.sh"
    hostile_git.write_text(
        "#!/bin/sh\n"
        f"(sleep 0.8; printf escaped > {shlex.quote(str(marker))}) &\n"
        "sleep 60\n",
        encoding="utf-8",
    )
    hostile_git.chmod(0o700)
    monkeypatch.setattr(registry_module, "_git_binary_v1", lambda: str(hostile_git))
    monkeypatch.setattr(registry_module, "GIT_TIMEOUT_SECONDS_V1", 0.2)

    # Act
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        registry_module._git_v1(
            tmp_path,
            ("rev-parse", "HEAD"),
            max_stdout_bytes=128,
        )

    # Assert
    assert captured.value.code == "GIT_EXECUTION"
    time.sleep(1.0)
    assert not marker.exists()


def test_aaa_given_exact_registry_when_checked_then_reports_closed_non_authority() -> None:
    # Arrange
    artifact_path = ROOT / ARTIFACT_RELATIVE_PATH_V1

    # Act
    report = check_operator_surface_registry_v1(ROOT, artifact_path)

    # Assert
    assert report["schema"] == CHECK_SCHEMA_V1
    assert report["ok"] is True
    assert report["findings"] == []
    assert report["quarantined_streams"] == [8, 9, 11]
    assert report["evidence_replayable"] is False
    checkout = report["evidence_checkout"]
    assert isinstance(checkout, dict)
    assert checkout["status"] == CHECKOUT_DRAFT_V1
    assert report["dynamic_runtime_liveness"] == "NOT_EVALUATED"
    assert report["complete_writer_reachability"] == "NOT_EVALUATED"
    assert report["ui_operability"] == "NOT_EVALUATED"
    _assert_no_authority(report)


def test_aaa_given_pinned_subject_when_rebuilt_then_artifact_bytes_match() -> None:
    # Arrange
    checked_in = (ROOT / ARTIFACT_RELATIVE_PATH_V1).read_bytes()

    # Act
    rebuilt = build_operator_surface_registry_v1(ROOT)

    # Assert
    assert rebuilt == checked_in


def test_registry_has_independent_expected_classifications_and_retained_keys() -> None:
    # Arrange
    expected = {
        "autotrader_api": "QUARANTINED",
        "confidential_attestation_api": "SOURCE_BOUND_UNEXECUTED",
        "keys_ui": "RETAINED_PRESENTATION",
        "oracle_api": "SOURCE_BOUND_UNEXECUTED",
        "perps_wallet_stream_8": "QUARANTINED",
        "spot_ledger_api": "SOURCE_BOUND_UNEXECUTED",
        "zusd_monetary_wallet_stream_11": "QUARANTINED",
        "zusd_tau_wallet_stream_9": "QUARANTINED",
    }

    # Act
    artifact = _artifact()
    routes = artifact["route_registry"]
    surfaces = artifact["surface_registry"]

    # Assert
    assert isinstance(routes, list)
    observed = {
        row["route_id"]: row["classification"]
        for row in routes
        if isinstance(row, dict) and row.get("route_id") in expected
    }
    assert observed == expected
    assert isinstance(surfaces, list)
    navigation = next(
        row
        for row in surfaces
        if isinstance(row, dict) and row.get("surface_id") == "ui-application-navigation"
    )
    projection = navigation["projection"]
    assert isinstance(projection, dict)
    assert projection["keys_component_id"] == "governance"
    assert projection["keys_label"] == "Keys"


def test_replay_given_clean_exact_descendant_when_classified_then_replayable(
    tmp_path: Path,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    (repo / "evidence.txt").write_text("e\n", encoding="utf-8")
    head = _commit(repo, "evidence")

    # Act
    result = classify_evidence_checkout_v1(
        repo,
        implementation_subject=subject,
        expected_changed_paths=("evidence.txt",),
    )

    # Assert
    assert result == {
        "changed_paths": ["evidence.txt"],
        "evidence_head": head,
        "replayable": True,
        "status": CHECKOUT_REPLAYABLE_V1,
    }


def test_replay_given_descendant_with_out_of_scope_path_when_classified_then_rejects(
    tmp_path: Path,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    (repo / "evidence.txt").write_text("e\n", encoding="utf-8")
    (repo / "outside.txt").write_text("unexpected\n", encoding="utf-8")
    _commit(repo, "overbroad evidence")

    # Act
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )

    # Assert
    assert captured.value.code == "EVIDENCE_CHANGED_PATH_SCOPE"


def test_replay_given_out_of_scope_gitlink_when_classified_then_rejects(
    tmp_path: Path,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    _create_gitlink(repo, "out-of-scope-gitlink")
    _commit(repo, "out of scope gitlink")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_CHANGED_PATH_SCOPE"


def test_replay_given_dirty_gitlink_when_draft_classified_then_rejects(
    tmp_path: Path,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    nested = _create_gitlink(repo, "tracked-gitlink")
    subject = _commit(repo, "implementation with gitlink")
    (nested / "nested.txt").write_text("dirty\n", encoding="utf-8")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_DRAFT_SCOPE"


@pytest.mark.parametrize(
    ("kind", "expected_code"),
    (("symlink", "GIT_BLOB_MODE"), ("gitlink", "GIT_BLOB_MODE")),
)
def test_replay_given_nonregular_committed_evidence_path_then_rejects(
    tmp_path: Path,
    kind: str,
    expected_code: str,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    if kind == "symlink":
        (repo / "evidence.txt").symlink_to("implementation.txt")
    else:
        _create_gitlink(repo, "evidence.txt")
    _commit(repo, f"{kind} evidence")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == expected_code


def test_draft_given_symlinked_evidence_path_then_lstat_rejects(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    (repo / "evidence.txt").symlink_to("implementation.txt")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_DRAFT_PATH_TYPE"


def test_draft_given_nonregular_evidence_path_then_lstat_rejects(tmp_path: Path) -> None:
    # Arrange
    evidence = tmp_path / "evidence.txt"
    evidence.mkdir()

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        registry_module._require_draft_regular_evidence_paths_v1(
            tmp_path,
            ("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_DRAFT_PATH_TYPE"


def test_replay_given_missing_expected_evidence_path_then_rejects(tmp_path: Path) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "implementation.txt").write_text("p\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    (repo / "evidence.txt").write_text("e\n", encoding="utf-8")
    _commit(repo, "evidence")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt", "missing.txt"),
        )
    assert captured.value.code == "GIT_TREE_ROW"


def test_replay_given_duplicate_expected_evidence_path_then_rejects(tmp_path: Path) -> None:
    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            tmp_path,
            expected_changed_paths=("evidence.txt", "evidence.txt"),
        )
    assert captured.value.code == "EVIDENCE_PATH_DUPLICATE"


@pytest.mark.parametrize("change", ("rename", "copy"))
def test_replay_given_rename_or_copy_identity_when_classified_then_rejects(
    tmp_path: Path,
    change: str,
) -> None:
    # Arrange
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    source = repo / "source.txt"
    source.write_text("same bytes\n", encoding="utf-8")
    subject = _commit(repo, "implementation")
    evidence = repo / "evidence.txt"
    if change == "rename":
        source.rename(evidence)
    else:
        evidence.write_text(source.read_text(encoding="utf-8"), encoding="utf-8")
    _commit(repo, f"{change} evidence")

    # Act / Assert
    with pytest.raises(OperatorSurfaceRegistryRejectV1) as captured:
        classify_evidence_checkout_v1(
            repo,
            implementation_subject=subject,
            expected_changed_paths=("evidence.txt",),
        )
    assert captured.value.code == "EVIDENCE_RENAME_COPY_AMBIGUITY"


def test_rejection_given_missing_artifact_then_fail_closed_with_no_authority(
    tmp_path: Path,
) -> None:
    # Arrange
    missing = tmp_path / "missing-registry.json"

    # Act
    report = check_operator_surface_registry_v1(ROOT, missing)

    # Assert
    assert report["ok"] is False
    assert report["surface_registry_complete"] is False
    _assert_no_authority(report)


def test_rejection_given_noncanonical_artifact_then_fail_closed(tmp_path: Path) -> None:
    # Arrange
    pretty = tmp_path / "pretty-registry.json"
    pretty.write_text('{\n  "schema": "zenodex/operator-surface-registry/v1"\n}\n')

    # Act
    report = check_operator_surface_registry_v1(ROOT, pretty)

    # Assert
    assert report["ok"] is False
    assert _finding_code(report) == "NONCANONICAL_ARTIFACT"
    _assert_no_authority(report)


def test_rejection_given_authority_mutant_then_exact_no_authority_observed(
    tmp_path: Path,
) -> None:
    # Arrange
    mutant = deepcopy(_artifact())
    authority = mutant["authority"]
    assert isinstance(authority, dict)
    authority["mount"] = "GRANTED"

    # Act
    report = check_operator_surface_registry_v1(ROOT, _write(tmp_path, mutant))

    # Assert
    assert report["ok"] is False
    assert _finding_code(report) == "AUTHORITY_DRIFT"
    _assert_no_authority(report)
