from __future__ import annotations

import io
import os
import shutil
import subprocess
import tarfile
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from typing import Any, Callable, cast

import pytest

from tools import o008a_risc0_dependency_patch_v1 as patch

ROOT = Path(__file__).resolve().parents[1]
SUBJECT = os.environ.get("O008A_TEST_SUBJECT", "")


def _toml(path: Path) -> dict[str, Any]:
    return patch.decode_toml_v1(path.read_bytes(), path)


def _reject_code(callable_: Callable[[], object]) -> str:
    with pytest.raises(patch.DependencyPatchRejectV1) as captured:
        callable_()
    code = captured.value.code
    assert isinstance(code, str)
    return code


def test_bdd_given_closed_patch_when_checked_then_selected_graph_is_validated_only() -> None:
    # Arrange / Act
    report = patch.check_v1(ROOT, SUBJECT)

    # Assert
    assert report["ok"] is True
    assert report["status"] == "PATCH_GRAPH_VALIDATED"
    assert report["resolved_advisories"] == [
        "RUSTSEC-2023-0071",
        "RUSTSEC-2025-0055",
    ]
    assert report["authority"] == patch.NO_AUTHORITY
    implementation_subject = cast(dict[str, object], report["implementation_subject"])
    write_set = cast(dict[str, object], report["write_set"])
    assert implementation_subject["commit"] == SUBJECT
    assert implementation_subject["parent_commit"] == patch.SUBJECT_PARENT_COMMIT
    assert implementation_subject["primary_patch_donor_commit"] == (
        patch.PRIMARY_PATCH_DONOR_COMMIT
    )
    assert set(implementation_subject) == {
        "commit",
        "parent_commit",
        "primary_patch_donor_commit",
        "tree",
    }
    assert write_set["file_count"] == 134
    assert write_set["vendor_file_count"] == 125
    assert report["build_host_qualified"] is False
    assert report["proof_validity"] == "NOT_CLAIMED"
    assert report["release_ready"] is False


def test_closed_vendor_identities_retain_upstream_and_patched_roots() -> None:
    # Arrange / Act
    rows = cast(
        list[dict[str, object]],
        patch.build_report_v1(ROOT, SUBJECT)["vendor_identities"],
    )

    # Assert
    assert [row["package"] for row in rows] == [
        "ark-relations",
        "rzup",
        "tracing-subscriber",
    ]
    assert rows[0]["upstream_tree_sha256"] != rows[0]["patched_tree_sha256"]
    assert rows[1]["upstream_tree_sha256"] != rows[1]["patched_tree_sha256"]
    assert rows[2]["upstream_tree_sha256"] == rows[2]["patched_tree_sha256"]
    assert [row["recorded_crates_io_archive_sha256"] for row in rows] == [
        "ec46ddc93e7af44bcab5230937635b06fb5744464dd6a7e7b083e80ebd274384",
        "96909a7ea8fdf7e18da727d7facbc43eea8a4f77635e7ec75a69794dede16fb6",
        "2f30143827ddab0d256fd843b7a66d164e9f271cfa0dde49142c5ca0ca291f1e",
    ]
    assert all(row["archive_rehashed_in_this_restage"] is False for row in rows)
    assert rows[0]["cached_upstream_restored_paths"] == []
    assert rows[1]["cached_upstream_restored_paths"] == []
    assert rows[2]["cached_upstream_restored_paths"] == list(
        patch.TRACING_CACHED_UPSTREAM_RESTORED_PATHS
    )


def test_subject_tree_contains_all_86_tracing_sources_and_exact_modes() -> None:
    # Arrange / Act
    snapshot = patch.read_subject_snapshot_v1(ROOT, SUBJECT)
    report = patch.validate_closed_write_set_v1(snapshot.changed_paths, snapshot.entries)
    tracing_prefix = "vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/"

    # Assert
    assert report["file_count"] == 134
    assert report["vendor_file_count"] == 125
    assert sum(path.startswith(tracing_prefix) for path in snapshot.entries) == 86
    assert {path.rsplit("/", 1)[-1] for path in snapshot.entries if "/src/filter/env/" in path} == {
        "builder.rs",
        "directive.rs",
        "field.rs",
        "mod.rs",
    }
    assert snapshot.entries[patch.EXECUTABLE_PATH].mode == "100755"
    assert all(
        entry.mode == "100644"
        for path, entry in snapshot.entries.items()
        if path in snapshot.changed_paths and path != patch.EXECUTABLE_PATH
    )


def test_mutation_subject_omits_ignored_tracing_env_source_is_rejected() -> None:
    # Arrange
    snapshot = patch.read_subject_snapshot_v1(ROOT, SUBJECT)
    omitted_path = "vendor/risc0-3.0.6-patches/tracing-subscriber-0.3.22/src/filter/env/builder.rs"
    entries = dict(snapshot.entries)
    entries.pop(omitted_path)
    changed_paths = snapshot.changed_paths - {omitted_path}

    # Act / Assert
    assert (
        _reject_code(lambda: patch.validate_closed_write_set_v1(changed_paths, entries))
        == "WRITE_SET_VENDOR_COUNT"
    )


def test_mutation_subject_adds_receipt_admission_path_is_rejected() -> None:
    # Arrange
    snapshot = patch.read_subject_snapshot_v1(ROOT, SUBJECT)
    extra = "zk/economic_initial_state_risc0/src/receipt_admission.rs"

    # Act / Assert
    assert (
        _reject_code(
            lambda: patch.validate_closed_write_set_v1(
                snapshot.changed_paths | {extra}, snapshot.entries
            )
        )
        == "WRITE_SET_PATHS"
    )


def test_mutation_subject_mode_changes_are_rejected() -> None:
    # Arrange
    snapshot = patch.read_subject_snapshot_v1(ROOT, SUBJECT)
    entries = dict(snapshot.entries)
    entries[patch.EXECUTABLE_PATH] = replace(entries[patch.EXECUTABLE_PATH], mode="100644")

    # Act / Assert
    assert (
        _reject_code(lambda: patch.validate_closed_write_set_v1(snapshot.changed_paths, entries))
        == "WRITE_SET_MODE"
    )
    entries = dict(snapshot.entries)
    entries[".gitattributes"] = replace(entries[".gitattributes"], mode="100755")
    assert (
        _reject_code(lambda: patch.validate_closed_write_set_v1(snapshot.changed_paths, entries))
        == "WRITE_SET_MODE"
    )


@pytest.mark.parametrize("subject", ["HEAD", "b6655bf", "A" * 40, "g" * 40])
def test_subject_cli_identity_requires_literal_lowercase_full_sha(subject: str) -> None:
    assert _reject_code(lambda: patch.validate_subject_literal_v1(subject)) == "SUBJECT_LITERAL"


def test_checker_cli_requires_subject_argument() -> None:
    completed = subprocess.run(
        [
            "python3",
            str(ROOT / "tools/check_o008a_risc0_dependency_patch_v1.py"),
            "--root",
            str(ROOT),
        ],
        check=False,
        capture_output=True,
        timeout=10,
    )
    assert completed.returncode == 2
    assert b"--subject" in completed.stderr and b"required" in completed.stderr


def test_mutation_subject_parent_or_parent_count_is_rejected() -> None:
    wrong_parent = (
        b"tree 0123456789012345678901234567890123456789\n"
        b"parent 0123456789012345678901234567890123456789\n\nmessage\n"
    )
    merge = (
        b"tree 0123456789012345678901234567890123456789\n"
        + f"parent {patch.SUBJECT_PARENT_COMMIT}\n".encode()
        + b"parent 0123456789012345678901234567890123456789\n\nmessage\n"
    )
    assert _reject_code(lambda: patch._parse_commit_header_v1(wrong_parent, "0" * 40)) == (
        "SUBJECT_PARENT"
    )
    assert _reject_code(lambda: patch._parse_commit_header_v1(merge, "0" * 40)) == (
        "SUBJECT_PARENT"
    )


@pytest.mark.parametrize(
    "path",
    ["/absolute", "../escape", "a/../escape", "a/./b", "a//b", "a\\b", ""],
)
def test_mutation_noncanonical_or_traversing_subject_path_is_rejected(path: str) -> None:
    assert _reject_code(lambda: patch.validate_canonical_git_path_v1(path)) == "SUBJECT_PATH"


def test_checker_rejects_foreign_scratch_and_nonroot_repository(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    monkeypatch.setenv("TMPDIR", "/dev/shm")
    snapshot = patch.read_subject_snapshot_v1(ROOT, SUBJECT)
    source = patch.read_subject_blob_v1(ROOT, snapshot, "tools/o008a_risc0_dependency_patch_v1.py")
    assert b"/dev/shm" not in source
    for token in (
        b'"GIT_CONFIG_NOSYSTEM": "1"',
        b'"GIT_NO_REPLACE_OBJECTS": "1"',
        b'"GIT_OPTIONAL_LOCKS": "0"',
        b'"HOME": "/nonexistent"',
        b'"core.fsmonitor=false"',
        b'"core.hooksPath=/dev/null"',
        b'"core.attributesFile=/dev/null"',
    ):
        assert token in source
    assert source.count(b'"--full-tree"') == 1
    assert source.count(b'"--no-relative"') == 1
    assert patch.build_report_v1(ROOT, SUBJECT)["ok"] is True
    assert patch.validate_scratch_parent_v1(patch.SCRATCH_PARENT) == Path("/tmp")
    assert (
        _reject_code(lambda: patch.validate_scratch_parent_v1(Path("/dev/shm"))) == "SCRATCH_DEVICE"
    )
    scratch_link = tmp_path / "scratch-link"
    scratch_link.symlink_to("/tmp", target_is_directory=True)
    assert _reject_code(lambda: patch.validate_scratch_parent_v1(scratch_link)) == "SCRATCH_SYMLINK"
    assert _reject_code(lambda: patch.build_report_v1(ROOT / "tools", SUBJECT)) == "REPOSITORY_ROOT"


def test_clean_git_archive_replays_committed_subject(tmp_path: Path) -> None:
    # Arrange
    snapshot = patch.read_subject_snapshot_v1(ROOT, SUBJECT)
    completed = subprocess.run(
        [
            "/usr/bin/git",
            "-C",
            str(ROOT),
            "archive",
            "--format=tar",
            SUBJECT,
            *sorted(snapshot.changed_paths),
        ],
        check=True,
        capture_output=True,
        timeout=10,
    )
    archive_root = tmp_path / "archive"
    archive_root.mkdir()

    # Act
    with tarfile.open(fileobj=io.BytesIO(completed.stdout), mode="r:") as archive:
        for member in archive.getmembers():
            if member.isdir():
                continue
            assert member.isfile()
            archive_path = Path(member.name)
            assert not archive_path.is_absolute() and ".." not in archive_path.parts
            source = archive.extractfile(member)
            assert source is not None
            target = archive_root / archive_path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source.read())
            target.chmod(member.mode)
    report = patch._build_content_report_v1(archive_root)

    # Assert
    assert report["ok"] is True
    for changed_path in snapshot.changed_paths:
        assert (archive_root / changed_path).read_bytes() == patch.read_subject_blob_v1(
            ROOT, snapshot, changed_path
        )


def test_mutation_workspace_patch_substitution_is_rejected() -> None:
    # Arrange
    workspace = _toml(ROOT / patch.WORKSPACE_PATH)
    mutated = deepcopy(workspace)
    mutated["patch"]["crates-io"]["rzup"]["path"] = "../../foreign/rzup"

    # Act / Assert
    assert _reject_code(lambda: patch.validate_workspace_patch_v1(mutated)) == "WORKSPACE_PATCH"


def test_mutation_rsa_reintroduced_into_selected_lock_is_rejected() -> None:
    # Arrange
    lock = _toml(ROOT / patch.LOCK_PATH)
    mutated = deepcopy(lock)
    mutated["package"].append({"name": "rsa", "version": "0.9.10"})

    # Act / Assert
    assert _reject_code(lambda: patch.validate_lock_v1(mutated)) == "LOCK_FORBIDDEN_PACKAGE"


def test_mutation_tracing_downgrade_in_selected_lock_is_rejected() -> None:
    # Arrange
    lock = _toml(ROOT / patch.LOCK_PATH)
    mutated = deepcopy(lock)
    row = next(package for package in mutated["package"] if package["name"] == "tracing-subscriber")
    row["version"] = "0.2.25"

    # Act / Assert
    assert _reject_code(lambda: patch.validate_lock_v1(mutated)) == "LOCK_VERSION"


def test_mutation_rzup_install_without_signature_is_rejected() -> None:
    # Arrange
    crate = ROOT / patch.VENDOR_ROOT / "rzup-0.5.2"
    cargo = _toml(crate / "Cargo.toml")
    mutated = deepcopy(cargo)
    mutated["features"]["install"].remove("signature")
    source = (crate / "src/distribution/signature.rs").read_text(encoding="utf-8")

    # Act / Assert
    assert (
        _reject_code(lambda: patch.validate_rzup_policy_v1(mutated, source))
        == "RZUP_FEATURE_POLICY"
    )


def test_mutation_signature_disabled_verifier_acceptance_is_rejected() -> None:
    # Arrange
    crate = ROOT / patch.VENDOR_ROOT / "rzup-0.5.2"
    cargo = _toml(crate / "Cargo.toml")
    source = (crate / "src/distribution/signature.rs").read_text(encoding="utf-8")
    mutated = source.replace(
        'Err(RzupError::Other("signature feature not enabled".into()))',
        "Ok(())",
    )

    # Act / Assert
    assert _reject_code(lambda: patch.validate_rzup_policy_v1(cargo, mutated)) == "RZUP_FAIL_CLOSED"


def test_mutation_no_feature_lane_imports_full_upstream_test_suite_is_rejected() -> None:
    # Arrange
    crate = ROOT / patch.VENDOR_ROOT / "rzup-0.5.2"
    lib_source = (crate / "src/lib.rs").read_text(encoding="utf-8")
    components_source = (crate / "src/components.rs").read_text(encoding="utf-8")
    mutated = lib_source.replace(
        '#[cfg(all(test, feature = "install", feature = "publish"))]',
        "#[cfg(test)]",
        1,
    )

    # Act / Assert
    assert (
        _reject_code(lambda: patch.validate_rzup_test_profile_v1(mutated, components_source))
        == "RZUP_TEST_PROFILE"
    )


def test_mutation_ark_tracing_compatibility_floor_is_rejected() -> None:
    # Arrange
    crate = ROOT / patch.VENDOR_ROOT / "ark-relations-0.5.1"
    cargo = _toml(crate / "Cargo.toml")
    mutated = deepcopy(cargo)
    mutated["dependencies"]["tracing-subscriber"]["version"] = "0.2"
    source = (crate / "src/r1cs/trace.rs").read_text(encoding="utf-8")

    # Act / Assert
    assert (
        _reject_code(lambda: patch.validate_ark_policy_v1(mutated, source)) == "ARK_TRACING_VERSION"
    )


def test_mutation_ark_old_layer_api_is_rejected() -> None:
    # Arrange
    crate = ROOT / patch.VENDOR_ROOT / "ark-relations-0.5.1"
    cargo = _toml(crate / "Cargo.toml")
    source = (crate / "src/r1cs/trace.rs").read_text(encoding="utf-8")
    mutated = source.replace("fn on_new_span(", "fn new_span(")

    # Act / Assert
    assert _reject_code(lambda: patch.validate_ark_policy_v1(cargo, mutated)) == "ARK_TRACING_API"


def test_mutation_closed_vendor_byte_is_rejected(tmp_path: Path) -> None:
    # Arrange
    copied_root = tmp_path / "subject"
    copied_vendor = copied_root / patch.VENDOR_ROOT
    shutil.copytree(ROOT / patch.VENDOR_ROOT, copied_vendor)
    target = copied_vendor / "tracing-subscriber-0.3.22" / "README.md"
    target.write_bytes(target.read_bytes() + b"\nmutation\n")
    identity = next(row for row in patch.VENDOR_IDENTITIES if row.package == "tracing-subscriber")

    # Act / Assert
    assert (
        _reject_code(lambda: patch.validate_vendor_identity_v1(copied_root, identity))
        == "VENDOR_TREE"
    )


def test_mutation_vendor_symlink_is_rejected(tmp_path: Path) -> None:
    # Arrange
    crate = tmp_path / "crate"
    crate.mkdir()
    (crate / "target.txt").write_text("target", encoding="utf-8")
    (crate / "alias.txt").symlink_to("target.txt")

    # Act / Assert
    assert _reject_code(lambda: patch.vendor_tree_entries_v1(crate)) == "VENDOR_SYMLINK"
