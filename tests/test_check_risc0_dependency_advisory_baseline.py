from __future__ import annotations

import hashlib
import json
import shutil
from pathlib import Path

from tools import check_risc0_dependency_advisory_baseline as checker

ROOT = Path(__file__).resolve().parents[1]


def _workspace_copy(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    source = ROOT / "zk/state_proof_risc0"
    destination = root / "zk/state_proof_risc0"
    for relative in checker.EXPECTED_MANIFEST_PATHS:
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / relative, target)
    shutil.copyfile(source / "Cargo.lock", destination / "Cargo.lock")
    return root


def _replace(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    assert old in text
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def _replace_lock_package_resolution(
    lock_path: Path,
    package: str,
    version: str,
    *,
    checksum: str | None = None,
) -> None:
    text = lock_path.read_text(encoding="utf-8")
    marker = f'name = "{package}"\nversion = "'
    start = text.index(marker) + len(marker)
    end = text.index('"', start)
    text = text[:start] + version + text[end:]
    if checksum is not None:
        checksum_start = text.index('checksum = "', start) + len('checksum = "')
        checksum_end = text.index('"', checksum_start)
        text = text[:checksum_start] + checksum + text[checksum_end:]
    lock_path.write_text(text, encoding="utf-8")


def _input_root_digest(inputs: list[dict[str, object]]) -> str:
    canonical = json.dumps(
        inputs,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")
    return "sha256:" + hashlib.sha256(canonical).hexdigest()


def test_repo_recursive_stark_dependency_baseline_passes() -> None:
    report = checker.check_risc0_dependency_advisory_baseline(root=ROOT)

    assert report["ok"], report["errors"]
    assert report["offline"] is True
    assert report["lock_versions"]["risc0-zkvm"] == ["3.0.5"]
    assert report["lock_versions"]["risc0-build"] == ["3.0.5"]
    assert report["lock_versions"]["risc0-zkvm-platform"] == ["2.2.2"]
    assert report["platform_matches_expected"] is True
    assert report["advisory_safety"]["platform_versions_in_safe_range"] is True
    assert report["advisory_safety"]["platform_resolution_in_reviewed_safe_set"] is True
    assert report["inspected_root"] == str(ROOT.resolve())
    assert report["production_ready"] is False
    assert len(report["inspected_inputs"]) == len(checker.EXPECTED_MANIFEST_PATHS) + 1
    assert report["input_root_sha256"] == _input_root_digest(report["inspected_inputs"])
    assert report["invalidated_evidence_versions"] == ["1.2.6"]
    assert "invalid as assurance or release evidence" in report["old_evidence_status"]


def test_baseline_snapshot_records_reviewed_critical_advisory() -> None:
    snapshot = json.loads(checker.DEFAULT_SNAPSHOT.read_text(encoding="utf-8"))

    assert snapshot["source"] == {
        "advisory_id": "GHSA-jqq4-c7wq-36h7",
        "cve_id": "CVE-2025-61588",
        "published": "2025-10-01",
        "severity": "critical",
        "updated": "2025-10-02",
        "url": "https://github.com/advisories/GHSA-jqq4-c7wq-36h7",
    }
    assert snapshot["workspace_policy"]["invalidated_evidence_versions"] == ["1.2.6"]


def test_rejects_snapshot_policy_drift(tmp_path: Path) -> None:
    snapshot = json.loads(checker.DEFAULT_SNAPSHOT.read_text(encoding="utf-8"))
    snapshot["workspace_policy"]["required_risc0_zkvm_version"] = "1.2.6"
    snapshot_path = tmp_path / "baseline.json"
    snapshot_path.write_text(json.dumps(snapshot), encoding="utf-8")

    report = checker.check_risc0_dependency_advisory_baseline(
        root=ROOT,
        snapshot_path=snapshot_path,
    )

    assert report["ok"] is False
    assert "snapshot SHA-256 mismatch" in report["errors"]


def test_rejects_duplicate_snapshot_key(tmp_path: Path) -> None:
    snapshot_path = tmp_path / "baseline.json"
    snapshot_path.write_text(
        '{"schema":"zenodex/risc0_dependency_advisory_baseline/v1","schema":"other"}',
        encoding="utf-8",
    )

    report = checker.check_risc0_dependency_advisory_baseline(
        root=ROOT,
        snapshot_path=snapshot_path,
    )

    assert report["ok"] is False
    assert "duplicate JSON key: schema" in report["errors"]


def test_rejects_symlink_nonregular_and_oversized_snapshots(tmp_path: Path) -> None:
    regular = tmp_path / "regular.json"
    regular.write_text("{}", encoding="utf-8")
    symlink = tmp_path / "symlink.json"
    symlink.symlink_to(regular)
    directory = tmp_path / "directory.json"
    directory.mkdir()
    oversized = tmp_path / "oversized.json"
    oversized.write_bytes(b" " * (checker.MAX_SNAPSHOT_BYTES + 1))

    for snapshot_path in (symlink, directory, oversized):
        report = checker.check_risc0_dependency_advisory_baseline(
            root=ROOT,
            snapshot_path=snapshot_path,
        )
        assert report["ok"] is False
        assert any(
            marker in error
            for error in report["errors"]
            for marker in ("cannot safely open", "not a regular file", "exceeds size limit")
        )


def test_rejects_affected_1_2_6_direct_dependency(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    manifest = root / "zk/state_proof_risc0/cli/Cargo.toml"
    _replace(manifest, 'version = "=3.0.5"', 'version = "=1.2.6"')

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert any("invalidated vulnerable RISC0 version 1.2.6" in error for error in report["errors"])


def test_rejects_missing_host_disable_dev_mode(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    manifest = root / "zk/state_proof_risc0/cli/Cargo.toml"
    _replace(manifest, ', features = ["disable-dev-mode"]', "")

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "host risc0-zkvm dependency must enable only disable-dev-mode" in report["errors"]


def test_rejects_nonexact_guest_version_requirement(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    manifest = root / "zk/state_proof_risc0/methods/aggregate/Cargo.toml"
    _replace(manifest, 'version = "=3.0.5"', 'version = "3.0.5"')

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "direct RISC0 dependency topology does not match the pinned baseline" in report["errors"]


def test_rejects_mixed_risc0_zkvm_lock_versions(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    lock_path = root / "zk/state_proof_risc0/Cargo.lock"
    with lock_path.open("a", encoding="utf-8") as handle:
        handle.write(
            "\n[[package]]\n"
            'name = "risc0-zkvm"\n'
            'version = "1.2.6"\n'
            f'source = "{checker.CRATES_IO_SOURCE}"\n'
            f'checksum = "{"1" * 64}"\n'
        )

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "Cargo.lock must resolve exactly one risc0-zkvm package, found 2" in report["errors"]
    assert any("risc0-zkvm 1.2.6 is affected" in error for error in report["errors"])


def test_rejects_safe_but_nonbaseline_platform_2_1_0(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    lock_path = root / "zk/state_proof_risc0/Cargo.lock"
    _replace_lock_package_resolution(
        lock_path,
        "risc0-zkvm-platform",
        "2.1.0",
        checksum="1e2dcebfc7103d98511f0fcb42f910c390ec5637d4bb3b463441fbcd30feeb1d",
    )

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert (
        "Cargo.lock risc0-zkvm-platform must resolve exactly 2.2.2 "
        "for baseline acceptance"
    ) in report["errors"]
    assert report["platform_matches_expected"] is False
    assert report["advisory_safety"]["platform_versions_in_safe_range"] is True
    assert report["advisory_safety"]["platform_resolution_in_reviewed_safe_set"] is True


def test_rejects_malformed_platform_version(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    lock_path = root / "zk/state_proof_risc0/Cargo.lock"
    _replace_lock_package_resolution(lock_path, "risc0-zkvm-platform", "2.1")

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert any("platform version is malformed or unsupported" in error for error in report["errors"])


def test_rejects_unknown_platform_major(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    lock_path = root / "zk/state_proof_risc0/Cargo.lock"
    _replace_lock_package_resolution(lock_path, "risc0-zkvm-platform", "3.0.0")

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "Cargo.lock risc0-zkvm-platform must be a stable version in [2.1.0,3.0.0)" in report["errors"]


def test_rejects_unpinned_platform_checksum(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    lock_path = root / "zk/state_proof_risc0/Cargo.lock"
    _replace_lock_package_resolution(
        lock_path,
        "risc0-zkvm-platform",
        "2.2.2",
        checksum="1" * 64,
    )

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "Cargo.lock risc0-zkvm-platform resolution is not in the pinned safe set" in report["errors"]


def test_rejects_unpinned_risc0_zkvm_checksum(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    lock_path = root / "zk/state_proof_risc0/Cargo.lock"
    _replace_lock_package_resolution(
        lock_path,
        "risc0-zkvm",
        "3.0.5",
        checksum="1" * 64,
    )

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "Cargo.lock risc0-zkvm resolution does not match the pinned checksum" in report["errors"]


def test_rejects_missing_risc0_build_direct_pin(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    manifest = root / "zk/state_proof_risc0/methods/Cargo.toml"
    _replace(manifest, "risc0-build =", "unreviewed-build =")

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "direct RISC0 dependency topology does not match the pinned baseline" in report["errors"]


def test_rejects_unexpected_cargo_manifest(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    unexpected = root / "zk/state_proof_risc0/new_guest/Cargo.toml"
    unexpected.parent.mkdir()
    unexpected.write_text('[package]\nname = "unreviewed"\nversion = "0.1.0"\n', encoding="utf-8")

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "Cargo manifest path set does not match the pinned baseline" in report["errors"]


def test_manifest_discovery_is_capped(
    tmp_path: Path, monkeypatch
) -> None:
    root = _workspace_copy(tmp_path)
    monkeypatch.setattr(checker, "MAX_DISCOVERED_MANIFESTS", 2)

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "Cargo manifest discovery count cap exceeded" in report["errors"]


def test_manifest_discovery_entry_walk_is_capped(
    tmp_path: Path, monkeypatch
) -> None:
    root = _workspace_copy(tmp_path)
    monkeypatch.setattr(checker, "MAX_DISCOVERY_ENTRIES", 4)

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert "Cargo manifest discovery entry cap exceeded" in report["errors"]


def test_rejects_symlink_manifest_and_does_not_hash_target(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    relative = "cli/Cargo.toml"
    manifest = root / "zk/state_proof_risc0" / relative
    outside = tmp_path / "outside.toml"
    shutil.copyfile(manifest, outside)
    manifest.unlink()
    manifest.symlink_to(outside)

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert f"symlink entry is forbidden during discovery: {relative}" in report["errors"]
    assert all(not item["path"].endswith(relative) for item in report["inspected_inputs"])


def test_rejects_nonregular_and_oversized_manifests(tmp_path: Path) -> None:
    for case in ("directory", "oversized"):
        root = _workspace_copy(tmp_path / case)
        relative = "cli/Cargo.toml"
        manifest = root / "zk/state_proof_risc0" / relative
        if case == "directory":
            manifest.unlink()
            manifest.mkdir()
        else:
            manifest.write_bytes(b"x" * (checker.MAX_MANIFEST_BYTES + 1))

        report = checker.check_risc0_dependency_advisory_baseline(root=root)

        assert report["ok"] is False
        expected = "not a regular file" if case == "directory" else "exceeds size limit"
        assert any(expected in error for error in report["errors"])


def test_rejects_root_and_workspace_ancestor_symlink_escapes(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path / "root-link")
    root_link = tmp_path / "repo-link"
    root_link.symlink_to(root, target_is_directory=True)

    root_report = checker.check_risc0_dependency_advisory_baseline(root=root_link)

    assert root_report["ok"] is False
    assert "inspection root must not traverse symbolic links" in root_report["errors"]
    assert root_report["inspected_root"] is None

    escaped_root = _workspace_copy(tmp_path / "workspace-link")
    original_zk = escaped_root / "zk"
    outside_zk = tmp_path / "outside-zk"
    shutil.move(original_zk, outside_zk)
    original_zk.symlink_to(outside_zk, target_is_directory=True)

    workspace_report = checker.check_risc0_dependency_advisory_baseline(
        root=escaped_root
    )

    assert workspace_report["ok"] is False
    assert any("workspace is missing, unsafe" in error for error in workspace_report["errors"])


def test_report_hashes_every_inspected_manifest_and_lock(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    first = checker.check_risc0_dependency_advisory_baseline(root=root)
    manifest = root / "zk/state_proof_risc0/shared/Cargo.toml"
    with manifest.open("a", encoding="utf-8") as handle:
        handle.write("\n# hash binding mutation\n")

    second = checker.check_risc0_dependency_advisory_baseline(root=root)

    expected_paths = {
        "zk/state_proof_risc0/Cargo.lock",
        *(f"zk/state_proof_risc0/{path}" for path in checker.EXPECTED_MANIFEST_PATHS),
    }
    assert {item["path"] for item in first["inspected_inputs"]} == expected_paths
    assert all(
        isinstance(item["sha256"], str)
        and item["sha256"].startswith("sha256:")
        and len(item["sha256"]) == 71
        for item in first["inspected_inputs"]
    )
    assert first["inspected_root"] == str(root.resolve())
    assert first["input_root_sha256"] == _input_root_digest(first["inspected_inputs"])
    assert second["input_root_sha256"] == _input_root_digest(second["inspected_inputs"])
    assert first["input_root_sha256"] != second["input_root_sha256"]
    assert second["production_ready"] is False


def test_rejects_alternate_risc0_dependency_source(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    manifest = root / "zk/state_proof_risc0/cli/Cargo.toml"
    _replace(
        manifest,
        'version = "=3.0.5", features',
        'version = "=3.0.5", git = "https://example.invalid/risc0", features',
    )

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert any("uses forbidden dependency source keys: git" in error for error in report["errors"])


def test_rejects_renamed_risc0_dependency(tmp_path: Path) -> None:
    root = _workspace_copy(tmp_path)
    manifest = root / "zk/state_proof_risc0/cli/Cargo.toml"
    _replace(
        manifest,
        'risc0-zkvm = { version = "=3.0.5",',
        'renamed-zkvm = { package = "risc0-zkvm", version = "=3.0.5",',
    )

    report = checker.check_risc0_dependency_advisory_baseline(root=root)

    assert report["ok"] is False
    assert any("uses forbidden dependency source keys: package" in error for error in report["errors"])


def test_cli_json_report_is_deterministic(capsys) -> None:
    code = checker.main(["--root", str(ROOT), "--json"])
    first = capsys.readouterr().out
    code_again = checker.main(["--root", str(ROOT), "--json"])
    second = capsys.readouterr().out

    assert code == 0
    assert code_again == 0
    assert first == second
    assert json.loads(first)["ok"] is True
