from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

from tools import build_zrpf_semantic_epoch_v1_local_evidence as builder
from tools import zrpf_semantic_epoch_v1_evidence_support as support


def _copy_bundle(tmp_path: Path) -> Path:
    source = support.REPO_ROOT / builder.ARTIFACT_ROOT
    destination = tmp_path / builder.ARTIFACT_ROOT
    destination.parent.mkdir(parents=True)
    shutil.copytree(source, destination)
    return destination


def test_real_bundle_build_is_deterministic_and_checker_accepted() -> None:
    first_document, first_raw, first_report = builder.build_validated_manifest()
    second_document, second_raw, second_report = builder.build_validated_manifest()

    assert first_document == second_document
    assert first_raw == second_raw
    assert support.sha256_bytes(first_raw) == support.sha256_bytes(second_raw)
    assert first_report["ok"] is True
    assert second_report["ok"] is True
    assert len(first_document["artifacts"]) == 27
    assert first_report["facts"]["python_verifies_risc0_seals"] is False


def test_governed_artifact_ids_and_paths_are_unique_and_sorted() -> None:
    ids = [spec.artifact_id for spec in builder.ARTIFACT_SPECS]
    paths = [spec.path for spec in builder.ARTIFACT_SPECS]

    assert ids == sorted(ids)
    assert len(ids) == len(set(ids)) == 27
    assert len(paths) == len(set(paths)) == 27


def test_builder_rejects_extra_bundle_inventory_entry(tmp_path: Path) -> None:
    artifact_root = _copy_bundle(tmp_path)
    (artifact_root / "unexpected.json").write_bytes(b"{}")

    with pytest.raises(builder.EvidenceBuildError, match="governed artifact inventory mismatch"):
        builder.build_validated_manifest(tmp_path)


def test_builder_rejects_symlinked_bundle_artifact(tmp_path: Path) -> None:
    artifact_root = _copy_bundle(tmp_path)
    target = artifact_root / "reports/adapter-ordinal-0.prove.json"
    replacement = tmp_path / "replacement.json"
    replacement.write_bytes(target.read_bytes())
    target.unlink()
    target.symlink_to(replacement)

    with pytest.raises(builder.EvidenceBuildError, match="inventory file rejected"):
        builder.build_validated_manifest(tmp_path)


def test_builder_rejects_cross_report_semantic_root_mutation(tmp_path: Path) -> None:
    artifact_root = _copy_bundle(tmp_path)
    report_path = artifact_root / "reports/semantic-positive.prove.json"
    report = support.strict_json_loads(report_path.read_bytes())
    report["semantic_epoch_root"] = "00" * 32
    report_path.write_bytes(support.canonical_artifact_bytes(report, "json_sorted_compact_newline"))

    with pytest.raises(builder.EvidenceBuildError, match="constructed manifest rejected"):
        builder.build_validated_manifest(tmp_path)


def test_builder_pins_verifier_source_closure_artifact_bytes(tmp_path: Path) -> None:
    artifact_root = _copy_bundle(tmp_path)
    closure_path = artifact_root / "provenance/verifier-source-closure.json"
    closure = support.strict_json_loads(closure_path.read_bytes())
    closure["git_commit"] = "00" * 20
    closure_path.write_bytes(support.canonical_artifact_bytes(closure, "json_sorted_compact"))

    with pytest.raises(
        builder.EvidenceBuildError,
        match="governed artifact SHA-256 mismatch: verifier-source-closure-record",
    ):
        builder.build_validated_manifest(tmp_path)


def test_manifest_write_requires_create_new_or_explicit_replace(tmp_path: Path) -> None:
    _, raw, _ = builder.build_validated_manifest()
    output = tmp_path / "manifest.json"

    builder.write_manifest(output, raw, replace=False)
    assert support.load_manifest(output).raw == raw

    with pytest.raises(builder.EvidenceBuildError, match="create_new failed"):
        builder.write_manifest(output, raw, replace=False)

    output.write_bytes(b"stale")
    builder.write_manifest(output, raw, replace=True)
    assert support.load_manifest(output).raw == raw


def test_replacement_refuses_symlink_target(tmp_path: Path) -> None:
    _, raw, _ = builder.build_validated_manifest()
    target = tmp_path / "target.json"
    target.write_bytes(b"target")
    output = tmp_path / "manifest.json"
    output.symlink_to(target)

    with pytest.raises(
        builder.EvidenceBuildError,
        match="replacement target is not a regular file",
    ):
        builder.write_manifest(output, raw, replace=True)

    assert target.read_bytes() == b"target"


def test_cli_reports_absolute_output_outside_repo_root(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output = tmp_path / "manifest.json"

    assert builder.main(["--output", str(output)]) == 0

    report = json.loads(capsys.readouterr().out)
    assert report["ok"] is True
    assert report["manifest_path"] == output.as_posix()
    assert output.read_bytes() == support.DEFAULT_MANIFEST.read_bytes()
