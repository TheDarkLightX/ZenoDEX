"""Mutation killers for the disaster-axis status manifest checker (fail-closed)."""

from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.check_disaster_axis_status_manifest import check_manifest  # noqa: E402

MANIFEST = ROOT / "tools/disaster_axis_status_manifest.json"


@pytest.fixture()
def workspace(tmp_path: Path) -> Path:
    (tmp_path / "tools").mkdir()
    shutil.copy(MANIFEST, tmp_path / "tools/disaster_axis_status_manifest.json")
    source = ROOT / "experiments/disaster_inductive_promotion"
    target = tmp_path / "experiments/disaster_inductive_promotion"
    shutil.copytree(source / "models", target / "models")
    shutil.copytree(source / "receipts", target / "receipts")
    return tmp_path


def _load(root: Path) -> dict:
    return json.loads((root / "tools/disaster_axis_status_manifest.json").read_text())


def _store(root: Path, manifest: dict) -> None:
    (root / "tools/disaster_axis_status_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=False) + "\n"
    )


def _check(root: Path) -> dict:
    return check_manifest(root, root / "tools/disaster_axis_status_manifest.json")


def test_committed_manifest_is_accepted() -> None:
    report = check_manifest(ROOT, MANIFEST)
    assert report["ok"] is True, report["errors"][:4]
    assert report["axis_count"] == 125
    assert report["status_counts"] == {"bounded_replay": 113, "inductive_esso": 12}


def test_dropping_a_row_names_the_unmapped_axis(workspace: Path) -> None:
    manifest = _load(workspace)
    dropped = manifest["rows"].pop(0)
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any(dropped["axis_id"] in e and "no status row" in e for e in report["errors"])


def test_dead_axis_row_is_rejected(workspace: Path) -> None:
    manifest = _load(workspace)
    manifest["rows"][0]["axis_id"] = "axis_that_never_existed"
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("dead axis" in e for e in report["errors"])


def test_unknown_status_is_rejected(workspace: Path) -> None:
    manifest = _load(workspace)
    manifest["rows"][0]["status"] = "vibes_certified"
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("unknown status" in e for e in report["errors"])


def test_axis_definition_drift_is_rejected(workspace: Path) -> None:
    manifest = _load(workspace)
    manifest["rows"][0]["axis_definition_sha256"] = "0" * 64
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("axis definition drift" in e for e in report["errors"])


def _first_inductive(manifest: dict) -> dict:
    return next(row for row in manifest["rows"] if row["status"] == "inductive_esso")


def test_missing_model_artifact_is_rejected(workspace: Path) -> None:
    manifest = _load(workspace)
    row = _first_inductive(manifest)
    (workspace / row["model_path"]).unlink()
    report = _check(workspace)
    assert report["ok"] is False
    assert any("model artifact missing" in e for e in report["errors"])


def test_model_sha_drift_is_rejected(workspace: Path) -> None:
    manifest = _load(workspace)
    row = _first_inductive(manifest)
    target = workspace / row["model_path"]
    target.write_text(target.read_text() + "\n# drift\n")
    report = _check(workspace)
    assert report["ok"] is False
    assert any("model sha256 drift" in e for e in report["errors"])


def test_tampered_receipt_verdict_is_rejected(workspace: Path) -> None:
    manifest = _load(workspace)
    row = _first_inductive(manifest)
    target = workspace / row["receipt_path"]
    receipt = json.loads(target.read_text())
    receipt["report"]["verdict"] = "REFUTED"
    rendered = json.dumps(receipt)
    target.write_text(rendered)
    import hashlib

    row["receipt_sha256"] = hashlib.sha256(rendered.encode()).hexdigest()
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("verdict is not VERIFIED" in e for e in report["errors"])


def test_duplicate_row_is_rejected(workspace: Path) -> None:
    manifest = _load(workspace)
    manifest["rows"].append(dict(manifest["rows"][0]))
    manifest["axis_count"] = len({r["axis_id"] for r in manifest["rows"]})
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("duplicate row" in e for e in report["errors"])
