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
    assert report["status_counts"] == {"bounded_replay": 114, "inductive_esso": 11}


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


def _two_inductive(manifest: dict) -> tuple[dict, dict]:
    rows = [row for row in manifest["rows"] if row["status"] == "inductive_esso"]
    return rows[0], rows[1]


def test_swapped_model_receipt_pair_is_rejected(workspace: Path) -> None:
    """Opus review P1-1: a row pointing at another axis's artifacts must fail."""

    manifest = _load(workspace)
    first, second = _two_inductive(manifest)
    for key in ("model_path", "model_sha256", "receipt_path", "receipt_sha256"):
        second[key] = first[key]
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("does not name the registered model" in e for e in report["errors"])
    assert any("duplicate model_path" in e or "duplicate receipt_path" in e for e in report["errors"])


def test_receipt_certifying_a_different_model_is_rejected(workspace: Path) -> None:
    """Opus review P1-1: the receipt's own model binding must match the row."""

    manifest = _load(workspace)
    first, second = _two_inductive(manifest)

    second["receipt_path"] = first["receipt_path"]
    second["receipt_sha256"] = first["receipt_sha256"]
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("certifies a different model path" in e for e in report["errors"])


def test_hand_written_verified_receipt_is_rejected(workspace: Path) -> None:
    """Opus review P1-2: a verdict without two-solver query evidence must fail."""

    import hashlib

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    forged = (
        '{"ok": true, "model": {"path": "%s"}, "solvers": ["z3", "cvc5"], "queries": {}, '
        '"report": {"verdict": "VERIFIED", "solvers_agreed": true, "failed_queries": 0, '
        '"inconclusive_queries": 0, "model_id": "%s"}}'
    ) % (row["model_path"], row["model_path"].rsplit("/", 1)[-1].removesuffix(".yaml"))
    (workspace / row["receipt_path"]).write_text(forged)
    row["receipt_sha256"] = hashlib.sha256(forged.encode()).hexdigest()
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("carries no queries" in e for e in report["errors"])


def test_single_solver_receipt_is_rejected(workspace: Path) -> None:
    """Opus review P1-2: stripping cvc5 while keeping solvers_agreed must fail."""

    import hashlib
    import json as jsonlib

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    target = workspace / row["receipt_path"]
    receipt = jsonlib.loads(target.read_text())
    receipt["solvers"] = ["z3"]
    for query in receipt["queries"].values():
        query.pop("cvc5", None)
    rendered = jsonlib.dumps(receipt)
    target.write_text(rendered)
    row["receipt_sha256"] = hashlib.sha256(rendered.encode()).hexdigest()
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("not exactly z3+cvc5" in e or "lacks an unsat cvc5 result" in e for e in report["errors"])


def test_downgraded_zusd_row_is_bounded_replay_with_the_review_note() -> None:
    """Opus review P2: the zusd axis must not claim an inductive certificate."""

    import json as jsonlib

    manifest = jsonlib.loads(MANIFEST.read_text())
    row = next(r for r in manifest["rows"] if r["axis_id"] == "zusd_oracle_recovery_split_brain")
    assert row["status"] == "bounded_replay"
    assert "downgraded from inductive_esso" in row["evidence_note"]
