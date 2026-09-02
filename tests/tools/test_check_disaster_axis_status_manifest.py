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
    assert report["status_counts"] == {"bounded_replay": 115, "inductive_esso": 10}


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
    assert any("not exactly z3+cvc5" in e for e in report["errors"])
    assert any("lacks an unsat cvc5 result" in e for e in report["errors"])


def test_downgraded_zusd_row_is_bounded_replay_with_the_review_note() -> None:
    """Opus review P2: the zusd axis must not claim an inductive certificate."""

    import json as jsonlib

    manifest = jsonlib.loads(MANIFEST.read_text())
    row = next(r for r in manifest["rows"] if r["axis_id"] == "zusd_oracle_recovery_split_brain")
    assert row["status"] == "bounded_replay"
    assert "downgraded from inductive_esso" in row["evidence_note"]


def _rebind_receipt(workspace: Path, row: dict, mutate) -> None:
    import hashlib
    import json as jsonlib

    target = workspace / row["receipt_path"]
    receipt = jsonlib.loads(target.read_text())
    mutate(receipt)
    rendered = jsonlib.dumps(receipt)
    target.write_text(rendered)
    row["receipt_sha256"] = hashlib.sha256(rendered.encode()).hexdigest()


def test_receipt_model_id_drift_is_rejected(workspace: Path) -> None:
    """G3 pinned individually (Opus round 2)."""

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    _rebind_receipt(workspace, row, lambda r: r["report"].__setitem__("model_id", "another_model"))
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("model_id does not match" in e for e in report["errors"])


def test_dropping_cvc5_from_one_query_is_rejected(workspace: Path) -> None:
    """G6 pinned individually (Opus round 2): solver list intact, evidence gutted."""

    def mutate(receipt: dict) -> None:
        query = next(iter(receipt["queries"].values()))
        query.pop("cvc5")

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    _rebind_receipt(workspace, row, mutate)
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("lacks an unsat cvc5 result" in e for e in report["errors"])


def test_query_count_drift_is_rejected(workspace: Path) -> None:
    """G7 pinned individually (Opus round 2)."""

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    _rebind_receipt(workspace, row, lambda r: r["report"].__setitem__("passed_queries", 99))
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("query counts disagree" in e for e in report["errors"])


def test_stripped_query_set_is_rejected(workspace: Path) -> None:
    """Opus round 2 R3: dropping a query with counts adjusted must fail."""

    def mutate(receipt: dict) -> None:
        name = sorted(receipt["queries"])[0]
        receipt["queries"].pop(name)
        receipt["report"]["passed_queries"] = len(receipt["queries"])
        receipt["report"]["total_queries"] = len(receipt["queries"])

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    _rebind_receipt(workspace, row, mutate)
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("does not match the model's declared checks" in e for e in report["errors"])


def test_invented_query_name_is_rejected(workspace: Path) -> None:
    """Opus round 2 R4: a query the model never declared must fail."""

    def mutate(receipt: dict) -> None:
        name = sorted(receipt["queries"])[0]
        receipt["queries"]["totally_made_up"] = receipt["queries"].pop(name)
        receipt["report"]["passed_queries"] = len(receipt["queries"])
        receipt["report"]["total_queries"] = len(receipt["queries"])

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    _rebind_receipt(workspace, row, mutate)
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("does not match the model's declared checks" in e for e in report["errors"])


def test_gutted_model_content_is_rejected(workspace: Path) -> None:
    """Opus round 2 R1: replacing the model bytes with garbage (sha resynced) must fail."""

    import hashlib

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    garbage = "this is not an ESSO model at all\n"
    (workspace / row["model_path"]).write_text(garbage)
    row["model_sha256"] = hashlib.sha256(garbage.encode()).hexdigest()
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("does not parse as an ESSO model" in e for e in report["errors"])


def test_string_model_field_in_receipt_is_an_error_not_a_crash(workspace: Path) -> None:
    """Opus round 2 R6: a malformed receipt shape must reject, never raise."""

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    _rebind_receipt(workspace, row, lambda r: r.__setitem__("model", "not-a-mapping"))
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("certifies a different model path" in e for e in report["errors"])


def test_builder_check_mode_catches_a_demoted_certificate(workspace: Path) -> None:
    """Opus round 2 R5: the registry is two-way once build --check is exercised."""

    import json as jsonlib

    from tools.build_disaster_axis_status_manifest import build_manifest

    rebuilt = build_manifest(workspace)
    committed = jsonlib.loads((workspace / "tools/disaster_axis_status_manifest.json").read_text())
    assert rebuilt == committed
    manifest = _load(workspace)
    row = _first_inductive(manifest)
    row_id = row["axis_id"]
    demoted = {
        "axis_id": row_id,
        "axis_definition_sha256": row["axis_definition_sha256"],
        "status": "bounded_replay",
        "evidence_note": "silently demoted",
    }
    manifest["rows"] = [demoted if r["axis_id"] == row_id else r for r in manifest["rows"]]
    _store(workspace, manifest)
    stored = jsonlib.loads((workspace / "tools/disaster_axis_status_manifest.json").read_text())
    assert build_manifest(workspace) != stored


def test_dex_settlement_recovery_row_is_downgraded_with_the_review_note() -> None:
    """Opus round 2: the model with no proof/claimability state must not claim inductive."""

    import json as jsonlib

    manifest = jsonlib.loads(MANIFEST.read_text())
    row = next(r for r in manifest["rows"] if r["axis_id"] == "dex_settlement_recovery_proof_unit_boundary")
    assert row["status"] == "bounded_replay"
    assert "downgraded from inductive_esso" in row["evidence_note"]


def test_partial_certifications_carry_their_caveats() -> None:
    """Opus round 3: the manifest is self-describing about partial certification."""

    import json as jsonlib

    manifest = jsonlib.loads(MANIFEST.read_text())
    by_id = {row["axis_id"]: row for row in manifest["rows"]}
    for axis_id, needle in (
        ("settlement_proof_recompute_gate", "root-match guard is removable"),
        ("state_accounting_size_boundary", "canonical-size guard is dead"),
    ):
        row = by_id[axis_id]
        assert row["status"] == "inductive_esso"
        assert needle in row["caveat"]


def test_inconsistent_ir_hash_fields_are_rejected(workspace: Path) -> None:
    """Opus round 3 T3: the receipt's two ir_hash fields must agree."""

    manifest = _load(workspace)
    row = _first_inductive(manifest)
    _rebind_receipt(workspace, row, lambda r: r["model"].__setitem__("ir_hash", "sha256:" + "ab" * 32))
    _store(workspace, manifest)
    report = _check(workspace)
    assert report["ok"] is False
    assert any("ir_hash fields are absent or inconsistent" in e for e in report["errors"])


def test_hostile_manifest_shapes_reject_instead_of_crashing(workspace: Path) -> None:
    """Opus round 3: totality over hostile shapes (no raise, always a verdict)."""

    from tools.check_disaster_axis_status_manifest import check_manifest_total

    target = workspace / "tools/disaster_axis_status_manifest.json"
    for hostile in ('[]', '{"schema": 7}', '{"schema": "zenodex/disaster-axis-status-manifest/v1", "rows": 3}',
                    '{"schema": "zenodex/disaster-axis-status-manifest/v1", "rows": [5]}', "not json at all"):
        target.write_text(hostile)
        report = check_manifest_total(workspace, target)
        assert report["ok"] is False
        assert report["errors"]


def test_inductive_receipts_replay_fresh_under_both_solvers() -> None:
    """Opus final round: fresh verify-multi must reproduce every committed receipt.

    Re-runs ESSO verify-multi (z3+cvc5) for every inductive_esso model and
    requires the fresh ir_hash, verdict, solver agreement, and query set to
    match the committed receipt. Requires external/ESSO (the repo's standard
    dependency location); its absence FAILS this gate rather than skipping."""

    import json as jsonlib
    import os
    import subprocess

    esso = ROOT / "external/ESSO"
    assert esso.is_dir(), "external/ESSO is required for the inductive replay gate"
    manifest = jsonlib.loads(MANIFEST.read_text())
    rows = [row for row in manifest["rows"] if row["status"] == "inductive_esso"]
    assert len(rows) == 10
    env = dict(os.environ, PYTHONPATH=str(esso), ZENO_ESSO_PYTHON="/usr/bin/python3")
    for row in rows:
        committed = jsonlib.loads((ROOT / row["receipt_path"]).read_text())
        fresh_raw = subprocess.run(
            ["/usr/bin/python3", "-m", "ESSO", "verify-multi", row["model_path"], "--solvers", "z3,cvc5"],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=300, check=True,
        ).stdout
        fresh = jsonlib.loads(fresh_raw)
        assert fresh["ok"] is True, row["axis_id"]
        assert fresh["model"]["ir_hash"] == committed["model"]["ir_hash"], row["axis_id"]
        assert fresh["report"]["verdict"] == "VERIFIED", row["axis_id"]
        assert fresh["report"]["solvers_agreed"] is True, row["axis_id"]
        assert set(fresh["queries"]) == set(committed["queries"]), row["axis_id"]
