from __future__ import annotations

import copy
import json
from pathlib import Path

from tools.check_zenodex_theorem_ledger import DEFAULT_LEDGER, ROOT, validate_ledger


def _ledger() -> dict[str, object]:
    value = json.loads(DEFAULT_LEDGER.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_repository_theorem_ledger_is_structurally_valid() -> None:
    report = validate_ledger(_ledger(), root=ROOT)
    assert report["ok"] is True, report["errors"]
    assert report["theorem_count"] == 18
    assert report["idea_count"] >= 6


def test_review_gate_fails_closed_while_ledger_is_research_candidate() -> None:
    report = validate_ledger(_ledger(), root=ROOT, require_reviewed=True)
    assert report["ok"] is False
    assert "review gate requires claim_status=reviewed" in report["errors"]


def test_duplicate_theorem_id_and_rank_are_rejected() -> None:
    value = _ledger()
    theorems = value["theorems"]
    assert isinstance(theorems, list)
    duplicate = copy.deepcopy(theorems[0])
    theorems[1]["id"] = duplicate["id"]
    theorems[1]["rank"] = duplicate["rank"]

    report = validate_ledger(value, root=ROOT)
    assert report["ok"] is False
    assert any("duplicate theorem id" in error for error in report["errors"])
    assert any("duplicate theorem rank" in error for error in report["errors"])


def test_assurance_chain_reordering_is_rejected() -> None:
    value = _ledger()
    chain = value["assurance_chain"]
    assert isinstance(chain, list)
    chain[0], chain[1] = chain[1], chain[0]

    report = validate_ledger(value, root=ROOT)
    assert report["ok"] is False
    assert "assurance_chain must match the required ordered proof chain exactly" in report["errors"]


def test_missing_branch_local_formal_artifact_is_rejected(tmp_path: Path) -> None:
    value = _ledger()
    theorems = value["theorems"]
    assert isinstance(theorems, list)
    theorem = next(item for item in theorems if item["id"] == "ENCODING-INJECTIVE-003")
    theorem["artifact"] = "lean-mathlib/Proofs/DoesNotExist.lean"

    report = validate_ledger(value, root=tmp_path)
    assert report["ok"] is False
    assert any("branch-local artifact does not exist" in error for error in report["errors"])


def test_unverifiable_source_locator_is_rejected() -> None:
    value = _ledger()
    theorems = value["theorems"]
    assert isinstance(theorems, list)
    theorems[0]["source"] = "someone said this on a forum"

    report = validate_ledger(value, root=ROOT)
    assert report["ok"] is False
    assert any("source must contain" in error for error in report["errors"])


def test_missing_required_idea_is_rejected() -> None:
    value = _ledger()
    ideas = value["ideas"]
    assert isinstance(ideas, list)
    value["ideas"] = [item for item in ideas if item["id"] != "ATOMIC-CANDIDATE"]

    report = validate_ledger(value, root=ROOT)
    assert report["ok"] is False
    assert any("missing required idea ids" in error for error in report["errors"])
