from __future__ import annotations

import copy
import json
from pathlib import Path

from tools.check_zenodex_tool_research_synthesis import (
    DEFAULT_LEDGER,
    ROOT,
    validate_synthesis,
)


def _ledger() -> dict[str, object]:
    value = json.loads(DEFAULT_LEDGER.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _tool(value: dict[str, object], tool_id: str) -> dict[str, object]:
    tools = value["tool_sources"]
    assert isinstance(tools, dict)
    tool = tools[tool_id]
    assert isinstance(tool, dict)
    return tool


def test_repository_synthesis_ledger_is_valid() -> None:
    report = validate_synthesis(_ledger(), root=ROOT)
    assert report["ok"] is True, report["errors"]
    assert report["tool_count"] == 3
    assert report["decision_count"] == 5


def test_failed_or_stale_workflow_evidence_rejects() -> None:
    value = _ledger()
    _tool(value, "research_kernel")["workflow_conclusion"] = "failure"

    report = validate_synthesis(value, root=ROOT)
    assert report["ok"] is False
    assert any("workflow_conclusion" in error for error in report["errors"])


def test_morph_candidates_cannot_be_silently_promoted() -> None:
    value = _ledger()
    morph = value["morph_result"]
    assert isinstance(morph, dict)
    morph["all_candidates_promotable"] = True

    report = validate_synthesis(value, root=ROOT)
    assert report["ok"] is False
    assert "Morph candidates must remain non-promotable" in report["errors"]


def test_naive_model_must_retain_partial_publication_witness() -> None:
    value = _ledger()
    esso = value["esso_result"]
    assert isinstance(esso, dict)
    naive = esso["naive_model"]
    assert isinstance(naive, dict)
    projection = naive["counterexample_projection"]
    assert isinstance(projection, dict)
    projection["post_effects_published"] = True

    report = validate_synthesis(value, root=ROOT)
    assert report["ok"] is False
    assert any("partial publication" in error for error in report["errors"])


def test_repaired_model_must_remain_verified() -> None:
    value = _ledger()
    esso = value["esso_result"]
    assert isinstance(esso, dict)
    repaired = esso["repaired_model"]
    assert isinstance(repaired, dict)
    repaired["verdict"] = "INCONCLUSIVE"

    report = validate_synthesis(value, root=ROOT)
    assert report["ok"] is False
    assert "repaired ESSO model must remain VERIFIED" in report["errors"]


def test_missing_formal_artifact_rejects(tmp_path: Path) -> None:
    value = _ledger()
    formal = value["new_formal_result"]
    assert isinstance(formal, dict)
    formal["artifact"] = "lean-mathlib/Proofs/MissingReadWriteProof.lean"

    report = validate_synthesis(value, root=tmp_path)
    assert report["ok"] is False
    assert any("formal artifact does not exist" in error for error in report["errors"])


def test_duplicate_decision_priority_rejects() -> None:
    value = _ledger()
    decisions = value["decisions"]
    assert isinstance(decisions, list)
    duplicate = copy.deepcopy(decisions[0])
    decisions[1]["priority"] = duplicate["priority"]

    report = validate_synthesis(value, root=ROOT)
    assert report["ok"] is False
    assert any("duplicate decision priority" in error for error in report["errors"])


def test_tool_source_hashes_are_exact_width() -> None:
    value = _ledger()
    _tool(value, "esso")["study_head_sha"] = "deadbeef"

    report = validate_synthesis(value, root=ROOT)
    assert report["ok"] is False
    assert any("study_head_sha has invalid format" in error for error in report["errors"])


def test_same_width_tool_source_substitution_rejects() -> None:
    value = _ledger()
    _tool(value, "research_kernel")["source_sha"] = "0" * 40

    report = validate_synthesis(value, root=ROOT)

    assert report["ok"] is False
    assert any(
        "tool_sources.research_kernel.source_sha must equal the pinned evidence value" in error
        for error in report["errors"]
    )


def test_same_shape_artifact_digest_substitution_rejects() -> None:
    value = _ledger()
    _tool(value, "morph")["artifact_digest"] = "sha256:" + ("0" * 64)

    report = validate_synthesis(value, root=ROOT)

    assert report["ok"] is False
    assert any(
        "tool_sources.morph.artifact_digest must equal the pinned evidence value" in error
        for error in report["errors"]
    )


def test_same_shape_result_hash_substitution_rejects() -> None:
    value = _ledger()
    _tool(value, "research_kernel")["decision_sha256"] = "0" * 64

    report = validate_synthesis(value, root=ROOT)

    assert report["ok"] is False
    assert any(
        "tool_sources.research_kernel.decision_sha256 must equal the pinned evidence value"
        in error
        for error in report["errors"]
    )


def test_same_shape_esso_fingerprint_substitution_rejects() -> None:
    value = _ledger()
    esso = value["esso_result"]
    assert isinstance(esso, dict)
    repaired = esso["repaired_model"]
    assert isinstance(repaired, dict)
    repaired["fingerprint"] = "0" * 64

    report = validate_synthesis(value, root=ROOT)

    assert report["ok"] is False
    assert any(
        "repaired_model.fingerprint must equal the pinned evidence value" in error
        for error in report["errors"]
    )
