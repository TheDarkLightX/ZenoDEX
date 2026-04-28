from __future__ import annotations

from pathlib import Path

from tools.check_disaster_search_closed_receipt import build_closed_receipt_ratchet_report
from tools.check_disaster_proof_schema_map import (
    CLOSED_AXIS_PROOF_SCHEMA_MAP,
    build_disaster_proof_schema_map_report,
)
from tools.check_formal_proof_hygiene import (
    CRITICAL_FORMAL_PROOF_ARTIFACTS,
    build_formal_proof_hygiene_report,
    strip_lean_comments,
)
from tools.stateful_scenario_bridge import (
    CLOSED_DISASTER_SEARCH_AXIS_IDS,
    DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA,
)


def _closed_receipt(axis_ids: list[str] | None = None, *, inconclusive_count: int = 0) -> dict:
    ids = axis_ids or list(CLOSED_DISASTER_SEARCH_AXIS_IDS)
    return {
        "schema": DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA,
        "ok": True,
        "policy": {"skips_are_inconclusive": True},
        "selected_axis_count": len(ids),
        "unreachable_count": len(ids) - inconclusive_count,
        "failed_count": 0,
        "inconclusive_count": inconclusive_count,
        "axis_results": [
            {
                "axis_id": axis_id,
                "status": "inconclusive" if idx < inconclusive_count else "unreachable_under_current_bounds",
            }
            for idx, axis_id in enumerate(ids)
        ],
    }


def test_closed_receipt_ratchet_accepts_current_pinned_axes() -> None:
    payload = build_closed_receipt_ratchet_report(_closed_receipt())

    assert payload["ok"] is True
    assert payload["pinned_axis_count"] == 29
    assert payload["receipt_unreachable_count"] == 29
    assert payload["receipt_failed_count"] == 0
    assert payload["receipt_inconclusive_count"] == 0


def test_closed_receipt_ratchet_rejects_missing_or_inconclusive_axis() -> None:
    receipt = _closed_receipt(list(CLOSED_DISASTER_SEARCH_AXIS_IDS)[:-1], inconclusive_count=1)

    payload = build_closed_receipt_ratchet_report(receipt)

    assert payload["ok"] is False
    assert any("missing closed axis id" in error for error in payload["errors"])
    assert any("inconclusive_count must be 0" in error for error in payload["errors"])
    assert any("closed axis status regressed" in error for error in payload["errors"])


def test_strip_lean_comments_ignores_placeholder_words_in_comments() -> None:
    text = """-- sorry in a line comment
/- block comment with admit
   /- nested sorry -/
-/
theorem demo : True := by
  trivial
"""

    stripped = strip_lean_comments(text)

    assert "sorry" not in stripped
    assert "admit" not in stripped
    assert "theorem demo" in stripped
    assert "trivial" in stripped


def test_formal_proof_hygiene_accepts_comment_only_placeholders(tmp_path: Path) -> None:
    proof = tmp_path / "Proof.lean"
    proof.write_text("-- no sorry in active code\nexample : True := by\n  trivial\n", encoding="utf-8")

    payload = build_formal_proof_hygiene_report(proof_files=[str(proof)])

    assert payload["ok"] is True
    assert payload["active_placeholder_count"] == 0


def test_formal_proof_hygiene_rejects_active_placeholder(tmp_path: Path) -> None:
    proof = tmp_path / "Proof.lean"
    proof.write_text("example : True := by\n  sorry\n", encoding="utf-8")

    payload = build_formal_proof_hygiene_report(proof_files=[str(proof)])

    assert payload["ok"] is False
    assert payload["active_placeholder_count"] == 1
    assert "sorry@2" in payload["errors"][0]


def test_formal_proof_hygiene_default_tracks_disaster_proof_schemas() -> None:
    tracked = set(CRITICAL_FORMAL_PROOF_ARTIFACTS)

    assert "lean-mathlib/Proofs/AMMIntegerRuntimeBridge.lean" in tracked
    assert "lean-mathlib/Proofs/DisasterAntichainBasis.lean" in tracked
    assert "lean-mathlib/Proofs/DisasterTraceDiscoveryChallenge.lean" in tracked
    assert "lean-mathlib/Proofs/CertificateGluing.lean" in tracked
    assert "lean-mathlib/Proofs/ForbiddenTraceMinor.lean" in tracked
    assert "lean-mathlib/Proofs/NoFreeResourceTraceLedger.lean" in tracked
    assert "lean-mathlib/Proofs/ZenoDEXDisasterSchemaInstantiations.lean" in tracked
    assert "lean-mathlib/Proofs/ZenoDEXClosedAxisProofSchemaMap.lean" in tracked


def test_disaster_proof_schema_map_covers_closed_axes() -> None:
    payload = build_disaster_proof_schema_map_report()

    assert payload["ok"] is True
    assert payload["axis_count"] == 29
    assert payload["schema_usage"]["forbidden_trace_minor"] >= 1
    assert payload["schema_usage"]["no_free_resource_trace_ledger"] >= 1
    assert payload["schema_usage"]["zenodex_disaster_schema_instantiations"] >= 1


def test_disaster_proof_schema_map_rejects_missing_axis() -> None:
    partial = dict(CLOSED_AXIS_PROOF_SCHEMA_MAP)
    partial.pop("resource_budget_abort")

    payload = build_disaster_proof_schema_map_report(axis_map=partial)

    assert payload["ok"] is False
    assert any("resource_budget_abort" in error for error in payload["errors"])
