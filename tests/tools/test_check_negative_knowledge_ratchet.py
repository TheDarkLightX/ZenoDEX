from __future__ import annotations

import json
from pathlib import Path

from tools.check_negative_knowledge_ratchet import (
    DEFAULT_NEGATIVE_KNOWLEDGE,
    check_negative_knowledge_ratchet,
)


def _load_negative_knowledge() -> dict:
    return json.loads(DEFAULT_NEGATIVE_KNOWLEDGE.read_text(encoding="utf-8"))


def test_negative_knowledge_ratchet_matches_current_baseline() -> None:
    report = check_negative_knowledge_ratchet()
    assert report["ok"] is True
    assert report["expected_schema"] == "shapeforge/negative-knowledge-seed/v2"
    assert report["narrowed_count"] == 1
    assert report["narrowed_hypothesis_ids"] == [
        "exact_out_runtime_order_is_semantic_canonicality_v1"
    ]
    assert report["expected_narrowed_hypothesis_ids"] == [
        "exact_out_runtime_order_is_semantic_canonicality_v1"
    ]
    assert (
        report["expected_narrowed_baselines"]["exact_out_runtime_order_is_semantic_canonicality_v1"][
            "replay_pointer"
        ]
        == "docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json#scenario_id=drop_exact_out_canonical_minimizer_tie_break"
    )


def test_negative_knowledge_ratchet_requires_remaining_excluded_domain(tmp_path: Path) -> None:
    data = _load_negative_knowledge()
    for record in data["records"]:
        if record["status"] == "narrowed":
            record.pop("remaining_excluded_domain", None)
            break
    broken = tmp_path / "negative_knowledge_missing_domain.json"
    broken.write_text(json.dumps(data, indent=2), encoding="utf-8")

    try:
        check_negative_knowledge_ratchet(negative_knowledge_path=broken)
    except ValueError as exc:
        assert "narrowed records must have a nonempty remaining_excluded_domain" in str(exc)
    else:
        raise AssertionError("expected narrowed negative-knowledge ratchet to fail")


def test_negative_knowledge_ratchet_requires_distinct_replacement_claim(tmp_path: Path) -> None:
    data = _load_negative_knowledge()
    for record in data["records"]:
        if record["status"] == "narrowed":
            record["replacement_claim"] = record["claim"]
            break
    broken = tmp_path / "negative_knowledge_same_claim.json"
    broken.write_text(json.dumps(data, indent=2), encoding="utf-8")

    try:
        check_negative_knowledge_ratchet(negative_knowledge_path=broken)
    except ValueError as exc:
        assert "replacement_claim must narrow or replace the original claim" in str(exc)
    else:
        raise AssertionError("expected identical replacement_claim to fail")


def test_negative_knowledge_ratchet_requires_expected_narrowed_record(tmp_path: Path) -> None:
    data = _load_negative_knowledge()
    data["records"] = [
        record
        for record in data["records"]
        if record["hypothesis_id"] != "exact_out_runtime_order_is_semantic_canonicality_v1"
    ]
    broken = tmp_path / "negative_knowledge_missing_narrowed_record.json"
    broken.write_text(json.dumps(data, indent=2), encoding="utf-8")

    try:
        check_negative_knowledge_ratchet(negative_knowledge_path=broken)
    except ValueError as exc:
        assert "narrowed hypothesis ids [] !=" in str(exc)
    else:
        raise AssertionError("expected missing narrowed record to fail")


def test_negative_knowledge_ratchet_requires_expected_narrowed_status(tmp_path: Path) -> None:
    data = _load_negative_knowledge()
    for record in data["records"]:
        if record["hypothesis_id"] == "exact_out_runtime_order_is_semantic_canonicality_v1":
            record["status"] = "blocked"
            break
    broken = tmp_path / "negative_knowledge_missing_narrowed_status.json"
    broken.write_text(json.dumps(data, indent=2), encoding="utf-8")

    try:
        check_negative_knowledge_ratchet(negative_knowledge_path=broken)
    except ValueError as exc:
        assert "narrowed hypothesis ids [] !=" in str(exc)
    else:
        raise AssertionError("expected changed narrowed status to fail")


def test_negative_knowledge_ratchet_requires_expected_narrowed_fields(tmp_path: Path) -> None:
    data = _load_negative_knowledge()
    for record in data["records"]:
        if record["hypothesis_id"] == "exact_out_runtime_order_is_semantic_canonicality_v1":
            record["remaining_excluded_domain"] = "rewritten"
            break
    broken = tmp_path / "negative_knowledge_drifted_narrowed_field.json"
    broken.write_text(json.dumps(data, indent=2), encoding="utf-8")

    try:
        check_negative_knowledge_ratchet(negative_knowledge_path=broken)
    except ValueError as exc:
        assert "field remaining_excluded_domain drifted from pinned baseline" in str(exc)
    else:
        raise AssertionError("expected drifted narrowed field to fail")


def test_negative_knowledge_ratchet_requires_v2_schema(tmp_path: Path) -> None:
    data = _load_negative_knowledge()
    data["schema"] = "shapeforge/negative-knowledge-seed/v1"
    broken = tmp_path / "negative_knowledge_wrong_schema.json"
    broken.write_text(json.dumps(data, indent=2), encoding="utf-8")

    try:
        check_negative_knowledge_ratchet(negative_knowledge_path=broken)
    except ValueError as exc:
        assert "schema 'shapeforge/negative-knowledge-seed/v1' !=" in str(exc)
    else:
        raise AssertionError("expected downgraded schema to fail")
