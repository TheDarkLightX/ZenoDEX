from __future__ import annotations

from pathlib import Path

from tools.check_production_key_management_spec import run_check


ROOT = Path(__file__).resolve().parents[1]


def test_production_key_management_property_model() -> None:
    result = run_check(ROOT / "formal/property/production_key_management_v0.json")

    assert result["ok"] is True
    assert result["case_count"] >= 80
    invariant_ids = {
        invariant_id
        for case in result["cases"]
        for invariant_id in case["invariant_ids"]
    }
    assert invariant_ids >= {
        "PKM-G-001",
        "PKM-G-002",
        "PKM-G-003",
        "PKM-G-004",
        "PKM-G-005",
        "PKM-G-006",
        "PKM-G-007",
    }
    negative_axes = {
        case["primary_axis"]
        for case in result["cases"]
        if case["polarity"] == "negative"
    }
    assert negative_axes >= {
        "packet",
        "signature_binding",
        "role",
        "environment",
        "status",
        "quorum",
        "storage",
        "timelock",
        "break_glass",
        "transparency",
    }
    for case in result["cases"]:
        assert "primary_axis" in case
        if case["polarity"] == "negative":
            assert case["reject_reason"]
    assert result["counterexamples"] == []
