from __future__ import annotations

from pathlib import Path

from tools.check_production_key_management_spec import run_check


ROOT = Path(__file__).resolve().parents[1]


def test_production_key_management_property_model() -> None:
    result = run_check(ROOT / "formal/property/production_key_management_v0.json")

    assert result["ok"] is True
    assert result["case_count"] >= 80
