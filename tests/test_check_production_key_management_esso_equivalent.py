from __future__ import annotations

from pathlib import Path

from tools.check_production_key_management_esso_equivalent import run_check


ROOT = Path(__file__).resolve().parents[1]


def test_production_key_management_esso_equivalent_check_accepts() -> None:
    result = run_check(
        esso_model_path=ROOT / "formal/esso/production_key_management_v0.esso.yaml",
        property_model_path=ROOT / "formal/property/production_key_management_v0.json",
    )

    assert result["ok"] is True
    assert result["equivalent_finite_model"] is True
    assert result["property_case_count"] >= 160
    assert set(result["property_invariant_ids"]) >= {
        "PKM-G-001",
        "PKM-G-002",
        "PKM-G-003",
        "PKM-G-004",
        "PKM-G-005",
        "PKM-G-006",
        "PKM-G-007",
    }
    assert set(result["esso_invariant_ids"]) >= {
        "PKM-ESSO-001-prod-keys-only",
        "PKM-ESSO-002-no-revoked-or-expired",
        "PKM-ESSO-003-role-authorized",
        "PKM-ESSO-004-quorum",
        "PKM-ESSO-005-distinct-custodians",
        "PKM-ESSO-006-storage",
        "PKM-ESSO-007-timelock",
        "PKM-ESSO-008-break-glass-scope",
        "PKM-ESSO-009-transparency",
        "PKM-ESSO-010-no-single-key-critical",
    }
