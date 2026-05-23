from __future__ import annotations

from internal.Gemini.zeno_logic import EnergyNot
from tools.check_gemini_jepa_logic_boundary import _Kernel, check_gemini_jepa_logic_boundary


def test_jepa_logic_boundary_is_advisory_only() -> None:
    report = check_gemini_jepa_logic_boundary()

    assert report["schema"] == "zenodex/energy/gemini_jepa_logic_boundary_receipt/v1"
    assert report["ok"] is True
    assert report["decision"] == "research_only_future_aware_advisory_score"
    assert report["jepa"]["future_tension_prefers_balanced"] is True
    assert report["safety_contract"]["deterministic_verifier_authoritative"] is True
    assert report["safety_contract"]["model_authorizes_settlement"] is False
    assert report["safety_contract"]["logic_expression_authorizes_settlement"] is False


def test_energy_not_can_invert_hard_barriers() -> None:
    inverted = EnergyNot(_Kernel("barrier", "hard_violation", 1_000.0))

    assert inverted.energy({"hard_violation": 1.0}) < inverted.energy({"hard_violation": 0.0})

    report = check_gemini_jepa_logic_boundary()
    negative = " ".join(report["negative_knowledge"]).lower()
    assert "energynot can invert hard barriers" in negative
    assert "must not be used over safety predicates" in negative
