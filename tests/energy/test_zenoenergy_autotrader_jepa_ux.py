from __future__ import annotations

from pathlib import Path

from tools import check_zenoenergy_autotrader_jepa_ux as jepa_ux_tool
from tools.check_zenoenergy_autotrader_jepa_ux import check_zenoenergy_autotrader_jepa_ux


ROOT = Path(__file__).resolve().parents[2]


def test_autotrader_jepa_ux_receipt_preserves_authority_boundary() -> None:
    report = check_zenoenergy_autotrader_jepa_ux(
        seed=20260531,
        contexts=24,
        candidates_per_context=10,
        future_weight=0.1,
    )

    assert report["schema"] == "zenodex/energy/autotrader_jepa_ux_receipt/v1"
    assert report["ok"] is True
    assert report["decision"] == "research_only_future_aware_autotrader_ux"
    assert report["future_aware_evaluation"]["invalid_accept_count"] == 0
    assert report["future_risk_prediction"]["later_policy_failure_auc"] >= 0.80
    assert report["future_risk_prediction"]["stress_correlations"]["slippage_stress"] >= 0.55
    assert report["future_risk_prediction"]["stress_correlations"]["budget_stress"] >= 0.55
    assert report["future_risk_prediction"]["stress_correlations"]["drawdown_stress"] >= 0.55
    assert report["control_metrics"]["safer_counterfactual_reduction_rate"] >= 0.95
    assert report["control_metrics"]["suggested_control_best_reduction_rate"] >= 0.95
    assert report["warning_metrics"]["blocked_status_match_rate"] == 1.0
    assert report["warning_metrics"]["future_warning_match_rate"] >= 0.80
    assert report["research_inputs"]["ok"] is True
    assert report["efficiency"]["parameter_count"] == 68
    assert report["safety_contract"]["deterministic_policy_guards_authoritative"] is True
    assert report["safety_contract"]["model_authorizes_trade"] is False
    assert report["safety_contract"]["ux_card_authorizes_trade"] is False


def test_autotrader_jepa_ux_receipt_explains_future_risk_and_controls() -> None:
    report = check_zenoenergy_autotrader_jepa_ux(
        seed=20260533,
        contexts=8,
        candidates_per_context=8,
        future_weight=0.1,
    )

    blocked_card = report["ux"]["blocked_card"]
    fragile_card = report["ux"]["fragile_card"]

    assert report["scenario_scores"]["future_tension_differentiates_fragility"] is True
    assert report["scenario_scores"]["fragile_future_tension"] > report["scenario_scores"]["balanced_future_tension"]
    assert blocked_card["status"] == "blocked_by_policy_guard"
    assert "stale signal or quote" in blocked_card["blocked_reasons"]
    assert any("Refresh oracle" in item for item in blocked_card["suggested_controls"])
    assert fragile_card["status"] in {"needs_risk_review", "policy_valid_with_caution"}
    assert fragile_card["control_effects"]
    assert any(
        float(effect["future_tension_delta"]) < 0.0
        for effect in fragile_card["control_effects"]
    )
    assert all(
        effect["control_authorizes_trade"] is False
        for effect in fragile_card["control_effects"]
    )
    assert report["ux"]["ux_explains_status_and_controls"] is True


def test_autotrader_jepa_ux_rejects_truthy_string_subreport_ok(monkeypatch) -> None:
    original_research_inputs = jepa_ux_tool._research_inputs
    original_efficiency = jepa_ux_tool._efficiency_profile

    def fake_research_inputs():
        report = dict(original_research_inputs())
        report["ok"] = "true"
        return report

    def fake_efficiency_profile(*, model):
        report = dict(original_efficiency(model=model))
        report["ok"] = 1
        return report

    monkeypatch.setattr(jepa_ux_tool, "_research_inputs", fake_research_inputs)
    monkeypatch.setattr(jepa_ux_tool, "_efficiency_profile", fake_efficiency_profile)

    report = check_zenoenergy_autotrader_jepa_ux(
        seed=20260531,
        contexts=8,
        candidates_per_context=8,
        future_weight=0.1,
    )

    assert report["research_inputs"]["ok"] == "true"
    assert report["efficiency"]["ok"] == 1
    assert report["ok"] is False


def test_autotrader_jepa_ux_main_rejects_truthy_string_top_level_ok(monkeypatch, capsys) -> None:
    def fake_check(**_kwargs):
        return {"schema": "zenodex/energy/autotrader_jepa_ux_receipt/v1", "ok": "true"}

    monkeypatch.setattr(jepa_ux_tool, "check_zenoenergy_autotrader_jepa_ux", fake_check)
    monkeypatch.setattr(jepa_ux_tool.sys, "argv", ["check_zenoenergy_autotrader_jepa_ux.py"])

    rc = jepa_ux_tool.main()
    payload = capsys.readouterr().out

    assert rc == 1
    assert '"ok": "true"' in payload
