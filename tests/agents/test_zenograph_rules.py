from __future__ import annotations

from pathlib import Path

from src.agents.zenograph_rules import (
    ZGRuleContext,
    ZGTrustTier,
    evaluate_rules_for_tactic,
    load_rule_specs,
)


RULES_PATH = Path("config/zenograph/rules_v1.yaml")


def test_onchain_flow_follow_is_admissible_on_positive_signal() -> None:
    rules = load_rule_specs(RULES_PATH)
    evaluation = evaluate_rules_for_tactic(
        rules,
        ZGRuleContext(
            tactic_id="onchain_flow_follow",
            signals={"smart_money_accumulation": True},
            source_trust=ZGTrustTier.TRUSTED,
            liquidity_state="deep",
        ),
    )
    assert evaluation.admissible is True
    assert evaluation.positive_reasons == ("trusted_accumulation_signal",)
    assert evaluation.blocked_reasons == ()


def test_governance_risk_blocks_onchain_flow_follow() -> None:
    rules = load_rule_specs(RULES_PATH)
    evaluation = evaluate_rules_for_tactic(
        rules,
        ZGRuleContext(
            tactic_id="onchain_flow_follow",
            facts={("protocol", "governance_attack_risk"): "elevated"},
            signals={"smart_money_accumulation": True},
            source_trust=ZGTrustTier.TRUSTED,
            liquidity_state="deep",
        ),
    )
    assert evaluation.admissible is False
    assert "governance_risk_elevated" in evaluation.blocked_reasons


def test_drawdown_lock_restricts_allowed_templates() -> None:
    rules = load_rule_specs(RULES_PATH)
    evaluation = evaluate_rules_for_tactic(
        rules,
        ZGRuleContext(
            tactic_id="onchain_flow_follow",
            user_state={"drawdown_lock": True},
            signals={"smart_money_accumulation": True},
            source_trust=ZGTrustTier.TRUSTED,
            liquidity_state="deep",
        ),
    )
    assert evaluation.admissible is False
    assert evaluation.allowed_templates_only == ("cash_preserve", "dca", "rebalance")
    assert "not_in_allowed_templates_only" in evaluation.blocked_reasons
