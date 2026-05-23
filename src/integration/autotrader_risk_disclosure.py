from __future__ import annotations

from typing import Any


AUTOTRADER_RISK_DISCLOSURE_SCHEMA = "zenodex/autotrader-risk-disclosure/v1"


def build_autotrader_risk_disclosure(
    *,
    mode: str,
    requires_explicit_acknowledgement: bool,
    user_acknowledged: bool,
) -> dict[str, Any]:
    live_like = mode == "live_prepare"
    summary = (
        "Advanced experimental automation and AI live-preparation surface. "
        "You can lose everything. Use only if you understand and accept the risk."
        if live_like
        else "Advanced experimental automation and AI shadow surface. "
        "This tool is dry-run only, but any live use of automation outputs is at your own risk "
        "and can still lead to total loss."
    )
    return {
        "schema": AUTOTRADER_RISK_DISCLOSURE_SCHEMA,
        "mode": mode,
        "advanced_feature": True,
        "experimental": True,
        "recommended_for_general_use": False,
        "at_your_own_risk": True,
        "ai_or_automation_involved": True,
        "can_submit_transactions": live_like,
        "direct_capital_loss_possible": live_like,
        "automation_can_lose_everything": True,
        "requires_explicit_acknowledgement": requires_explicit_acknowledgement,
        "user_acknowledged": user_acknowledged,
        "summary": summary,
        "guidance": (
            "Do not use unless you understand the strategy, market, and failure modes.",
            "Do not risk funds you cannot afford to lose in full.",
            "Prefer shadow/replay mode before any live-preparation workflow.",
        ),
    }
