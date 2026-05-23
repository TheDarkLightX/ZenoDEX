from __future__ import annotations

from src.integration.zenograph_ranking_stage_summary import (
    render_zenograph_ranking_stage_markdown,
)


def test_render_zenograph_ranking_stage_markdown_includes_block_state() -> None:
    text = render_zenograph_ranking_stage_markdown(
        {
            "schema": "zenodex/zenograph-autotrader-ranking-stage-report/v1",
            "risk_disclosure": {
                "summary": "Advanced experimental automation and AI shadow surface.",
                "guidance": [
                    "Do not use unless you understand the strategy.",
                    "Do not risk funds you cannot afford to lose in full.",
                ],
            },
            "ranking_stage": {
                "current_template_id": "dca",
                "effective_ranking_template_id": "dca",
                "zenograph_selected_template_id": None,
                "stage_tag": "blocked",
                "block_reason": "submit_vs_block_disagreement",
                "unmet_criteria": [
                    "submit_vs_block_zero",
                    "block_vs_allow_zero",
                ],
            },
            "zenograph_advisory": {
                "tactic_evaluation": {
                    "admissible": False,
                    "blocked_reasons": ["governance_risk_elevated"],
                }
            },
        }
    )

    assert "# ZenoGraph Ranking Stage" in text
    assert "Advanced experimental automation and AI surface" in text
    assert "- Stage tag: `blocked`" in text
    assert "- Gate block reason: `submit_vs_block_disagreement`" in text
    assert "`submit_vs_block_zero`" in text
    assert "`governance_risk_elevated`" in text
    assert "does not change controller execution" in text
