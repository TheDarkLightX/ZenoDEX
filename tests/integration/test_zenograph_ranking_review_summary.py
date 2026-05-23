from __future__ import annotations

from src.integration.zenograph_ranking_review_summary import (
    render_zenograph_ranking_review_markdown,
)


def test_render_zenograph_ranking_review_markdown_includes_contract_and_gate() -> None:
    text = render_zenograph_ranking_review_markdown(
        {
            "schema": "zenodex/zenograph-autotrader-shadow-compare-baseline/v1",
            "case_count": 20,
            "disagreement_rate": 0.6,
            "controller_submit_vs_zenograph_block_rate": 0.2,
            "controller_block_vs_zenograph_allow_rate": 0.4,
            "family_summary": {
                "aligned_neutral": {"case_count": 4, "disagreement_rate": 0.0},
                "governance_block": {"case_count": 4, "disagreement_rate": 1.0},
            },
        },
        {
            "schema": "zenodex/zenograph-autotrader-ranking-promotion-gate-report/v1",
            "gate": {
                "ranking_influence_allowed": False,
                "block_reason": "submit_vs_block_disagreement",
                "unmet_criteria": ["submit_vs_block_zero", "block_vs_allow_zero"],
            },
            "promotion_contract": {
                "required_case_count": 20,
                "required_families": ["aligned_neutral", "governance_block"],
            },
        },
    )

    assert "# ZenoGraph Ranking Review Bundle" in text
    assert "Case count: `20`" in text
    assert "Block reason: `submit_vs_block_disagreement`" in text
    assert "`submit_vs_block_zero`" in text
    assert "`aligned_neutral`" in text
    assert "does not change controller execution" in text
