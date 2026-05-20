from __future__ import annotations

from src.agents.zenograph_selector import ZGTemplateCandidate, select_best_template


def test_selector_ignores_inadmissible_templates() -> None:
    winner = select_best_template(
        (
            ZGTemplateCandidate(template_id="onchain_flow_follow", rank=1, admissible=False),
            ZGTemplateCandidate(template_id="dca", rank=3, admissible=True),
        )
    )
    assert winner is not None
    assert winner.template_id == "dca"


def test_selector_uses_rank_then_template_id_tie_break() -> None:
    winner = select_best_template(
        (
            ZGTemplateCandidate(template_id="rebalance", rank=5, admissible=True),
            ZGTemplateCandidate(template_id="dca", rank=5, admissible=True),
        )
    )
    assert winner is not None
    assert winner.template_id == "dca"
