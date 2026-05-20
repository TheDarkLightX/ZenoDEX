from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..agents.strategy_ir import StrategyIR
from .zenograph_autotrader_adapter import ZenoGraphAutoTraderAdvisoryObservation


ZENOGRAPH_AUTOTRADER_RANKING_STAGE_SCHEMA = (
    "zenodex/zenograph-autotrader-ranking-stage/v1"
)


@dataclass(frozen=True)
class ZenoGraphAutoTraderRankingStageObservation:
    current_template_id: str
    zenograph_selected_template_id: str | None
    zenograph_selected_template_rank: int | None
    ranking_influence_allowed: bool
    effective_ranking_template_id: str
    stage_tag: str
    block_reason: str | None
    unmet_criteria: tuple[str, ...]
    schema: str = ZENOGRAPH_AUTOTRADER_RANKING_STAGE_SCHEMA

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "current_template_id": self.current_template_id,
            "zenograph_selected_template_id": self.zenograph_selected_template_id,
            "zenograph_selected_template_rank": self.zenograph_selected_template_rank,
            "ranking_influence_allowed": bool(self.ranking_influence_allowed),
            "effective_ranking_template_id": self.effective_ranking_template_id,
            "stage_tag": self.stage_tag,
            "block_reason": self.block_reason,
            "unmet_criteria": list(self.unmet_criteria),
        }


def build_zenograph_autotrader_ranking_stage_observation(
    *,
    strategy: StrategyIR,
    advisory: ZenoGraphAutoTraderAdvisoryObservation,
    gate_report: Mapping[str, object],
) -> ZenoGraphAutoTraderRankingStageObservation:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(advisory, ZenoGraphAutoTraderAdvisoryObservation):
        raise TypeError("advisory must be a ZenoGraphAutoTraderAdvisoryObservation")
    if not isinstance(gate_report, Mapping):
        raise TypeError("gate_report must be a mapping")

    gate = gate_report.get("gate")
    if not isinstance(gate, Mapping):
        raise ValueError("gate_report must contain a gate object")

    ranking_influence_allowed = _require_bool(
        "gate.ranking_influence_allowed", gate.get("ranking_influence_allowed")
    )
    block_reason = gate.get("block_reason")
    if block_reason is not None and not isinstance(block_reason, str):
        raise TypeError("gate.block_reason must be a string or null")
    unmet_raw = gate.get("unmet_criteria", ())
    if not isinstance(unmet_raw, list):
        raise TypeError("gate.unmet_criteria must be a list when present")
    unmet_criteria = tuple(_require_str("gate.unmet_criteria[]", item) for item in unmet_raw)

    current_template_id = strategy.template.value
    selected_template_id = advisory.selected_template_id
    selected_template_rank = advisory.selected_template_rank

    if not ranking_influence_allowed:
        stage_tag = "blocked"
        effective_ranking_template_id = current_template_id
    elif selected_template_id is None or selected_template_id == current_template_id:
        stage_tag = "aligned"
        effective_ranking_template_id = current_template_id
    else:
        stage_tag = "candidate"
        effective_ranking_template_id = selected_template_id

    return ZenoGraphAutoTraderRankingStageObservation(
        current_template_id=current_template_id,
        zenograph_selected_template_id=selected_template_id,
        zenograph_selected_template_rank=selected_template_rank,
        ranking_influence_allowed=ranking_influence_allowed,
        effective_ranking_template_id=effective_ranking_template_id,
        stage_tag=stage_tag,
        block_reason=block_reason,
        unmet_criteria=unmet_criteria,
    )


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_str(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return value
