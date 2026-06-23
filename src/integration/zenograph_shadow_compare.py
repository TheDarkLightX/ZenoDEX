from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from ..agents.strategy_ir import StrategyIR
from ..agents.zenograph_rules import ZGTrustTier
from ..state.pools import PoolState
from .autotrader_controller import (
    AutoTraderControllerState,
    AutoTraderTauConfig,
    evaluate_autotrader_quote_receipt,
)
from .zenograph_autotrader_adapter import (
    ZenoGraphAutoTraderAdvisoryObservation,
    build_zenograph_autotrader_advisory_observation,
)


ZENOGRAPH_AUTOTRADER_SHADOW_COMPARISON_SCHEMA = (
    "zenodex/zenograph-autotrader-shadow-comparison/v1"
)


@dataclass(frozen=True)
class ZenoGraphAutoTraderShadowDisagreement:
    disagreement: bool
    controller_submit_vs_zenograph_block: bool
    controller_block_vs_zenograph_allow: bool
    selected_template_mismatch: bool
    current_template: str
    selected_template_id: str | None

    def to_dict(self) -> dict[str, object]:
        return {
            "disagreement": bool(self.disagreement),
            "controller_submit_vs_zenograph_block": bool(
                self.controller_submit_vs_zenograph_block
            ),
            "controller_block_vs_zenograph_allow": bool(
                self.controller_block_vs_zenograph_allow
            ),
            "selected_template_mismatch": bool(self.selected_template_mismatch),
            "current_template": str(self.current_template),
            "selected_template_id": self.selected_template_id,
        }


@dataclass(frozen=True)
class ZenoGraphAutoTraderShadowComparisonObservation:
    strategy_id: str
    current_epoch: int
    controller_tag: str
    controller_reason: str
    controller_explain: tuple[str, ...]
    zenograph_advisory: ZenoGraphAutoTraderAdvisoryObservation
    disagreement: ZenoGraphAutoTraderShadowDisagreement
    schema: str = ZENOGRAPH_AUTOTRADER_SHADOW_COMPARISON_SCHEMA

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "strategy_id": str(self.strategy_id),
            "current_epoch": int(self.current_epoch),
            "controller_tag": str(self.controller_tag),
            "controller_reason": str(self.controller_reason),
            "controller_explain": list(self.controller_explain),
            "zenograph_advisory": self.zenograph_advisory.to_dict(),
            "disagreement": self.disagreement.to_dict(),
        }


def build_zenograph_autotrader_shadow_comparison(
    *,
    strategy: StrategyIR,
    controller_state: AutoTraderControllerState,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    current_epoch: int,
    intent_deadline: int,
    chain_id: str,
    facts: Mapping[tuple[str, str], object] | None = None,
    signals: Mapping[str, object] | None = None,
    user_state: Mapping[str, object] | None = None,
    source_trust: ZGTrustTier = ZGTrustTier.ADVISORY,
    liquidity_state: str | None = None,
    controller_slippage_bps: int | None = None,
    tau_config: AutoTraderTauConfig | None = None,
) -> ZenoGraphAutoTraderShadowComparisonObservation:
    decision = evaluate_autotrader_quote_receipt(
        strategy=strategy,
        controller_state=controller_state,
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=int(current_epoch),
        intent_deadline=int(intent_deadline),
        slippage_bps=controller_slippage_bps,
        tau_config=tau_config,
    )
    advisory = build_zenograph_autotrader_advisory_observation(
        strategy=strategy,
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=int(current_epoch),
        chain_id=chain_id,
        facts=facts or {},
        signals=signals or {},
        user_state=user_state or {},
        source_trust=source_trust,
        liquidity_state=liquidity_state,
        tau_enabled=bool(tau_config.enabled) if tau_config is not None else False,
        include_krr=False,
    )
    current_template = strategy.template.value
    controller_submit = bool(decision.should_submit)
    selected_template_id = advisory.selected_template_id
    controller_submit_vs_zenograph_block = controller_submit and (
        not advisory.tactic_evaluation.admissible
    )
    controller_block_vs_zenograph_allow = (not controller_submit) and bool(
        advisory.tactic_evaluation.admissible
    )
    selected_template_mismatch = (
        selected_template_id is not None and selected_template_id != current_template
    )
    disagreement = ZenoGraphAutoTraderShadowDisagreement(
        disagreement=bool(
            controller_submit_vs_zenograph_block
            or controller_block_vs_zenograph_allow
            or selected_template_mismatch
        ),
        controller_submit_vs_zenograph_block=bool(controller_submit_vs_zenograph_block),
        controller_block_vs_zenograph_allow=bool(controller_block_vs_zenograph_allow),
        selected_template_mismatch=bool(selected_template_mismatch),
        current_template=current_template,
        selected_template_id=selected_template_id,
    )
    return ZenoGraphAutoTraderShadowComparisonObservation(
        strategy_id=str(strategy.strategy_id),
        current_epoch=int(current_epoch),
        controller_tag=decision.tag.value,
        controller_reason=str(decision.reason),
        controller_explain=tuple(str(item) for item in decision.explain),
        zenograph_advisory=advisory,
        disagreement=disagreement,
    )
