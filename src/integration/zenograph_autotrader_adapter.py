from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping

import yaml

from ..agents.krr_policy_advisor import AUTOTRADER_KRR_DEFAULT_BACKEND, advise_autotrader_krr
from ..agents.strategy_ir import StrategyIR
from ..agents.zenograph_microtheories import (
    ZGMicrotheorySpec,
    load_microtheory_specs,
    resolve_active_microtheories,
)
from ..agents.zenograph_rules import (
    ZGRuleContext,
    ZGTacticEvaluation,
    ZGTrustTier,
    evaluate_rules_for_tactic,
    load_rule_specs,
)
from ..agents.zenograph_selector import ZGTemplateCandidate, select_best_template
from ..integration.autotrader_signals import (
    AutoTraderObservationPacket,
    ExternalSignalObservation,
    build_autotrader_observation_packet,
    build_quote_receipt_signal_packet,
    build_wallet_capability_from_strategy,
)
from ..state.pools import PoolState

if TYPE_CHECKING:
    from .autotrader_signal_registry import ExternalSignalSourceRegistry


ZENOGRAPH_AUTOTRADER_ADVISORY_OBSERVATION_SCHEMA = (
    "zenodex/zenograph-autotrader-advisory-observation/v1"
)
_DEFAULT_MICROTHEORY_PATH = Path("config/zenograph/microtheories_v1.yaml")
_DEFAULT_RULE_PATH = Path("config/zenograph/rules_v1.yaml")
_DEFAULT_TEMPLATE_PATH = Path("config/zenograph/strategy_templates_v1.yaml")


@dataclass(frozen=True)
class ZenoGraphAutoTraderAdvisoryObservation:
    strategy_template: str
    active_microtheories: tuple[str, ...]
    tactic_evaluation: ZGTacticEvaluation
    selected_template_id: str | None
    selected_template_rank: int | None
    observation_packet: AutoTraderObservationPacket
    zenograph_flags: dict[str, bool]
    krr_advice: dict[str, Any] | None
    schema: str = ZENOGRAPH_AUTOTRADER_ADVISORY_OBSERVATION_SCHEMA

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "strategy_template": self.strategy_template,
            "active_microtheories": list(self.active_microtheories),
            "tactic_evaluation": {
                "tactic_id": self.tactic_evaluation.tactic_id,
                "admissible": bool(self.tactic_evaluation.admissible),
                "positive_reasons": list(self.tactic_evaluation.positive_reasons),
                "blocked_reasons": list(self.tactic_evaluation.blocked_reasons),
                "allowed_templates_only": list(self.tactic_evaluation.allowed_templates_only),
                "explain": list(self.tactic_evaluation.explain),
            },
            "selected_template_id": self.selected_template_id,
            "selected_template_rank": self.selected_template_rank,
            "observation_packet": self.observation_packet.to_dict(),
            "zenograph_flags": dict(self.zenograph_flags),
            "krr_advice": None if self.krr_advice is None else dict(self.krr_advice),
        }


def build_zenograph_autotrader_advisory_observation(
    *,
    strategy: StrategyIR,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    current_epoch: int,
    chain_id: str,
    facts: Mapping[tuple[str, str], object] | None = None,
    signals: Mapping[str, object] | None = None,
    user_state: Mapping[str, object] | None = None,
    source_trust: ZGTrustTier = ZGTrustTier.TRUSTED,
    liquidity_state: str | None = None,
    flags: Mapping[str, bool] | None = None,
    external_signals: tuple[ExternalSignalObservation, ...] = (),
    signal_source_registry: ExternalSignalSourceRegistry | None = None,
    tau_enabled: bool = False,
    include_krr: bool = True,
    krr_backend: str = AUTOTRADER_KRR_DEFAULT_BACKEND,
    microtheory_path: str | Path = _DEFAULT_MICROTHEORY_PATH,
    rule_path: str | Path = _DEFAULT_RULE_PATH,
    template_path: str | Path = _DEFAULT_TEMPLATE_PATH,
) -> ZenoGraphAutoTraderAdvisoryObservation:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(pools_by_id, Mapping):
        raise TypeError("pools_by_id must be a mapping")
    if not isinstance(receipt, Mapping):
        raise TypeError("receipt must be a mapping")

    microtheory_specs = load_microtheory_specs(microtheory_path)
    rule_specs = load_rule_specs(rule_path)
    template_ids = _load_template_ids(template_path)

    effective_flags = _default_flags(
        strategy=strategy,
        external_signals=external_signals,
        flags=flags or {},
        user_state=user_state or {},
        tau_enabled=tau_enabled,
    )
    active_microtheories = resolve_active_microtheories(microtheory_specs, effective_flags)

    primary_signal = build_quote_receipt_signal_packet(
        receipt=receipt,
        pools_by_id=pools_by_id,
        current_epoch=int(current_epoch),
    )
    wallet_capability = build_wallet_capability_from_strategy(
        strategy=strategy,
        chain_id=chain_id,
    )
    observation_packet = build_autotrader_observation_packet(
        primary_signal=primary_signal,
        wallet_capability=wallet_capability,
        external_signals=external_signals,
        signal_source_registry=signal_source_registry,
        tau_enabled=tau_enabled,
    )

    current_tactic = strategy.template.value
    tactic_evaluation = _evaluate_tactic(
        tactic_id=current_tactic,
        rules=rule_specs,
        context=_build_rule_context(
            tactic_id=current_tactic,
            facts=facts or {},
            signals=signals or {},
            user_state=user_state or {},
            source_trust=source_trust,
            liquidity_state=liquidity_state,
        ),
        active_microtheories=active_microtheories,
    )

    candidates = tuple(
        _evaluate_template_candidate(
            template_id=template_id,
            index=index,
            rules=rule_specs,
            facts=facts or {},
            signals=signals or {},
            user_state=user_state or {},
            source_trust=source_trust,
            liquidity_state=liquidity_state,
            active_microtheories=active_microtheories,
        )
        for index, template_id in enumerate(template_ids)
    )
    selected = select_best_template(candidates)

    krr_advice = None
    if include_krr:
        krr_advice = advise_autotrader_krr(
            strategy=strategy,
            phase="shadow",
            current_epoch=int(current_epoch),
            backend=krr_backend,
            tau_enabled=tau_enabled,
            observation_packet=observation_packet,
            quote_receipt=receipt,
            pools_by_id=pools_by_id,
        )

    return ZenoGraphAutoTraderAdvisoryObservation(
        strategy_template=current_tactic,
        active_microtheories=active_microtheories,
        tactic_evaluation=tactic_evaluation,
        selected_template_id=None if selected is None else selected.template_id,
        selected_template_rank=None if selected is None else int(selected.rank),
        observation_packet=observation_packet,
        zenograph_flags=dict(sorted(effective_flags.items())),
        krr_advice=krr_advice,
    )


def _build_rule_context(
    *,
    tactic_id: str,
    facts: Mapping[tuple[str, str], object],
    signals: Mapping[str, object],
    user_state: Mapping[str, object],
    source_trust: ZGTrustTier,
    liquidity_state: str | None,
) -> ZGRuleContext:
    return ZGRuleContext(
        tactic_id=tactic_id,
        facts=facts,
        signals=signals,
        user_state=user_state,
        source_trust=source_trust,
        liquidity_state=liquidity_state,
    )


def _evaluate_tactic(
    *,
    tactic_id: str,
    rules: tuple[Any, ...],
    context: ZGRuleContext,
    active_microtheories: tuple[str, ...],
) -> ZGTacticEvaluation:
    scoped_rules = tuple(rule for rule in rules if rule.microtheory in active_microtheories)
    return evaluate_rules_for_tactic(scoped_rules, context)


def _evaluate_template_candidate(
    *,
    template_id: str,
    index: int,
    rules: tuple[Any, ...],
    facts: Mapping[tuple[str, str], object],
    signals: Mapping[str, object],
    user_state: Mapping[str, object],
    source_trust: ZGTrustTier,
    liquidity_state: str | None,
    active_microtheories: tuple[str, ...],
) -> ZGTemplateCandidate:
    evaluation = _evaluate_tactic(
        tactic_id=template_id,
        rules=rules,
        context=_build_rule_context(
            tactic_id=template_id,
            facts=facts,
            signals=signals,
            user_state=user_state,
            source_trust=source_trust,
            liquidity_state=liquidity_state,
        ),
        active_microtheories=active_microtheories,
    )
    return ZGTemplateCandidate(
        template_id=template_id,
        rank=index,
        admissible=evaluation.admissible,
        explain=evaluation.explain,
    )


def _default_flags(
    *,
    strategy: StrategyIR,
    external_signals: tuple[ExternalSignalObservation, ...],
    flags: Mapping[str, bool],
    user_state: Mapping[str, object],
    tau_enabled: bool,
) -> dict[str, bool]:
    out = {
        "strategy_templates_present": True,
        "execution_path_active": True,
        "route_guard_required": True,
        "user_policy_present": True,
        "automation_enabled": True,
        "source_registry_present": False,
        "external_signals_present": bool(external_signals),
        "taxable_account_present": False,
        "tax_lot_state_present": False,
        "risk_policy_present": True,
        "drawdown_lock_active": bool(user_state.get("drawdown_lock", False)),
        "regime_signals_present": False,
        "volatility_signal_present": False,
        "tau_enabled": bool(tau_enabled),
        "policy_backend_tau": bool(strategy.policy_backend.value == "tau"),
    }
    for key, value in flags.items():
        out[str(key)] = bool(value)
    return out


def _load_template_ids(path: str | Path) -> tuple[str, ...]:
    raw = yaml.safe_load(Path(path).read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("template config must be a mapping")
    items = raw.get("templates")
    if not isinstance(items, list) or not items:
        raise ValueError("template config must define a non-empty templates list")
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if not isinstance(item, dict):
            raise ValueError("each template entry must be a mapping")
        template_id = str(item["id"]).strip()
        if not template_id or template_id in seen:
            continue
        seen.add(template_id)
        out.append(template_id)
    if not out:
        raise ValueError("template config did not yield any template ids")
    return tuple(out)
