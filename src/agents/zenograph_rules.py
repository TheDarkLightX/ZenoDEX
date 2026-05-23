from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Mapping

import yaml


class ZGTrustTier(Enum):
    UNTRUSTED = "untrusted"
    ADVISORY = "advisory"
    TRUSTED = "trusted"
    VERIFIED = "verified"


_TRUST_RANK: dict[ZGTrustTier, int] = {
    ZGTrustTier.UNTRUSTED: 0,
    ZGTrustTier.ADVISORY: 1,
    ZGTrustTier.TRUSTED: 2,
    ZGTrustTier.VERIFIED: 3,
}


@dataclass(frozen=True)
class ZGRuleCondition:
    predicate: str
    op: str
    value: object
    subject: str | None = None
    key: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.predicate, str) or not self.predicate.strip():
            raise ValueError("predicate must be a non-empty string")
        if not isinstance(self.op, str) or not self.op.strip():
            raise ValueError("op must be a non-empty string")
        object.__setattr__(self, "predicate", self.predicate.strip())
        object.__setattr__(self, "op", self.op.strip())
        if self.subject is not None and (not isinstance(self.subject, str) or not self.subject.strip()):
            raise ValueError("subject must be a non-empty string when present")
        if self.key is not None and (not isinstance(self.key, str) or not self.key.strip()):
            raise ValueError("key must be a non-empty string when present")


@dataclass(frozen=True)
class ZGRuleSpec:
    rule_id: str
    microtheory: str
    conditions: tuple[ZGRuleCondition, ...]
    decision: str
    reason: str
    value: tuple[str, ...] = field(default_factory=tuple)

    def __post_init__(self) -> None:
        if not isinstance(self.rule_id, str) or not self.rule_id.strip():
            raise ValueError("rule_id must be a non-empty string")
        if not isinstance(self.microtheory, str) or not self.microtheory.strip():
            raise ValueError("microtheory must be a non-empty string")
        if not self.conditions:
            raise ValueError("conditions must be non-empty")
        if not isinstance(self.decision, str) or not self.decision.strip():
            raise ValueError("decision must be a non-empty string")
        if not isinstance(self.reason, str) or not self.reason.strip():
            raise ValueError("reason must be a non-empty string")


@dataclass(frozen=True)
class ZGRuleMatch:
    rule_id: str
    microtheory: str
    decision: str
    reason: str
    value: tuple[str, ...]


@dataclass(frozen=True)
class ZGRuleContext:
    tactic_id: str
    facts: Mapping[tuple[str, str], object] = field(default_factory=dict)
    signals: Mapping[str, object] = field(default_factory=dict)
    user_state: Mapping[str, object] = field(default_factory=dict)
    source_trust: ZGTrustTier = ZGTrustTier.ADVISORY
    liquidity_state: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.tactic_id, str) or not self.tactic_id.strip():
            raise ValueError("tactic_id must be a non-empty string")
        if not isinstance(self.source_trust, ZGTrustTier):
            raise TypeError("source_trust must be a ZGTrustTier")
        if self.liquidity_state is not None and (not isinstance(self.liquidity_state, str) or not self.liquidity_state.strip()):
            raise ValueError("liquidity_state must be a non-empty string when present")


@dataclass(frozen=True)
class ZGTacticEvaluation:
    tactic_id: str
    admissible: bool
    matched_rules: tuple[ZGRuleMatch, ...]
    positive_reasons: tuple[str, ...]
    blocked_reasons: tuple[str, ...]
    allowed_templates_only: tuple[str, ...]
    explain: tuple[str, ...]


def load_rule_specs(path: str | Path) -> tuple[ZGRuleSpec, ...]:
    raw = yaml.safe_load(Path(path).read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("rule config must be a mapping")
    items = raw.get("rules")
    if not isinstance(items, list) or not items:
        raise ValueError("rule config must define a non-empty rules list")
    specs: list[ZGRuleSpec] = []
    for item in items:
        if not isinstance(item, dict):
            raise ValueError("each rule must be a mapping")
        conditions_raw = item.get("if_all")
        if not isinstance(conditions_raw, list) or not conditions_raw:
            raise ValueError("rule must define non-empty if_all")
        conditions = tuple(
            ZGRuleCondition(
                predicate=str(condition["predicate"]),
                op=str(condition["op"]),
                value=condition["value"],
                subject=condition.get("subject"),
                key=condition.get("key"),
            )
            for condition in conditions_raw
        )
        then_raw = item.get("then")
        if not isinstance(then_raw, dict):
            raise ValueError("rule must define a then mapping")
        value = then_raw.get("value", ())
        if isinstance(value, list):
            value_tuple = tuple(str(entry) for entry in value)
        elif value in ((), None):
            value_tuple = ()
        else:
            value_tuple = (str(value),)
        specs.append(
            ZGRuleSpec(
                rule_id=str(item["id"]),
                microtheory=str(item["microtheory"]),
                conditions=conditions,
                decision=str(then_raw["decision"]),
                reason=str(then_raw["reason"]),
                value=value_tuple,
            )
        )
    return tuple(specs)


def evaluate_rules_for_tactic(
    rules: tuple[ZGRuleSpec, ...],
    context: ZGRuleContext,
) -> ZGTacticEvaluation:
    matched: list[ZGRuleMatch] = []
    allowed_templates: set[str] | None = None
    for rule in rules:
        if all(_condition_matches(condition, context) for condition in rule.conditions):
            match = ZGRuleMatch(
                rule_id=rule.rule_id,
                microtheory=rule.microtheory,
                decision=rule.decision,
                reason=rule.reason,
                value=rule.value,
            )
            matched.append(match)
            if rule.decision == "allowed_templates_only":
                current = set(rule.value)
                allowed_templates = current if allowed_templates is None else allowed_templates.intersection(current)

    positive_reasons = tuple(match.reason for match in matched if match.decision == "tactic_admissible")
    blocked_reasons = list(match.reason for match in matched if match.decision == "invalidate_tactic")
    allowed_templates_tuple = tuple(sorted(allowed_templates)) if allowed_templates is not None else ()
    if allowed_templates is not None and context.tactic_id not in allowed_templates:
        blocked_reasons.append("not_in_allowed_templates_only")
    admissible = bool(positive_reasons) and not blocked_reasons
    explain = tuple(_build_explain(matched, admissible, context.tactic_id))
    return ZGTacticEvaluation(
        tactic_id=context.tactic_id,
        admissible=admissible,
        matched_rules=tuple(matched),
        positive_reasons=positive_reasons,
        blocked_reasons=tuple(blocked_reasons),
        allowed_templates_only=allowed_templates_tuple,
        explain=explain,
    )


def _build_explain(
    matched: list[ZGRuleMatch],
    admissible: bool,
    tactic_id: str,
) -> list[str]:
    out = [f"tactic={tactic_id}", f"admissible={1 if admissible else 0}"]
    for match in matched:
        out.append(f"{match.decision}:{match.reason}")
    return out


def _condition_matches(condition: ZGRuleCondition, context: ZGRuleContext) -> bool:
    left = _resolve_left_operand(condition, context)
    if condition.predicate == "source_trust":
        left_rank = _TRUST_RANK[context.source_trust]
        right_rank = _TRUST_RANK[ZGTrustTier(str(condition.value))]
        return _compare(left_rank, condition.op, right_rank)
    return _compare(left, condition.op, condition.value)


def _resolve_left_operand(condition: ZGRuleCondition, context: ZGRuleContext) -> object:
    if condition.predicate == "fact":
        return context.facts.get((str(condition.subject), str(condition.key)))
    if condition.predicate == "tactic":
        return context.tactic_id
    if condition.predicate == "signal":
        return context.signals.get(str(condition.key))
    if condition.predicate == "source_trust":
        return context.source_trust.value
    if condition.predicate == "liquidity_state":
        return context.liquidity_state
    if condition.predicate == "user_state":
        return context.user_state.get(str(condition.key))
    raise ValueError(f"unsupported predicate: {condition.predicate}")


def _compare(left: object, op: str, right: object) -> bool:
    if op == "eq":
        return left == right
    if op == "neq":
        return left != right
    if op == "in":
        if not isinstance(right, list):
            if not isinstance(right, tuple):
                raise TypeError("right side of 'in' must be a list or tuple")
            candidates = right
        else:
            candidates = tuple(right)
        return left in candidates
    if op == "ge":
        if not isinstance(left, int) or not isinstance(right, int):
            raise TypeError("ge requires integer operands")
        return left >= right
    raise ValueError(f"unsupported op: {op}")
