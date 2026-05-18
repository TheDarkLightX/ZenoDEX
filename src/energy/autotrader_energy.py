"""Advisory energy ranking helpers for AutoTrader candidate actions.

The scorer in this module is research-only. It ranks bounded candidate actions
for later deterministic guard checks, and it never authorizes a trade by itself.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from hashlib import sha256
from math import log1p
from pathlib import Path
from typing import Any, Iterable, Sequence

from src.energy.upba_v2_energy_model import LinearEnergyModel

FEATURE_NAMES: tuple[str, ...] = (
    "kind_no_op",
    "kind_submit",
    "kind_reduce",
    "kind_reroute",
    "kind_hedge",
    "kind_wait",
    "requested_flag",
    "admissible_hint_flag",
    "wallet_capability_flag",
    "signal_provenance_flag",
    "route_sanity_flag",
    "oracle_freshness_flag",
    "execution_window_flag",
    "nonce_contiguous_flag",
    "kill_switch_flag",
    "budget_remaining_ratio",
    "window_budget_used_ratio",
    "lifetime_spent_ratio",
    "live_orders_ratio",
    "order_size_ratio",
    "trade_size_vs_budget_ratio",
    "quote_age_ratio",
    "slippage_ratio",
    "slippage_over_limit_ratio",
    "edge_ratio",
    "gas_ratio",
    "risk_ratio",
    "inventory_skew_ratio",
    "trust_ratio",
    "volatility_ratio",
    "guard_failure_count_norm",
    "policy_violation_flag",
    "positive_utility_hint",
    "safe_noop_flag",
    "candidate_priority_norm",
)

ACTION_KINDS: tuple[str, ...] = ("no_op", "submit", "reduce", "reroute", "hedge", "wait")
FEATURE_DIM = len(FEATURE_NAMES)


@dataclass(frozen=True)
class AutoTraderContext:
    """Synthetic AutoTrader observation and policy snapshot."""

    context_id: str
    budget_remaining: int
    window_budget: int
    window_budget_used: int
    lifetime_limit: int
    lifetime_spent: int
    live_orders: int
    max_live_orders: int
    max_quote_age_s: int
    max_slippage_bps: int
    volatility_bps: int
    inventory_skew_bps: int
    trust_bps: int
    kill_switch_active: bool
    session_nonce_expected: int


@dataclass(frozen=True)
class AutoTraderCandidate:
    """Bounded advisory action candidate."""

    candidate_id: str
    kind: str
    requested: bool
    admissible_hint: bool
    wallet_capability_ok: bool
    signal_provenance_ok: bool
    route_sanity_ok: bool
    oracle_freshness_ok: bool
    execution_window_ok: bool
    nonce: int
    order_size: int
    quote_age_s: int
    slippage_bps: int
    edge_bps: int
    gas_bps: int
    risk_bps: int
    action_priority: int


@dataclass(frozen=True)
class AutoTraderFeatureRecord:
    feature_names: tuple[str, ...]
    values: tuple[float, ...]
    raw: dict[str, Any]


@dataclass(frozen=True)
class AutoTraderVerificationResult:
    ok: bool
    error: str | None
    utility: int
    risk_penalty: int


def candidate_hash(candidate: AutoTraderCandidate) -> str:
    payload = json.dumps(candidate_to_dict(candidate), sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "sha256:" + sha256(payload).hexdigest()


def candidate_to_dict(candidate: AutoTraderCandidate) -> dict[str, Any]:
    return {
        "candidate_id": candidate.candidate_id,
        "kind": candidate.kind,
        "requested": candidate.requested,
        "admissible_hint": candidate.admissible_hint,
        "wallet_capability_ok": candidate.wallet_capability_ok,
        "signal_provenance_ok": candidate.signal_provenance_ok,
        "route_sanity_ok": candidate.route_sanity_ok,
        "oracle_freshness_ok": candidate.oracle_freshness_ok,
        "execution_window_ok": candidate.execution_window_ok,
        "nonce": candidate.nonce,
        "order_size": candidate.order_size,
        "quote_age_s": candidate.quote_age_s,
        "slippage_bps": candidate.slippage_bps,
        "edge_bps": candidate.edge_bps,
        "gas_bps": candidate.gas_bps,
        "risk_bps": candidate.risk_bps,
        "action_priority": candidate.action_priority,
    }


def verify_autotrader_candidate(
    context: AutoTraderContext,
    candidate: AutoTraderCandidate,
) -> AutoTraderVerificationResult:
    """Deterministic synthetic guard verdict for a candidate action."""

    if candidate.kind not in ACTION_KINDS:
        return AutoTraderVerificationResult(False, "unknown_action_kind", 0, 0)
    if not candidate.requested:
        return AutoTraderVerificationResult(False, "candidate_not_requested", 0, 0)
    if candidate.kind == "no_op":
        return AutoTraderVerificationResult(True, None, 0, 0)
    if context.kill_switch_active:
        return AutoTraderVerificationResult(False, "kill_switch_active", 0, 0)
    if not candidate.wallet_capability_ok:
        return AutoTraderVerificationResult(False, "wallet_capability_rejected", 0, 0)
    if not candidate.signal_provenance_ok:
        return AutoTraderVerificationResult(False, "signal_provenance_rejected", 0, 0)
    if not candidate.route_sanity_ok:
        return AutoTraderVerificationResult(False, "route_sanity_rejected", 0, 0)
    if not candidate.oracle_freshness_ok or candidate.quote_age_s > context.max_quote_age_s:
        return AutoTraderVerificationResult(False, "oracle_freshness_rejected", 0, 0)
    if not candidate.execution_window_ok:
        return AutoTraderVerificationResult(False, "execution_window_rejected", 0, 0)
    if candidate.nonce != context.session_nonce_expected:
        return AutoTraderVerificationResult(False, "nonce_not_contiguous", 0, 0)
    if candidate.order_size <= 0:
        return AutoTraderVerificationResult(False, "order_size_nonpositive", 0, 0)
    if candidate.order_size > context.budget_remaining:
        return AutoTraderVerificationResult(False, "budget_remaining_exceeded", 0, 0)
    if candidate.order_size + context.window_budget_used > context.window_budget:
        return AutoTraderVerificationResult(False, "window_budget_exceeded", 0, 0)
    if candidate.order_size + context.lifetime_spent > context.lifetime_limit:
        return AutoTraderVerificationResult(False, "lifetime_budget_exceeded", 0, 0)
    if context.live_orders >= context.max_live_orders:
        return AutoTraderVerificationResult(False, "max_live_orders_reached", 0, 0)
    if candidate.slippage_bps > context.max_slippage_bps:
        return AutoTraderVerificationResult(False, "slippage_limit_exceeded", 0, 0)

    utility = _candidate_utility(context, candidate)
    if utility <= 0:
        return AutoTraderVerificationResult(False, "nonpositive_risk_adjusted_utility", 0, 0)
    return AutoTraderVerificationResult(
        True,
        None,
        utility,
        candidate.risk_bps + context.volatility_bps + abs(context.inventory_skew_bps),
    )


def extract_autotrader_feature_record(
    context: AutoTraderContext,
    candidate: AutoTraderCandidate,
    *,
    include_verifier_label: bool = True,
) -> AutoTraderFeatureRecord:
    result = verify_autotrader_candidate(context, candidate) if include_verifier_label else None
    guard_failures = _guard_failure_count(context, candidate)
    policy_violation = int(guard_failures > 0 and candidate.kind != "no_op")
    utility_hint = _candidate_utility(context, candidate)
    values_by_name = {
        "kind_no_op": _flag(candidate.kind == "no_op"),
        "kind_submit": _flag(candidate.kind == "submit"),
        "kind_reduce": _flag(candidate.kind == "reduce"),
        "kind_reroute": _flag(candidate.kind == "reroute"),
        "kind_hedge": _flag(candidate.kind == "hedge"),
        "kind_wait": _flag(candidate.kind == "wait"),
        "requested_flag": _flag(candidate.requested),
        "admissible_hint_flag": _flag(candidate.admissible_hint),
        "wallet_capability_flag": _flag(candidate.wallet_capability_ok),
        "signal_provenance_flag": _flag(candidate.signal_provenance_ok),
        "route_sanity_flag": _flag(candidate.route_sanity_ok),
        "oracle_freshness_flag": _flag(candidate.oracle_freshness_ok),
        "execution_window_flag": _flag(candidate.execution_window_ok),
        "nonce_contiguous_flag": _flag(candidate.nonce == context.session_nonce_expected),
        "kill_switch_flag": _flag(context.kill_switch_active),
        "budget_remaining_ratio": _ratio(context.budget_remaining, context.window_budget),
        "window_budget_used_ratio": _ratio(context.window_budget_used, context.window_budget),
        "lifetime_spent_ratio": _ratio(context.lifetime_spent, context.lifetime_limit),
        "live_orders_ratio": _ratio(context.live_orders, max(1, context.max_live_orders)),
        "order_size_ratio": _ratio(candidate.order_size, context.window_budget),
        "trade_size_vs_budget_ratio": _ratio(candidate.order_size, context.budget_remaining),
        "quote_age_ratio": _ratio(candidate.quote_age_s, context.max_quote_age_s),
        "slippage_ratio": _ratio(candidate.slippage_bps, max(1, context.max_slippage_bps)),
        "slippage_over_limit_ratio": _ratio(
            max(0, candidate.slippage_bps - context.max_slippage_bps),
            max(1, context.max_slippage_bps),
        ),
        "edge_ratio": _clip(candidate.edge_bps / 1_000.0, -5.0, 5.0),
        "gas_ratio": _clip(candidate.gas_bps / 1_000.0, 0.0, 5.0),
        "risk_ratio": _clip(candidate.risk_bps / 1_000.0, 0.0, 5.0),
        "inventory_skew_ratio": _clip(abs(context.inventory_skew_bps) / 1_000.0, 0.0, 5.0),
        "trust_ratio": _ratio(context.trust_bps, 10_000),
        "volatility_ratio": _clip(context.volatility_bps / 1_000.0, 0.0, 5.0),
        "guard_failure_count_norm": _clip(guard_failures / 10.0, 0.0, 1.0),
        "policy_violation_flag": float(policy_violation),
        "positive_utility_hint": _flag(utility_hint > 0),
        "safe_noop_flag": _flag(candidate.kind == "no_op" and candidate.requested),
        "candidate_priority_norm": _clip(candidate.action_priority / 10.0, 0.0, 1.0),
    }
    raw = {
        "guard_failure_count": guard_failures,
        "policy_violation": policy_violation,
        "utility_hint": utility_hint,
        "verifier_ok": bool(result.ok) if result else None,
        "verifier_error": result.error if result else None,
        "objective_utility": int(result.utility) if result else 0,
        "risk_penalty": int(result.risk_penalty) if result else 0,
    }
    return AutoTraderFeatureRecord(
        feature_names=FEATURE_NAMES,
        values=tuple(float(values_by_name[name]) for name in FEATURE_NAMES),
        raw=raw,
    )


def hand_energy_from_record(record: AutoTraderFeatureRecord) -> float:
    features = dict(zip(record.feature_names, record.values, strict=True))
    invalid_pressure = (
        (1.0 - features["requested_flag"])
        + (1.0 - features["wallet_capability_flag"])
        + (1.0 - features["signal_provenance_flag"])
        + (1.0 - features["route_sanity_flag"])
        + (1.0 - features["oracle_freshness_flag"])
        + (1.0 - features["execution_window_flag"])
        + (1.0 - features["nonce_contiguous_flag"])
        + features["kill_switch_flag"]
        + features["slippage_over_limit_ratio"]
        + features["policy_violation_flag"]
    )
    return (
        1_000_000.0 * invalid_pressure
        + 10_000.0 * features["guard_failure_count_norm"]
        + 500.0 * features["slippage_ratio"]
        + 300.0 * features["risk_ratio"]
        + 250.0 * features["volatility_ratio"]
        + 100.0 * features["live_orders_ratio"]
        + 50.0 * features["quote_age_ratio"]
        - 1_000.0 * features["positive_utility_hint"]
        - 500.0 * features["edge_ratio"]
        - 50.0 * features["trust_ratio"]
        - 10.0 * features["safe_noop_flag"]
    )


def initial_autotrader_hand_model() -> LinearEnergyModel:
    weights = {name: 0.0 for name in FEATURE_NAMES}
    weights["requested_flag"] = -100_000.0
    weights["wallet_capability_flag"] = -100_000.0
    weights["signal_provenance_flag"] = -100_000.0
    weights["route_sanity_flag"] = -100_000.0
    weights["oracle_freshness_flag"] = -100_000.0
    weights["execution_window_flag"] = -100_000.0
    weights["nonce_contiguous_flag"] = -100_000.0
    weights["kill_switch_flag"] = 1_000_000.0
    weights["policy_violation_flag"] = 1_000_000.0
    weights["guard_failure_count_norm"] = 100_000.0
    weights["slippage_over_limit_ratio"] = 1_000_000.0
    weights["slippage_ratio"] = 500.0
    weights["risk_ratio"] = 300.0
    weights["volatility_ratio"] = 250.0
    weights["quote_age_ratio"] = 50.0
    weights["edge_ratio"] = -500.0
    weights["trust_ratio"] = -50.0
    weights["positive_utility_hint"] = -1_000.0
    weights["safe_noop_flag"] = -10.0
    return LinearEnergyModel(
        feature_names=FEATURE_NAMES,
        weights=tuple(float(weights[name]) for name in FEATURE_NAMES),
        bias=0.0,
    )


def rank_autotrader_candidates(
    context: AutoTraderContext,
    candidates: Sequence[AutoTraderCandidate],
    *,
    model: LinearEnergyModel | None = None,
) -> tuple[AutoTraderCandidate, ...]:
    def energy(candidate: AutoTraderCandidate) -> float:
        record = extract_autotrader_feature_record(context, candidate, include_verifier_label=False)
        if model is None:
            return hand_energy_from_record(record)
        return float(model.energy(record.values))

    return tuple(sorted(candidates, key=lambda candidate: (energy(candidate), candidate_hash(candidate))))


def deterministic_best_candidate(
    context: AutoTraderContext,
    candidates: Sequence[AutoTraderCandidate],
) -> AutoTraderCandidate | None:
    valid: list[tuple[AutoTraderCandidate, AutoTraderVerificationResult]] = []
    for candidate in candidates:
        result = verify_autotrader_candidate(context, candidate)
        if result.ok:
            valid.append((candidate, result))
    if not valid:
        return None
    return max(
        valid,
        key=lambda item: (
            item[1].utility,
            -item[1].risk_penalty,
            -item[0].action_priority,
            candidate_hash(item[0]),
        ),
    )[0]


def rows_for_candidate_set(
    context: AutoTraderContext,
    candidates: Sequence[AutoTraderCandidate],
) -> list[dict[str, Any]]:
    winner = deterministic_best_candidate(context, candidates)
    winner_hash = candidate_hash(winner) if winner is not None else None
    rows: list[dict[str, Any]] = []
    for index, candidate in enumerate(candidates):
        record = extract_autotrader_feature_record(context, candidate, include_verifier_label=True)
        row = {
            "schema": "zenodex/energy/autotrader_dataset_row/v1",
            "source": "synthetic",
            "context_id": context.context_id,
            "candidate_index": index,
            "candidate_hash": candidate_hash(candidate),
            "candidate_kind": candidate.kind,
            "feature_names": list(FEATURE_NAMES),
            "features": list(record.values),
            "label": {
                "valid": bool(record.raw["verifier_ok"]),
                "objective_utility": int(record.raw["objective_utility"]),
                "risk_penalty": int(record.raw["risk_penalty"]),
                "verifier_error": record.raw["verifier_error"],
                "hand_energy": hand_energy_from_record(record),
                "is_winner": candidate_hash(candidate) == winner_hash,
            },
        }
        rows.append(row)
    return rows


def save_jsonl(rows: Iterable[dict[str, Any]], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")


def _candidate_utility(context: AutoTraderContext, candidate: AutoTraderCandidate) -> int:
    size_bonus = int(log1p(max(0, candidate.order_size)) * 10)
    trust_bonus = context.trust_bps // 400
    return (
        candidate.edge_bps
        - candidate.slippage_bps
        - candidate.gas_bps
        - candidate.risk_bps
        - context.volatility_bps // 4
        - abs(context.inventory_skew_bps) // 5
        - max(0, candidate.quote_age_s - context.max_quote_age_s // 2) // 4
        + size_bonus
        + trust_bonus
    )


def _guard_failure_count(context: AutoTraderContext, candidate: AutoTraderCandidate) -> int:
    failures = 0
    failures += int(not candidate.requested)
    failures += int(context.kill_switch_active and candidate.kind != "no_op")
    failures += int(candidate.kind not in ACTION_KINDS)
    failures += int(candidate.kind != "no_op" and not candidate.wallet_capability_ok)
    failures += int(candidate.kind != "no_op" and not candidate.signal_provenance_ok)
    failures += int(candidate.kind != "no_op" and not candidate.route_sanity_ok)
    failures += int(candidate.kind != "no_op" and (not candidate.oracle_freshness_ok or candidate.quote_age_s > context.max_quote_age_s))
    failures += int(candidate.kind != "no_op" and not candidate.execution_window_ok)
    failures += int(candidate.kind != "no_op" and candidate.nonce != context.session_nonce_expected)
    failures += int(candidate.kind != "no_op" and candidate.order_size > context.budget_remaining)
    failures += int(candidate.kind != "no_op" and candidate.order_size + context.window_budget_used > context.window_budget)
    failures += int(candidate.kind != "no_op" and candidate.order_size + context.lifetime_spent > context.lifetime_limit)
    failures += int(candidate.kind != "no_op" and context.live_orders >= context.max_live_orders)
    failures += int(candidate.kind != "no_op" and candidate.slippage_bps > context.max_slippage_bps)
    return failures


def _ratio(numerator: int | float, denominator: int | float) -> float:
    return _clip(float(numerator) / max(1.0, float(denominator)), 0.0, 5.0)


def _clip(value: float, low: float, high: float) -> float:
    return min(high, max(low, float(value)))


def _flag(value: bool) -> float:
    return 1.0 if value else 0.0
