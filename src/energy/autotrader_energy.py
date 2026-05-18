"""Tiny advisory energy scorer for synthetic AutoTrader guard ordering."""

from __future__ import annotations

import json
from dataclasses import dataclass
from hashlib import sha256
from random import Random
from statistics import mean
from typing import Any, Iterable, Sequence

AUTOTRADER_FEATURE_NAMES: tuple[str, ...] = (
    "insufficient_balance_flag",
    "stale_signal_flag",
    "budget_violation_flag",
    "cooldown_violation_flag",
    "slippage_violation_flag",
    "route_violation_flag",
    "missing_capability_flag",
    "nonce_violation_flag",
    "expected_edge_norm",
    "signal_strength_norm",
    "liquidity_score_norm",
    "hedge_coverage_norm",
    "execution_urgency_norm",
    "drawdown_risk_norm",
    "slippage_bps_norm",
    "fee_bps_norm",
    "budget_used_norm",
    "price_deviation_norm",
    "position_pressure_norm",
    "nonce_age_norm",
)

_FLAG_NAMES = AUTOTRADER_FEATURE_NAMES[:8]


@dataclass(frozen=True)
class AutoTraderLinearEnergyModel:
    """Small pure-Python linear energy model for AutoTrader ranking receipts."""

    feature_names: tuple[str, ...]
    weights: tuple[float, ...]
    bias: float = 0.0

    def __post_init__(self) -> None:
        if len(self.feature_names) != len(self.weights):
            raise ValueError("feature_names and weights must have the same length")

    def energy(self, features: Sequence[float]) -> float:
        if len(features) != len(self.weights):
            raise ValueError("feature length does not match model")
        return float(
            sum(weight * float(value) for weight, value in zip(self.weights, features, strict=True))
            + self.bias
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/energy/autotrader_linear_ranker/v1",
            "model_type": "linear_energy",
            "feature_names": list(self.feature_names),
            "weights": list(self.weights),
            "bias": float(self.bias),
        }

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "AutoTraderLinearEnergyModel":
        if payload.get("schema") != "zenodex/energy/autotrader_linear_ranker/v1":
            raise ValueError("unsupported AutoTrader energy model schema")
        feature_names_obj = payload.get("feature_names")
        weights_obj = payload.get("weights")
        if not isinstance(feature_names_obj, list) or not all(isinstance(name, str) for name in feature_names_obj):
            raise TypeError("model feature_names must be a list of strings")
        if not isinstance(weights_obj, list) or not all(isinstance(weight, int | float) for weight in weights_obj):
            raise TypeError("model weights must be numeric")
        return cls(
            feature_names=tuple(feature_names_obj),
            weights=tuple(float(weight) for weight in weights_obj),
            bias=float(payload.get("bias", 0.0)),
        )


def initial_autotrader_hand_model() -> AutoTraderLinearEnergyModel:
    """Return the hand-coded advisory energy as a linear model."""

    weights = {name: 0.0 for name in AUTOTRADER_FEATURE_NAMES}
    for name in _FLAG_NAMES:
        weights[name] = 1_000.0
    weights["expected_edge_norm"] = -9.0
    weights["signal_strength_norm"] = -3.0
    weights["liquidity_score_norm"] = -1.5
    weights["hedge_coverage_norm"] = -1.0
    weights["execution_urgency_norm"] = -0.75
    weights["drawdown_risk_norm"] = 20.0
    weights["slippage_bps_norm"] = 8.0
    weights["fee_bps_norm"] = 4.0
    weights["budget_used_norm"] = 5.0
    weights["price_deviation_norm"] = 3.0
    weights["position_pressure_norm"] = 2.0
    weights["nonce_age_norm"] = 1.0
    return AutoTraderLinearEnergyModel(
        feature_names=AUTOTRADER_FEATURE_NAMES,
        weights=tuple(weights[name] for name in AUTOTRADER_FEATURE_NAMES),
    )


def hand_energy_from_autotrader_row(row: dict[str, Any]) -> float:
    return initial_autotrader_hand_model().energy(_features(row))


def generate_rows(
    *,
    seed: int,
    contexts: int,
    candidates_per_context: int,
    profile: str = "hard",
) -> list[dict[str, Any]]:
    """Generate synthetic AutoTrader action candidates with deterministic guard labels."""

    if contexts <= 0:
        raise ValueError("contexts must be positive")
    if candidates_per_context < 4:
        raise ValueError("candidates_per_context must be at least four")
    if profile not in {"easy", "hard"}:
        raise ValueError("profile must be 'easy' or 'hard'")

    rng = Random(seed)
    rows: list[dict[str, Any]] = []
    for context_index in range(contexts):
        batch_id = f"autotrader-{seed}-{context_index}"
        candidates = [
            _make_candidate(rng=rng, batch_id=batch_id, candidate_index=index, profile=profile)
            for index in range(candidates_per_context)
        ]
        valid_candidates = [candidate for candidate in candidates if candidate["label"]["valid"]]
        if not valid_candidates:
            candidate = candidates[0]
            _clear_flags(candidate)
            _refresh_label(candidate)
            valid_candidates = [candidate]
        winner_hash = max(
            valid_candidates,
            key=lambda row: (
                float(row["label"]["objective"]),
                str(row["candidate_hash"]),
            ),
        )["candidate_hash"]
        for candidate in candidates:
            candidate["label"]["is_winner"] = candidate["candidate_hash"] == winner_hash
            candidate["label"]["hand_energy"] = hand_energy_from_autotrader_row(candidate)
            rows.append(candidate)
    return rows


def train_autotrader_linear_ranker(
    rows: list[dict[str, Any]],
    *,
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    init: str = "hand",
) -> AutoTraderLinearEnergyModel:
    """Train a tiny pairwise hinge ranker; lower energy means check earlier."""

    if not rows:
        raise ValueError("training rows are empty")
    if epochs <= 0:
        raise ValueError("epochs must be positive")
    if learning_rate <= 0:
        raise ValueError("learning_rate must be positive")
    if margin <= 0:
        raise ValueError("margin must be positive")
    if init == "hand":
        weights = list(initial_autotrader_hand_model().weights)
    elif init == "zero":
        weights = [0.0 for _ in AUTOTRADER_FEATURE_NAMES]
    else:
        raise ValueError("init must be 'hand' or 'zero'")

    by_batch: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        if tuple(row["feature_names"]) != AUTOTRADER_FEATURE_NAMES:
            raise ValueError("AutoTrader feature schema mismatch")
        by_batch.setdefault(str(row["batch_id"]), []).append(row)

    rng = Random(seed)
    batches = list(by_batch.values())
    for _epoch in range(epochs):
        rng.shuffle(batches)
        for batch_rows in batches:
            ranked = sorted(batch_rows, key=_label_score, reverse=True)
            for good_index, good in enumerate(ranked):
                good_x = _features(good)
                for bad in ranked[good_index + 1 :]:
                    if _label_score(good) <= _label_score(bad):
                        continue
                    bad_x = _features(bad)
                    if margin + _dot(weights, good_x) - _dot(weights, bad_x) <= 0:
                        continue
                    pair_weight = _pair_weight(good=good, bad=bad)
                    for index, (good_value, bad_value) in enumerate(zip(good_x, bad_x, strict=True)):
                        weights[index] -= learning_rate * pair_weight * (good_value - bad_value)
    return AutoTraderLinearEnergyModel(
        feature_names=AUTOTRADER_FEATURE_NAMES,
        weights=tuple(weights),
    )


def evaluate_autotrader_rows(
    rows: list[dict[str, Any]],
    *,
    mode: str,
    model: AutoTraderLinearEnergyModel | None = None,
    seed: int = 20260518,
) -> dict[str, Any]:
    """Evaluate candidate ordering cost under deterministic guard-authoritative acceptance."""

    if mode not in {"random", "hand", "learned", "hybrid"}:
        raise ValueError("unknown AutoTrader evaluation mode")
    by_batch: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        by_batch.setdefault(str(row["batch_id"]), []).append(row)

    top_ks = (1, 5, 10, 25)
    hits = {k: 0 for k in top_ks}
    calls: list[int] = []
    invalid_top_1_count = 0
    invalid_accept_count = 0
    batches = 0
    candidate_counts: list[int] = []

    for batch_id, batch_rows in by_batch.items():
        winners = [row for row in batch_rows if row["label"]["is_winner"]]
        if not winners:
            continue
        batches += 1
        winner_hash = str(winners[0]["candidate_hash"])
        ordered = _ordered_rows(batch_rows, mode=mode, model=model, seed=seed)
        candidate_counts.append(len(ordered))
        if ordered and not bool(ordered[0]["label"]["valid"]):
            invalid_top_1_count += 1
        winner_position = next(
            index for index, row in enumerate(ordered, start=1) if str(row["candidate_hash"]) == winner_hash
        )
        calls.append(winner_position)
        for k in top_ks:
            if winner_position <= min(k, len(ordered)):
                hits[k] += 1
        accepted = _first_guard_accepted(ordered)
        if accepted is not None and not bool(accepted["label"]["valid"]):
            invalid_accept_count += 1

    return {
        "schema": "zenodex/energy/autotrader_evaluation_report/v1",
        "mode": mode,
        "batches": batches,
        "candidate_count_mean": mean(candidate_counts) if candidate_counts else 0.0,
        "top_1_recall": _ratio(hits[1], batches),
        "top_5_recall": _ratio(hits[5], batches),
        "top_10_recall": _ratio(hits[10], batches),
        "top_25_recall": _ratio(hits[25], batches),
        "mean_guard_calls": mean(calls) if calls else 0.0,
        "p95_guard_calls": _percentile(calls, 0.95),
        "p99_guard_calls": _percentile(calls, 0.99),
        "invalid_top_1_rate": _ratio(invalid_top_1_count, batches),
        "invalid_accept_count": invalid_accept_count,
        "policy_guards_authoritative": True,
        "scorer_authorizes_trade": False,
    }


def save_autotrader_model(model: AutoTraderLinearEnergyModel, path: str) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(model.to_dict(), handle, indent=2, sort_keys=True)
        handle.write("\n")


def load_autotrader_model(path: str) -> AutoTraderLinearEnergyModel:
    with open(path, "r", encoding="utf-8") as handle:
        payload = json.load(handle)
    return AutoTraderLinearEnergyModel.from_dict(payload)


def _make_candidate(
    *,
    rng: Random,
    batch_id: str,
    candidate_index: int,
    profile: str,
) -> dict[str, Any]:
    invalid_rate = 0.24 if profile == "hard" else 0.12
    flags = [1.0 if rng.random() < invalid_rate / len(_FLAG_NAMES) else 0.0 for _ in _FLAG_NAMES]
    expected_edge = _clip01(rng.betavariate(2.0, 2.2))
    signal_strength = _clip01(0.35 * expected_edge + 0.65 * rng.random())
    liquidity_score = _clip01(rng.betavariate(2.4, 1.8))
    hedge_coverage = _clip01(rng.betavariate(1.8, 2.0))
    execution_urgency = _clip01(rng.random())
    drawdown_risk = _clip01((0.45 if profile == "hard" else 0.3) * expected_edge + 0.55 * rng.random())
    slippage_bps = _clip01(0.55 * rng.random() + 0.35 * (1.0 - liquidity_score))
    fee_bps = _clip01(0.15 + 0.5 * rng.random())
    budget_used = _clip01(0.25 + 0.7 * rng.random())
    price_deviation = _clip01(0.55 * rng.random() + 0.25 * drawdown_risk)
    position_pressure = _clip01(0.7 * rng.random())
    nonce_age = _clip01(rng.random())
    features = flags + [
        expected_edge,
        signal_strength,
        liquidity_score,
        hedge_coverage,
        execution_urgency,
        drawdown_risk,
        slippage_bps,
        fee_bps,
        budget_used,
        price_deviation,
        position_pressure,
        nonce_age,
    ]
    row = {
        "schema": "zenodex/energy/autotrader_candidate_row/v1",
        "batch_id": batch_id,
        "candidate_id": f"{batch_id}-{candidate_index}",
        "candidate_hash": _candidate_hash(batch_id, candidate_index, features),
        "feature_names": list(AUTOTRADER_FEATURE_NAMES),
        "features": features,
        "label": {},
    }
    _refresh_label(row)
    return row


def _refresh_label(row: dict[str, Any]) -> None:
    features = _feature_map(row)
    valid = not any(features[name] > 0.0 for name in _FLAG_NAMES)
    objective = 0.0
    if valid:
        objective = (
            100.0 * features["expected_edge_norm"]
            + 30.0 * features["signal_strength_norm"]
            + 20.0 * features["liquidity_score_norm"]
            + 10.0 * features["hedge_coverage_norm"]
            + 8.0 * features["execution_urgency_norm"]
            - 35.0 * features["drawdown_risk_norm"]
            - 10.0 * features["slippage_bps_norm"]
            - 7.0 * features["fee_bps_norm"]
            - 12.0 * features["budget_used_norm"]
            - 4.0 * features["price_deviation_norm"]
            - 3.0 * features["position_pressure_norm"]
            - 1.0 * features["nonce_age_norm"]
        )
    row["label"] = {
        "valid": valid,
        "objective": objective,
        "is_winner": False,
    }


def _clear_flags(row: dict[str, Any]) -> None:
    features = list(row["features"])
    for index in range(len(_FLAG_NAMES)):
        features[index] = 0.0
    row["features"] = features


def _ordered_rows(
    rows: list[dict[str, Any]],
    *,
    mode: str,
    model: AutoTraderLinearEnergyModel | None,
    seed: int,
) -> list[dict[str, Any]]:
    if mode == "random":
        return sorted(
            rows,
            key=lambda row: sha256(
                f"{seed}:{row['batch_id']}:{row['candidate_hash']}".encode("utf-8")
            ).hexdigest(),
        )
    if mode == "hand":
        return sorted(rows, key=lambda row: (float(row["label"]["hand_energy"]), str(row["candidate_hash"])))
    if mode == "learned":
        if model is None:
            raise ValueError("learned mode requires a model")
        return sorted(rows, key=lambda row: (model.energy(_features(row)), str(row["candidate_hash"])))
    if mode == "hybrid":
        if model is None:
            raise ValueError("hybrid mode requires a model")
        return sorted(
            rows,
            key=lambda row: (
                _hard_guard_barrier(row),
                model.energy(_features(row)),
                str(row["candidate_hash"]),
            ),
        )
    raise ValueError("unknown AutoTrader mode")


def _first_guard_accepted(rows: Iterable[dict[str, Any]]) -> dict[str, Any] | None:
    for row in rows:
        if bool(row["label"]["valid"]):
            return row
    return None


def _hard_guard_barrier(row: dict[str, Any]) -> float:
    features = _feature_map(row)
    return 1_000_000.0 * sum(1 for name in _FLAG_NAMES if features[name] > 0.0)


def _label_score(row: dict[str, Any]) -> tuple[int, float, str]:
    label = row["label"]
    return (
        1 if bool(label["valid"]) else 0,
        float(label["objective"]),
        str(row["candidate_hash"]),
    )


def _pair_weight(*, good: dict[str, Any], bad: dict[str, Any]) -> float:
    if good["label"]["is_winner"]:
        return 4.0
    if bool(good["label"]["valid"]) and not bool(bad["label"]["valid"]):
        return 2.0
    return 1.0


def _features(row: dict[str, Any]) -> list[float]:
    return [float(value) for value in row["features"]]


def _feature_map(row: dict[str, Any]) -> dict[str, float]:
    return {
        str(name): float(value)
        for name, value in zip(row["feature_names"], row["features"], strict=True)
    }


def _candidate_hash(batch_id: str, candidate_index: int, features: Sequence[float]) -> str:
    payload = json.dumps(
        {
            "batch_id": batch_id,
            "candidate_index": candidate_index,
            "features": [round(float(value), 12) for value in features],
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return sha256(payload.encode("utf-8")).hexdigest()


def _dot(weights: Sequence[float], features: Sequence[float]) -> float:
    return sum(weight * value for weight, value in zip(weights, features, strict=True))


def _clip01(value: float) -> float:
    return min(1.0, max(0.0, float(value)))


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]
