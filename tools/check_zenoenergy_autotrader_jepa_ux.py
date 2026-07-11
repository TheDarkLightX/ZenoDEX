#!/usr/bin/env python3
"""Check source-level ZenoJEPA AutoTrader scoring and UX receipts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from statistics import mean
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy import (  # noqa: E402
    AUTOTRADER_CONTROL_IDS,
    apply_autotrader_control,
    autotrader_feature_map,
    build_autotrader_advisory_card,
    build_autotrader_batch_ux,
    default_autotrader_jepa_model,
    evaluate_autotrader_rows,
    evaluate_autotrader_future_aware_rows,
    generate_rows,
    model_fingerprint,
    project_autotrader_future_stress,
    score_autotrader_future_tension,
    train_autotrader_linear_ranker,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260531)
    parser.add_argument("--train-seed", type=int, default=20260522)
    parser.add_argument("--train-contexts", type=int, default=1200)
    parser.add_argument("--contexts", type=int, default=96)
    parser.add_argument("--candidates-per-context", type=int, default=12)
    parser.add_argument("--future-weight", type=float, default=0.1)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = check_zenoenergy_autotrader_jepa_ux(
        seed=args.seed,
        train_seed=args.train_seed,
        train_contexts=args.train_contexts,
        contexts=args.contexts,
        candidates_per_context=args.candidates_per_context,
        future_weight=args.future_weight,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown(report), encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def check_zenoenergy_autotrader_jepa_ux(
    *,
    seed: int = 20260531,
    train_seed: int = 20260522,
    train_contexts: int = 1200,
    contexts: int = 96,
    candidates_per_context: int = 12,
    future_weight: float = 0.1,
) -> dict[str, Any]:
    if contexts <= 0:
        raise ValueError("contexts must be positive")
    train_rows = generate_rows(
        seed=train_seed,
        contexts=train_contexts,
        candidates_per_context=max(16, candidates_per_context),
        profile="hard",
    )
    rows = generate_rows(
        seed=seed,
        contexts=contexts,
        candidates_per_context=candidates_per_context,
        profile="hard",
    )
    ranker = train_autotrader_linear_ranker(
        train_rows,
        epochs=6,
        learning_rate=0.001,
        margin=1.0,
        seed=train_seed,
        init="hand",
    )
    model = default_autotrader_jepa_model()
    hand_report = evaluate_autotrader_rows(rows, mode="hand", seed=seed)
    learned_report = evaluate_autotrader_rows(rows, mode="hybrid", model=ranker, seed=seed)
    hand_future_report = evaluate_autotrader_future_aware_rows(
        rows,
        model=model,
        future_weight=future_weight,
    )
    future_report = evaluate_autotrader_future_aware_rows(
        rows,
        model=model,
        base_model=ranker,
        future_weight=future_weight,
    )
    balanced = _balanced_features()
    fragile = _fragile_features()
    blocked = _blocked_features()
    balanced_tension = score_autotrader_future_tension(balanced, model=model)
    fragile_tension = score_autotrader_future_tension(fragile, model=model)
    blocked_card = build_autotrader_advisory_card(
        blocked,
        candidate_id="blocked-stale-route",
        model=model,
    )
    fragile_card = build_autotrader_advisory_card(
        fragile,
        candidate_id="fragile-but-policy-valid",
        model=model,
    )
    first_batch = [row for row in rows if row["batch_id"] == rows[0]["batch_id"]]
    batch_ux = build_autotrader_batch_ux(first_batch, model=model, max_cards=3)
    future_prediction = _future_prediction_metrics(rows, model=model)
    control_metrics = _control_metrics(rows, model=model)
    warning_metrics = _warning_metrics(rows, model=model)
    research_inputs = _research_inputs()
    efficiency = _efficiency_profile(model=model)
    authority_ok = (
        future_report["invalid_accept_count"] == 0
        and future_report["policy_guards_authoritative"] is True
        and future_report["model_authorizes_trade"] is False
        and blocked_card["authority"]["ux_card_authorizes_trade"] is False
        and fragile_card["authority"]["future_tension_authorizes_trade"] is False
    )
    future_differentiates = fragile_tension > balanced_tension
    ranking_guardrail = (
        future_report["top_5_recall"] >= 0.99
        and future_report["mean_guard_calls"] <= 1.10
        and future_report["invalid_accept_count"] == 0
    )
    ux_explains = (
        blocked_card["status"] == "blocked_by_policy_guard"
        and "stale signal or quote" in blocked_card["blocked_reasons"]
        and any("Refresh oracle" in item for item in blocked_card["suggested_controls"])
        and fragile_card["status"] in {"needs_risk_review", "policy_valid_with_caution"}
        and any(
            float(effect["future_tension_delta"]) < 0.0
            for effect in fragile_card["control_effects"]
        )
        and bool(batch_ux["cards"])
    )
    prediction_ok = (
        future_prediction["later_policy_failure_auc"] >= 0.80
        and future_prediction["future_failure_tension_delta_mean"] > 0.25
        and future_prediction["stress_correlations"]["drawdown_stress"] >= 0.55
        and future_prediction["stress_correlations"]["slippage_stress"] >= 0.55
        and future_prediction["stress_correlations"]["budget_stress"] >= 0.55
    )
    controls_ok = (
        control_metrics["safer_counterfactual_reduction_rate"] >= 0.95
        and control_metrics["suggested_control_best_reduction_rate"] >= 0.95
        and control_metrics["suggested_control_authority_ok"] is True
    )
    warnings_ok = (
        warning_metrics["blocked_status_match_rate"] == 1.0
        and warning_metrics["future_warning_match_rate"] >= 0.80
        and warning_metrics["ux_card_authorizes_trade_count"] == 0
    )
    ok = (
        authority_ok
        and future_differentiates
        and ranking_guardrail
        and ux_explains
        and prediction_ok
        and controls_ok
        and warnings_ok
        and bool(research_inputs["ok"])
        and bool(efficiency["ok"])
    )
    return {
        "schema": "zenodex/energy/autotrader_jepa_ux_receipt/v1",
        "ok": ok,
        "decision": "research_only_future_aware_autotrader_ux",
        "train_seed": train_seed,
        "train_contexts": train_contexts,
        "seed": seed,
        "contexts": contexts,
        "candidates_per_context": candidates_per_context,
        "future_weight": future_weight,
        "model": {
            "schema": model.to_dict()["schema"],
            "fingerprint": model_fingerprint(model),
            "state_feature_names": list(model.state_feature_names),
            "action_feature_names": list(model.action_feature_names),
            "latent_names": list(model.latent_names),
        },
        "hand_evaluation": hand_report,
        "learned_evaluation": learned_report,
        "hand_future_aware_evaluation": hand_future_report,
        "future_aware_evaluation": future_report,
        "ranking": {
            "learned_future_top_5_recall": future_report["top_5_recall"],
            "learned_future_top_1_recall": future_report["top_1_recall"],
            "learned_future_mean_guard_calls": future_report["mean_guard_calls"],
            "hand_mean_guard_calls": hand_report["mean_guard_calls"],
            "learned_mean_guard_calls": learned_report["mean_guard_calls"],
            "hand_future_top_5_recall": hand_future_report["top_5_recall"],
            "ranking_guardrail_passed": ranking_guardrail,
        },
        "future_risk_prediction": future_prediction,
        "control_metrics": control_metrics,
        "warning_metrics": warning_metrics,
        "research_inputs": research_inputs,
        "efficiency": efficiency,
        "scenario_scores": {
            "balanced_future_tension": balanced_tension,
            "fragile_future_tension": fragile_tension,
            "future_tension_differentiates_fragility": future_differentiates,
        },
        "ux": {
            "blocked_card": blocked_card,
            "fragile_card": fragile_card,
            "batch_ux": batch_ux,
            "ux_explains_status_and_controls": ux_explains,
        },
        "safety_contract": {
            "deterministic_policy_guards_authoritative": True,
            "deterministic_verifier_authoritative": True,
            "model_authorizes_trade": False,
            "future_tension_authorizes_trade": False,
            "ux_card_authorizes_trade": False,
            "authority_ok": authority_ok,
        },
        "positive_knowledge": (
            "Source-level JEPA future tension predicts synthetic later policy failures "
            "and stress axes well enough to drive user-facing warnings and safer "
            "counterfactual controls while deterministic policy guards remain authoritative."
        ),
        "negative_knowledge": [
            "Future-tension UX is a warning and proposal-shaping feature, not execution authority.",
            "JEPA-over-hand ordering is weaker than learned AutoTraderEnergy; use learned ranking as the ordering guardrail.",
            "Synthetic UX receipts do not prove live AutoTrader profitability.",
            "Production use still needs source-manifested real shadow replay and wallet-level policy gates.",
        ],
    }


def _future_prediction_metrics(
    rows: Sequence[Mapping[str, Any]],
    *,
    model: Any,
) -> dict[str, Any]:
    tensions: list[float] = []
    later_failure_labels: list[bool] = []
    slippage: list[float] = []
    budget: list[float] = []
    drawdown: list[float] = []
    operational: list[float] = []
    for row in rows:
        features = row["features"]
        tension = score_autotrader_future_tension(features, model=model)
        stress = project_autotrader_future_stress(features)
        tensions.append(tension)
        later_failure_labels.append(bool(stress["any_later_policy_failure"]))
        slippage.append(float(stress["slippage_stress"]))
        budget.append(float(stress["budget_stress"]))
        drawdown.append(float(stress["drawdown_stress"]))
        operational.append(float(stress["operational_stress"]))

    positive = [
        tension
        for tension, label in zip(tensions, later_failure_labels, strict=True)
        if label
    ]
    negative = [
        tension
        for tension, label in zip(tensions, later_failure_labels, strict=True)
        if not label
    ]
    positive_mean = mean(positive) if positive else 0.0
    negative_mean = mean(negative) if negative else 0.0
    return {
        "schema": "zenodex/energy/autotrader_future_risk_prediction/v1",
        "sample_count": len(tensions),
        "later_policy_failure_count": len(positive),
        "non_failure_count": len(negative),
        "later_policy_failure_auc": _binary_auc(tensions, later_failure_labels),
        "future_failure_tension_mean": positive_mean,
        "future_non_failure_tension_mean": negative_mean,
        "future_failure_tension_delta_mean": positive_mean - negative_mean,
        "stress_correlations": {
            "slippage_stress": _pearson(tensions, slippage),
            "budget_stress": _pearson(tensions, budget),
            "drawdown_stress": _pearson(tensions, drawdown),
            "operational_stress": _pearson(tensions, operational),
        },
        "model_authorizes_trade": False,
    }


def _control_metrics(
    rows: Sequence[Mapping[str, Any]],
    *,
    model: Any,
    max_rows: int = 256,
) -> dict[str, Any]:
    risk_rows = [
        row
        for row in rows
        if project_autotrader_future_stress(row["features"])["any_later_policy_failure"]
        or score_autotrader_future_tension(row["features"], model=model) >= 2.5
    ][:max_rows]
    safer_control_ids = ("improve_route", "reduce_notional", "slow_execution", "wait_budget_recovery")
    safer_deltas: list[float] = []
    per_control: dict[str, dict[str, float]] = {}
    for control_id in safer_control_ids:
        deltas = [
            _control_tension_delta(row["features"], control_id, model=model)
            for row in risk_rows
        ]
        safer_deltas.extend(deltas)
        per_control[control_id] = {
            "sample_count": len(deltas),
            "mean_delta": mean(deltas) if deltas else 0.0,
            "reduction_rate": _ratio(sum(1 for delta in deltas if delta < 0.0), len(deltas)),
        }

    suggested_cards = [
        build_autotrader_advisory_card(
            row["features"],
            candidate_id=str(row.get("candidate_id", row.get("candidate_hash", "row"))),
            model=model,
        )
        for row in risk_rows
    ]
    best_suggested_deltas: list[float] = []
    suggested_authority_ok = True
    control_effect_count = 0
    for card in suggested_cards:
        effects = list(card.get("control_effects", ()))
        if not effects:
            continue
        control_effect_count += len(effects)
        best_suggested_deltas.append(
            min(float(effect["future_tension_delta"]) for effect in effects)
        )
        if any(bool(effect.get("control_authorizes_trade", True)) for effect in effects):
            suggested_authority_ok = False

    return {
        "schema": "zenodex/energy/autotrader_control_counterfactuals/v1",
        "risk_row_count": len(risk_rows),
        "safer_counterfactual_count": len(safer_deltas),
        "safer_counterfactual_mean_delta": mean(safer_deltas) if safer_deltas else 0.0,
        "safer_counterfactual_reduction_rate": _ratio(
            sum(1 for delta in safer_deltas if delta < 0.0),
            len(safer_deltas),
        ),
        "per_control": per_control,
        "suggested_card_count": len(suggested_cards),
        "suggested_control_effect_count": control_effect_count,
        "suggested_control_best_mean_delta": (
            mean(best_suggested_deltas) if best_suggested_deltas else 0.0
        ),
        "suggested_control_best_reduction_rate": _ratio(
            sum(1 for delta in best_suggested_deltas if delta < 0.0),
            len(best_suggested_deltas),
        ),
        "suggested_control_authority_ok": suggested_authority_ok,
        "available_control_ids": list(AUTOTRADER_CONTROL_IDS),
        "model_authorizes_trade": False,
    }


def _warning_metrics(
    rows: Sequence[Mapping[str, Any]],
    *,
    model: Any,
    max_rows: int = 512,
) -> dict[str, Any]:
    checked = list(rows[:max_rows])
    blocked_matches = 0
    future_positive_valid = 0
    future_warning_matches = 0
    ux_card_authorizes_trade_count = 0
    status_counts: dict[str, int] = {}
    for row in checked:
        label = row["label"]
        card = build_autotrader_advisory_card(
            row["features"],
            candidate_id=str(row.get("candidate_id", row.get("candidate_hash", "row"))),
            model=model,
        )
        status = str(card["status"])
        status_counts[status] = status_counts.get(status, 0) + 1
        if (not bool(label["valid"])) == (status == "blocked_by_policy_guard"):
            blocked_matches += 1
        if bool(card["authority"]["ux_card_authorizes_trade"]):
            ux_card_authorizes_trade_count += 1
        future_stress = project_autotrader_future_stress(row["features"])
        if bool(label["valid"]) and bool(future_stress["any_later_policy_failure"]):
            future_positive_valid += 1
            if status in {"needs_risk_review", "policy_valid_with_caution"}:
                future_warning_matches += 1

    return {
        "schema": "zenodex/energy/autotrader_ux_warning_alignment/v1",
        "sample_count": len(checked),
        "blocked_status_match_count": blocked_matches,
        "blocked_status_match_rate": _ratio(blocked_matches, len(checked)),
        "future_positive_valid_count": future_positive_valid,
        "future_warning_match_count": future_warning_matches,
        "future_warning_match_rate": _ratio(
            future_warning_matches,
            future_positive_valid,
        ),
        "ux_card_authorizes_trade_count": ux_card_authorizes_trade_count,
        "status_counts": status_counts,
        "deterministic_policy_guard_authoritative": True,
        "model_authorizes_trade": False,
    }


def _research_inputs() -> dict[str, Any]:
    inputs = {
        "experiments_ideas": ROOT / "experiments/ideas.md",
        "experiments_breakthroughs": ROOT / "experiments/breakthroughs.md",
    }
    artifacts: dict[str, dict[str, Any]] = {}
    for name, path in inputs.items():
        text = path.read_text(encoding="utf-8")
        artifacts[name] = {
            "path": str(path.relative_to(ROOT)),
            "sha256": _sha256_text(text),
            "byte_length": len(text.encode("utf-8")),
        }
    ideas_text = inputs["experiments_ideas"].read_text(encoding="utf-8").lower()
    breakthroughs_text = inputs["experiments_breakthroughs"].read_text(encoding="utf-8").lower()
    return {
        "schema": "zenodex/energy/autotrader_jepa_research_inputs/v1",
        "ok": (
            "canonical" in breakthroughs_text
            and "hypergraph" in ideas_text
            and "negative" in breakthroughs_text
        ),
        "artifacts": artifacts,
        "incorporated_lessons": [
            "Use canonical feature projections before JEPA scoring.",
            "Treat sequence-sensitive winner roots as negative knowledge for UPBA-style semantics.",
            "Keep ZenoEnergy advisory: models propose warnings and controls; guards decide execution.",
        ],
    }


def _efficiency_profile(*, model: Any) -> dict[str, Any]:
    model_payload = model.to_dict()
    parameter_count = (
        sum(len(row) for row in model_payload["w_encoder"])
        + sum(len(row) for row in model_payload["w_predictor"])
        + len(model_payload["bias"])
    )
    return {
        "schema": "zenodex/energy/autotrader_jepa_efficiency_profile/v1",
        "parameter_count": parameter_count,
        "runtime_dependency_profile": "pure_python_no_runtime_ml_dependency",
        "score_path": "linear_encoder_plus_linear_predictor",
        "ok": parameter_count <= 128,
        "model_authorizes_trade": False,
    }


def _control_tension_delta(
    features: Mapping[str, float] | Sequence[float],
    control_id: str,
    *,
    model: Any,
) -> float:
    before = score_autotrader_future_tension(features, model=model)
    after_features = apply_autotrader_control(features, control_id)
    after = score_autotrader_future_tension(after_features, model=model)
    return after - before


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _binary_auc(scores: Sequence[float], labels: Sequence[bool]) -> float:
    positives = [float(score) for score, label in zip(scores, labels, strict=True) if label]
    negatives = [float(score) for score, label in zip(scores, labels, strict=True) if not label]
    if not positives or not negatives:
        return 0.5
    wins = 0.0
    for positive in positives:
        for negative in negatives:
            if positive > negative:
                wins += 1.0
            elif positive == negative:
                wins += 0.5
    return wins / (len(positives) * len(negatives))


def _pearson(xs: Sequence[float], ys: Sequence[float]) -> float:
    if len(xs) != len(ys) or len(xs) < 2:
        return 0.0
    x_mean = mean(float(value) for value in xs)
    y_mean = mean(float(value) for value in ys)
    centered = [
        (float(x) - x_mean, float(y) - y_mean)
        for x, y in zip(xs, ys, strict=True)
    ]
    numerator = sum(x * y for x, y in centered)
    x_norm = sum(x * x for x, _y in centered)
    y_norm = sum(y * y for _x, y in centered)
    if x_norm == 0.0 or y_norm == 0.0:
        return 0.0
    return numerator / ((x_norm * y_norm) ** 0.5)


def _sha256_text(text: str) -> str:
    import hashlib

    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _balanced_features() -> dict[str, float]:
    return autotrader_feature_map(
        {
            "expected_edge_norm": 0.86,
            "signal_strength_norm": 0.82,
            "liquidity_score_norm": 0.9,
            "hedge_coverage_norm": 0.8,
            "execution_urgency_norm": 0.35,
            "drawdown_risk_norm": 0.15,
            "slippage_bps_norm": 0.12,
            "fee_bps_norm": 0.2,
            "budget_used_norm": 0.18,
            "price_deviation_norm": 0.1,
            "position_pressure_norm": 0.1,
            "nonce_age_norm": 0.1,
        }
    )


def _fragile_features() -> dict[str, float]:
    features = _balanced_features()
    features.update(
        {
            "liquidity_score_norm": 0.18,
            "drawdown_risk_norm": 0.82,
            "execution_urgency_norm": 0.88,
            "slippage_bps_norm": 0.78,
            "budget_used_norm": 0.88,
            "price_deviation_norm": 0.72,
            "position_pressure_norm": 0.81,
        }
    )
    return features


def _blocked_features() -> dict[str, float]:
    features = _fragile_features()
    features.update(
        {
            "stale_signal_flag": 1.0,
            "route_violation_flag": 1.0,
            "slippage_violation_flag": 1.0,
        }
    )
    return autotrader_feature_map(features)


def _markdown(report: dict[str, Any]) -> str:
    eval_report = report["future_aware_evaluation"]
    ranking = report["ranking"]
    scenario = report["scenario_scores"]
    prediction = report["future_risk_prediction"]
    controls = report["control_metrics"]
    warnings = report["warning_metrics"]
    correlations = prediction["stress_correlations"]
    lines = [
        "# ZenoEnergy AutoTrader JEPA UX",
        "",
        "```text",
        f"ok: {str(report['ok']).lower()}",
        f"decision: {report['decision']}",
        f"contexts: {report['contexts']}",
        f"future_weight: {report['future_weight']}",
        f"later_policy_failure_auc: {prediction['later_policy_failure_auc']:.6f}",
        f"future_failure_tension_delta_mean: {prediction['future_failure_tension_delta_mean']:.6f}",
        f"slippage_stress_correlation: {correlations['slippage_stress']:.6f}",
        f"budget_stress_correlation: {correlations['budget_stress']:.6f}",
        f"drawdown_stress_correlation: {correlations['drawdown_stress']:.6f}",
        f"safer_counterfactual_reduction_rate: {controls['safer_counterfactual_reduction_rate']:.6f}",
        f"suggested_control_best_reduction_rate: {controls['suggested_control_best_reduction_rate']:.6f}",
        f"blocked_status_match_rate: {warnings['blocked_status_match_rate']:.6f}",
        f"future_warning_match_rate: {warnings['future_warning_match_rate']:.6f}",
        f"mean_guard_calls: {eval_report['mean_guard_calls']:.6f}",
        f"top_1_recall: {eval_report['top_1_recall']:.6f}",
        f"top_5_recall: {eval_report['top_5_recall']:.6f}",
        f"invalid_accept_count: {eval_report['invalid_accept_count']}",
        f"balanced_future_tension: {scenario['balanced_future_tension']:.6f}",
        f"fragile_future_tension: {scenario['fragile_future_tension']:.6f}",
        "```",
        "",
        "The UX layer presents advisory risk and explanation cards. It does not authorize execution; deterministic policy guards remain authoritative.",
        "",
        "## UX Checks",
        "",
        "| check | status |",
        "| --- | --- |",
        f"| future tension predicts later policy failures | {'pass' if prediction['later_policy_failure_auc'] >= 0.80 else 'fail'} |",
        f"| future tension predicts drawdown, slippage, and budget stress | {'pass' if min(correlations['drawdown_stress'], correlations['slippage_stress'], correlations['budget_stress']) >= 0.55 else 'fail'} |",
        f"| safer counterfactual controls lower future tension | {'pass' if controls['safer_counterfactual_reduction_rate'] >= 0.95 else 'fail'} |",
        f"| suggested controls lower future tension | {'pass' if controls['suggested_control_best_reduction_rate'] >= 0.95 else 'fail'} |",
        f"| UX warnings match deterministic guard outcomes | {'pass' if warnings['blocked_status_match_rate'] == 1.0 else 'fail'} |",
        f"| ranking remains a guardrail, top-5 recall at least 0.99 | {'pass' if ranking['ranking_guardrail_passed'] else 'fail'} |",
        f"| future tension differentiates fragile from balanced | {'pass' if scenario['future_tension_differentiates_fragility'] else 'fail'} |",
        f"| no invalid accepts | {'pass' if eval_report['invalid_accept_count'] == 0 else 'fail'} |",
        f"| UX explains blocked state and controls | {'pass' if report['ux']['ux_explains_status_and_controls'] else 'fail'} |",
        f"| model and UX cannot authorize trade | {'pass' if report['safety_contract']['authority_ok'] else 'fail'} |",
        f"| research inputs are linked | {'pass' if report['research_inputs']['ok'] else 'fail'} |",
        f"| JEPA path is small and dependency-light | {'pass' if report['efficiency']['ok'] else 'fail'} |",
        "",
        "## Negative Knowledge",
        "",
    ]
    for item in report["negative_knowledge"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
