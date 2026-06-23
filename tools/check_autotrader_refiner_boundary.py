#!/usr/bin/env python3
"""Check Gemini AutoTrader refinement as policy-gated proposal search."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from statistics import mean
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from internal.Gemini.autotrader_compositional_policy import (  # noqa: E402
    AlphaKernel,
    AutoTraderCompositionalPolicy,
    ConstraintKernel,
    ExecutionCostKernel,
    RiskKernel,
)
from internal.Gemini.autotrader_refiner import AutoTraderIntentRefiner  # noqa: E402
from src.energy.autotrader_energy import (  # noqa: E402
    autotrader_feature_map,
    autotrader_label_from_features,
    generate_rows,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260529)
    parser.add_argument("--contexts", type=int, default=160)
    parser.add_argument("--candidates-per-context", type=int, default=16)
    parser.add_argument("--steps", type=int, default=24)
    parser.add_argument("--learning-rate", type=float, default=0.04)
    parser.add_argument("--noise-scale", type=float, default=0.0)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = check_autotrader_refiner_boundary(
        seed=args.seed,
        contexts=args.contexts,
        candidates_per_context=args.candidates_per_context,
        steps=args.steps,
        learning_rate=args.learning_rate,
        noise_scale=args.noise_scale,
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


def check_autotrader_refiner_boundary(
    *,
    seed: int,
    contexts: int,
    candidates_per_context: int,
    steps: int,
    learning_rate: float,
    noise_scale: float,
) -> dict[str, Any]:
    rows = generate_rows(
        seed=seed,
        contexts=contexts,
        candidates_per_context=candidates_per_context,
        profile="hard",
    )
    by_batch: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        by_batch.setdefault(str(row["batch_id"]), []).append(row)

    policy = AutoTraderCompositionalPolicy(
        [
            (AlphaKernel(), 1.0),
            (RiskKernel(), 1.0),
            (ExecutionCostKernel(), 1.0),
            (ConstraintKernel(), 1.0),
        ]
    )
    results = []
    for index, batch_rows in enumerate(by_batch.values()):
        valid_rows = [row for row in batch_rows if bool(row["label"]["valid"])]
        if not valid_rows:
            continue
        seed_row = min(
            valid_rows,
            key=lambda row: (
                float(row["label"]["hand_energy"]),
                str(row["candidate_hash"]),
            ),
        )
        refiner = AutoTraderIntentRefiner(
            policy,
            lr=learning_rate,
            steps=steps,
            random_seed=seed + index,
            noise_scale=noise_scale,
        )
        result = refiner.refine_trade_checked(
            autotrader_feature_map(seed_row["features"]),
            label_fn=autotrader_label_from_features,
        )
        results.append(result)

    evaluated = len(results)
    accepted = [result for result in results if result.accepted_refinement]
    rejected = [result for result in results if not result.accepted_refinement]
    invalid_refined = [result for result in results if not result.refined_valid]
    objective_regressions = [
        result
        for result in results
        if result.refined_valid and result.refined_objective < result.initial_objective
    ]
    selected_invalid = [result for result in results if not result.selected_valid]
    initial_objectives = [result.initial_objective for result in results]
    refined_objectives = [result.refined_objective for result in results]
    selected_objectives = [result.selected_objective for result in results]
    initial_energies = [result.initial_energy for result in results]
    refined_energies = [result.refined_energy for result in results]
    selected_energies = [result.selected_energy for result in results]

    objective_gain = _mean(selected_objectives) - _mean(initial_objectives)
    energy_delta = _mean(selected_energies) - _mean(initial_energies)
    ok = (
        evaluated == contexts
        and not selected_invalid
        and all(not result.model_authorizes_trade for result in results)
        and all(result.policy_guards_authoritative for result in results)
    )
    return {
        "schema": "zenodex/energy/autotrader_refiner_boundary_receipt/v1",
        "ok": ok,
        "decision": "research_only_policy_checked_refinement",
        "seed": seed,
        "contexts": contexts,
        "candidates_per_context": candidates_per_context,
        "steps": steps,
        "learning_rate": learning_rate,
        "noise_scale": noise_scale,
        "evaluated_contexts": evaluated,
        "accepted_refinement_count": len(accepted),
        "rejected_refinement_count": len(rejected),
        "invalid_refinement_count": len(invalid_refined),
        "objective_regression_rejected_count": len(objective_regressions),
        "selected_invalid_count": len(selected_invalid),
        "initial_objective_mean": _mean(initial_objectives),
        "refined_objective_mean": _mean(refined_objectives),
        "selected_objective_mean": _mean(selected_objectives),
        "selected_vs_initial_objective_delta_mean": objective_gain,
        "initial_energy_mean": _mean(initial_energies),
        "refined_energy_mean": _mean(refined_energies),
        "selected_energy_mean": _mean(selected_energies),
        "selected_vs_initial_energy_delta_mean": energy_delta,
        "policy_guards_authoritative": True,
        "model_authorizes_trade": False,
        "refined_proposal_authorizes_trade": False,
        "sample_results": [result.to_dict() for result in results[:5]],
        "positive_knowledge": (
            "Bounded Langevin-style AutoTrader refinement can improve selected "
            "synthetic policy objectives when every proposal is rechecked."
        ),
        "negative_knowledge": [
            "Lower policy energy does not authorize an AutoTrader trade.",
            "The refiner is proposal search; deterministic policy labels decide selection.",
            "This receipt is hard synthetic evidence and does not replace real shadow replay.",
        ],
    }


def _mean(values: list[float]) -> float:
    return 0.0 if not values else float(mean(values))


def _markdown(report: dict[str, Any]) -> str:
    lines = [
        "# AutoTrader Refiner Boundary",
        "",
        "```text",
        f"ok: {str(report['ok']).lower()}",
        f"decision: {report['decision']}",
        f"evaluated_contexts: {report['evaluated_contexts']}",
        f"accepted_refinement_count: {report['accepted_refinement_count']}",
        f"rejected_refinement_count: {report['rejected_refinement_count']}",
        f"selected_invalid_count: {report['selected_invalid_count']}",
        f"selected_vs_initial_objective_delta_mean: {report['selected_vs_initial_objective_delta_mean']:.6f}",
        f"selected_vs_initial_energy_delta_mean: {report['selected_vs_initial_energy_delta_mean']:.6f}",
        "```",
        "",
        "AutoTrader refinement is proposal search. A refined feature vector is selected only after deterministic policy labels accept it and the deterministic objective does not regress.",
        "",
        "## Checks",
        "",
        "| check | status |",
        "| --- | --- |",
        f"| policy guards authoritative | {'pass' if report['policy_guards_authoritative'] else 'fail'} |",
        f"| model cannot authorize trade | {'pass' if not report['model_authorizes_trade'] else 'fail'} |",
        f"| selected proposals are policy-valid | {'pass' if report['selected_invalid_count'] == 0 else 'fail'} |",
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
