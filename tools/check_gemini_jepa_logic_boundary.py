#!/usr/bin/env python3
"""Check Gemini JEPA and ZenoLogic as advisory scoring surfaces."""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from internal.Gemini.zeno_jepa_model import ZenoJepaModel  # noqa: E402
from internal.Gemini.zeno_logic import (  # noqa: E402
    EnergyAnd,
    EnergyAtom,
    EnergyNot,
    EnergyOr,
)


@dataclass(frozen=True)
class _Kernel:
    name: str
    feature: str
    weight: float

    def energy(self, features: Mapping[str, float]) -> float:
        return float(features.get(self.feature, 0.0)) * self.weight


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = check_gemini_jepa_logic_boundary()
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown(report), encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def check_gemini_jepa_logic_boundary() -> dict[str, Any]:
    model = _demo_jepa_model()
    state = [0.8, 0.6, 0.2, 0.1]
    balanced_action = [0.45, 0.08, 0.05, 0.04]
    draining_action = [1.0, 0.72, 0.08, 0.65]
    balanced_tension = model.predict_latent_tension(state, balanced_action)
    draining_tension = model.predict_latent_tension(state, draining_action)

    max_volume = EnergyAtom(_Kernel("max_volume", "volume_gap", -1.0))
    price_impact = EnergyAtom(_Kernel("price_impact", "price_impact", 12.0))
    barrier = EnergyAtom(_Kernel("barrier", "hard_violation", 1_000.0))
    conjunction = EnergyAnd(max_volume, price_impact)
    disjunction = EnergyOr(price_impact, barrier)
    inverted_barrier = EnergyNot(barrier)

    valid_features = {
        "volume_gap": 0.9,
        "price_impact": 0.1,
        "hard_violation": 0.0,
    }
    invalid_features = {
        "volume_gap": 0.9,
        "price_impact": 0.1,
        "hard_violation": 1.0,
    }
    valid_and_energy = conjunction.energy(valid_features)
    invalid_not_energy = inverted_barrier.energy(invalid_features)
    valid_not_energy = inverted_barrier.energy(valid_features)
    large_or_energy = EnergyOr(
        EnergyAtom(_Kernel("large_1", "x", 1_000.0)),
        EnergyAtom(_Kernel("large_2", "y", 1_000.0)),
    ).energy({"x": 1.0, "y": 2.0})

    future_tension_prefers_balanced = balanced_tension < draining_tension
    energy_not_inverts_barrier = invalid_not_energy < valid_not_energy
    stable_or_finite = math.isfinite(disjunction.energy(invalid_features)) and math.isfinite(large_or_energy)
    ok = future_tension_prefers_balanced and energy_not_inverts_barrier and stable_or_finite
    return {
        "schema": "zenodex/energy/gemini_jepa_logic_boundary_receipt/v1",
        "ok": ok,
        "decision": "research_only_future_aware_advisory_score",
        "jepa": {
            "schema": model.to_dict()["schema"],
            "state_feature_dim": len(model.feature_names),
            "action_dim": model.action_dim,
            "latent_dim": model.latent_dim,
            "balanced_action_tension": balanced_tension,
            "draining_action_tension": draining_tension,
            "future_tension_prefers_balanced": future_tension_prefers_balanced,
            "model_authorizes_settlement": False,
        },
        "zeno_logic": {
            "and_energy_valid": valid_and_energy,
            "or_energy_invalid": disjunction.energy(invalid_features),
            "large_or_energy": large_or_energy,
            "stable_or_finite": stable_or_finite,
            "energy_not_valid_barrier": valid_not_energy,
            "energy_not_invalid_barrier": invalid_not_energy,
            "energy_not_inverts_barrier": energy_not_inverts_barrier,
        },
        "safety_contract": {
            "deterministic_verifier_authoritative": True,
            "deterministic_policy_guards_authoritative": True,
            "model_authorizes_settlement": False,
            "model_authorizes_trade": False,
            "future_tension_authorizes_settlement": False,
            "logic_expression_authorizes_settlement": False,
        },
        "positive_knowledge": (
            "A latent future-tension score can rank a balanced action ahead of "
            "a draining action in a bounded demo."
        ),
        "negative_knowledge": [
            "Future-tension energy is a search feature, not a proof of future market safety.",
            "ZenoLogic composes advisory energies and does not create a formal verifier.",
            "EnergyNot can invert hard barriers, so it must not be used over safety predicates.",
            "Production use still requires deterministic verifier or policy-gate checks and real replay.",
        ],
    }


def _demo_jepa_model() -> ZenoJepaModel:
    return ZenoJepaModel(
        feature_names=("reserve_depth", "liquidity_balance", "volatility", "fee_pressure"),
        latent_dim=3,
        action_dim=4,
        bias_jepa=0.0,
        w_encoder=[
            [0.2, 0.0, 0.1],
            [0.0, 0.2, 0.0],
            [0.1, 0.1, 0.3],
            [0.0, 0.1, 0.2],
        ],
        w_predictor=[
            [0.4, 0.0, 0.0],
            [0.0, 0.4, 0.0],
            [0.0, 0.0, 0.4],
            [0.2, 0.1, 0.1],
            [0.1, 0.9, 0.2],
            [0.0, 0.2, 0.1],
            [0.2, 0.1, 0.9],
        ],
    )


def _markdown(report: dict[str, Any]) -> str:
    jepa = report["jepa"]
    logic = report["zeno_logic"]
    lines = [
        "# Gemini JEPA And ZenoLogic Boundary",
        "",
        "```text",
        f"ok: {str(report['ok']).lower()}",
        f"decision: {report['decision']}",
        f"balanced_action_tension: {jepa['balanced_action_tension']:.6f}",
        f"draining_action_tension: {jepa['draining_action_tension']:.6f}",
        f"future_tension_prefers_balanced: {str(jepa['future_tension_prefers_balanced']).lower()}",
        f"energy_not_inverts_barrier: {str(logic['energy_not_inverts_barrier']).lower()}",
        "```",
        "",
        "JEPA and ZenoLogic are advisory scoring surfaces. They can rank or shape proposals, but deterministic verification or policy gates remain authoritative.",
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
