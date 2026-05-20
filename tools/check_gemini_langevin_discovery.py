#!/usr/bin/env python3
"""Replay the Gemini Langevin discovery boundary check."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from random import Random
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from internal.Gemini.gemini_mlp_model import load_mlp_model
from internal.Gemini.langevin_discovery import LangevinDiscovery
from internal.Gemini.zeno_guard_model import load_guard_model
from src.core.uniform_batch_clearing import verify_uniform_batch_certificate_v1
from src.energy.upba_v2_ranker import verify_candidates_in_order
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = check_langevin_discovery()
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown(report), encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def check_langevin_discovery() -> dict[str, Any]:
    seed = 20260580
    batch = generate_synthetic_batch(
        rng=Random(seed),
        batch_index=0,
        target_candidate_count=32,
    )
    verified = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[item.candidate for item in batch.candidates],
    )
    seed_candidate = next(
        result.candidate for result in verified if result.ok and result.candidate.fills
    )
    explorer = LangevinDiscovery(
        load_mlp_model("internal/Gemini/gemini_mlp_v6_final.json"),
        load_guard_model("internal/Gemini/zeno_guard_v1.json"),
        lr=10.0,
        steps=5,
        random_seed=20260519,
    )
    result = explorer.discover_verified(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        seed=seed_candidate,
    )
    selected_verdict = None
    if result.selected is not None:
        selected_verdict = verify_uniform_batch_certificate_v1(
            intents=batch.intents,
            pool=batch.pool,
            balances=batch.balances,
            certificate=result.selected,
        )
    checks = [
        _check("seed_verifier_ok", result.seed_verifier_ok),
        _check("selected_verifier_ok", bool(selected_verdict and selected_verdict.ok)),
        _check("model_does_not_authorize_settlement", not result.model_authorizes_settlement),
        _check(
            "invalid_refinement_falls_back",
            (
                result.refined_verifier_ok
                or (not result.accepted_refinement and result.fallback_to_seed)
            ),
        ),
    ]
    return {
        "schema": "zenodex/energy/gemini_langevin_discovery_receipt/v1",
        "ok": all(item["passed"] for item in checks),
        "checks": checks,
        "seed": seed,
        "candidate_count": 32,
        "model": "internal/Gemini/gemini_mlp_v6_final.json",
        "guard": "internal/Gemini/zeno_guard_v1.json",
        "seed_energy": result.seed_energy,
        "refined_energy": result.refined_energy,
        "energy_delta": result.refined_energy - result.seed_energy,
        "seed_verifier_ok": result.seed_verifier_ok,
        "refined_verifier_ok": result.refined_verifier_ok,
        "refined_verifier_error": result.refined_verifier_error,
        "accepted_refinement": result.accepted_refinement,
        "fallback_to_seed": result.fallback_to_seed,
        "selected_verifier_ok": bool(selected_verdict and selected_verdict.ok),
        "decision": "research_only_verifier_checked_proposal",
        "negative_knowledge": [
            "Lower learned energy does not imply verifier acceptance.",
            "ZenoGuard is an advisory soft prior and cannot prove candidate validity.",
            "Langevin proposals must be canonicalized and checked by the deterministic verifier before selection.",
        ],
    }


def _check(check_id: str, passed: bool) -> dict[str, Any]:
    return {"check_id": f"langevin_discovery.{check_id}", "passed": bool(passed)}


def _markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Gemini Langevin Discovery Boundary",
        "",
        "```text",
        f"ok: {str(report['ok']).lower()}",
        f"decision: {report['decision']}",
        f"seed_energy: {report['seed_energy']:.6f}",
        f"refined_energy: {report['refined_energy']:.6f}",
        f"energy_delta: {report['energy_delta']:.6f}",
        f"seed_verifier_ok: {str(report['seed_verifier_ok']).lower()}",
        f"refined_verifier_ok: {str(report['refined_verifier_ok']).lower()}",
        f"accepted_refinement: {str(report['accepted_refinement']).lower()}",
        f"fallback_to_seed: {str(report['fallback_to_seed']).lower()}",
        f"selected_verifier_ok: {str(report['selected_verifier_ok']).lower()}",
        "```",
        "",
        "Langevin refinement is a proposal mechanism. The selected candidate is verifier-backed; a lower-energy refined proposal is rejected when deterministic verification fails.",
        "",
        "## Checks",
        "",
        "| check | status |",
        "| --- | --- |",
    ]
    for item in report["checks"]:
        lines.append(
            f"| `{item['check_id']}` | {'pass' if item['passed'] else 'fail'} |"
        )
    lines.extend(["", "## Negative Knowledge", ""])
    for item in report["negative_knowledge"]:
        lines.append(f"- {item}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
