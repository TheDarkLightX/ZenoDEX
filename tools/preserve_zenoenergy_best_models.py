#!/usr/bin/env python3
"""Retain current best ZenoEnergy advisory models with hashes and metrics."""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from hashlib import sha256
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.autotrader_energy import (
    evaluate_autotrader_rows,
    generate_rows,
    save_autotrader_model,
    train_autotrader_linear_ranker,
)
from src.energy.upba_v2_energy_model import load_linear_model


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("data/upba_energy/best_models"),
    )
    parser.add_argument(
        "--registry-json",
        type=Path,
        default=Path("data/upba_energy/zenoenergy_best_model_registry.json"),
    )
    parser.add_argument(
        "--registry-markdown",
        type=Path,
        default=Path("docs/ZENO_ENERGY_BEST_MODELS.md"),
    )
    args = parser.parse_args()

    registry = build_registry(
        output_dir=args.output_dir,
        registry_json=args.registry_json,
        registry_markdown=args.registry_markdown,
    )
    print(json.dumps(registry, indent=2, sort_keys=True))
    return 0


def build_registry(
    *,
    output_dir: Path,
    registry_json: Path,
    registry_markdown: Path,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)

    upba_entries = _retain_upba_models(output_dir)
    upba_entry = next(
        entry
        for entry in upba_entries
        if entry["role"] == "current_preferred_research_checkpoint"
    )
    autotrader_entries = _retain_autotrader_hard_cross_seed(output_dir)
    best_autotrader = min(
        autotrader_entries,
        key=lambda entry: (
            float(entry["metrics"]["mean_guard_calls"]),
            -float(entry["metrics"]["top_1_recall"]),
            int(entry["train_seed"]),
        ),
    )

    registry = {
        "schema": "zenodex/energy/best_model_registry/v1",
        "created_date": "2026-05-19",
        "scope": "advisory_ranking_only",
        "safety_contract": {
            "model_authorizes_settlement": False,
            "model_authorizes_trade": False,
            "deterministic_verifier_authoritative": True,
            "deterministic_policy_guards_authoritative": True,
            "state_root_dependency": False,
        },
        "models": [*upba_entries, *autotrader_entries],
        "promoted": {
            "upba_v2": upba_entry["model_id"],
            "autotrader_hard_synthetic_best_seed_pair": best_autotrader["model_id"],
        },
        "negative_knowledge": [
            "A retained model is an advisory search-order artifact with no consensus or policy authority.",
            "The AutoTrader retained models are still synthetic cross-seed artifacts until real shadow evidence promotes them.",
            "The UPBA retained model remains bounded synthetic research evidence until real replay and production-gate evidence pass.",
        ],
    }
    registry_json.parent.mkdir(parents=True, exist_ok=True)
    registry_json.write_text(
        json.dumps(registry, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    registry_markdown.parent.mkdir(parents=True, exist_ok=True)
    registry_markdown.write_text(_markdown(registry), encoding="utf-8")
    return registry


def _retain_upba_models(output_dir: Path) -> list[dict[str, Any]]:
    return [
        _retain_upba_v6(output_dir),
        _retain_upba_highwinner(output_dir),
        _retain_upba_gap_weighted(output_dir),
    ]


def _retain_upba_v6(output_dir: Path) -> dict[str, Any]:
    source = Path("internal/Gemini/gemini_mlp_v6_final.json")
    retained = output_dir / "upba_v2_gemini_mlp_v6_seed20260519.json"
    shutil.copyfile(source, retained)

    payload = _load_json(source)
    review = _load_json(
        Path("data/upba_energy/upba_v2_energy_gemini_v6_promotion_review.json")
    )
    metrics = review["metrics"]
    return {
        "model_id": "gemini_mlp_v6_seed20260519",
        "domain": "upba_v2_partial_fill_exact_in",
        "role": "current_preferred_research_checkpoint",
        "schema": "zenodex/energy/gemini_mlp/v1",
        "source_path": str(source),
        "retained_path": str(retained),
        "sha256": _sha256_file(retained),
        "feature_dim": len(payload["feature_names"]),
        "parameter_count": _model_parameter_count(payload),
        "metrics": _promotion_metrics(metrics, promotion_allowed=review["promotion_allowed"]),
        "retention_reason": (
            "Promoted UPBA v2 advisory ranker: the v6 MLP beats the retained "
            "highwinner linear checkpoint on holdout mean calls, holdout top-1, "
            "cross-seed mean calls, hard-case top-1, and hard-case miss count "
            "while preserving worst cross-seed top-1 and clean safety counts."
        ),
        "promotion_review": "data/upba_energy/upba_v2_energy_gemini_v6_promotion_review.json",
        "supersedes": "gemini_highwinner_seed20260517",
        "advisory_only": True,
    }


def _retain_upba_highwinner(output_dir: Path) -> dict[str, Any]:
    source = Path("data/upba_energy/upba_v2_energy_gemini_highwinner_seed20260517.json")
    retained = output_dir / "upba_v2_gemini_highwinner_seed20260517.json"
    shutil.copyfile(source, retained)

    model = load_linear_model(source)
    review = _load_json(
        Path("data/upba_energy/upba_v2_energy_gemini_highwinner_promotion_review.json")
    )
    metrics = review["metrics"]
    return {
        "model_id": "gemini_highwinner_seed20260517",
        "domain": "upba_v2_partial_fill_exact_in",
        "role": "superseded_linear_checkpoint",
        "schema": "zenodex/energy/linear_ranker/v1",
        "source_path": str(source),
        "retained_path": str(retained),
        "sha256": _sha256_file(retained),
        "feature_dim": len(model.feature_names),
        "parameter_count": len(model.weights) + 1,
        "metrics": _promotion_metrics(metrics, promotion_allowed=review["promotion_allowed"]),
        "retention_reason": (
            "Retained linear fallback UPBA v2 advisory ranker: highwinner beats "
            "the gap-weighted checkpoint and is superseded by the v6 MLP "
            "research checkpoint."
        ),
        "promotion_review": "data/upba_energy/upba_v2_energy_gemini_highwinner_promotion_review.json",
        "supersedes": "upba_v2_gap_weighted_default_seed20260517",
        "superseded_by": "gemini_mlp_v6_seed20260519",
        "advisory_only": True,
    }


def _retain_upba_gap_weighted(output_dir: Path) -> dict[str, Any]:
    source = Path("data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json")
    retained = output_dir / "upba_v2_linear_gap_weighted_seed20260517.json"
    shutil.copyfile(source, retained)

    model = load_linear_model(source)
    stress = _load_json(
        Path("data/upba_energy/upba_v2_energy_gap_weighted_cross_seed_stress_250x3x3.json")
    )
    hard_cases = _load_json(
        Path("data/upba_energy/upba_v2_energy_gap_weighted_hard_cases_500x3x3.json")
    )
    audit = _load_json(Path("data/upba_energy/upba_v2_energy_gap_weighted_model_audit.json"))
    data_scaling = _load_json(
        Path("data/upba_energy/upba_v2_energy_data_scaling_seed20260517.json")
    )
    learned = stress["summary"]["learned"]
    return {
        "model_id": "upba_v2_gap_weighted_default_seed20260517",
        "domain": "upba_v2_partial_fill_exact_in",
        "role": "superseded_baseline_checkpoint",
        "schema": "zenodex/energy/linear_ranker/v1",
        "source_path": str(source),
        "retained_path": str(retained),
        "sha256": _sha256_file(retained),
        "feature_dim": len(model.feature_names),
        "parameter_count": len(model.weights) + 1,
        "metrics": {
            "cross_seed_configs": learned["configs"],
            "cross_seed_mean_verifier_calls_mean": learned["mean_verifier_calls_mean"],
            "cross_seed_mean_verifier_calls_max": learned["mean_verifier_calls_max"],
            "cross_seed_top_1_recall_mean": learned["top_1_recall_mean"],
            "cross_seed_top_1_recall_min": learned["top_1_recall_min"],
            "cross_seed_top_10_recall_min": learned["top_10_recall_min"],
            "cross_seed_invalid_accept_count_total": learned["invalid_accept_count_total"],
            "hard_case_top_10_recall": hard_cases["summary"]["top_10_recall"],
            "hard_case_top10_miss_count": hard_cases["summary"]["top10_miss_count"],
            "reserved_nonzero_count": audit["reserved_nonzero_count"],
            "data_scaling_full_budget_mean_calls": data_scaling["runs"][-1]["metrics"][
                "mean_verifier_calls"
            ],
            "data_scaling_current_checkpoint_mean_calls": data_scaling["baselines"][
                "current_gap_weighted"
            ]["mean_verifier_calls"],
        },
        "retention_reason": (
            "Retained baseline UPBA v2 advisory ranker: gap-weighted default beats hand "
            "energy, keeps top-10 recall complete on current cross-seed stress, and is "
            "the baseline checkpoint superseded by Gemini research checkpoints."
        ),
        "superseded_by": "gemini_mlp_v6_seed20260519",
        "advisory_only": True,
    }


def _promotion_metrics(
    metrics: dict[str, Any],
    *,
    promotion_allowed: bool,
) -> dict[str, Any]:
    return {
        "holdout_mean_verifier_calls": metrics["holdout"]["candidate"][
            "mean_verifier_calls"
        ],
        "holdout_top_1_recall": metrics["holdout"]["candidate"]["top_1_recall"],
        "holdout_top_10_recall": metrics["holdout"]["candidate"]["top_10_recall"],
        "holdout_invalid_accept_count": metrics["holdout"]["candidate"][
            "invalid_accept_count"
        ],
        "cross_seed_configs": 9,
        "cross_seed_mean_verifier_calls_mean": metrics["cross_seed"]["candidate"][
            "mean_verifier_calls_mean"
        ],
        "cross_seed_mean_verifier_calls_max": metrics["cross_seed"]["candidate"][
            "mean_verifier_calls_max"
        ],
        "cross_seed_top_1_recall_mean": metrics["cross_seed"]["candidate"][
            "top_1_recall_mean"
        ],
        "cross_seed_top_1_recall_min": metrics["cross_seed"]["candidate"][
            "top_1_recall_min"
        ],
        "cross_seed_top_10_recall_min": metrics["cross_seed"]["candidate"][
            "top_10_recall_min"
        ],
        "cross_seed_invalid_accept_count_total": metrics["cross_seed"]["candidate"][
            "invalid_accept_count_total"
        ],
        "cross_seed_permutation_violation_count_total": metrics["cross_seed"][
            "candidate"
        ]["permutation_violation_count_total"],
        "hard_case_top_1_recall": metrics["hard_cases"]["candidate"][
            "top_1_recall"
        ],
        "hard_case_top_5_recall": metrics["hard_cases"]["candidate"][
            "top_5_recall"
        ],
        "hard_case_top_10_recall": metrics["hard_cases"]["candidate"][
            "top_10_recall"
        ],
        "hard_case_top1_miss_count": metrics["hard_cases"]["candidate"][
            "top1_miss_count"
        ],
        "hard_case_top5_miss_count": metrics["hard_cases"]["candidate"][
            "top5_miss_count"
        ],
        "hard_case_top10_miss_count": metrics["hard_cases"]["candidate"][
            "top10_miss_count"
        ],
        "promotion_allowed": bool(promotion_allowed),
    }


def _model_parameter_count(payload: dict[str, Any]) -> int:
    if payload.get("schema") == "zenodex/energy/gemini_mlp/v1":
        return (
            sum(len(row) for row in payload["w1"])
            + len(payload["b1"])
            + len(payload["w2"])
            + 1
        )
    return len(payload["weights"]) + 1


def _retain_autotrader_hard_cross_seed(output_dir: Path) -> list[dict[str, Any]]:
    report = _load_json(
        Path("data/upba_energy/autotrader_energy_hard_cross_seed_3x_seed20260522_20260527.json")
    )
    entries: list[dict[str, Any]] = []
    for run in report["runs"]:
        train_seed = int(run["train_seed"])
        holdout_seed = int(run["holdout_seed"])
        train_rows = generate_rows(
            seed=train_seed,
            contexts=int(report["train_contexts"]),
            candidates_per_context=int(report["candidates_per_context"]),
            profile=str(report["profile"]),
        )
        holdout_rows = generate_rows(
            seed=holdout_seed,
            contexts=int(report["holdout_contexts"]),
            candidates_per_context=int(report["candidates_per_context"]),
            profile=str(report["profile"]),
        )
        model = train_autotrader_linear_ranker(
            train_rows,
            epochs=int(report["epochs"]),
            learning_rate=float(report["learning_rate"]),
            margin=float(report["margin"]),
            seed=train_seed,
            init=str(report["init"]),
        )
        retained = (
            output_dir
            / f"autotrader_linear_hard_train{train_seed}_holdout{holdout_seed}.json"
        )
        save_autotrader_model(model, str(retained))
        metrics = evaluate_autotrader_rows(
            holdout_rows,
            mode="hybrid",
            model=model,
            seed=holdout_seed,
        )
        expected = run["modes"]["hybrid"]
        _assert_close(metrics["mean_guard_calls"], expected["mean_guard_calls"])
        _assert_close(metrics["top_1_recall"], expected["top_1_recall"])
        _assert_close(metrics["top_5_recall"], expected["top_5_recall"])
        entries.append(
            {
                "model_id": f"autotrader_hard_train{train_seed}_holdout{holdout_seed}",
                "domain": "autotrader_policy_guard_ordering",
                "role": "retained_synthetic_cross_seed_model",
                "schema": "zenodex/energy/autotrader_linear_ranker/v1",
                "source_report": "data/upba_energy/autotrader_energy_hard_cross_seed_3x_seed20260522_20260527.json",
                "retained_path": str(retained),
                "sha256": _sha256_file(retained),
                "train_seed": train_seed,
                "holdout_seed": holdout_seed,
                "feature_dim": int(run["model"]["feature_dim"]),
                "parameter_count": int(run["model"]["parameters"]),
                "metrics": {
                    "mean_guard_calls": metrics["mean_guard_calls"],
                    "top_1_recall": metrics["top_1_recall"],
                    "top_5_recall": metrics["top_5_recall"],
                    "top_10_recall": metrics["top_10_recall"],
                    "invalid_accept_count": metrics["invalid_accept_count"],
                    "invalid_top_1_rate": metrics["invalid_top_1_rate"],
                    "policy_guards_authoritative": metrics[
                        "policy_guards_authoritative"
                    ],
                    "scorer_authorizes_trade": metrics["scorer_authorizes_trade"],
                },
                "retention_reason": (
                    "Deterministically regenerated from the hard synthetic AutoTrader "
                    "cross-seed receipt; retained so the measured advisory rankers are "
                    "available for future shadow comparison."
                ),
                "advisory_only": True,
            }
        )
    return entries


def _markdown(registry: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Best Model Registry",
        "",
        f"schema: `{registry['schema']}`",
        f"scope: `{registry['scope']}`",
        "",
        "These files are retained research checkpoints. They rank candidate checks only.",
        "Deterministic UPBA verification and AutoTrader policy guards remain authoritative.",
        "",
        "| model | domain | parameters | retained path | primary metric | sha256 |",
        "| --- | --- | ---: | --- | --- | --- |",
    ]
    for entry in registry["models"]:
        metrics = entry["metrics"]
        if entry["domain"] == "upba_v2_partial_fill_exact_in":
            primary = (
                "cross-seed mean calls "
                f"{metrics['cross_seed_mean_verifier_calls_mean']:.4f}, "
                f"top-1 min {metrics.get('cross_seed_top_1_recall_min', 0.0):.4f}, "
                f"top-10 min {metrics['cross_seed_top_10_recall_min']:.4f}"
            )
        else:
            primary = (
                f"guard calls {metrics['mean_guard_calls']:.4f}, "
                f"top-5 {metrics['top_5_recall']:.4f}"
            )
        lines.append(
            "| "
            + " | ".join(
                [
                    entry["model_id"],
                    entry["domain"],
                    str(entry["parameter_count"]),
                    f"`{entry['retained_path']}`",
                    primary,
                    f"`{entry['sha256']}`",
                ]
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Promoted Research Defaults",
            "",
            f"UPBA v2: `{registry['promoted']['upba_v2']}`",
            "",
            "AutoTrader hard synthetic best seed pair: "
            f"`{registry['promoted']['autotrader_hard_synthetic_best_seed_pair']}`",
            "",
            "## Boundaries",
            "",
        ]
    )
    for item in registry["negative_knowledge"]:
        lines.append(f"- {item}")
    return "\n".join(lines) + "\n"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256_file(path: Path) -> str:
    return "sha256:" + sha256(path.read_bytes()).hexdigest()


def _assert_close(left: Any, right: Any, *, tolerance: float = 1e-12) -> None:
    if abs(float(left) - float(right)) > tolerance:
        raise AssertionError(f"metric drift: {left!r} != {right!r}")


if __name__ == "__main__":
    raise SystemExit(main())
