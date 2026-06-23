from __future__ import annotations

from pathlib import Path

from tools.build_upba_energy_candidate_review import build_review


def test_candidate_review_holds_when_worst_case_regresses() -> None:
    holdout = {
        "modes": {
            "gap_weighted": {
                "top_1_recall": 0.98,
                "top_10_recall": 1.0,
                "mean_verifier_calls": 1.02,
                "invalid_accept_count": 0,
            },
            "gemini": {
                "top_1_recall": 0.99,
                "top_10_recall": 1.0,
                "mean_verifier_calls": 1.01,
                "invalid_accept_count": 0,
            },
        }
    }
    baseline_cross = {
        "summary": {
            "learned": {
                "top_1_recall_mean": 0.98,
                "top_1_recall_min": 0.97,
                "top_10_recall_min": 1.0,
                "mean_verifier_calls_mean": 1.02,
                "mean_verifier_calls_max": 1.03,
                "invalid_accept_count_total": 0,
                "permutation_violation_count_total": 0,
            }
        }
    }
    candidate_cross = {
        "summary": {
            "learned": {
                "top_1_recall_mean": 0.981,
                "top_1_recall_min": 0.96,
                "top_10_recall_min": 1.0,
                "mean_verifier_calls_mean": 1.01,
                "mean_verifier_calls_max": 1.04,
                "invalid_accept_count_total": 0,
                "permutation_violation_count_total": 0,
            }
        }
    }
    baseline_hard = {
        "summary": {
            "top_1_recall": 0.985,
            "top_5_recall": 1.0,
            "top_10_recall": 1.0,
            "top1_miss_count": 65,
            "top5_miss_count": 0,
            "top10_miss_count": 0,
            "mean_winner_position_mean": 1.017,
            "max_mean_winner_position": 1.032,
        }
    }
    candidate_hard = {
        "summary": {
            "top_1_recall": 0.981,
            "top_5_recall": 1.0,
            "top_10_recall": 1.0,
            "top1_miss_count": 87,
            "top5_miss_count": 0,
            "top10_miss_count": 0,
            "mean_winner_position_mean": 1.019,
            "max_mean_winner_position": 1.032,
        }
    }

    report = build_review(
        candidate_id="candidate_a",
        baseline_id="baseline_b",
        candidate_model=Path("data/upba_energy/upba_v2_energy_gemini_log_interactions_seed20260517.json"),
        holdout_compare=holdout,
        candidate_cross_seed=candidate_cross,
        candidate_hard_cases=candidate_hard,
        baseline_cross_seed=baseline_cross,
        baseline_hard_cases=baseline_hard,
        source_paths={},
    )

    assert report["decision"] == "hold_candidate"
    assert report["candidate_id"] == "candidate_a"
    assert report["baseline_id"] == "baseline_b"
    assert report["promotion_allowed"] is False
    assert report["blocked_reasons"] == [
        "cross_seed_preserves_worst_top1",
        "hard_cases_preserve_top1",
    ]
