from __future__ import annotations

from tools.build_upba_energy_model_leaderboard import build_leaderboard


def test_highwinner_leads_comparable_upba_energy_leaderboard() -> None:
    report = build_leaderboard()

    assert report["schema"] == "zenodex/energy/upba_v2_model_leaderboard/v1"
    assert report["scope"] == "advisory_ranking_only"
    assert report["decision"] == "promote_v6_research_candidate"
    assert report["promoted_model_id"] == "gemini_mlp_v6_seed20260519"
    assert report["compared_model_count"] == 7
    assert report["full_three_lane_model_count"] == 6
    assert report["blocked_reasons"] == []
    assert all(item["passed"] for item in report["obligations"])

    rows = {row["model_id"]: row for row in report["models"]}
    v6 = rows["gemini_mlp_v6_seed20260519"]
    v5 = rows["gemini_linear_v5_seed20260519"]
    highwinner = rows["gemini_highwinner_seed20260517"]
    gap = rows["upba_v2_gap_weighted_default_seed20260517"]
    objective8 = rows["gemini_objective8_seed20260517"]
    handinit = rows["gemini_handinit_seed20260517"]

    assert v6["metrics"]["holdout"]["mean_verifier_calls"] < highwinner["metrics"]["holdout"][
        "mean_verifier_calls"
    ]
    assert v6["metrics"]["holdout"]["mean_verifier_calls"] < gap["metrics"]["holdout"][
        "mean_verifier_calls"
    ]
    assert v6["metrics"]["holdout"]["mean_verifier_calls"] < objective8["metrics"][
        "holdout"
    ]["mean_verifier_calls"]
    assert v6["metrics"]["holdout"]["mean_verifier_calls"] < handinit["metrics"][
        "holdout"
    ]["mean_verifier_calls"]
    assert v6["metrics"]["cross_seed"]["top_1_recall_min"] > gap["metrics"][
        "cross_seed"
    ]["top_1_recall_min"]
    assert v6["metrics"]["cross_seed"]["mean_verifier_calls_mean"] < highwinner["metrics"][
        "cross_seed"
    ]["mean_verifier_calls_mean"]
    assert v6["metrics"]["hard_cases"]["top1_miss_count"] < highwinner["metrics"][
        "hard_cases"
    ]["top1_miss_count"]
    assert v6["metrics"]["hard_cases"]["top1_miss_count"] < gap["metrics"][
        "hard_cases"
    ]["top1_miss_count"]
    assert v5["metrics"]["cross_seed"]["mean_verifier_calls_mean"] > gap["metrics"][
        "cross_seed"
    ]["mean_verifier_calls_mean"]
