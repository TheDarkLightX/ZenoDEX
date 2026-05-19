from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def test_quality_selection_receipt_records_quality_tradeoff() -> None:
    report = json.loads(
        (
            ROOT / "data/upba_energy/upba_v2_energy_quality_selection_seed20260517.json"
        ).read_text(encoding="utf-8")
    )
    raw = report["runs"]["raw_winner_bearing"]
    quality = report["runs"]["quality_hard_winner_bearing"]
    interpretation = report["interpretation"]

    assert report["schema"] == "zenodex/energy/upba_v2_quality_selection_report/v1"
    assert report["winner_bearing_train_batches"] == 9916
    assert report["selection"]["excluded_no_winner_train_batches"] == 84
    assert report["safety"]["invalid_accept_count_total"] == 0
    assert len(raw) == len(quality) == 6
    assert interpretation["quality_beats_raw_budget_count"] == 4
    assert interpretation["quality_worse_than_raw_budget_count"] == 1
    assert interpretation["best_quality_matches_or_beats_current_gap_weighted"] is False
    assert quality[0]["metrics"]["mean_verifier_calls"] > raw[0]["metrics"]["mean_verifier_calls"]
    assert quality[1]["metrics"]["mean_verifier_calls"] < raw[1]["metrics"]["mean_verifier_calls"]
    assert "hard-only quality budgets" in interpretation["negative_knowledge"]
