from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def test_data_scaling_receipt_records_saturation() -> None:
    report = json.loads(
        (ROOT / "data/upba_energy/upba_v2_energy_data_scaling_seed20260517.json").read_text(
            encoding="utf-8"
        )
    )
    runs = report["runs"]
    first = runs[0]["metrics"]
    last = runs[-1]["metrics"]
    baseline = report["baselines"]["current_gap_weighted"]

    assert report["schema"] == "zenodex/energy/upba_v2_data_scaling_report/v1"
    assert report["available_train_rows"] == 199860
    assert report["safety"]["invalid_accept_count_total"] == 0
    assert last["mean_verifier_calls"] < first["mean_verifier_calls"]
    assert last["mean_verifier_calls"] >= baseline["mean_verifier_calls"]
    assert report["interpretation"]["best_budget_beats_current_gap_weighted"] is False
    assert "raw volume alone" in report["interpretation"]["negative_knowledge"]
