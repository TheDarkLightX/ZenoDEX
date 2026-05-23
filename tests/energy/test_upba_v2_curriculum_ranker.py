from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def test_curriculum_ranker_receipt_records_negative_result() -> None:
    report = json.loads(
        (
            ROOT
            / "data/upba_energy/upba_v2_energy_curriculum_ranker_seed20260517.json"
        ).read_text(encoding="utf-8")
    )
    doc = (ROOT / "docs/ZENO_ENERGY_CURRICULUM_RANKER.md").read_text(
        encoding="utf-8"
    )
    model = ROOT / "data/upba_energy/upba_v2_energy_linear_curriculum_seed20260517.json"

    assert report["schema"] == "zenodex/energy/upba_v2_curriculum_ranker_report/v1"
    assert report["max_train_batches"] == 1000
    assert report["train_rows"] < report["train_rows_available"]
    assert model.exists()

    baseline = report["stress"]["summary"]["baseline_learned"]
    curriculum = report["stress"]["summary"]["curriculum_learned"]
    assert baseline["invalid_accept_count_total"] == 0
    assert curriculum["invalid_accept_count_total"] == 0
    assert curriculum["permutation_violation_count_total"] == 0
    assert curriculum["top_10_recall_min"] == 1.0
    assert curriculum["mean_verifier_calls_mean"] > baseline["mean_verifier_calls_mean"]

    interpretation = report["interpretation"]
    assert interpretation["promotion_decision"] == "keep_default"
    assert interpretation["curriculum_improved_cross_seed_mean_calls"] is False
    assert "did not beat the gap-weighted default" in doc
