from __future__ import annotations

import json
from pathlib import Path

from src.energy.upba_v2_energy_model import LinearEnergyModel
from src.energy.upba_v2_ensemble import LinearEnergyEnsemble


ROOT = Path(__file__).resolve().parents[2]


def test_linear_energy_ensemble_rank_stats_are_batch_local() -> None:
    rows = [
        {"candidate_hash": "a", "features": [0.0]},
        {"candidate_hash": "b", "features": [1.0]},
        {"candidate_hash": "c", "features": [2.0]},
    ]
    low_first = LinearEnergyModel(feature_names=("x",), weights=(1.0,))
    high_first = LinearEnergyModel(feature_names=("x",), weights=(-1.0,))
    ensemble = LinearEnergyEnsemble((low_first, high_first))

    stats = ensemble.rank_stats(rows, feature_getter=lambda row: row["features"])
    ordered = ensemble.order_by_rank_consensus(
        rows,
        feature_getter=lambda row: row["features"],
        disagreement_weight=1.0,
    )

    assert stats["a"].min_rank == 1
    assert stats["a"].max_rank == 3
    assert stats["b"].mean_rank == 2
    assert [row["candidate_hash"] for row in ordered] == ["b", "a", "c"]


def test_ensemble_report_records_negative_default_decision() -> None:
    report = _load_json(ROOT / "data/upba_energy/upba_v2_energy_ensemble_seed20260556.json")
    baseline = report["baselines"]["current_gap_weighted"]
    interpretation = report["interpretation"]

    assert report["schema"] == "zenodex/energy/upba_v2_ensemble_report/v1"
    assert report["ensemble"]["member_count"] == 6
    assert report["ensemble"]["total_parameter_count"] == 582
    assert report["safety"]["invalid_accept_count_total"] == 0
    assert report["safety"]["verifier_authoritative"] is True
    assert report["safety"]["model_authorizes_settlement"] is False
    assert baseline["mean_verifier_calls"] < interpretation["best_ensemble_mean_verifier_calls"]
    assert interpretation["best_ensemble_beats_current_gap_weighted"] is False
    assert interpretation["best_uncertainty_auc"] > 0.6
    assert all(mode["top_10_recall"] == 1.0 for mode in report["modes"].values())
    assert all(mode["invalid_accept_count"] == 0 for mode in report["modes"].values())


def test_ensemble_source_hooks_are_present() -> None:
    tool = (ROOT / "tools/benchmark_upba_energy_ensemble.py").read_text(encoding="utf-8")
    doc = (ROOT / "docs/ZENO_ENERGY_ENSEMBLE.md").read_text(encoding="utf-8")

    assert "LinearEnergyEnsemble" in tool
    assert "ensemble_rank_std_penalty" in tool
    assert "Deterministic UPBA verification and fallback remain the authority" in doc


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))
