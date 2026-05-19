from __future__ import annotations

import json
from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def test_best_model_registry_pins_current_models() -> None:
    registry = _load_json(ROOT / "data/upba_energy/zenoenergy_best_model_registry.json")
    models = {entry["model_id"]: entry for entry in registry["models"]}

    assert registry["schema"] == "zenodex/energy/best_model_registry/v1"
    assert registry["scope"] == "advisory_ranking_only"
    assert registry["safety_contract"]["model_authorizes_settlement"] is False
    assert registry["safety_contract"]["model_authorizes_trade"] is False
    assert registry["promoted"]["upba_v2"] == "upba_v2_gap_weighted_default_seed20260517"
    assert (
        registry["promoted"]["autotrader_hard_synthetic_best_seed_pair"]
        == "autotrader_hard_train20260526_holdout20260527"
    )
    assert set(models) == {
        "upba_v2_gap_weighted_default_seed20260517",
        "autotrader_hard_train20260522_holdout20260523",
        "autotrader_hard_train20260524_holdout20260525",
        "autotrader_hard_train20260526_holdout20260527",
    }

    for entry in models.values():
        path = ROOT / entry["retained_path"]
        payload = _load_json(path)
        assert path.exists()
        assert entry["sha256"] == _sha256_file(path)
        assert payload["schema"] == entry["schema"]
        assert len(payload["weights"]) + 1 == entry["parameter_count"]
        assert len(payload["feature_names"]) == entry["feature_dim"]
        assert entry["advisory_only"] is True


def test_upba_promoted_model_is_exact_retained_copy() -> None:
    registry = _load_json(ROOT / "data/upba_energy/zenoenergy_best_model_registry.json")
    entry = next(
        model
        for model in registry["models"]
        if model["model_id"] == "upba_v2_gap_weighted_default_seed20260517"
    )
    source = ROOT / entry["source_path"]
    retained = ROOT / entry["retained_path"]
    metrics = entry["metrics"]

    assert source.read_bytes() == retained.read_bytes()
    assert metrics["cross_seed_invalid_accept_count_total"] == 0
    assert metrics["cross_seed_top_10_recall_min"] == 1.0
    assert metrics["hard_case_top10_miss_count"] == 0
    assert (
        metrics["data_scaling_current_checkpoint_mean_calls"]
        < metrics["data_scaling_full_budget_mean_calls"]
    )


def test_autotrader_retained_models_keep_guard_authority() -> None:
    registry = _load_json(ROOT / "data/upba_energy/zenoenergy_best_model_registry.json")
    autotrader = [
        model
        for model in registry["models"]
        if model["domain"] == "autotrader_policy_guard_ordering"
    ]

    assert len(autotrader) == 3
    assert all(model["parameter_count"] == 21 for model in autotrader)
    assert all(model["metrics"]["invalid_accept_count"] == 0 for model in autotrader)
    assert all(model["metrics"]["top_5_recall"] == 1.0 for model in autotrader)
    assert all(model["metrics"]["scorer_authorizes_trade"] is False for model in autotrader)
    assert min(model["metrics"]["mean_guard_calls"] for model in autotrader) == 1.008


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256_file(path: Path) -> str:
    return "sha256:" + sha256(path.read_bytes()).hexdigest()
