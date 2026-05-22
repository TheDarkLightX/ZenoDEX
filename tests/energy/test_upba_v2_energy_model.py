from __future__ import annotations

from src.energy.upba_v2_energy_model import (
    LinearEnergyModel,
    count_mlp_parameters,
    initial_hand_weight_model,
    load_linear_model,
    save_linear_model,
)
from src.energy.upba_v2_features import FEATURE_DIM, FEATURE_NAMES
from tools.inspect_upba_energy_model import inspect_model


def test_tiny_mlp_parameter_counts_match_expected_sizes() -> None:
    assert count_mlp_parameters(input_dim=96, hidden_dim=64) == 6_273
    assert count_mlp_parameters(input_dim=128, hidden_dim=64) == 8_321
    assert count_mlp_parameters(input_dim=128, hidden_dim=64, hidden_layers=2) == 12_481


def test_linear_energy_model_round_trips_json(tmp_path) -> None:
    model = initial_hand_weight_model()
    path = tmp_path / "linear_energy.json"

    save_linear_model(model, path)
    loaded = load_linear_model(path)

    assert loaded.feature_names == FEATURE_NAMES
    assert len(loaded.weights) == FEATURE_DIM
    assert loaded.energy([0.0] * FEATURE_DIM) == model.bias


def test_linear_energy_model_rejects_mismatched_feature_length() -> None:
    model = LinearEnergyModel(feature_names=("a",), weights=(1.0,))

    try:
        model.energy(())
    except ValueError as exc:
        assert str(exc) == "feature length does not match model"
    else:  # pragma: no cover
        raise AssertionError("expected feature length rejection")


def test_model_inspection_reports_no_label_like_features(tmp_path) -> None:
    model = initial_hand_weight_model()
    path = tmp_path / "linear_energy.json"
    save_linear_model(model, path)

    report = inspect_model(path, top_n=4)

    assert report["feature_dim"] == FEATURE_DIM
    assert report["parameter_count"] == FEATURE_DIM + 1
    assert report["forbidden_feature_names"] == []
    assert report["reserved_nonzero_count"] == 0
