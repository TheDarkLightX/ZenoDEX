from __future__ import annotations

from src.energy.upba_v2_features import FEATURE_NAMES
from tools.train_upba_energy import (
    CURRICULUM_DISQUALIFIER_FEATURES,
    _batch_objective_scale,
    _negative_curriculum_weight,
    _pair_update_weight,
    _positive_row_keys,
    train_linear_ranker,
)


def test_objective_equivalent_positive_class_includes_tied_argmax() -> None:
    rows = [
        _row("winner", valid=True, volume=100, surplus=7, is_winner=True),
        _row("tied", valid=True, volume=100, surplus=7, is_winner=False),
        _row("lower", valid=True, volume=99, surplus=9, is_winner=False),
        _row("invalid", valid=False, volume=0, surplus=0, is_winner=False),
    ]

    assert _positive_row_keys(rows, positive_class="hash-winner") == {"winner"}
    assert _positive_row_keys(rows, positive_class="objective-equivalent") == {
        "winner",
        "tied",
    }


def test_objective_equivalent_positive_class_controls_winner_pair_weight() -> None:
    tied = _row("tied", valid=True, volume=100, surplus=7, is_winner=False)
    lower = _row("lower", valid=True, volume=99, surplus=7, is_winner=False)
    batch_scale = _batch_objective_scale([tied, lower])

    default_weight = _pair_update_weight(
        good=tied,
        bad=lower,
        good_is_positive=False,
        batch_scale=batch_scale,
        winner_pair_weight=3.0,
        objective_gap_weight=0.0,
        same_volume_surplus_gap_weight=0.0,
        max_pair_weight=8.0,
    )
    objective_equiv_weight = _pair_update_weight(
        good=tied,
        bad=lower,
        good_is_positive=True,
        batch_scale=batch_scale,
        winner_pair_weight=3.0,
        objective_gap_weight=0.0,
        same_volume_surplus_gap_weight=0.0,
        max_pair_weight=8.0,
    )

    assert default_weight == 1.0
    assert objective_equiv_weight == 3.0


def test_train_linear_ranker_accepts_objective_equivalent_positive_class() -> None:
    rows = [
        _row("winner", valid=True, volume=100, surplus=7, is_winner=True, feature0=0.1),
        _row("tied", valid=True, volume=100, surplus=7, is_winner=False, feature0=0.2),
        _row("lower", valid=True, volume=90, surplus=5, is_winner=False, feature0=1.0),
    ]

    model = train_linear_ranker(
        rows,
        epochs=1,
        learning_rate=0.01,
        margin=1.0,
        seed=11,
        init="zero",
        winner_pair_weight=2.0,
        objective_gap_weight=1.0,
        same_volume_surplus_gap_weight=1.0,
        max_pair_weight=8.0,
        positive_class="objective-equivalent",
    )

    assert model.feature_names == FEATURE_NAMES
    assert len(model.weights) == len(FEATURE_NAMES)


def test_negative_curriculum_weights_invalid_disqualifiers_only() -> None:
    invalid = _row(
        "invalid",
        valid=False,
        volume=0,
        surplus=0,
        is_winner=False,
        flagged_feature=CURRICULUM_DISQUALIFIER_FEATURES["output_mismatch_count"],
    )
    valid = _row(
        "valid",
        valid=True,
        volume=1,
        surplus=0,
        is_winner=False,
        flagged_feature=CURRICULUM_DISQUALIFIER_FEATURES["output_mismatch_count"],
    )
    weights = {
        CURRICULUM_DISQUALIFIER_FEATURES["output_mismatch_count"]: 3.17,
    }

    assert _negative_curriculum_weight(
        invalid,
        negative_curriculum_weights=weights,
    ) == 3.17
    assert _negative_curriculum_weight(valid, negative_curriculum_weights=weights) == 1.0

    weighted = _pair_update_weight(
        good=_row("winner", valid=True, volume=10, surplus=1, is_winner=True),
        bad=invalid,
        good_is_positive=True,
        batch_scale={"volume": 10, "surplus": 1},
        winner_pair_weight=2.0,
        objective_gap_weight=0.0,
        same_volume_surplus_gap_weight=0.0,
        max_pair_weight=8.0,
        bad_curriculum_weight=3.17,
    )
    assert weighted == 6.34


def _row(
    candidate_hash: str,
    *,
    valid: bool,
    volume: int,
    surplus: int,
    is_winner: bool,
    feature0: float = 0.0,
    flagged_feature: str | None = None,
) -> dict[str, object]:
    features = [0.0 for _ in FEATURE_NAMES]
    features[0] = feature0
    if flagged_feature is not None:
        features[FEATURE_NAMES.index(flagged_feature)] = 1.0
    return {
        "schema": "zenodex/energy/upba_v2_dataset_row/v1",
        "source": "unit",
        "batch_id": "batch",
        "candidate_hash": candidate_hash,
        "feature_names": list(FEATURE_NAMES),
        "features": features,
        "label": {
            "valid": valid,
            "objective_volume": volume,
            "objective_surplus": surplus,
            "is_winner": is_winner,
        },
    }
