from __future__ import annotations

from dataclasses import replace
from random import Random

from src.energy.upba_v2_energy_model import LinearEnergyModel, save_linear_model
from src.energy.upba_v2_ranker import rank_upba_v2_candidates, scorer_from_linear_model
from src.energy.upba_v2_set_features import (
    SET_AWARE_FEATURE_DIM,
    SET_AWARE_FEATURE_NAMES,
    SET_FEATURE_DIM,
    SET_FEATURE_NAMES,
    extract_upba_v2_set_aware_feature_record,
    extract_upba_v2_set_feature_record,
)
from tools.generate_upba_energy_dataset import generate_dataset_rows, generate_synthetic_batch
from tools.inspect_upba_energy_model import inspect_model
from tools.train_upba_energy import train_linear_ranker


def test_set_features_are_fixed_width_and_do_not_expose_labels() -> None:
    batch = generate_synthetic_batch(rng=Random(601), batch_index=0, target_candidate_count=12)
    record = extract_upba_v2_set_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=batch.candidates[0].candidate,
    )

    assert len(SET_FEATURE_NAMES) == SET_FEATURE_DIM
    assert len(record.values) == SET_FEATURE_DIM
    assert record.raw["feature_schema"] == "zenodex/energy/upba_v2_set_features/v1"
    assert not any("verifier" in name or "is_winner" in name for name in SET_FEATURE_NAMES)


def test_set_aware_features_are_permutation_invariant_over_intents_and_fills() -> None:
    batch = generate_synthetic_batch(rng=Random(602), batch_index=0, target_candidate_count=12)
    candidate = batch.candidates[0].candidate
    shuffled_candidate = replace(candidate, fills=tuple(reversed(candidate.fills)))

    original = extract_upba_v2_set_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=candidate,
    )
    shuffled = extract_upba_v2_set_feature_record(
        pool=batch.pool,
        intents=tuple(reversed(batch.intents)),
        balances=batch.balances,
        candidate=shuffled_candidate,
    )

    assert shuffled.values == original.values


def test_set_aware_feature_record_combines_aggregate_and_set_blocks() -> None:
    batch = generate_synthetic_batch(rng=Random(603), batch_index=0, target_candidate_count=12)
    record = extract_upba_v2_set_aware_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=batch.candidates[0].candidate,
    )

    assert record.feature_names == SET_AWARE_FEATURE_NAMES
    assert len(record.values) == SET_AWARE_FEATURE_DIM
    assert record.raw["aggregate_feature_dim"] == 96
    assert record.raw["set_feature_dim"] == SET_FEATURE_DIM


def test_dataset_rows_include_optional_set_aware_feature_block() -> None:
    rows = list(generate_dataset_rows(batches=1, candidates_per_batch=8, seed=604))

    assert rows
    assert tuple(rows[0]["set_feature_names"]) == SET_FEATURE_NAMES
    assert tuple(rows[0]["set_aware_feature_names"]) == SET_AWARE_FEATURE_NAMES
    assert len(rows[0]["set_features"]) == SET_FEATURE_DIM
    assert len(rows[0]["set_aware_features"]) == SET_AWARE_FEATURE_DIM


def test_set_aware_linear_model_scores_candidates_without_verifier_authority(tmp_path) -> None:
    batch = generate_synthetic_batch(rng=Random(605), batch_index=0, target_candidate_count=12)
    model = LinearEnergyModel(
        feature_names=SET_AWARE_FEATURE_NAMES,
        weights=tuple(0.0 for _ in SET_AWARE_FEATURE_NAMES),
    )
    scorer = scorer_from_linear_model(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        model=model,
    )

    ranked = rank_upba_v2_candidates(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[item.candidate for item in batch.candidates],
        scorer=scorer,
    )

    assert len(ranked) == len(batch.candidates)
    assert {item.energy for item in ranked} == {0.0}

    model_path = tmp_path / "set_aware_model.json"
    save_linear_model(model, model_path)
    report = inspect_model(model_path, top_n=3)
    assert report["feature_block"] == "set-aware"
    assert report["feature_dim"] == SET_AWARE_FEATURE_DIM
    assert report["forbidden_feature_names"] == []


def test_train_linear_ranker_supports_set_aware_feature_block() -> None:
    rows = list(generate_dataset_rows(batches=2, candidates_per_batch=10, seed=606))
    model = train_linear_ranker(
        rows,
        epochs=1,
        learning_rate=0.01,
        margin=1.0,
        seed=606,
        init="zero",
        feature_block="set-aware",
    )

    assert model.feature_names == SET_AWARE_FEATURE_NAMES
    assert len(model.weights) == SET_AWARE_FEATURE_DIM
