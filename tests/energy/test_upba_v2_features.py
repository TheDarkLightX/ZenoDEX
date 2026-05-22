from __future__ import annotations

from random import Random

from src.energy.upba_v2_features import FEATURE_DIM, FEATURE_NAMES, extract_upba_v2_feature_record
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_upba_v2_feature_schema_is_fixed_width_and_advisory() -> None:
    batch = generate_synthetic_batch(rng=Random(101), batch_index=0, target_candidate_count=12)
    candidate = batch.candidates[0].candidate

    record = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=candidate,
        include_verifier_label=True,
    )

    assert len(FEATURE_NAMES) == FEATURE_DIM == 96
    assert len(record.values) == FEATURE_DIM
    assert "candidate_verifier_accept_flag" not in FEATURE_NAMES
    assert "candidate_valid_objective_volume_log1p" not in FEATURE_NAMES
    assert record.raw["feature_schema"] == "zenodex/energy/upba_v2_features/v1"
    assert record.raw["verifier_ok"] in (True, False)


def test_upba_v2_features_flag_all_zero_candidate_without_verifier_features() -> None:
    batch = generate_synthetic_batch(rng=Random(102), batch_index=0, target_candidate_count=12)
    all_zero = next(item.candidate for item in batch.candidates if item.candidate_type == "invalid_all_zero")

    record = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=all_zero,
        include_verifier_label=True,
    )
    feature_dict = record.feature_dict()

    assert record.raw["verifier_ok"] is False
    assert record.raw["all_zero_fill_vector_flag"] == 1
    assert record.raw["noncanonical_fill_vector_flag"] == 1
    assert feature_dict["candidate_all_zero_fill_vector_flag"] == 1.0
    assert feature_dict["candidate_noncanonical_fill_vector_flag"] == 1.0


def test_upba_v2_features_flag_hard_adversarial_candidate_types() -> None:
    batch = generate_synthetic_batch(rng=Random(103), batch_index=0, target_candidate_count=32)
    by_type = {item.candidate_type: item.candidate for item in batch.candidates}

    unreduced = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=by_type["hard_unreduced_price"],
        include_verifier_label=True,
    )
    schema = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=by_type["hard_schema_policy_mismatch"],
        include_verifier_label=True,
    )

    assert unreduced.raw["verifier_ok"] is False
    assert unreduced.raw["price_ratio_unreduced_flag"] == 1
    assert unreduced.feature_dict()["candidate_price_ratio_unreduced_flag"] == 1.0
    assert schema.raw["verifier_ok"] is False
    assert schema.raw["schema_policy_mismatch_flag"] == 1
    assert schema.feature_dict()["candidate_schema_policy_mismatch_flag"] == 1.0
