from __future__ import annotations

from tools.audit_upba_energy_synthetic_coverage import (
    EXPECTED_MUTATION_TYPES,
    HARD_NEGATIVE_TYPES,
    audit_synthetic_candidate_coverage,
)


def test_synthetic_candidate_coverage_audit_records_required_classes() -> None:
    report = audit_synthetic_candidate_coverage(
        batches=12,
        candidates_per_batch=24,
        seed=20260540,
    )

    assert report["schema"] == "zenodex/energy/upba_v2_synthetic_candidate_coverage/v1"
    assert report["coverage_ok"] is True
    assert report["synthetic_only"] is True
    assert report["duplicate_hash_batches"] == 0
    assert report["live_secret_key_hits"] == {}
    assert report["missing_required_candidate_types"] == []
    assert set(EXPECTED_MUTATION_TYPES).issubset(set(report["observed_candidate_types"]))
    assert set(HARD_NEGATIVE_TYPES).issubset(set(report["observed_candidate_types"]))
    assert report["winner_batch_rate"] >= 0.90
    assert report["invalid_candidate_count"] > report["valid_candidate_count"]
    assert report["feature_dim_counts"] == {"96": report["candidate_count_total"]}
    assert report["set_feature_dim_counts"] == {"51": report["candidate_count_total"]}
    assert report["set_aware_feature_dim_counts"] == {"147": report["candidate_count_total"]}
