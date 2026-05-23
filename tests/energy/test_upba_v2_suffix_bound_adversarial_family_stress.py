from __future__ import annotations

from tools.stress_upba_v2_suffix_bound_adversarial_families import (
    stress_adversarial_suffix_bound_families,
)


def test_suffix_bound_adversarial_family_stress_smoke() -> None:
    report = stress_adversarial_suffix_bound_families(
        batches=4,
        candidates_per_batch=16,
        seed=20260545,
    )
    summary = report["summary"]

    assert (
        report["schema"]
        == "zenodex/energy/upba_v2_suffix_bound_adversarial_family_stress/v1"
    )
    assert report["ok"] is True
    assert report["safety"]["invalid_accept_count"] == 0
    assert summary["evaluated_batches"] == 4
    assert summary["family_count"] == 8
    assert summary["total_cases"] == 32
    assert summary["adversary_invalid_count"] == 32
    assert summary["adversary_disqualified_count"] == 32
    assert summary["with_disqualifiers_certificate_ok_count"] == 32
    assert summary["high_declared_output_forced_fail_count"] == 4
    assert summary["observed_disqualifier_count"] >= 6
