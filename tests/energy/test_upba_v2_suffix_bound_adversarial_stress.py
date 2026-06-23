from __future__ import annotations

from tools.stress_upba_v2_suffix_bound_adversarial import stress_adversarial_suffix_bound


def test_suffix_bound_adversarial_stress_smoke() -> None:
    report = stress_adversarial_suffix_bound(
        batches=3,
        candidates_per_batch=16,
        seed=20260544,
    )
    summary = report["summary"]

    assert report["schema"] == "zenodex/energy/upba_v2_suffix_bound_adversarial_stress/v1"
    assert report["ok"] is True
    assert report["safety"]["invalid_accept_count"] == 0
    assert summary["evaluated_batches"] == 3
    assert summary["adversary_invalid_count"] == 3
    assert summary["adversary_disqualified_count"] == 3
    assert summary["with_disqualifiers_certificate_ok_count"] == 3
    assert summary["without_disqualifiers_certificate_ok_count"] == 0
    assert summary["declared_output_only_forced_fail_count"] == 3
