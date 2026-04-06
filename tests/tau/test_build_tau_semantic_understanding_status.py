from __future__ import annotations

from tools.build_tau_semantic_understanding_status import build_semantic_understanding_status


def test_build_tau_semantic_understanding_status() -> None:
    status = build_semantic_understanding_status()
    summary = status["summary"]
    entries = status["entries"]

    assert status["schema"] == "zenodex/tau/semantic-understanding-status/v1"
    assert summary["recommended_spec_count"] == len(entries)
    assert summary["execution_observed_count"] == 149
    assert summary["execution_hard_count"] == 25
    assert summary["confirmed_reviewed_spec_count"] == 11
    assert summary["lightweight_contract_count"] == 4
    assert summary["semantic_contract_count"] == 4
    assert summary["formal_contract_count"] == 4
    assert summary["formal_active_or_promoted_count"] == 4
    assert summary["bounded_formal_seed_count"] == 4

    by_id = {entry["spec_id"]: entry for entry in entries}
    assert by_id["sandwich_detection_v1"]["understanding_tier"] == "bounded_formal_seeded"
    assert by_id["sandwich_detection_v1"]["formal_contract_covered"] is True
    assert by_id["sandwich_detection_v1"]["formal_contract_status"] == "active"
    assert by_id["sandwich_detection_v1"]["proof_scope"] == "bounded_assurance_domain"
    assert by_id["sandwich_detection_v1"]["promotion_blocker"] == "bounded_scope_only"
    assert by_id["slippage_bounds_v2"]["understanding_tier"] == "source_backed_confirmed_review"
    assert by_id["slippage_bounds_v2"]["formal_contract_covered"] is False
    assert by_id["slippage_bounds_v2"]["promotion_blocker"] == "missing_formal_contract"
    assert by_id["perp_tau_ingress_schema_guard_v1"]["understanding_tier"] == "semantic_contract_covered"
    assert by_id["perp_tau_ingress_schema_guard_v1"]["lightweight_contract_covered"] is True
    assert by_id["perp_tau_ingress_schema_guard_v1"]["formal_contract_covered"] is False
    assert by_id["perp_tau_ingress_schema_guard_v1"]["promotion_blocker"] == "missing_formal_contract"
    assert by_id["fee_distribution_v1"]["understanding_tier"] == "structured_hard_review"
