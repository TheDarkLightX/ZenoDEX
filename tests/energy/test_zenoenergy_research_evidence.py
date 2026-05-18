from __future__ import annotations

from pathlib import Path

from tools.check_zenoenergy_research_evidence import replay_zenoenergy_evidence


ROOT = Path(__file__).resolve().parents[2]


def test_research_evidence_replay_receipt_passes_without_doctor() -> None:
    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)
    check_ids = {str(check["check_id"]) for check in report["checks"]}

    assert report["schema"] == "zenodex/energy/research_evidence_replay_receipt/v1"
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["passed_count"] == report["check_count"] == 74
    assert {
        "set_aware.negative_knowledge_recorded",
        "listwise_set.safety",
        "listwise_set.top10_and_checked_stop",
        "listwise_set.negative_knowledge",
        "listwise_cross_seed.safety",
        "listwise_cross_seed.top10_and_checked_stop",
        "listwise_cross_seed.negative_knowledge",
        "gap_weighted_default.cross_seed_safety",
        "gap_weighted_default.cross_seed_beats_hand",
        "gap_weighted_default.hard_case_recall",
        "gap_weighted_default.model_audit_boundary",
        "neighborhood.call_cost_negative",
        "repair_selector_cross_seed.compression_all_pairs",
        "repair_selector_cross_seed.hand_negative",
        "formal_boundary.names",
        "fallback_checked_stop_formal.names",
        "fallback_permutation_audit.permutation_premise",
        "fallback_permutation_audit.checked_stop_offline",
        "topk_sweep.learned_checked_stop_k2",
        "topk_sweep.random_top10_negative",
        "sota_decision_map.schema",
        "sota_decision_map.sources_and_boundary",
        "sota_decision_map.decisions",
        "sota_decision_map.next_experiments",
        "sota_decision_map.negative_knowledge",
        "popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517",
        "popperpad.status.H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517",
        "popperpad.status.H_ZENOENERGY_SOTA_DECISION_MAP_RECEIPT_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_STRICTLY_IMPROVES_PAIRWISE_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_STRICTLY_IMPROVES_PAIRWISE_20260518",
        "popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_BEATS_HAND_ENERGY_20260518",
    }.issubset(check_ids)
