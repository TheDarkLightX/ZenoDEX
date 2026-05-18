from __future__ import annotations

import os
from pathlib import Path

from tools.check_zenoenergy_research_evidence import (
    _popperpad_env,
    replay_zenoenergy_evidence,
)


ROOT = Path(__file__).resolve().parents[2]


def test_research_evidence_replay_receipt_passes_without_doctor() -> None:
    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)
    check_ids = {str(check["check_id"]) for check in report["checks"]}

    assert report["schema"] == "zenodex/energy/research_evidence_replay_receipt/v1"
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["passed_count"] == report["check_count"] == 104
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
        "objective_tuned.cross_seed_safety",
        "objective_tuned.beats_hand",
        "objective_tuned.hard_case_top10",
        "objective_tuned.negative_vs_gap_weighted",
        "synthetic_candidate_coverage.synthetic_only",
        "synthetic_candidate_coverage.candidate_types",
        "synthetic_candidate_coverage.bounded_rows",
        "synthetic_candidate_coverage.winner_and_hard_negative_balance",
        "synthetic_candidate_coverage.feature_schema_dims",
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
        "autotrader_energy.schema",
        "autotrader_energy.synthetic_metadata",
        "autotrader_energy.safety",
        "autotrader_energy.learned_beats_random",
        "autotrader_energy.negative_vs_hand",
        "autotrader_energy_hard.schema",
        "autotrader_energy_hard.synthetic_metadata",
        "autotrader_energy_hard.safety",
        "autotrader_energy_hard.learned_beats_hand",
        "autotrader_energy_hard.profile_nonvacuous",
        "popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517",
        "popperpad.status.H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517",
        "popperpad.status.H_ZENOENERGY_SOTA_DECISION_MAP_RECEIPT_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_STRICTLY_IMPROVES_PAIRWISE_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_STRICTLY_IMPROVES_PAIRWISE_20260518",
        "popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_BEATS_HAND_ENERGY_20260518",
        "popperpad.status.H_ZENOENERGY_OBJECTIVE_TUNED_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_OBJECTIVE_TUNED_STRICTLY_BEATS_GAP_WEIGHTED_20260518",
        "popperpad.status.H_ZENOENERGY_SYNTHETIC_CANDIDATE_COVERAGE_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_V0_SAFETY_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_V0_BEATS_RANDOM_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_V0_STRICTLY_BEATS_HAND_ENERGY_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_HARD_V1_SAFETY_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_HARD_V1_BEATS_HAND_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_HARD_V1_PROFILE_NONVACUOUS_20260518",
    }.issubset(check_ids)


def test_popperpad_doctor_env_preserves_caller_pythonpath(
    monkeypatch, tmp_path: Path
) -> None:
    repo_popperpad = tmp_path / "external/PopperPad/src"
    repo_popperpad.mkdir(parents=True)
    caller_path = "/tmp/local-popperpad-src"
    monkeypatch.setenv("PYTHONPATH", caller_path)

    env = _popperpad_env(tmp_path)
    entries = env["PYTHONPATH"].split(os.pathsep)

    assert entries == [str(repo_popperpad), caller_path]
