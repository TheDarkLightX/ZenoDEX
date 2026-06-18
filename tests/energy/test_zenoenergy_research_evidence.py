from __future__ import annotations

from pathlib import Path

import pytest

from tools import check_zenoenergy_research_evidence as research_mod
from tools.check_zenoenergy_research_evidence import replay_zenoenergy_evidence

ROOT = Path(__file__).resolve().parents[2]


def _check_by_id(report: dict[str, object], check_id: str) -> dict[str, object]:
    for check in report["checks"]:  # type: ignore[index]
        if isinstance(check, dict) and check.get("check_id") == check_id:
            return check
    raise AssertionError(f"missing check {check_id}")


def test_research_evidence_replay_receipt_passes_without_doctor() -> None:
    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)
    check_ids = {str(check["check_id"]) for check in report["checks"]}

    assert report["schema"] == "zenodex/energy/research_evidence_replay_receipt/v1"
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["passed_count"] == report["check_count"] == 280
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
        "fallback_checked_stop_formal.objective_equivalence_limit",
        "energy_order_alone_formal.schema",
        "energy_order_alone_formal.commands",
        "energy_order_alone_formal.names",
        "energy_order_alone_formal.negative_boundary",
        "fallback_permutation_audit.permutation_premise",
        "fallback_permutation_audit.checked_stop_offline",
        "fallback_permutation_audit.objective_equivalence_metrics",
        "topk_sweep.learned_checked_stop_k2",
        "topk_sweep.objective_equivalence_metrics",
        "topk_sweep.random_top10_negative",
        "objective_equiv_training_hygiene.schema",
        "objective_equiv_training_hygiene.modes",
        "objective_equiv_training_hygiene.source_hooks",
        "objective_equiv_training_hygiene.safety_boundary",
        "objective_equiv_training_hygiene.no_metric_claim",
        "production_promotion_gate.schema",
        "production_promotion_gate.blocks_current_research",
        "production_promotion_gate.research_replay_clean",
        "production_promotion_gate.safety_contract",
        "production_promotion_gate.doc_and_source",
        "replay_source_manifest.schema",
        "replay_source_manifest.schemas_and_artifacts",
        "replay_source_manifest.source_hygiene_hooks",
        "replay_source_manifest.production_gate_hook",
        "replay_source_manifest.negative_knowledge",
        "replay_source_manifest_builder.schema",
        "replay_source_manifest_builder.artifacts_and_schemas",
        "replay_source_manifest_builder.fail_closed_hooks",
        "replay_source_manifest_builder.safety_and_limits",
        "replay_secret_scan.schema",
        "replay_secret_scan.schemas_rules_and_artifacts",
        "replay_secret_scan.source_hooks",
        "replay_secret_scan.safety_and_limits",
        "replay_coverage_profile.schema",
        "replay_coverage_profile.schemas_thresholds_and_artifacts",
        "replay_coverage_profile.source_hooks",
        "replay_coverage_profile.production_hooks",
        "replay_coverage_profile.safety_and_limits",
        "real_replay_report_builder.schema",
        "real_replay_report_builder.targets_and_artifacts",
        "real_replay_report_builder.source_hygiene_hooks",
        "real_replay_report_builder.safety_boundary",
        "production_evidence_bundle.schema",
        "production_evidence_bundle.artifacts_and_schemas",
        "production_evidence_bundle.source_hooks",
        "production_evidence_bundle.safety_and_limits",
        "sota_decision_map.schema",
        "sota_decision_map.sources_and_boundary",
        "sota_decision_map.decisions",
        "sota_decision_map.next_experiments",
        "sota_decision_map.negative_knowledge",
        "autotrader_energy_hard_cross_seed.schema",
        "autotrader_energy_hard_cross_seed.safety",
        "autotrader_energy_hard_cross_seed.learned_beats_hand_all",
        "autotrader_energy_hard_cross_seed.profile_nonvacuous",
        "autotrader_energy_hard_cross_seed.doc_and_recall",
        "autotrader_energy_shadow_bridge.schema",
        "autotrader_energy_shadow_bridge.safety",
        "autotrader_energy_shadow_bridge.nonvacuous_fixture",
        "autotrader_energy_shadow_bridge.learned_ties_hand_negative",
        "autotrader_energy_shadow_bridge.objective_equiv_argmax",
        "autotrader_energy_shadow_bridge.doc_boundary",
        "dominance_cover.schema",
        "dominance_cover.winner_only_passes",
        "dominance_cover.weak_pruned_rejected",
        "dominance_cover.hand_top1_nonvacuous",
        "dominance_cover.safety_and_hooks",
        "wes_dominance_search.schema",
        "wes_dominance_search.candidate_corpus",
        "wes_dominance_search.useful_ordering",
        "wes_dominance_search.safety",
        "wes_dominance_search.source_hooks",
        "dominance_prefix.schema",
        "dominance_prefix.safety",
        "dominance_prefix.learned_and_hybrid_cover_first",
        "dominance_prefix.beats_controls",
        "dominance_prefix.boundary_and_hooks",
        "suffix_bound.schema",
        "suffix_bound.safety",
        "suffix_bound.learned_and_hybrid_stop_first",
        "suffix_bound.beats_controls",
        "suffix_bound.boundary_and_hooks",
        "suffix_bound_cross_seed.schema",
        "suffix_bound_cross_seed.safety",
        "suffix_bound_cross_seed.learned_and_hybrid_hold",
        "suffix_bound_cross_seed.beats_controls",
        "suffix_bound_cross_seed.boundary_and_hooks",
        "suffix_bound_adversarial.schema",
        "suffix_bound_adversarial.safety",
        "suffix_bound_adversarial.disqualifier_closes",
        "suffix_bound_adversarial.declared_output_negative",
        "suffix_bound_adversarial.boundary_and_hooks",
        "suffix_bound_adversarial_families.schema",
        "suffix_bound_adversarial_families.safety",
        "suffix_bound_adversarial_families.family_coverage",
        "suffix_bound_adversarial_families.disqualifiers_close",
        "suffix_bound_adversarial_families.declared_output_negative",
        "suffix_bound_adversarial_families.boundary_and_hooks",
        "negative_curriculum.schema",
        "negative_curriculum.weights",
        "negative_curriculum.epiplexity_proxy",
        "negative_curriculum.source_hooks",
        "negative_curriculum.negative_knowledge",
        "curriculum_ranker.schema",
        "curriculum_ranker.safety",
        "curriculum_ranker.negative_result",
        "curriculum_ranker.source_hooks",
        "curriculum_ranker.doc_boundary",
        "data_scaling.schema",
        "data_scaling.safety",
        "data_scaling.quantity_curve",
        "data_scaling.saturates_below_current",
        "data_scaling.source_hooks",
        "quality_selection.schema",
        "quality_selection.safety",
        "quality_selection.medium_budget_gain",
        "quality_selection.small_budget_negative",
        "quality_selection.source_hooks",
        "ensemble.schema",
        "ensemble.safety",
        "ensemble.top10_and_default_negative",
        "ensemble.uncertainty_signal",
        "ensemble.source_hooks",
        "best_model_registry.schema_and_promoted",
        "best_model_registry.files_and_hashes",
        "best_model_registry.upba_default",
        "best_model_registry.autotrader_retained",
        "best_model_registry.advisory_boundary",
        "upba_v2_model_leaderboard.schema_and_decision",
        "upba_v2_model_leaderboard.obligations",
        "upba_v2_model_leaderboard.metric_dominance",
        "upba_v2_model_leaderboard.safety_boundary",
        "upba_v2_model_leaderboard.source_hooks",
        "epiplexity_literature.schema",
        "epiplexity_literature.sources",
        "epiplexity_literature.task_relevance_gate",
        "epiplexity_literature.proxy_boundary",
        "epiplexity_literature.source_hooks",
        "synthetic_data_limits.schema",
        "synthetic_data_limits.sources",
        "synthetic_data_limits.verifier_label_boundary",
        "synthetic_data_limits.replay_boundary",
        "synthetic_data_limits.source_hooks",
        "langevin_discovery.schema",
        "langevin_discovery.verifier_selection",
        "langevin_discovery.energy_is_not_safety",
        "langevin_discovery.source_hooks",
        "autotrader_refiner_boundary.schema",
        "autotrader_refiner_boundary.policy_selection",
        "autotrader_refiner_boundary.synthetic_gain",
        "autotrader_refiner_boundary.source_hooks",
        "jepa_logic_boundary.schema",
        "jepa_logic_boundary.future_score_advisory",
        "jepa_logic_boundary.logic_negation_warning",
        "jepa_logic_boundary.safety_contract",
        "jepa_logic_boundary.source_hooks",
        "autotrader_jepa_ux.schema",
        "autotrader_jepa_ux.future_tension",
        "autotrader_jepa_ux.future_policy_prediction",
        "autotrader_jepa_ux.stress_correlations",
        "autotrader_jepa_ux.counterfactual_controls",
        "autotrader_jepa_ux.warning_match",
        "autotrader_jepa_ux.policy_boundary",
        "autotrader_jepa_ux.ranking_quality",
        "autotrader_jepa_ux.ux_explanations",
        "autotrader_jepa_ux.research_inputs",
        "autotrader_jepa_ux.source_hooks",
        "popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517",
        "popperpad.status.H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517",
        "popperpad.status.H_ZENOENERGY_SOTA_DECISION_MAP_RECEIPT_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_STRICTLY_IMPROVES_PAIRWISE_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_STRICTLY_IMPROVES_PAIRWISE_20260518",
        "popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_SAFETY_20260518",
        "popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_BEATS_HAND_ENERGY_20260518",
        "popperpad.status.H_ZENOENERGY_OBJECTIVE_EQUIV_FORMAL_BOUNDARY_RECEIPT_20260518",
        "popperpad.status.H_ZENOENERGY_OBJECTIVE_EQUIV_RUNTIME_TELEMETRY_20260518",
        "popperpad.status.H_ZENOENERGY_OBJECTIVE_EQUIV_TRAINING_HYGIENE_20260518",
        "popperpad.status.H_ZENOENERGY_PRODUCTION_GATE_BLOCKS_WITHOUT_REAL_REPLAY_20260518",
        "popperpad.status.H_ZENOENERGY_REPLAY_SOURCE_MANIFEST_CHECKER_20260518",
        "popperpad.status.H_ZENOENERGY_REPLAY_SOURCE_MANIFEST_BUILDER_20260518",
        "popperpad.status.H_ZENOENERGY_REPLAY_SECRET_SCAN_20260518",
        "popperpad.status.H_ZENOENERGY_REPLAY_COVERAGE_PROFILE_20260518",
        "popperpad.status.H_ZENOENERGY_REAL_REPLAY_REPORT_BUILDER_20260518",
        "popperpad.status.H_ZENOENERGY_PRODUCTION_EVIDENCE_BUNDLE_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_SAFETY_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_BEATS_HAND_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_PROFILE_NONVACUOUS_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_SAFETY_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_NONVACUOUS_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_LEARNED_BEATS_HAND_20260518",
        "popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_OBJECTIVE_EQUIV_TOP1_20260518",
        "popperpad.status.H_ZENOENERGY_DOMINANCE_COVER_RUNTIME_20260518",
        "popperpad.status.H_ZENOENERGY_WEAK_PRUNED_DOMINANCE_ALWAYS_PASSES_20260518",
        "popperpad.status.H_ZENOENERGY_WES_DOMINANCE_SEARCH_BRIDGE_20260518",
        "popperpad.status.H_ZENOENERGY_WES_REMOVES_FULL_LIST_COMPLETENESS_20260518",
        "popperpad.status.H_ZENOENERGY_DOMINANCE_PREFIX_AUDIT_20260519",
        "popperpad.status.H_ZENOENERGY_DOMINANCE_PREFIX_AUTHORIZES_LIVE_EARLY_STOP_20260519",
        "popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_EARLY_STOP_20260519",
        "popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_REMOVES_COVERAGE_OBLIGATION_20260519",
        "popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_CROSS_SEED_STRESS_20260519",
        "popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_CROSS_SEED_REMOVES_REAL_REPLAY_NEED_20260519",
        "popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS_20260519",
        "popperpad.status.H_ZENOENERGY_DECLARED_OUTPUT_SUFFIX_BOUND_SUFFICIENT_20260519",
        "popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_ADVERSARIAL_FAMILY_STRESS_20260519",
        "popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_ADVERSARIAL_FAMILY_STRESS_PROVES_GRID_COMPLETENESS_20260519",
        "popperpad.status.H_ZENOENERGY_NEGATIVE_CURRICULUM_EPIPLEXITY_20260519_V2",
        "popperpad.status.H_ZENOENERGY_EPIPLEXITY_PROXY_IS_CORRECTNESS_CERTIFICATE_20260519_V2",
        "popperpad.status.H_ZENOENERGY_EPIPLEXITY_LITERATURE_TASK_GATE_20260519",
        "popperpad.status.H_ZENOENERGY_EPIPLEXITY_PROXY_PREDICTS_DOWNSTREAM_IMPROVEMENT_20260519",
        "popperpad.status.H_ZENOENERGY_CURRICULUM_RANKER_SAFETY_20260519",
        "popperpad.status.H_ZENOENERGY_CURRICULUM_RANKER_BEATS_GAP_WEIGHTED_20260519",
        "popperpad.status.H_ZENOENERGY_ENERGY_ORDER_ALONE_FORMAL_BOUNDARY_20260519",
        "popperpad.status.H_ZENOENERGY_ENERGY_ORDER_ALONE_AUTHORIZES_OPTIMALITY_20260519",
        "popperpad.status.H_ZENOENERGY_DATA_SCALING_RAW_VOLUME_HELPS_20260519",
        "popperpad.status.H_ZENOENERGY_DATA_SCALING_RAW_VOLUME_BEATS_DEFAULT_20260519",
        "popperpad.status.H_ZENOENERGY_QUALITY_SELECTION_MEDIUM_BUDGET_HELPS_20260519",
        "popperpad.status.H_ZENOENERGY_QUALITY_SELECTION_ALWAYS_BEATS_RAW_20260519",
        "popperpad.status.H_ZENOENERGY_ENSEMBLE_SAFETY_20260519",
        "popperpad.status.H_ZENOENERGY_ENSEMBLE_DISAGREEMENT_SIGNAL_20260519",
        "popperpad.status.H_ZENOENERGY_ENSEMBLE_BEATS_GAP_WEIGHTED_20260519",
        "popperpad.status.H_AUTOTRADER_JEPA_UX_FUTURE_RISK_20260519",
    }.issubset(check_ids)


def test_research_evidence_rejects_coerced_coverage_profile_thresholds() -> None:
    report = _coverage_profile_receipt()
    thresholds = report["thresholds"]
    assert isinstance(thresholds, dict)
    upba = thresholds["upba"]
    assert isinstance(upba, dict)
    upba["min_pool_count"] = "3"

    checks = research_mod._check_replay_coverage_profile(
        report,
        doc_text=(
            "zenodex/energy/replay_coverage_profile/v1 "
            "zenodex/energy/replay_coverage_profile_check/v1"
        ),
        source_text=(
            "MIN_UPBA_POOL_COUNT MIN_UPBA_HARD_NEGATIVE_FAMILY_COUNT "
            "MIN_AUTOTRADER_GUARD_FAMILY_COUNT source_report_count_match "
            "coverage_profile_summary"
        ),
        test_text=(
            "test_upba_coverage_profile_rejects_thin_hard_negatives "
            "test_autotrader_coverage_profile_rejects_source_mismatch"
        ),
        production_gate_source=(
            "_coverage_profile_check_ok coverage_profile_ok replay coverage profile check"
        ),
    )

    by_id = {check.check_id: check for check in checks}
    assert by_id["replay_coverage_profile.schemas_thresholds_and_artifacts"].passed is False


def _coverage_profile_receipt() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_coverage_profile_receipt/v1",
        "profile_schema": "zenodex/energy/replay_coverage_profile/v1",
        "profile_check_schema": "zenodex/energy/replay_coverage_profile_check/v1",
        "artifacts": [
            "tools/check_zenoenergy_replay_coverage_profile.py",
            "tests/energy/test_zenoenergy_replay_coverage_profile.py",
            "docs/ZENO_ENERGY_REPLAY_COVERAGE_PROFILE.md",
        ],
        "integrations": [
            "tools/build_zenoenergy_real_replay_report.py",
            "tools/check_zenoenergy_production_promotion.py",
            "tools/build_zenoenergy_production_evidence_bundle.py",
        ],
        "thresholds": {
            "upba": {
                "min_pool_count": 3,
                "min_hard_negative_family_count": 4,
            },
            "autotrader": {
                "min_guard_family_count": 4,
            },
        },
        "safety": {
            "verifier_authoritative": True,
            "policy_guards_authoritative": True,
            "scorer_authorizes_settlement_or_trade": False,
            "coverage_profile_authorizes_production": False,
        },
        "limits": ["representative traffic is an external assumption"],
        "negative_knowledge": [
            "Aggregate batch counts are insufficient.",
            "This is not a production authorization path.",
        ],
    }


def test_research_evidence_replay_rejects_truthy_string_receipt_ok(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_truthy_ok(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_suffix_bound_cross_seed_seed20260541_20260543.json":
            payload["ok"] = "true"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_truthy_ok)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "suffix_bound_cross_seed.schema")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_suffix_bound_parameters(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_parameter(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_suffix_bound_cross_seed_seed20260541_20260543.json":
            payload["batches_per_config"] = "60"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_parameter)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "suffix_bound_cross_seed.schema")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_formal_command_exit_code(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_exit_code(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_fallback_checked_stop_formal_receipt.json":
            commands = payload["commands"]
            assert isinstance(commands, list)
            first = commands[0]
            assert isinstance(first, dict)
            first["exit_code"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_exit_code)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "fallback_checked_stop_formal.commands")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_mode_safety_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_mode_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_set_aware_compare_120x80_seed20260523_20260524.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            aggregate = modes["aggregate_learned"]
            assert isinstance(aggregate, dict)
            aggregate["invalid_accept_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_mode_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "set_aware.zero_invalid_accepts")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_performance_metric(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_metric(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_set_aware_compare_120x80_seed20260523_20260524.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            aggregate = modes["aggregate_learned"]
            assert isinstance(aggregate, dict)
            aggregate["top_10_recall"] = "1.0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_metric)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "set_aware.aggregate_top10_recall")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_listwise_permutation_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_listwise_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_listwise_set_ranker_seed20260532_20260533.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            listwise = modes["listwise_set"]
            assert isinstance(listwise, dict)
            listwise["permutation_violation_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_listwise_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "listwise_set.safety")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_listwise_rate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_listwise_rate(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_listwise_set_ranker_seed20260532_20260533.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            listwise = modes["listwise_set"]
            assert isinstance(listwise, dict)
            listwise["top_10_recall"] = "1.0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_listwise_rate)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "listwise_set.top10_and_checked_stop")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_listwise_cross_seed_safety_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_cross_seed_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_listwise_set_ranker_cross_seed_seed20260532_20260537.json":
            safety = payload["safety"]
            assert isinstance(safety, dict)
            safety["invalid_accept_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_cross_seed_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "listwise_cross_seed.safety")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_listwise_cross_seed_pass_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_cross_seed_pass_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_listwise_set_ranker_cross_seed_seed20260532_20260537.json":
            aggregate = payload["aggregate"]
            assert isinstance(aggregate, dict)
            aggregate["listwise_top10_pass_count"] = str(payload["run_count"])
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_cross_seed_pass_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "listwise_cross_seed.top10_and_checked_stop")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_gap_weighted_safety_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_gap_weighted_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_gap_weighted_cross_seed_stress_250x3x3.json":
            summary = payload["summary"]
            assert isinstance(summary, dict)
            learned = summary["learned"]
            assert isinstance(learned, dict)
            learned["invalid_accept_count_total"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_gap_weighted_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "gap_weighted_default.cross_seed_safety")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_gap_weighted_hard_case_rate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_hard_case_rate(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_gap_weighted_hard_cases_500x3x3.json":
            summary = payload["summary"]
            assert isinstance(summary, dict)
            summary["top_10_recall"] = "1.0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_hard_case_rate)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "gap_weighted_default.hard_case_recall")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_gap_weighted_model_audit_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_model_audit_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_gap_weighted_model_audit.json":
            payload["feature_dim"] = "96"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_model_audit_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "gap_weighted_default.model_audit_boundary")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_neighborhood_safety_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_neighborhood_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_neighborhood_benchmark_seed20260525.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            neighborhood = modes["neighborhood"]
            assert isinstance(neighborhood, dict)
            neighborhood["invalid_accept_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_neighborhood_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "neighborhood.safety")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_neighborhood_regret_metric(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_neighborhood_metric(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_neighborhood_benchmark_seed20260525.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            neighborhood = modes["neighborhood"]
            assert isinstance(neighborhood, dict)
            neighborhood["mean_volume_regret"] = "4.7"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_neighborhood_metric)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "neighborhood.regret_reduced")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_repair_selector_safety_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_repair_selector_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_repair_selector_benchmark_seed20260526_20260527.json":
            safety = payload["safety"]
            assert isinstance(safety, dict)
            safety["invalid_accept_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_repair_selector_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "repair_selector.safety")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_repair_selector_compression_metric(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_repair_selector_metric(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_repair_selector_benchmark_seed20260526_20260527.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            learned = modes["learned_selected"]
            assert isinstance(learned, dict)
            learned["candidate_count_mean"] = "8"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_repair_selector_metric)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "repair_selector.compression")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_repair_selector_cross_seed_safety_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_cross_seed_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_repair_selector_cross_seed_seed20260526_20260531.json":
            safety = payload["safety"]
            assert isinstance(safety, dict)
            safety["invalid_accept_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_cross_seed_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "repair_selector_cross_seed.safety")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_repair_selector_cross_seed_regret_metric(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_cross_seed_metric(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_repair_selector_cross_seed_seed20260526_20260531.json":
            aggregate = payload["aggregate"]
            assert isinstance(aggregate, dict)
            modes = aggregate["modes"]
            assert isinstance(modes, dict)
            learned = modes["learned_selected"]
            assert isinstance(learned, dict)
            mean_volume_regret = learned["mean_volume_regret"]
            assert isinstance(mean_volume_regret, dict)
            mean_volume_regret["mean"] = "0.0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_cross_seed_metric)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "repair_selector_cross_seed.aggregate_regret")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_fallback_permutation_safety_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_fallback_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_fallback_permutation_audit_200_seed20260518.json":
            payload["invalid_accept_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_fallback_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "fallback_permutation_audit.zero_invalid_accepts")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_fallback_permutation_recovery_metric(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_fallback_metric(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_fallback_permutation_audit_200_seed20260518.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            learned = modes["learned"]
            assert isinstance(learned, dict)
            learned["fallback_recovered_count"] = "200"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_fallback_metric)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "fallback_permutation_audit.learned_recovery")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_topk_sweep_permutation_count(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_topk_permutation_count(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_topk_sweep_holdout_seed20260518.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            learned = modes["learned"]
            assert isinstance(learned, dict)
            learned["permutation_violation_count"] = "0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_topk_permutation_count)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "topk_sweep.permutation_premise")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_coerced_topk_sweep_false_exclusion_metric(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_coerced_topk_metric(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_topk_sweep_holdout_seed20260518.json":
            modes = payload["modes"]
            assert isinstance(modes, dict)
            learned = modes["learned"]
            assert isinstance(learned, dict)
            top_k = learned["top_k"]
            assert isinstance(top_k, dict)
            k2 = top_k["2"]
            assert isinstance(k2, dict)
            k2["false_exclusion_rate"] = "0.0"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_coerced_topk_metric)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "topk_sweep.learned_checked_stop_k2")
    assert check["passed"] is False


def test_research_evidence_replay_rejects_truthy_string_obligation_passed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_load_json = research_mod._load_json

    def load_json_with_truthy_obligation(path: Path) -> dict[str, object]:
        payload = original_load_json(path)
        if path.name == "upba_v2_energy_model_leaderboard.json":
            obligations = payload["obligations"]
            assert isinstance(obligations, list)
            first = obligations[0]
            assert isinstance(first, dict)
            first["passed"] = "true"
        return payload

    monkeypatch.setattr(research_mod, "_load_json", load_json_with_truthy_obligation)

    report = replay_zenoenergy_evidence(root=ROOT, run_popperpad_doctor=False)

    assert report["ok"] is False
    check = _check_by_id(report, "upba_v2_model_leaderboard.obligations")
    assert check["passed"] is False
