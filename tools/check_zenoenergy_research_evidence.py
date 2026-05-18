#!/usr/bin/env python3
"""Replay committed ZenoEnergy research evidence and fail closed on drift."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


@dataclass(frozen=True)
class EvidenceCheck:
    check_id: str
    passed: bool
    detail: str

    def to_dict(self) -> dict[str, object]:
        return {
            "check_id": self.check_id,
            "passed": self.passed,
            "detail": self.detail,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    parser.add_argument("--skip-popperpad-doctor", action="store_true")
    args = parser.parse_args()

    report = replay_zenoenergy_evidence(
        root=args.root,
        run_popperpad_doctor=not args.skip_popperpad_doctor,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def replay_zenoenergy_evidence(
    *,
    root: Path = ROOT,
    run_popperpad_doctor: bool = True,
) -> dict[str, Any]:
    checks: list[EvidenceCheck] = []
    payloads: dict[str, Any] = {}

    set_aware = _load_json(
        root / "data/upba_energy/upba_v2_energy_set_aware_compare_120x80_seed20260523_20260524.json"
    )
    payloads["set_aware"] = set_aware
    checks.extend(_check_set_aware(set_aware))

    listwise_set = _load_json(
        root / "data/upba_energy/upba_v2_energy_listwise_set_ranker_seed20260532_20260533.json"
    )
    payloads["listwise_set"] = listwise_set
    checks.extend(_check_listwise_set(listwise_set))

    listwise_cross_seed = _load_json(
        root
        / "data/upba_energy/upba_v2_energy_listwise_set_ranker_cross_seed_seed20260532_20260537.json"
    )
    payloads["listwise_cross_seed"] = listwise_cross_seed
    checks.extend(_check_listwise_cross_seed(listwise_cross_seed))

    gap_weighted_stress = _load_json(
        root / "data/upba_energy/upba_v2_energy_gap_weighted_cross_seed_stress_250x3x3.json"
    )
    gap_weighted_hard_cases = _load_json(
        root / "data/upba_energy/upba_v2_energy_gap_weighted_hard_cases_500x3x3.json"
    )
    gap_weighted_model_audit = _load_json(
        root / "data/upba_energy/upba_v2_energy_gap_weighted_model_audit.json"
    )
    payloads["gap_weighted_stress"] = gap_weighted_stress
    payloads["gap_weighted_hard_cases"] = gap_weighted_hard_cases
    payloads["gap_weighted_model_audit"] = gap_weighted_model_audit
    checks.extend(
        _check_gap_weighted_default(
            gap_weighted_stress,
            gap_weighted_hard_cases,
            gap_weighted_model_audit,
        )
    )

    neighborhood = _load_json(
        root / "data/upba_energy/upba_v2_energy_neighborhood_benchmark_seed20260525.json"
    )
    payloads["neighborhood"] = neighborhood
    checks.extend(_check_neighborhood(neighborhood))

    repair = _load_json(
        root / "data/upba_energy/upba_v2_energy_repair_selector_benchmark_seed20260526_20260527.json"
    )
    payloads["repair_selector"] = repair
    checks.extend(_check_repair_selector(repair))

    cross_seed = _load_json(
        root / "data/upba_energy/upba_v2_repair_selector_cross_seed_seed20260526_20260531.json"
    )
    payloads["repair_selector_cross_seed"] = cross_seed
    checks.extend(_check_repair_selector_cross_seed(cross_seed))

    formal = _load_json(
        root / "data/upba_energy/upba_v2_repair_selector_formal_boundary_receipt.json"
    )
    payloads["formal_boundary"] = formal
    checks.extend(_check_formal_boundary(formal))

    fallback_formal = _load_json(
        root / "data/upba_energy/upba_v2_fallback_checked_stop_formal_receipt.json"
    )
    lean_source = (
        root / "lean-mathlib/Proofs/UniformBatchOptimality.lean"
    ).read_text(encoding="utf-8")
    payloads["fallback_checked_stop_formal"] = fallback_formal
    checks.extend(_check_fallback_checked_stop_formal(fallback_formal, lean_source))

    fallback_audit = _load_json(
        root / "data/upba_energy/upba_v2_energy_fallback_permutation_audit_200_seed20260518.json"
    )
    payloads["fallback_permutation_audit"] = fallback_audit
    checks.extend(_check_fallback_permutation_audit(fallback_audit))

    topk_sweep = _load_json(
        root / "data/upba_energy/upba_v2_energy_topk_sweep_holdout_seed20260518.json"
    )
    payloads["topk_sweep"] = topk_sweep
    checks.extend(_check_topk_sweep(topk_sweep))

    training_hygiene = _load_json(
        root / "data/upba_energy/upba_v2_objective_equiv_training_hygiene_receipt.json"
    )
    trainer_source = (root / "tools/train_upba_energy.py").read_text(encoding="utf-8")
    training_test_source = (
        root / "tests/energy/test_upba_v2_training_hygiene.py"
    ).read_text(encoding="utf-8")
    training_hygiene_doc = (
        root / "docs/ZENO_ENERGY_OBJECTIVE_EQUIV_TRAINING_HYGIENE.md"
    ).read_text(encoding="utf-8")
    payloads["objective_equiv_training_hygiene"] = training_hygiene
    checks.extend(
        _check_objective_equiv_training_hygiene(
            training_hygiene,
            trainer_source,
            training_test_source,
            training_hygiene_doc,
        )
    )

    production_gate = _load_json(
        root / "data/upba_energy/zenoenergy_production_promotion_gate_receipt.json"
    )
    production_gate_doc = (
        root / "docs/ZENO_ENERGY_PRODUCTION_GATE.md"
    ).read_text(encoding="utf-8")
    production_gate_source = (
        root / "tools/check_zenoenergy_production_promotion.py"
    ).read_text(encoding="utf-8")
    payloads["production_promotion_gate"] = production_gate
    checks.extend(
        _check_production_promotion_gate(
            production_gate,
            production_gate_doc,
            production_gate_source,
        )
    )

    sota_decision_map = _load_json(
        root / "data/upba_energy/upba_v2_sota_decision_map_receipt.json"
    )
    sota_doc = (
        root / str(sota_decision_map["artifact"])
    ).read_text(encoding="utf-8")
    payloads["sota_decision_map"] = sota_decision_map
    checks.extend(_check_sota_decision_map(sota_decision_map, sota_doc))

    autotrader_hard_cross_seed = _load_json(
        root / "data/upba_energy/autotrader_energy_hard_cross_seed_3x_seed20260522_20260527.json"
    )
    autotrader_hard_doc = (
        root / "docs/AUTOTRADER_ENERGY_HARD_CROSS_SEED.md"
    ).read_text(encoding="utf-8")
    payloads["autotrader_energy_hard_cross_seed"] = autotrader_hard_cross_seed
    checks.extend(
        _check_autotrader_energy_hard_cross_seed(
            autotrader_hard_cross_seed,
            autotrader_hard_doc,
        )
    )

    autotrader_shadow_bridge = _load_json(
        root / "data/upba_energy/autotrader_energy_shadow_bridge_baseline_seed20260528.json"
    )
    autotrader_shadow_doc = (
        root / "docs/AUTOTRADER_ENERGY_SHADOW_BRIDGE.md"
    ).read_text(encoding="utf-8")
    payloads["autotrader_energy_shadow_bridge"] = autotrader_shadow_bridge
    checks.extend(
        _check_autotrader_energy_shadow_bridge(
            autotrader_shadow_bridge,
            autotrader_shadow_doc,
        )
    )

    popperpad_readme = (
        root / "internal/popperpad/zenoenergy/README.md"
    ).read_text(encoding="utf-8")
    checks.extend(_check_popperpad_status_text(popperpad_readme))
    if run_popperpad_doctor:
        checks.append(_run_popperpad_doctor(root))

    ok = all(check.passed for check in checks)
    return {
        "schema": "zenodex/energy/research_evidence_replay_receipt/v1",
        "ok": ok,
        "check_count": len(checks),
        "passed_count": sum(1 for check in checks if check.passed),
        "failed_count": sum(1 for check in checks if not check.passed),
        "checks": [check.to_dict() for check in checks],
        "summary": _summary(payloads),
    }


def _check_set_aware(report: dict[str, Any]) -> list[EvidenceCheck]:
    checks: list[EvidenceCheck] = []
    checks.append(
        _expect_equal(
            "set_aware.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_set_aware_comparison/v1",
        )
    )
    modes = report["modes"]
    checks.append(
        _expect_true(
            "set_aware.zero_invalid_accepts",
            all(int(mode["invalid_accept_count"]) == 0 for mode in modes.values()),
            "all modes have invalid_accept_count = 0",
        )
    )
    checks.append(
        _expect_true(
            "set_aware.aggregate_top10_recall",
            float(modes["aggregate_learned"]["top_10_recall"]) >= 1.0,
            "aggregate learned top_10_recall is 1.0",
        )
    )
    checks.append(
        _expect_true(
            "set_aware.negative_knowledge_recorded",
            bool(report["interpretation"]["set_aware_top1_improved"]) is False
            and float(modes["set_aware_learned"]["mean_verifier_calls"])
            >= float(modes["aggregate_learned"]["mean_verifier_calls"]),
            "set-aware linear ranker did not beat aggregate learned baseline",
        )
    )
    return checks


def _check_listwise_set(report: dict[str, Any]) -> list[EvidenceCheck]:
    modes = report["modes"]
    listwise = modes["listwise_set"]
    aggregate = modes["aggregate_pairwise"]
    return [
        _expect_equal(
            "listwise_set.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_listwise_set_ranker_comparison/v1",
        ),
        _expect_true(
            "listwise_set.safety",
            _all_modes_zero(modes)
            and int(listwise["permutation_violation_count"]) == 0
            and bool(report["interpretation"]["permutation_violation_count"] == 0),
            "zero invalid accepts and zero listwise permutation violations",
        ),
        _expect_true(
            "listwise_set.top10_and_checked_stop",
            float(listwise["top_10_recall"]) == 1.0
            and float(listwise["false_exclusion_rate_top_10"]) == 0.0
            and float(listwise["checked_stop_at_winner_rate"]) == 1.0,
            "listwise top-10 recall and checked-stop-at-winner audit remain complete",
        ),
        _expect_true(
            "listwise_set.negative_knowledge",
            bool(report["interpretation"]["listwise_improved_over_best_pairwise"]) is False
            and float(listwise["mean_verifier_calls"]) > float(aggregate["mean_verifier_calls"])
            and "did not improve mean verifier calls"
            in str(report["interpretation"]["negative_knowledge"]),
            "listwise ranker did not beat the strongest pairwise baseline on mean calls",
        ),
    ]


def _check_listwise_cross_seed(report: dict[str, Any]) -> list[EvidenceCheck]:
    aggregate = report["aggregate"]
    listwise = aggregate["modes"]["listwise_set"]
    pairwise = aggregate["modes"]["aggregate_pairwise"]
    return [
        _expect_equal(
            "listwise_cross_seed.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_listwise_set_ranker_cross_seed/v1",
        ),
        _expect_true(
            "listwise_cross_seed.safety",
            bool(aggregate["all_safety_passed"]) is True
            and int(report["safety"]["invalid_accept_count"]) == 0
            and int(report["safety"]["permutation_violation_count"]) == 0,
            "all cross-seed listwise runs have zero invalid accepts and zero permutation violations",
        ),
        _expect_true(
            "listwise_cross_seed.top10_and_checked_stop",
            int(aggregate["listwise_top10_pass_count"]) == int(report["run_count"])
            and int(aggregate["listwise_top10_fail_count"]) == 0
            and int(aggregate["checked_stop_at_winner_pass_count"]) == int(report["run_count"])
            and int(aggregate["checked_stop_at_winner_fail_count"]) == 0,
            "listwise top-10 recall and checked-stop-at-winner audits pass on every seed pair",
        ),
        _expect_true(
            "listwise_cross_seed.negative_knowledge",
            int(aggregate["strict_improvement_count"]) == 0
            and float(listwise["mean_verifier_calls"]["mean"])
            > float(pairwise["mean_verifier_calls"]["mean"])
            and "did not strictly improve"
            in str(report["interpretation"]["negative_knowledge"]),
            "listwise ranker does not strictly improve over pairwise on cross-seed stress",
        ),
    ]


def _check_gap_weighted_default(
    stress: dict[str, Any],
    hard_cases: dict[str, Any],
    model_audit: dict[str, Any],
) -> list[EvidenceCheck]:
    learned = stress["summary"]["learned"]
    hand = stress["summary"]["hand"]
    hard_summary = hard_cases["summary"]
    return [
        _expect_true(
            "gap_weighted_default.schemas",
            stress.get("schema") == "zenodex/energy/upba_v2_cross_seed_stress/v1"
            and hard_cases.get("schema") == "zenodex/energy/upba_v2_hard_case_mining/v1"
            and model_audit.get("schema") == "zenodex/energy/upba_v2_model_inspection/v1",
            "gap-weighted stress, hard-case, and model-audit schemas are stable",
        ),
        _expect_true(
            "gap_weighted_default.cross_seed_safety",
            int(learned["invalid_accept_count_total"]) == 0
            and float(learned["top_10_recall_min"]) == 1.0
            and float(learned["top_5_recall_min"]) == 1.0
            and float(learned["p99_verifier_calls_max"]) <= 2.0
            and float(learned["mean_verifier_calls_max"]) <= 1.04,
            "learned gap-weighted scorer has zero invalid accepts, complete top-10 recall, and low p99 calls",
        ),
        _expect_true(
            "gap_weighted_default.cross_seed_beats_hand",
            float(learned["mean_verifier_calls_mean"]) < float(hand["mean_verifier_calls_mean"])
            and float(learned["top_1_recall_mean"]) > float(hand["top_1_recall_mean"])
            and float(learned["top_5_recall_min"]) >= float(hand["top_5_recall_min"]),
            "learned gap-weighted scorer improves mean verifier calls and top-1 recall over hand energy",
        ),
        _expect_true(
            "gap_weighted_default.hard_case_recall",
            int(hard_summary["top5_miss_count"]) == 0
            and int(hard_summary["top10_miss_count"]) == 0
            and float(hard_summary["top_5_recall"]) == 1.0
            and float(hard_summary["top_10_recall"]) == 1.0
            and float(hard_summary["max_p99_winner_position"]) <= 2.0,
            "hard-case mining has no top-5/top-10 misses and p99 winner position at most 2",
        ),
        _expect_true(
            "gap_weighted_default.model_audit_boundary",
            int(model_audit["feature_dim"]) == 96
            and int(model_audit["parameter_count"]) == 97
            and list(model_audit["forbidden_feature_names"]) == []
            and int(model_audit["reserved_nonzero_count"]) == 0
            and float(model_audit["reserved_weight_abs_sum"]) == 0.0,
            "model audit keeps the tiny linear scorer away from forbidden and reserved features",
        ),
    ]


def _check_neighborhood(report: dict[str, Any]) -> list[EvidenceCheck]:
    limited = report["modes"]["limited"]
    neighborhood = report["modes"]["neighborhood"]
    return [
        _expect_equal(
            "neighborhood.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_neighborhood_benchmark/v1",
        ),
        _expect_true(
            "neighborhood.safety",
            int(neighborhood["invalid_accept_count"]) == 0
            and int(neighborhood["original_subset_violation_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True,
            "zero invalid accepts, zero subset violations, verifier authoritative",
        ),
        _expect_true(
            "neighborhood.regret_reduced",
            float(neighborhood["mean_volume_regret"]) < float(limited["mean_volume_regret"]),
            "neighborhood reduces mean volume regret versus limited",
        ),
        _expect_true(
            "neighborhood.call_cost_negative",
            float(neighborhood["mean_calls_until_full_winner_or_exhausted"])
            > float(limited["mean_calls_until_full_winner_or_exhausted"]),
            "neighborhood increases calls until full winner, negative knowledge preserved",
        ),
    ]


def _check_repair_selector(report: dict[str, Any]) -> list[EvidenceCheck]:
    modes = report["modes"]
    full = modes["full_neighborhood"]
    learned = modes["learned_selected"]
    hand = modes["hand_selected"]
    return [
        _expect_equal(
            "repair_selector.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_repair_selector_benchmark/v1",
        ),
        _expect_true(
            "repair_selector.safety",
            _all_modes_zero(modes)
            and int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True,
            "zero invalid accepts and verifier authoritative",
        ),
        _expect_true(
            "repair_selector.compression",
            float(learned["candidate_count_mean"]) < float(full["candidate_count_mean"])
            and float(learned["mean_added_count"]) < float(full["mean_added_count"])
            and float(learned["mean_volume_regret"]) <= float(full["mean_volume_regret"]),
            "learned selector compresses full neighborhood without higher mean volume regret",
        ),
        _expect_true(
            "repair_selector.hand_baseline_negative",
            float(learned["mean_volume_regret"]) >= float(hand["mean_volume_regret"]),
            "learned selector does not strictly beat hand-selected subset on this split",
        ),
    ]


def _check_repair_selector_cross_seed(report: dict[str, Any]) -> list[EvidenceCheck]:
    aggregate = report["aggregate"]
    learned = aggregate["modes"]["learned_selected"]
    full = aggregate["modes"]["full_neighborhood"]
    return [
        _expect_equal(
            "repair_selector_cross_seed.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_repair_selector_cross_seed/v1",
        ),
        _expect_true(
            "repair_selector_cross_seed.safety",
            bool(aggregate["all_safety_passed"]) is True
            and int(report["safety"]["invalid_accept_count"]) == 0
            and int(report["safety"]["original_subset_violation_count"]) == 0,
            "all cross-seed runs have zero invalid accepts and zero subset violations",
        ),
        _expect_true(
            "repair_selector_cross_seed.compression_all_pairs",
            int(aggregate["compression_pass_count"]) == int(report["run_count"])
            and int(aggregate["compression_fail_count"]) == 0,
            "compression passed on every seed pair",
        ),
        _expect_true(
            "repair_selector_cross_seed.aggregate_regret",
            float(learned["mean_volume_regret"]["mean"])
            <= float(full["mean_volume_regret"]["mean"]),
            "learned selected aggregate mean regret is no worse than full neighborhood",
        ),
        _expect_true(
            "repair_selector_cross_seed.hand_negative",
            int(aggregate["strict_hand_win_count"]) < int(report["run_count"]),
            "learned selector does not strictly beat hand-selected subset on every seed pair",
        ),
    ]


def _check_formal_boundary(report: dict[str, Any]) -> list[EvidenceCheck]:
    names = set(str(name) for name in report["formal_names"])
    return [
        _expect_equal(
            "formal_boundary.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_repair_selector_formal_boundary_receipt/v1",
        ),
        _expect_true(
            "formal_boundary.commands",
            all(int(command["exit_code"]) == 0 for command in report["commands"]),
            "Lean target and focused formal regression are recorded as passing",
        ),
        _expect_true(
            "formal_boundary.names",
            {
                "def AdvisorySelectedRepairSet",
                "theorem advisory_selected_repair_set_implies_candidate_subset",
                "theorem advisory_selected_repair_set_upper_bound_certificate_implies_base_weak_optimal",
            }.issubset(names),
            "selector-specific Lean names are present in receipt",
        ),
        _expect_true(
            "formal_boundary.scope_limit",
            "base list" in str(report["limits"]),
            "receipt states base-list scope limit",
        ),
    ]


def _check_fallback_checked_stop_formal(
    report: dict[str, Any],
    lean_source: str,
) -> list[EvidenceCheck]:
    names = set(str(name) for name in report["formal_names"])
    required = {
        "def FullFallbackEquivalentOrder",
        "theorem full_fallback_equivalent_order_preserves_membership_iff",
        "theorem full_fallback_equivalent_order_preserves_weak_optimality_iff",
        "def CheckedStopCertificate",
        "theorem checked_stop_certificate_implies_concat_weak_optimal",
        "theorem checked_stop_certificate_with_full_permutation_implies_full_weak_optimal",
        "theorem checked_stop_certificate_with_exact_full_implies_global_weak_optimal",
        "theorem reordered_exact_upper_bound_certificate_implies_global_weak_optimal",
        "theorem upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
        "theorem upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
        "theorem upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
        "def ObjectiveEquivalent",
        "theorem objective_equivalent_transfers_weak_dominance",
        "theorem objective_equivalent_preserves_weak_optimal_in",
        "theorem objective_equivalent_preserves_global_weak_optimal",
        "theorem objective_equivalent_exact_upper_bound_certificate_implies_global_weak_optimal",
        "theorem objective_equivalent_reordered_exact_upper_bound_certificate_implies_global_weak_optimal",
    }
    missing_from_source = [
        name
        for name in sorted(required)
        if name not in lean_source
    ]
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    return [
        _expect_equal(
            "fallback_checked_stop_formal.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_fallback_checked_stop_formal_receipt/v1",
        ),
        _expect_true(
            "fallback_checked_stop_formal.commands",
            all(int(command["exit_code"]) == 0 for command in report["commands"]),
            "Lean target and focused formal regression are recorded as passing",
        ),
        _expect_true(
            "fallback_checked_stop_formal.names",
            required.issubset(names) and not missing_from_source,
            "fallback and checked-stop theorem names are present in receipt and Lean source",
        ),
        _expect_true(
            "fallback_checked_stop_formal.no_placeholders",
            forbidden.search(lean_source) is None,
            "Lean source has no sorry/admit/axiom/unsafe placeholders",
        ),
        _expect_true(
            "fallback_checked_stop_formal.scope_limit",
            "Online early stop" in " ".join(str(limit) for limit in report["limits"]),
            "receipt states online early-stop suffix-bound limit",
        ),
        _expect_true(
            "fallback_checked_stop_formal.objective_equivalence_limit",
            "Objective-equivalent winners require deterministic verifier acceptance"
            in " ".join(str(limit) for limit in report["limits"])
            and "same volume and surplus" in str(report["claim"]),
            "receipt states objective-equivalent verifier-acceptance limit",
        ),
    ]


def _check_fallback_permutation_audit(report: dict[str, Any]) -> list[EvidenceCheck]:
    modes = report["modes"]
    learned = modes["learned"]
    hybrid = modes["hybrid"]
    return [
        _expect_equal(
            "fallback_permutation_audit.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_benchmark_report/v1",
        ),
        _expect_true(
            "fallback_permutation_audit.zero_invalid_accepts",
            int(report["invalid_accept_count"]) == 0 and _all_modes_zero(modes),
            "all fallback audit modes have zero invalid accepts",
        ),
        _expect_true(
            "fallback_permutation_audit.permutation_premise",
            all(int(mode["permutation_violation_count"]) == 0 for mode in modes.values()),
            "all audit modes preserve the full-fallback permutation premise",
        ),
        _expect_true(
            "fallback_permutation_audit.learned_recovery",
            int(learned["fallback_recovered_count"]) == int(learned["batches"])
            and float(learned["top_10_recall"]) == 1.0
            and float(hybrid["top_10_recall"]) == 1.0,
            "learned and hybrid orderings recover every exact winner by top-k or fallback",
        ),
        _expect_true(
            "fallback_permutation_audit.checked_stop_offline",
            float(learned["checked_stop_top_k_rate"]) == 1.0
            and float(learned["checked_stop_at_winner_rate"]) == 1.0
            and float(modes["random"]["checked_stop_top_k_rate"]) < 1.0,
            "checked-stop audit succeeds for learned top-k and remains nontrivial versus random",
        ),
        _expect_true(
            "fallback_permutation_audit.objective_equivalence_metrics",
            float(learned["top_10_objective_recall"]) == 1.0
            and float(hybrid["top_10_objective_recall"]) == 1.0
            and float(learned["mean_verifier_calls_to_objective_winner"])
            <= float(learned["mean_verifier_calls"])
            and float(learned["objective_argmax_class_size_mean"]) >= 1.0,
            "fallback audit reports objective-equivalent recall and call position",
        ),
    ]


def _check_topk_sweep(report: dict[str, Any]) -> list[EvidenceCheck]:
    modes = report["modes"]
    learned = modes["learned"]
    hybrid = modes["hybrid"]
    return [
        _expect_equal(
            "topk_sweep.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_topk_sweep/v1",
        ),
        _expect_true(
            "topk_sweep.permutation_premise",
            all(int(mode["permutation_violation_count"]) == 0 for mode in modes.values()),
            "all top-k sweep modes preserve hash-permutation ordering",
        ),
        _expect_true(
            "topk_sweep.learned_checked_stop_k2",
            float(learned["top_k"]["2"]["checked_stop_top_k_rate"]) == 1.0
            and float(learned["top_k"]["2"]["false_exclusion_rate"]) == 0.0
            and float(hybrid["top_k"]["2"]["checked_stop_top_k_rate"]) == 1.0,
            "learned and hybrid checked-stop audits reach 100% by k=2 on holdout",
        ),
        _expect_true(
            "topk_sweep.checked_stop_at_winner",
            all(float(mode["checked_stop_at_winner_rate"]) == 1.0 for mode in modes.values()),
            "checked-stop certificate holds at the exact winner for every mode",
        ),
        _expect_true(
            "topk_sweep.objective_equivalence_metrics",
            float(learned["top_k"]["2"]["objective_top_k_recall"]) == 1.0
            and float(learned["top_k"]["2"]["objective_false_exclusion_rate"]) == 0.0
            and float(learned["checked_stop_at_objective_winner_rate"]) == 1.0
            and float(learned["mean_objective_winner_position"])
            <= float(learned["mean_winner_position"])
            and float(learned["objective_argmax_class_size_mean"]) >= 1.0,
            "top-k sweep reports objective-equivalent recall and call position",
        ),
        _expect_true(
            "topk_sweep.random_top10_negative",
            float(modes["random"]["top_k"]["10"]["false_exclusion_rate"]) > 0.0,
            "random top-10 misses many winners, so the sweep is not vacuous",
        ),
    ]


def _check_objective_equiv_training_hygiene(
    report: dict[str, Any],
    trainer_source: str,
    test_source: str,
    doc_text: str,
) -> list[EvidenceCheck]:
    modes = set(str(mode) for mode in report["positive_class_modes"])
    doc_lower = doc_text.lower()
    return [
        _expect_equal(
            "objective_equiv_training_hygiene.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_objective_equiv_training_hygiene_receipt/v1",
        ),
        _expect_true(
            "objective_equiv_training_hygiene.modes",
            modes == {"hash-winner", "objective-equivalent"}
            and report["default_positive_class"] == "hash-winner"
            and report["recommended_research_positive_class"] == "objective-equivalent",
            "receipt records replay default and objective-equivalent research mode",
        ),
        _expect_true(
            "objective_equiv_training_hygiene.source_hooks",
            "POSITIVE_CLASS_MODES" in trainer_source
            and "--positive-class" in trainer_source
            and "_positive_row_keys" in trainer_source
            and "good_is_positive" in trainer_source
            and "objective-equivalent" in test_source
            and "_positive_row_keys" in test_source,
            "trainer and focused tests expose objective-equivalent positive-class hooks",
        ),
        _expect_true(
            "objective_equiv_training_hygiene.safety_boundary",
            bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and "training-target change" in doc_lower
            and "deterministic verification" in doc_lower,
            "receipt and doc keep the change on the advisory training boundary",
        ),
        _expect_true(
            "objective_equiv_training_hygiene.no_metric_claim",
            "not a new benchmark improvement" in " ".join(
                str(limit).lower() for limit in report["limits"]
            )
            and "does not claim a new benchmark improvement" in doc_lower,
            "receipt records this as label hygiene rather than performance evidence",
        ),
    ]


def _check_production_promotion_gate(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
) -> list[EvidenceCheck]:
    obligations = {
        str(item["id"]): item for item in report.get("obligations", [])
    }
    blocked_reasons = set(str(reason) for reason in report.get("blocked_reasons", []))
    doc_lower = doc_text.lower()
    return [
        _expect_equal(
            "production_promotion_gate.schema",
            report.get("schema"),
            "zenodex/energy/production_promotion_gate/v1",
        ),
        _expect_true(
            "production_promotion_gate.blocks_current_research",
            report.get("decision") == "blocked"
            and bool(report.get("promotion_allowed")) is False
            and "missing real UPBA replay report" in blocked_reasons
            and "missing real AutoTrader shadow report" in blocked_reasons
            and "operator must explicitly enable advisory ranking-only promotion"
            in blocked_reasons,
            "gate blocks current synthetic/fixture-only evidence",
        ),
        _expect_true(
            "production_promotion_gate.research_replay_clean",
            bool(obligations["research_replay_clean"]["passed"]) is True
            and bool(obligations["upba_real_replay_coverage"]["passed"]) is False
            and bool(obligations["autotrader_real_shadow_coverage"]["passed"]) is False,
            "clean research replay is necessary but insufficient for promotion",
        ),
        _expect_true(
            "production_promotion_gate.safety_contract",
            bool(report["safety_contract"]["verifier_authoritative"]) is True
            and bool(report["safety_contract"]["policy_guards_authoritative"]) is True
            and bool(
                report["safety_contract"]["scorer_authorizes_settlement_or_trade"]
            )
            is False
            and bool(report["safety_contract"]["model_output_in_state_root"]) is False
            and bool(report["safety_contract"]["deterministic_fallback_required"])
            is True,
            "gate preserves verifier/policy authority and fallback boundary",
        ),
        _expect_true(
            "production_promotion_gate.doc_and_source",
            "ProductionEligible" in doc_text
            and "advisory ranking" in doc_lower
            and "zenodex/energy/upba_real_replay_report/v1" in doc_text
            and "zenodex/energy/autotrader_real_shadow_report/v1" in doc_text
            and "MIN_UPBA_REAL_BATCHES" in source_text
            and "MIN_AUTOTRADER_REAL_CONTEXTS" in source_text,
            "doc and source record real replay thresholds and ranking-only scope",
        ),
    ]


def _check_sota_decision_map(
    report: dict[str, Any],
    doc_text: str,
) -> list[EvidenceCheck]:
    expected_decisions = {
        "full generative EBM: defer",
        "pairwise linear ranking: keep as baseline",
        "listwise set ranker: test next",
        "larger transformer: defer",
        "learned repair selector: continue",
        "top-k without fallback: reject",
        "online checked stop: prototype only with suffix-bound certificate",
    }
    expected_experiments = {
        "listwise set ranker",
        "repair selector with outcome-level labels",
        "hard-negative generator refresh",
        "dominance-cover certificate prototype",
    }
    expected_negative = {
        "set-aware linear ranker did not beat aggregate learned baseline",
        "deterministic neighborhood repair reduced regret but increased verifier work",
        "learned repair selector did not consistently beat hand-selected repairs",
    }
    required_sources = {
        "https://cs.nyu.edu/~yann/research/ebm/",
        "https://neurips.cc/virtual/2006/tutorial/3",
        "https://arxiv.org/abs/2101.03288",
        "https://logicalintelligence.com/blog/energy-based-models-for-reasoning",
        "https://papers.nips.cc/paper/6931-deep-sets",
        "https://proceedings.mlr.press/v97/lee19d.html",
        "https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2007-40.pdf",
        "https://ojs.aaai.org/index.php/AAAI/article/view/10080",
        "https://papers.neurips.cc/paper/9690-exact-combinatorial-optimization-with-graph-convolutional-neural-networks",
        "https://arxiv.org/abs/2107.10201",
    }
    doc_lower = doc_text.lower()
    decisions = set(str(item) for item in report["required_decisions"])
    experiments = set(str(item) for item in report["next_experiments"])
    negative = set(str(item) for item in report["negative_knowledge"])
    doc_decision_terms = {
        "full generative ebm",
        "defer",
        "pairwise linear ranking",
        "keep as baseline",
        "listwise set ranker",
        "test next",
        "larger transformer",
        "learned repair selector",
        "continue",
        "top-k without fallback",
        "reject",
        "online checked stop",
        "prototype only with suffix-bound certificate",
    }
    return [
        _expect_equal(
            "sota_decision_map.schema",
            report.get("schema"),
            "zenodex/energy/upba_v2_sota_decision_map_receipt/v1",
        ),
        _expect_true(
            "sota_decision_map.sources_and_boundary",
            int(report["source_count"]) >= len(required_sources)
            and all(source in doc_text for source in required_sources)
            and "model proposes" in doc_lower
            and "verifier decides" in doc_lower
            and "fallback or certificate preserves exactness" in doc_lower,
            "decision map records all required sources and verifier/fallback boundary",
        ),
        _expect_true(
            "sota_decision_map.decisions",
            expected_decisions.issubset(decisions)
            and all(term in doc_lower for term in doc_decision_terms),
            "all required model-direction decisions are recorded in receipt and doc",
        ),
        _expect_true(
            "sota_decision_map.next_experiments",
            expected_experiments.issubset(experiments)
            and all(experiment in doc_lower for experiment in expected_experiments),
            "all next experiments are recorded in receipt and doc",
        ),
        _expect_true(
            "sota_decision_map.negative_knowledge",
            expected_negative.issubset(negative)
            and "negative knowledge" in doc_lower
            and "research guidance rather than benchmark evidence" in " ".join(
                str(limit).lower() for limit in report["limits"]
            ),
            "negative knowledge and guidance-only limit are preserved",
        ),
    ]


def _check_autotrader_energy_hard_cross_seed(
    report: dict[str, Any],
    doc_text: str,
) -> list[EvidenceCheck]:
    aggregate = report["aggregate"]
    learned = aggregate["modes"]["learned"]
    hand = aggregate["modes"]["hand"]
    random = aggregate["modes"]["random"]
    doc_lower = doc_text.lower()
    return [
        _expect_equal(
            "autotrader_energy_hard_cross_seed.schema",
            report.get("schema"),
            "zenodex/energy/autotrader_cross_seed_report/v1",
        ),
        _expect_true(
            "autotrader_energy_hard_cross_seed.safety",
            int(report["safety"]["invalid_accept_count_total"]) == 0
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_trade"]) is False
            and int(aggregate["safety_pass_count"]) == int(report["run_count"]),
            "zero invalid accepts and deterministic AutoTrader policy guards remain authoritative",
        ),
        _expect_true(
            "autotrader_energy_hard_cross_seed.learned_beats_hand_all",
            int(aggregate["learned_beats_hand_count"]) == int(report["run_count"])
            and int(aggregate["learned_beats_random_count"]) == int(report["run_count"])
            and float(learned["mean_guard_calls_mean"]) < float(hand["mean_guard_calls_mean"])
            and float(learned["mean_guard_calls_mean"]) < float(random["mean_guard_calls_mean"]),
            "learned AutoTraderEnergy ordering reduces mean guard calls versus hand and random on every seed pair",
        ),
        _expect_true(
            "autotrader_energy_hard_cross_seed.profile_nonvacuous",
            report["profile"] == "hard"
            and int(aggregate["profile_nonvacuous_count"]) == int(report["run_count"])
            and float(hand["mean_guard_calls_min"]) >= 2.0,
            "hard profile exercises nontrivial guard ordering",
        ),
        _expect_true(
            "autotrader_energy_hard_cross_seed.doc_and_recall",
            float(learned["top_5_recall_min"]) >= 0.98
            and float(learned["invalid_top_1_rate_max"]) == 0.0
            and "every evaluated seed pair" in doc_lower
            and "production-shadow observations" in doc_lower,
            "receipt records high top-5 recall plus the synthetic-to-shadow evidence boundary",
        ),
    ]


def _check_autotrader_energy_shadow_bridge(
    report: dict[str, Any],
    doc_text: str,
) -> list[EvidenceCheck]:
    shadow = report["shadow"]
    modes = report["modes"]
    learned = modes["hybrid"]
    hand = modes["hand"]
    random = modes["random"]
    doc_lower = doc_text.lower()
    return [
        _expect_equal(
            "autotrader_energy_shadow_bridge.schema",
            report.get("schema"),
            "zenodex/energy/autotrader_shadow_bridge_report/v1",
        ),
        _expect_true(
            "autotrader_energy_shadow_bridge.safety",
            int(report["safety"]["invalid_accept_count_total"]) == 0
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_trade"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and _all_modes_zero(modes),
            "zero invalid accepts and deterministic AutoTrader policy guards remain authoritative",
        ),
        _expect_true(
            "autotrader_energy_shadow_bridge.nonvacuous_fixture",
            int(shadow["context_count"]) >= 4
            and int(shadow["row_count"]) >= 20
            and int(shadow["valid_count"]) > 0
            and int(shadow["invalid_count"]) > 0
            and int(shadow["winner_count"]) == int(shadow["context_count"])
            and all(int(count) >= 2 for count in shadow["group_counts"].values()),
            "shadow fixture has multiple candidates per context plus valid and invalid outcomes",
        ),
        _expect_true(
            "autotrader_energy_shadow_bridge.learned_ties_hand_negative",
            bool(report["interpretation"]["learned_beats_hand_on_mean_guard_calls"]) is False
            and float(learned["mean_guard_calls"]) == float(hand["mean_guard_calls"])
            and float(learned["mean_guard_calls"]) < float(random["mean_guard_calls"])
            and float(learned["top_5_recall"]) == 1.0
            and float(learned["top_1_recall"]) == 0.0,
            "learned ordering ties hand energy, beats random mean calls, and records top-1 miss knowledge",
        ),
        _expect_true(
            "autotrader_energy_shadow_bridge.objective_equiv_argmax",
            float(learned["top_1_objective_recall"]) == 1.0
            and float(learned["mean_guard_calls_to_objective_winner"]) == 1.0
            and int(learned["objective_tie_batch_count"]) == int(shadow["context_count"])
            and float(learned["objective_tie_batch_rate"]) == 1.0,
            "objective-equivalent argmax recall separates tied maxima from hash-selected exact winner misses",
        ),
        _expect_true(
            "autotrader_energy_shadow_bridge.doc_boundary",
            "not live production distribution evidence" in doc_lower
            and "schema and boundary replay" in doc_lower
            and "quotient/equivalence issue" in doc_lower,
            "shadow bridge doc records fixture scope and argmax-equivalence boundary",
        ),
    ]


def _check_popperpad_status_text(readme: str) -> list[EvidenceCheck]:
    expected = {
        "H_ZENOENERGY_SET_AWARE_COMPARE_SAFETY_20260517": "supported",
        "H_ZENOENERGY_SET_AWARE_LINEAR_STRICTLY_IMPROVES_AGGREGATE_20260517": "falsified",
        "H_ZENOENERGY_NEIGHBORHOOD_SAFETY_SUBSET_20260517_V2": "supported",
        "H_ZENOENERGY_NEIGHBORHOOD_REDUCES_REGRET_20260517_V2": "supported",
        "H_ZENOENERGY_NEIGHBORHOOD_REDUCES_VERIFIER_CALLS_20260517_V2": "falsified",
        "H_ZENOENERGY_REPAIR_SELECTOR_SAFETY_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_COMPRESSES_FULL_NEIGHBORHOOD_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_STRICTLY_BEATS_HAND_SELECTED_20260517": "falsified",
        "H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_SAFETY_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_COMPRESSES_FULL_NEIGHBORHOOD_20260517": "supported",
        "H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_STRICTLY_BEATS_HAND_SELECTED_20260517": "falsified",
        "H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517": "supported",
        "H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517": "supported",
        "H_ZENOENERGY_SOTA_DECISION_MAP_RECEIPT_20260518": "supported",
        "H_ZENOENERGY_LISTWISE_SET_RANKER_SAFETY_20260518": "supported",
        "H_ZENOENERGY_LISTWISE_SET_RANKER_STRICTLY_IMPROVES_PAIRWISE_20260518": "falsified",
        "H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_SAFETY_20260518": "supported",
        "H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_STRICTLY_IMPROVES_PAIRWISE_20260518": "falsified",
        "H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_SAFETY_20260518": "supported",
        "H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_BEATS_HAND_ENERGY_20260518": "supported",
        "H_ZENOENERGY_OBJECTIVE_EQUIV_FORMAL_BOUNDARY_RECEIPT_20260518": "supported",
        "H_ZENOENERGY_OBJECTIVE_EQUIV_RUNTIME_TELEMETRY_20260518": "supported",
        "H_ZENOENERGY_OBJECTIVE_EQUIV_TRAINING_HYGIENE_20260518": "supported",
        "H_ZENOENERGY_PRODUCTION_GATE_BLOCKS_WITHOUT_REAL_REPLAY_20260518": "supported",
        "H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_SAFETY_20260518": "supported",
        "H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_BEATS_HAND_20260518": "supported",
        "H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_PROFILE_NONVACUOUS_20260518": "supported",
        "H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_SAFETY_20260518": "supported",
        "H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_NONVACUOUS_20260518": "supported",
        "H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_LEARNED_BEATS_HAND_20260518": "falsified",
        "H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_OBJECTIVE_EQUIV_TOP1_20260518": "supported",
    }
    checks = []
    for hypothesis_id, state in expected.items():
        checks.append(
            _expect_true(
                f"popperpad.status.{hypothesis_id}",
                f"{hypothesis_id}: {state}" in readme,
                f"{hypothesis_id} is recorded as {state}",
            )
        )
    return checks


def _run_popperpad_doctor(root: Path) -> EvidenceCheck:
    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "popperpad",
            "--pad",
            "internal/popperpad/zenoenergy",
            "doctor",
        ],
        cwd=root,
        env={**_clean_env(), "PYTHONPATH": "external/PopperPad/src"},
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    if proc.returncode != 0:
        return EvidenceCheck(
            check_id="popperpad.doctor",
            passed=False,
            detail=(proc.stdout + proc.stderr).strip()[:500],
        )
    try:
        payload = json.loads(proc.stdout)
        passed = bool(payload["ok"]) and bool(payload["result"]["ok"])
    except (json.JSONDecodeError, KeyError, TypeError):
        passed = False
    return EvidenceCheck(
        check_id="popperpad.doctor",
        passed=passed,
        detail="PopperPad doctor ok" if passed else proc.stdout.strip()[:500],
    )


def _summary(payloads: dict[str, Any]) -> dict[str, Any]:
    repair_cross = payloads["repair_selector_cross_seed"]
    listwise_set = payloads["listwise_set"]
    listwise_cross = payloads["listwise_cross_seed"]
    gap_weighted_stress = payloads["gap_weighted_stress"]
    gap_weighted_hard_cases = payloads["gap_weighted_hard_cases"]
    gap_weighted_audit = payloads["gap_weighted_model_audit"]
    fallback_audit = payloads["fallback_permutation_audit"]
    topk_sweep = payloads["topk_sweep"]
    training_hygiene = payloads["objective_equiv_training_hygiene"]
    production_gate = payloads["production_promotion_gate"]
    sota_decision_map = payloads["sota_decision_map"]
    autotrader = payloads["autotrader_energy_hard_cross_seed"]
    autotrader_aggregate = autotrader["aggregate"]
    autotrader_shadow = payloads["autotrader_energy_shadow_bridge"]
    return {
        "set_aware_negative_knowledge": payloads["set_aware"]["interpretation"][
            "negative_knowledge"
        ],
        "listwise_set": {
            "listwise_improved_over_best_pairwise": listwise_set["interpretation"][
                "listwise_improved_over_best_pairwise"
            ],
            "negative_knowledge": listwise_set["interpretation"]["negative_knowledge"],
            "listwise_mean_verifier_calls": listwise_set["modes"]["listwise_set"][
                "mean_verifier_calls"
            ],
            "aggregate_pairwise_mean_verifier_calls": listwise_set["modes"][
                "aggregate_pairwise"
            ]["mean_verifier_calls"],
            "listwise_top_10_recall": listwise_set["modes"]["listwise_set"][
                "top_10_recall"
            ],
            "listwise_permutation_violation_count": listwise_set["modes"][
                "listwise_set"
            ]["permutation_violation_count"],
        },
        "listwise_cross_seed": {
            "run_count": listwise_cross["run_count"],
            "listwise_top10_pass_count": listwise_cross["aggregate"][
                "listwise_top10_pass_count"
            ],
            "checked_stop_at_winner_pass_count": listwise_cross["aggregate"][
                "checked_stop_at_winner_pass_count"
            ],
            "strict_improvement_count": listwise_cross["aggregate"][
                "strict_improvement_count"
            ],
            "invalid_accept_count": listwise_cross["safety"]["invalid_accept_count"],
            "permutation_violation_count": listwise_cross["safety"][
                "permutation_violation_count"
            ],
            "negative_knowledge": listwise_cross["interpretation"]["negative_knowledge"],
        },
        "gap_weighted_default": {
            "cross_seed_configs": gap_weighted_stress["summary"]["learned"]["configs"],
            "learned_mean_verifier_calls": gap_weighted_stress["summary"]["learned"][
                "mean_verifier_calls_mean"
            ],
            "hand_mean_verifier_calls": gap_weighted_stress["summary"]["hand"][
                "mean_verifier_calls_mean"
            ],
            "learned_top_10_recall_min": gap_weighted_stress["summary"]["learned"][
                "top_10_recall_min"
            ],
            "learned_invalid_accept_count_total": gap_weighted_stress["summary"][
                "learned"
            ]["invalid_accept_count_total"],
            "hard_case_batches_with_winner": gap_weighted_hard_cases["summary"][
                "batches_with_winner"
            ],
            "hard_case_top_10_recall": gap_weighted_hard_cases["summary"][
                "top_10_recall"
            ],
            "hard_case_top10_miss_count": gap_weighted_hard_cases["summary"][
                "top10_miss_count"
            ],
            "model_parameter_count": gap_weighted_audit["parameter_count"],
            "model_reserved_nonzero_count": gap_weighted_audit["reserved_nonzero_count"],
        },
        "neighborhood_regret_delta": payloads["neighborhood"]["deltas"][
            "mean_volume_regret_delta"
        ],
        "repair_selector_cross_seed": {
            "run_count": repair_cross["run_count"],
            "compression_pass_count": repair_cross["aggregate"]["compression_pass_count"],
            "strict_hand_win_count": repair_cross["aggregate"]["strict_hand_win_count"],
            "invalid_accept_count": repair_cross["safety"]["invalid_accept_count"],
            "original_subset_violation_count": repair_cross["safety"][
                "original_subset_violation_count"
            ],
        },
        "formal_boundary_claim": payloads["formal_boundary"]["claim"],
        "fallback_checked_stop_claim": payloads["fallback_checked_stop_formal"]["claim"],
        "fallback_permutation_audit": {
            "batches": fallback_audit["modes"]["learned"]["batches"],
            "learned_top_10_recall": fallback_audit["modes"]["learned"]["top_10_recall"],
            "learned_checked_stop_top_k_rate": fallback_audit["modes"]["learned"][
                "checked_stop_top_k_rate"
            ],
            "learned_permutation_violation_count": fallback_audit["modes"]["learned"][
                "permutation_violation_count"
            ],
            "learned_top_10_objective_recall": fallback_audit["modes"]["learned"][
                "top_10_objective_recall"
            ],
            "learned_mean_calls_to_objective_winner": fallback_audit["modes"]["learned"][
                "mean_verifier_calls_to_objective_winner"
            ],
            "invalid_accept_count": fallback_audit["invalid_accept_count"],
        },
        "topk_sweep": {
            "batches": topk_sweep["modes"]["learned"]["batches"],
            "learned_k2_checked_stop_rate": topk_sweep["modes"]["learned"]["top_k"]["2"][
                "checked_stop_top_k_rate"
            ],
            "learned_k2_false_exclusion_rate": topk_sweep["modes"]["learned"]["top_k"]["2"][
                "false_exclusion_rate"
            ],
            "learned_k2_objective_false_exclusion_rate": topk_sweep["modes"]["learned"][
                "top_k"
            ]["2"]["objective_false_exclusion_rate"],
            "learned_mean_objective_winner_position": topk_sweep["modes"]["learned"][
                "mean_objective_winner_position"
            ],
            "objective_tie_batch_count": topk_sweep["modes"]["learned"][
                "objective_tie_batch_count"
            ],
            "random_k10_false_exclusion_rate": topk_sweep["modes"]["random"]["top_k"]["10"][
                "false_exclusion_rate"
            ],
        },
        "objective_equiv_training_hygiene": {
            "positive_class_modes": training_hygiene["positive_class_modes"],
            "default_positive_class": training_hygiene["default_positive_class"],
            "recommended_research_positive_class": training_hygiene[
                "recommended_research_positive_class"
            ],
            "claim": training_hygiene["claim"],
        },
        "production_promotion_gate": {
            "decision": production_gate["decision"],
            "promotion_allowed": production_gate["promotion_allowed"],
            "blocked_reasons": production_gate["blocked_reasons"],
            "scope": production_gate["scope"],
            "negative_knowledge": production_gate["negative_knowledge"],
        },
        "sota_decision_map": {
            "source_count": sota_decision_map["source_count"],
            "required_decision_count": len(sota_decision_map["required_decisions"]),
            "next_experiment_count": len(sota_decision_map["next_experiments"]),
            "negative_knowledge_count": len(sota_decision_map["negative_knowledge"]),
            "claim": sota_decision_map["claim"],
        },
        "autotrader_energy_hard_cross_seed": {
            "run_count": autotrader["run_count"],
            "learned_beats_hand_count": autotrader_aggregate["learned_beats_hand_count"],
            "safety_pass_count": autotrader_aggregate["safety_pass_count"],
            "learned_mean_guard_calls": autotrader_aggregate["modes"]["learned"][
                "mean_guard_calls_mean"
            ],
            "hand_mean_guard_calls": autotrader_aggregate["modes"]["hand"][
                "mean_guard_calls_mean"
            ],
            "random_mean_guard_calls": autotrader_aggregate["modes"]["random"][
                "mean_guard_calls_mean"
            ],
            "learned_top_5_recall_min": autotrader_aggregate["modes"]["learned"][
                "top_5_recall_min"
            ],
            "invalid_accept_count_total": autotrader["safety"][
                "invalid_accept_count_total"
            ],
            "positive_knowledge": autotrader["positive_knowledge"],
        },
        "autotrader_energy_shadow_bridge": {
            "source": autotrader_shadow["source"],
            "context_count": autotrader_shadow["shadow"]["context_count"],
            "row_count": autotrader_shadow["shadow"]["row_count"],
            "valid_count": autotrader_shadow["shadow"]["valid_count"],
            "invalid_count": autotrader_shadow["shadow"]["invalid_count"],
            "learned_mean_guard_calls": autotrader_shadow["modes"]["hybrid"][
                "mean_guard_calls"
            ],
            "learned_mean_guard_calls_to_objective_winner": autotrader_shadow[
                "modes"
            ]["hybrid"]["mean_guard_calls_to_objective_winner"],
            "hand_mean_guard_calls": autotrader_shadow["modes"]["hand"][
                "mean_guard_calls"
            ],
            "random_mean_guard_calls": autotrader_shadow["modes"]["random"][
                "mean_guard_calls"
            ],
            "learned_top_1_recall": autotrader_shadow["modes"]["hybrid"][
                "top_1_recall"
            ],
            "learned_top_1_objective_recall": autotrader_shadow["modes"]["hybrid"][
                "top_1_objective_recall"
            ],
            "learned_top_5_recall": autotrader_shadow["modes"]["hybrid"][
                "top_5_recall"
            ],
            "objective_tie_batch_count": autotrader_shadow["modes"]["hybrid"][
                "objective_tie_batch_count"
            ],
            "invalid_accept_count_total": autotrader_shadow["safety"][
                "invalid_accept_count_total"
            ],
            "argmax_equivalence_note": autotrader_shadow["interpretation"][
                "argmax_equivalence_note"
            ],
            "negative_knowledge": autotrader_shadow["interpretation"][
                "negative_knowledge"
            ],
        },
    }


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Research Evidence Replay",
        "",
        "```text",
        f"ok: {str(report['ok']).lower()}",
        f"check_count: {report['check_count']}",
        f"passed_count: {report['passed_count']}",
        f"failed_count: {report['failed_count']}",
        "```",
        "",
        "| check | result | detail |",
        "| --- | --- | --- |",
    ]
    for check in report["checks"]:
        lines.append(
            "| "
            + " | ".join(
                (
                    str(check["check_id"]),
                    "pass" if check["passed"] else "fail",
                    str(check["detail"]).replace("|", "/"),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Summary",
            "",
            "```json",
            json.dumps(report["summary"], indent=2, sort_keys=True),
            "```",
        ]
    )
    return "\n".join(lines) + "\n"


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(path)
    return json.loads(path.read_text(encoding="utf-8"))


def _all_modes_zero(modes: dict[str, Any]) -> bool:
    return all(
        int(mode["invalid_accept_count"]) == 0
        and int(mode.get("original_subset_violation_count", 0)) == 0
        for mode in modes.values()
    )


def _expect_equal(check_id: str, actual: object, expected: object) -> EvidenceCheck:
    return EvidenceCheck(
        check_id=check_id,
        passed=actual == expected,
        detail=f"expected {expected!r}, observed {actual!r}",
    )


def _expect_true(check_id: str, condition: bool, detail: str) -> EvidenceCheck:
    return EvidenceCheck(check_id=check_id, passed=bool(condition), detail=detail)


def _clean_env() -> dict[str, str]:
    import os

    return {key: value for key, value in os.environ.items() if key != "PYTHONPATH"}


if __name__ == "__main__":
    raise SystemExit(main())
