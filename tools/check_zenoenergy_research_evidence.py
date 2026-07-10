#!/usr/bin/env python3
"""Replay committed ZenoEnergy research evidence and fail closed on drift."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.operator_report_output import emit_operator_json  # noqa: E402


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
    args = parser.parse_args()

    report = replay_zenoenergy_evidence(root=args.root)
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    emit_operator_json(report)
    return 0 if report["ok"] else 1


def replay_zenoenergy_evidence(
    *,
    root: Path = ROOT,
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

    energy_order_alone_formal = _load_json(
        root / "data/upba_energy/zenoenergy_energy_order_alone_formal_receipt.json"
    )
    energy_boundary_lean_source = (
        root / "lean-mathlib/Proofs/ZenoEnergyAdvisoryBoundary.lean"
    ).read_text(encoding="utf-8")
    energy_order_alone_doc = (
        root / "docs/ZENO_ENERGY_ENERGY_ORDER_ALONE_FORMAL.md"
    ).read_text(encoding="utf-8")
    payloads["energy_order_alone_formal"] = energy_order_alone_formal
    checks.extend(
        _check_energy_order_alone_formal(
            energy_order_alone_formal,
            energy_boundary_lean_source,
            energy_order_alone_doc,
        )
    )

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

    replay_source_manifest = _load_json(
        root / "data/upba_energy/zenoenergy_replay_source_manifest_receipt.json"
    )
    replay_source_manifest_doc = (
        root / "docs/ZENO_ENERGY_REPLAY_SOURCE_MANIFEST.md"
    ).read_text(encoding="utf-8")
    replay_source_manifest_source = (
        root / "tools/check_zenoenergy_replay_source_manifest.py"
    ).read_text(encoding="utf-8")
    replay_source_manifest_tests = (
        root / "tests/energy/test_zenoenergy_replay_source_manifest.py"
    ).read_text(encoding="utf-8")
    payloads["replay_source_manifest"] = replay_source_manifest
    checks.extend(
        _check_replay_source_manifest(
            replay_source_manifest,
            replay_source_manifest_doc,
            replay_source_manifest_source,
            replay_source_manifest_tests,
            production_gate_source,
        )
    )

    replay_source_manifest_builder = _load_json(
        root / "data/upba_energy/zenoenergy_replay_source_manifest_builder_receipt.json"
    )
    replay_source_manifest_builder_doc = (
        root / "docs/ZENO_ENERGY_REPLAY_SOURCE_MANIFEST_BUILDER.md"
    ).read_text(encoding="utf-8")
    replay_source_manifest_builder_source = (
        root / "tools/build_zenoenergy_replay_source_manifest.py"
    ).read_text(encoding="utf-8")
    replay_source_manifest_builder_tests = (
        root / "tests/energy/test_zenoenergy_replay_source_manifest_builder.py"
    ).read_text(encoding="utf-8")
    payloads["replay_source_manifest_builder"] = replay_source_manifest_builder
    checks.extend(
        _check_replay_source_manifest_builder(
            replay_source_manifest_builder,
            replay_source_manifest_builder_doc,
            replay_source_manifest_builder_source,
            replay_source_manifest_builder_tests,
        )
    )

    replay_secret_scan = _load_json(
        root / "data/upba_energy/zenoenergy_replay_secret_scan_receipt.json"
    )
    replay_secret_scan_doc = (
        root / "docs/ZENO_ENERGY_REPLAY_SECRET_SCAN.md"
    ).read_text(encoding="utf-8")
    replay_secret_scan_source = (
        root / "tools/check_zenoenergy_replay_secret_scan.py"
    ).read_text(encoding="utf-8")
    replay_secret_scan_tests = (
        root / "tests/energy/test_zenoenergy_replay_secret_scan.py"
    ).read_text(encoding="utf-8")
    payloads["replay_secret_scan"] = replay_secret_scan
    checks.extend(
        _check_replay_secret_scan(
            replay_secret_scan,
            replay_secret_scan_doc,
            replay_secret_scan_source,
            replay_secret_scan_tests,
            replay_source_manifest_builder_source,
        )
    )

    replay_coverage_profile = _load_json(
        root / "data/upba_energy/zenoenergy_replay_coverage_profile_receipt.json"
    )
    replay_coverage_profile_doc = (
        root / "docs/ZENO_ENERGY_REPLAY_COVERAGE_PROFILE.md"
    ).read_text(encoding="utf-8")
    replay_coverage_profile_source = (
        root / "tools/check_zenoenergy_replay_coverage_profile.py"
    ).read_text(encoding="utf-8")
    replay_coverage_profile_tests = (
        root / "tests/energy/test_zenoenergy_replay_coverage_profile.py"
    ).read_text(encoding="utf-8")
    payloads["replay_coverage_profile"] = replay_coverage_profile
    checks.extend(
        _check_replay_coverage_profile(
            replay_coverage_profile,
            replay_coverage_profile_doc,
            replay_coverage_profile_source,
            replay_coverage_profile_tests,
            production_gate_source,
        )
    )

    real_replay_builder = _load_json(
        root / "data/upba_energy/zenoenergy_real_replay_report_builder_receipt.json"
    )
    real_replay_builder_doc = (
        root / "docs/ZENO_ENERGY_REAL_REPLAY_REPORTS.md"
    ).read_text(encoding="utf-8")
    real_replay_builder_source = (
        root / "tools/build_zenoenergy_real_replay_report.py"
    ).read_text(encoding="utf-8")
    real_replay_builder_tests = (
        root / "tests/energy/test_zenoenergy_real_replay_report.py"
    ).read_text(encoding="utf-8")
    payloads["real_replay_report_builder"] = real_replay_builder
    checks.extend(
        _check_real_replay_report_builder(
            real_replay_builder,
            real_replay_builder_doc,
            real_replay_builder_source,
            real_replay_builder_tests,
        )
    )

    production_evidence_bundle = _load_json(
        root / "data/upba_energy/zenoenergy_production_evidence_bundle_receipt.json"
    )
    production_evidence_bundle_doc = (
        root / "docs/ZENO_ENERGY_PRODUCTION_EVIDENCE_BUNDLE.md"
    ).read_text(encoding="utf-8")
    production_evidence_bundle_source = (
        root / "tools/build_zenoenergy_production_evidence_bundle.py"
    ).read_text(encoding="utf-8")
    production_evidence_bundle_tests = (
        root / "tests/energy/test_zenoenergy_production_evidence_bundle.py"
    ).read_text(encoding="utf-8")
    payloads["production_evidence_bundle"] = production_evidence_bundle
    checks.extend(
        _check_production_evidence_bundle(
            production_evidence_bundle,
            production_evidence_bundle_doc,
            production_evidence_bundle_source,
            production_evidence_bundle_tests,
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

    dominance_cover = _load_json(
        root / "data/upba_energy/upba_v2_dominance_cover_benchmark_seed20260538.json"
    )
    dominance_cover_doc = (
        root / "docs/ZENO_ENERGY_DOMINANCE_COVER.md"
    ).read_text(encoding="utf-8")
    dominance_cover_source = (
        root / "src/energy/upba_v2_dominance_cover.py"
    ).read_text(encoding="utf-8")
    dominance_cover_tool = (
        root / "tools/check_upba_v2_dominance_cover.py"
    ).read_text(encoding="utf-8")
    dominance_cover_tests = (
        root / "tests/energy/test_upba_v2_dominance_cover.py"
    ).read_text(encoding="utf-8")
    payloads["dominance_cover"] = dominance_cover
    checks.extend(
        _check_dominance_cover(
            dominance_cover,
            dominance_cover_doc,
            dominance_cover_source,
            dominance_cover_tool,
            dominance_cover_tests,
        )
    )

    wes_dominance_search = _load_json(
        root / "data/upba_energy/zenoenergy_wes_dominance_search_seed20260539.json"
    )
    wes_dominance_doc = (
        root / "docs/ZENO_ENERGY_WES_DOMINANCE_SEARCH.md"
    ).read_text(encoding="utf-8")
    wes_dominance_tool = (
        root / "tools/run_zenoenergy_wes_dominance_search.py"
    ).read_text(encoding="utf-8")
    wes_dominance_tests = (
        root / "tests/energy/test_zenoenergy_wes_dominance_search.py"
    ).read_text(encoding="utf-8")
    payloads["wes_dominance_search"] = wes_dominance_search
    checks.extend(
        _check_wes_dominance_search(
            wes_dominance_search,
            wes_dominance_doc,
            wes_dominance_tool,
            wes_dominance_tests,
        )
    )

    dominance_prefix = _load_json(
        root / "data/upba_energy/upba_v2_dominance_prefix_benchmark_seed20260540.json"
    )
    dominance_prefix_doc = (
        root / "docs/ZENO_ENERGY_DOMINANCE_PREFIX.md"
    ).read_text(encoding="utf-8")
    dominance_prefix_tool = (
        root / "tools/check_upba_v2_dominance_prefix.py"
    ).read_text(encoding="utf-8")
    dominance_prefix_source = (
        root / "src/energy/upba_v2_dominance_cover.py"
    ).read_text(encoding="utf-8")
    dominance_prefix_tests = (
        root / "tests/energy/test_upba_v2_dominance_cover.py"
    ).read_text(encoding="utf-8")
    payloads["dominance_prefix"] = dominance_prefix
    checks.extend(
        _check_dominance_prefix(
            dominance_prefix,
            dominance_prefix_doc,
            dominance_prefix_tool,
            dominance_prefix_source,
            dominance_prefix_tests,
        )
    )

    suffix_bound = _load_json(
        root / "data/upba_energy/upba_v2_suffix_bound_benchmark_seed20260541.json"
    )
    suffix_bound_doc = (
        root / "docs/ZENO_ENERGY_SUFFIX_BOUND.md"
    ).read_text(encoding="utf-8")
    suffix_bound_source = (
        root / "src/energy/upba_v2_suffix_bound.py"
    ).read_text(encoding="utf-8")
    suffix_bound_tool = (
        root / "tools/check_upba_v2_suffix_bound.py"
    ).read_text(encoding="utf-8")
    suffix_bound_tests = (
        root / "tests/energy/test_upba_v2_suffix_bound.py"
    ).read_text(encoding="utf-8")
    suffix_bound_lean = (
        root / "lean-mathlib/Proofs/ZenoEnergyAdvisoryBoundary.lean"
    ).read_text(encoding="utf-8")
    payloads["suffix_bound"] = suffix_bound
    checks.extend(
        _check_suffix_bound(
            suffix_bound,
            suffix_bound_doc,
            suffix_bound_source,
            suffix_bound_tool,
            suffix_bound_tests,
            suffix_bound_lean,
        )
    )

    suffix_bound_cross_seed = _load_json(
        root / "data/upba_energy/upba_v2_suffix_bound_cross_seed_seed20260541_20260543.json"
    )
    suffix_bound_cross_seed_doc = (
        root / "docs/ZENO_ENERGY_SUFFIX_BOUND_CROSS_SEED.md"
    ).read_text(encoding="utf-8")
    suffix_bound_cross_seed_tool = (
        root / "tools/stress_upba_v2_suffix_bound.py"
    ).read_text(encoding="utf-8")
    suffix_bound_cross_seed_tests = (
        root / "tests/energy/test_upba_v2_suffix_bound_stress.py"
    ).read_text(encoding="utf-8")
    payloads["suffix_bound_cross_seed"] = suffix_bound_cross_seed
    checks.extend(
        _check_suffix_bound_cross_seed(
            suffix_bound_cross_seed,
            suffix_bound_cross_seed_doc,
            suffix_bound_cross_seed_tool,
            suffix_bound_cross_seed_tests,
        )
    )

    suffix_bound_adversarial = _load_json(
        root / "data/upba_energy/upba_v2_suffix_bound_adversarial_stress_seed20260544.json"
    )
    suffix_bound_adversarial_doc = (
        root / "docs/ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS.md"
    ).read_text(encoding="utf-8")
    suffix_bound_adversarial_tool = (
        root / "tools/stress_upba_v2_suffix_bound_adversarial.py"
    ).read_text(encoding="utf-8")
    suffix_bound_adversarial_tests = (
        root / "tests/energy/test_upba_v2_suffix_bound_adversarial_stress.py"
    ).read_text(encoding="utf-8")
    payloads["suffix_bound_adversarial"] = suffix_bound_adversarial
    checks.extend(
        _check_suffix_bound_adversarial(
            suffix_bound_adversarial,
            suffix_bound_adversarial_doc,
            suffix_bound_adversarial_tool,
            suffix_bound_adversarial_tests,
        )
    )

    suffix_bound_adversarial_families = _load_json(
        root
        / "data/upba_energy/upba_v2_suffix_bound_adversarial_family_stress_seed20260545.json"
    )
    suffix_bound_adversarial_families_doc = (
        root / "docs/ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_FAMILY_STRESS.md"
    ).read_text(encoding="utf-8")
    suffix_bound_adversarial_families_tool = (
        root / "tools/stress_upba_v2_suffix_bound_adversarial_families.py"
    ).read_text(encoding="utf-8")
    suffix_bound_adversarial_families_tests = (
        root / "tests/energy/test_upba_v2_suffix_bound_adversarial_family_stress.py"
    ).read_text(encoding="utf-8")
    payloads["suffix_bound_adversarial_families"] = (
        suffix_bound_adversarial_families
    )
    checks.extend(
        _check_suffix_bound_adversarial_families(
            suffix_bound_adversarial_families,
            suffix_bound_adversarial_families_doc,
            suffix_bound_adversarial_families_tool,
            suffix_bound_adversarial_families_tests,
        )
    )

    negative_curriculum = _load_json(
        root / "data/upba_energy/zenoenergy_negative_curriculum_seed20260545.json"
    )
    negative_curriculum_doc = (
        root / "docs/ZENO_ENERGY_NEGATIVE_CURRICULUM.md"
    ).read_text(encoding="utf-8")
    negative_curriculum_tool = (
        root / "tools/zenoenergy_negative_curriculum.jl"
    ).read_text(encoding="utf-8")
    negative_curriculum_tests = (
        root / "tests/energy/test_zenoenergy_negative_curriculum_julia.py"
    ).read_text(encoding="utf-8")
    payloads["negative_curriculum"] = negative_curriculum
    checks.extend(
        _check_negative_curriculum(
            negative_curriculum,
            negative_curriculum_doc,
            negative_curriculum_tool,
            negative_curriculum_tests,
        )
    )

    curriculum_ranker = _load_json(
        root / "data/upba_energy/upba_v2_energy_curriculum_ranker_seed20260517.json"
    )
    curriculum_ranker_doc = (
        root / "docs/ZENO_ENERGY_CURRICULUM_RANKER.md"
    ).read_text(encoding="utf-8")
    curriculum_ranker_tool = (
        root / "tools/benchmark_upba_energy_curriculum.py"
    ).read_text(encoding="utf-8")
    curriculum_ranker_tests = (
        root / "tests/energy/test_upba_v2_curriculum_ranker.py"
    ).read_text(encoding="utf-8")
    trainer_source = (root / "tools/train_upba_energy.py").read_text(encoding="utf-8")
    payloads["curriculum_ranker"] = curriculum_ranker
    checks.extend(
        _check_curriculum_ranker(
            curriculum_ranker,
            curriculum_ranker_doc,
            curriculum_ranker_tool,
            curriculum_ranker_tests,
            trainer_source,
        )
    )

    data_scaling = _load_json(
        root / "data/upba_energy/upba_v2_energy_data_scaling_seed20260517.json"
    )
    data_scaling_doc = (
        root / "docs/ZENO_ENERGY_DATA_SCALING.md"
    ).read_text(encoding="utf-8")
    data_scaling_tool = (
        root / "tools/benchmark_upba_energy_data_scaling.py"
    ).read_text(encoding="utf-8")
    data_scaling_tests = (
        root / "tests/energy/test_upba_v2_data_scaling.py"
    ).read_text(encoding="utf-8")
    payloads["data_scaling"] = data_scaling
    checks.extend(
        _check_data_scaling(
            data_scaling,
            data_scaling_doc,
            data_scaling_tool,
            data_scaling_tests,
        )
    )

    quality_selection = _load_json(
        root / "data/upba_energy/upba_v2_energy_quality_selection_seed20260517.json"
    )
    quality_selection_doc = (
        root / "docs/ZENO_ENERGY_QUALITY_SELECTION.md"
    ).read_text(encoding="utf-8")
    quality_selection_tool = (
        root / "tools/benchmark_upba_energy_quality_selection.py"
    ).read_text(encoding="utf-8")
    quality_selection_tests = (
        root / "tests/energy/test_upba_v2_quality_selection.py"
    ).read_text(encoding="utf-8")
    payloads["quality_selection"] = quality_selection
    checks.extend(
        _check_quality_selection(
            quality_selection,
            quality_selection_doc,
            quality_selection_tool,
            quality_selection_tests,
        )
    )

    ensemble = _load_json(
        root / "data/upba_energy/upba_v2_energy_ensemble_seed20260556.json"
    )
    ensemble_doc = (
        root / "docs/ZENO_ENERGY_ENSEMBLE.md"
    ).read_text(encoding="utf-8")
    ensemble_tool = (
        root / "tools/benchmark_upba_energy_ensemble.py"
    ).read_text(encoding="utf-8")
    ensemble_module = (
        root / "src/energy/upba_v2_ensemble.py"
    ).read_text(encoding="utf-8")
    ensemble_tests = (
        root / "tests/energy/test_upba_v2_ensemble.py"
    ).read_text(encoding="utf-8")
    payloads["ensemble"] = ensemble
    checks.extend(
        _check_ensemble(
            ensemble,
            ensemble_doc,
            ensemble_tool,
            ensemble_module,
            ensemble_tests,
        )
    )

    best_model_registry = _load_json(
        root / "data/upba_energy/zenoenergy_best_model_registry.json"
    )
    best_model_doc = (
        root / "docs/ZENO_ENERGY_BEST_MODELS.md"
    ).read_text(encoding="utf-8")
    best_model_tool = (
        root / "tools/preserve_zenoenergy_best_models.py"
    ).read_text(encoding="utf-8")
    best_model_tests = (
        root / "tests/energy/test_zenoenergy_best_model_registry.py"
    ).read_text(encoding="utf-8")
    payloads["best_model_registry"] = best_model_registry
    checks.extend(
        _check_best_model_registry(
            root,
            best_model_registry,
            best_model_doc,
            best_model_tool,
            best_model_tests,
        )
    )

    upba_v2_model_leaderboard = _load_json(
        root / "data/upba_energy/upba_v2_energy_model_leaderboard.json"
    )
    upba_v2_model_leaderboard_doc = (
        root / "docs/ZENO_ENERGY_UPBA_V2_MODEL_LEADERBOARD.md"
    ).read_text(encoding="utf-8")
    upba_v2_model_leaderboard_tool = (
        root / "tools/build_upba_energy_model_leaderboard.py"
    ).read_text(encoding="utf-8")
    upba_v2_model_leaderboard_tests = (
        root / "tests/energy/test_upba_v2_model_leaderboard.py"
    ).read_text(encoding="utf-8")
    payloads["upba_v2_model_leaderboard"] = upba_v2_model_leaderboard
    checks.extend(
        _check_upba_v2_model_leaderboard(
            upba_v2_model_leaderboard,
            upba_v2_model_leaderboard_doc,
            upba_v2_model_leaderboard_tool,
            upba_v2_model_leaderboard_tests,
        )
    )

    epiplexity_literature = _load_json(
        root / "data/upba_energy/zenoenergy_epiplexity_literature_receipt.json"
    )
    epiplexity_literature_doc = (
        root / "docs/ZENO_ENERGY_EPIPLEXITY_LITERATURE.md"
    ).read_text(encoding="utf-8")
    epiplexity_literature_tool = (
        root / "tools/check_zenoenergy_epiplexity_literature.py"
    ).read_text(encoding="utf-8")
    epiplexity_literature_tests = (
        root / "tests/energy/test_zenoenergy_epiplexity_literature.py"
    ).read_text(encoding="utf-8")
    payloads["epiplexity_literature"] = epiplexity_literature
    checks.extend(
        _check_epiplexity_literature(
            epiplexity_literature,
            epiplexity_literature_doc,
            epiplexity_literature_tool,
            epiplexity_literature_tests,
        )
    )

    synthetic_data_limits = _load_json(
        root / "data/upba_energy/zenoenergy_synthetic_data_limits_receipt.json"
    )
    synthetic_data_limits_doc = (
        root / "docs/ZENO_ENERGY_SYNTHETIC_DATA_LIMITS.md"
    ).read_text(encoding="utf-8")
    synthetic_data_limits_tool = (
        root / "tools/check_zenoenergy_synthetic_data_limits.py"
    ).read_text(encoding="utf-8")
    synthetic_data_limits_tests = (
        root / "tests/energy/test_zenoenergy_synthetic_data_limits.py"
    ).read_text(encoding="utf-8")
    payloads["synthetic_data_limits"] = synthetic_data_limits
    checks.extend(
        _check_synthetic_data_limits(
            synthetic_data_limits,
            synthetic_data_limits_doc,
            synthetic_data_limits_tool,
            synthetic_data_limits_tests,
        )
    )

    langevin_discovery = _load_json(
        root / "data/upba_energy/gemini_langevin_discovery_receipt.json"
    )
    langevin_discovery_doc = (
        root / "docs/ZENO_ENERGY_GEMINI_LANGEVIN_DISCOVERY.md"
    ).read_text(encoding="utf-8")
    langevin_discovery_tool = (
        root / "tools/check_gemini_langevin_discovery.py"
    ).read_text(encoding="utf-8")
    langevin_discovery_tests = (
        root / "tests/energy/test_gemini_langevin.py"
    ).read_text(encoding="utf-8")
    payloads["langevin_discovery"] = langevin_discovery
    checks.extend(
        _check_langevin_discovery(
            langevin_discovery,
            langevin_discovery_doc,
            langevin_discovery_tool,
            langevin_discovery_tests,
        )
    )

    autotrader_refiner_boundary = _load_json(
        root / "data/upba_energy/autotrader_refiner_boundary_seed20260529.json"
    )
    autotrader_refiner_doc = (
        root / "docs/AUTOTRADER_REFINER_BOUNDARY.md"
    ).read_text(encoding="utf-8")
    autotrader_refiner_tool = (
        root / "tools/check_autotrader_refiner_boundary.py"
    ).read_text(encoding="utf-8")
    autotrader_refiner_tests = (
        root / "tests/energy/test_autotrader_refiner_boundary.py"
    ).read_text(encoding="utf-8")
    payloads["autotrader_refiner_boundary"] = autotrader_refiner_boundary
    checks.extend(
        _check_autotrader_refiner_boundary(
            autotrader_refiner_boundary,
            autotrader_refiner_doc,
            autotrader_refiner_tool,
            autotrader_refiner_tests,
        )
    )

    jepa_logic_boundary = _load_json(
        root / "data/upba_energy/gemini_jepa_logic_boundary_receipt.json"
    )
    jepa_logic_doc = (
        root / "docs/ZENO_ENERGY_GEMINI_JEPA_LOGIC_BOUNDARY.md"
    ).read_text(encoding="utf-8")
    jepa_logic_tool = (
        root / "tools/check_gemini_jepa_logic_boundary.py"
    ).read_text(encoding="utf-8")
    jepa_logic_tests = (
        root / "tests/energy/test_gemini_jepa_logic_boundary.py"
    ).read_text(encoding="utf-8")
    payloads["jepa_logic_boundary"] = jepa_logic_boundary
    checks.extend(
        _check_jepa_logic_boundary(
            jepa_logic_boundary,
            jepa_logic_doc,
            jepa_logic_tool,
            jepa_logic_tests,
        )
    )

    autotrader_jepa_ux = _load_json(
        root / "data/upba_energy/autotrader_jepa_ux_receipt_seed20260531.json"
    )
    autotrader_jepa_ux_doc = (
        root / "docs/ZENO_ENERGY_AUTOTRADER_JEPA_UX.md"
    ).read_text(encoding="utf-8")
    autotrader_jepa_ux_tool = (
        root / "tools/check_zenoenergy_autotrader_jepa_ux.py"
    ).read_text(encoding="utf-8")
    autotrader_jepa_ux_tests = (
        root / "tests/energy/test_zenoenergy_autotrader_jepa_ux.py"
    ).read_text(encoding="utf-8") + (
        root / "tests/energy/test_zeno_jepa_autotrader_ux.py"
    ).read_text(encoding="utf-8")
    autotrader_jepa_ux_source = (
        root / "src/energy/zeno_jepa.py"
    ).read_text(encoding="utf-8") + (
        root / "src/energy/autotrader_ux.py"
    ).read_text(encoding="utf-8")
    payloads["autotrader_jepa_ux"] = autotrader_jepa_ux
    checks.extend(
        _check_autotrader_jepa_ux(
            autotrader_jepa_ux,
            autotrader_jepa_ux_doc,
            autotrader_jepa_ux_tool,
            autotrader_jepa_ux_tests,
            autotrader_jepa_ux_source,
        )
    )

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


def _check_energy_order_alone_formal(
    report: dict[str, Any],
    lean_source: str,
    doc_text: str,
) -> list[EvidenceCheck]:
    names = set(str(name) for name in report["formal_names"])
    required = {
        "theorem energy_order_alone_does_not_imply_true_weakly_best",
        "theorem energy_order_alone_does_not_imply_true_weakly_max",
    }
    joined_negative = " ".join(str(item) for item in report["negative_knowledge"])
    joined_limits = " ".join(str(item) for item in report["limits"])
    doc_lower = doc_text.lower()
    return [
        _expect_equal(
            "energy_order_alone_formal.schema",
            report.get("schema"),
            "zenodex/energy/energy_order_alone_formal_receipt/v1",
        ),
        _expect_true(
            "energy_order_alone_formal.commands",
            all(int(command["exit_code"]) == 0 for command in report["commands"]),
            "Lean boundary target and focused formal regression are recorded as passing",
        ),
        _expect_true(
            "energy_order_alone_formal.names",
            required.issubset(names)
            and all(name in lean_source for name in required),
            "energy-order-alone counterexample theorem names are present in receipt and Lean source",
        ),
        _expect_true(
            "energy_order_alone_formal.negative_boundary",
            "ordering alone" in str(report["claim"])
            and "cannot prove verifier optimality" in joined_negative
            and "not a quantitative model-performance claim" in joined_limits
            and "cannot authorize" in doc_lower
            and "suffix-bound checked-stop certificate" in doc_text,
            "receipt and docs preserve the model-proposes verifier-decides boundary",
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
            and "passing replay source manifest" in doc_lower
            and "coverage profile" in doc_lower
            and "MIN_UPBA_REAL_BATCHES" in source_text
            and "_source_manifest_check_ok" in source_text
            and "_coverage_profile_check_ok" in source_text
            and "MIN_AUTOTRADER_REAL_CONTEXTS" in source_text,
            "doc and source record real replay thresholds and ranking-only scope",
        ),
    ]


def _check_replay_source_manifest(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    test_text: str,
    production_gate_source: str,
) -> list[EvidenceCheck]:
    artifacts = set(str(item) for item in report.get("artifacts", []))
    doc_lower = doc_text.lower()
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_equal(
            "replay_source_manifest.schema",
            report.get("schema"),
            "zenodex/energy/replay_source_manifest_receipt/v1",
        ),
        _expect_true(
            "replay_source_manifest.schemas_and_artifacts",
            report.get("source_manifest_schema")
            == "zenodex/energy/replay_source_manifest/v1"
            and report.get("source_manifest_check_schema")
            == "zenodex/energy/replay_source_manifest_check/v1"
            and {
                "tools/check_zenoenergy_replay_source_manifest.py",
                "tests/energy/test_zenoenergy_replay_source_manifest.py",
                "docs/ZENO_ENERGY_REPLAY_SOURCE_MANIFEST.md",
            }.issubset(artifacts)
            and "zenodex/energy/replay_source_manifest/v1" in doc_text
            and "zenodex/energy/replay_source_manifest_check/v1" in doc_text,
            "receipt and doc record source manifest schemas and artifacts",
        ),
        _expect_true(
            "replay_source_manifest.source_hygiene_hooks",
            "FORBIDDEN_SOURCE_MARKERS" in source_text
            and "secret_scan_clean" in source_text
            and "source_reports_match" in source_text
            and "canonical_sha256" in source_text
            and "test_manifest_check_rejects_dirty_secret_scan" in test_text
            and "test_manifest_check_rejects_source_report_hash_mismatch" in test_text,
            "checker validates fixture markers, secret scan, and source report hashes",
        ),
        _expect_true(
            "replay_source_manifest.production_gate_hook",
            "_source_manifest_check_ok" in production_gate_source
            and "source_manifest_ok" in production_gate_source
            and "source-manifested" in production_gate_source
            and "production promotion requires" in doc_lower,
            "production gate requires a passing source manifest check on real reports",
        ),
        _expect_true(
            "replay_source_manifest.negative_knowledge",
            bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement_or_trade"])
            is False
            and "cannot prove external data custody" in limits_lower
            and "without a passing replay source manifest check" in negative_lower,
            "receipt preserves advisory boundary and source-custody limits",
        ),
    ]


def _check_replay_source_manifest_builder(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    artifacts = set(str(item) for item in report.get("artifacts", []))
    fail_closed = " ".join(str(item).lower() for item in report.get("fail_closed_rules", []))
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_equal(
            "replay_source_manifest_builder.schema",
            report.get("schema"),
            "zenodex/energy/replay_source_manifest_builder_receipt/v1",
        ),
        _expect_true(
            "replay_source_manifest_builder.artifacts_and_schemas",
            report.get("builder_schema")
            == "zenodex/energy/replay_source_manifest_builder/v1"
            and report.get("output_schema")
            == "zenodex/energy/replay_source_manifest/v1"
            and report.get("check_schema")
            == "zenodex/energy/replay_source_manifest_check/v1"
            and {
                "tools/build_zenoenergy_replay_source_manifest.py",
                "tests/energy/test_zenoenergy_replay_source_manifest_builder.py",
                "docs/ZENO_ENERGY_REPLAY_SOURCE_MANIFEST_BUILDER.md",
            }.issubset(artifacts)
            and "zenodex/energy/replay_source_manifest_builder/v1" in source_text
            and "tools/build_zenoenergy_replay_source_manifest.py" in doc_text,
            "receipt, source, and doc record the manifest builder schema and artifacts",
        ),
        _expect_true(
            "replay_source_manifest_builder.fail_closed_hooks",
            "source_report_from_path" in source_text
            and "validate_replay_source_manifest" in source_text
            and "secret_scan_ok" in source_text
            and "--deterministic-replay-ok" in source_text
            and "--no-live-secrets" in source_text
            and "return 2" in source_text
            and "test_cli_fails_closed_without_clean_secret_scan" in test_text
            and "test_cli_rejects_secret_scan_source_count_mismatch" in test_text
            and "test_builds_manifest_with_canonical_source_report_hash" in test_text
            and "dirty secret scans fail" in fail_closed,
            "builder computes source hashes, requires attestations, and fails closed on dirty secret scans",
        ),
        _expect_true(
            "replay_source_manifest_builder.safety_and_limits",
            bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement_or_trade"])
            is False
            and bool(report["safety"]["manifest_builder_authorizes_production"])
            is False
            and "external data custody" in limits_lower
            and "not sufficient production evidence" in negative_lower,
            "builder preserves advisory boundary and records custody limits",
        ),
    ]


def _check_replay_secret_scan(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    test_text: str,
    manifest_builder_source: str,
) -> list[EvidenceCheck]:
    artifacts = set(str(item) for item in report.get("artifacts", []))
    rules = set(str(item) for item in report.get("scanner_rules", []))
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_equal(
            "replay_secret_scan.schema",
            report.get("schema"),
            "zenodex/energy/replay_secret_scan_receipt/v1",
        ),
        _expect_true(
            "replay_secret_scan.schemas_rules_and_artifacts",
            report.get("secret_scan_schema")
            == "zenodex/energy/replay_secret_scan/v1"
            and {
                "tools/check_zenoenergy_replay_secret_scan.py",
                "tests/energy/test_zenoenergy_replay_secret_scan.py",
                "docs/ZENO_ENERGY_REPLAY_SECRET_SCAN.md",
            }.issubset(artifacts)
            and {
                "private_key_pem",
                "aws_access_key_id",
                "openai_api_key",
                "github_token",
                "sensitive_json_key",
            }.issubset(rules)
            and "zenodex/energy/replay_secret_scan/v1" in doc_text
            and "tools/check_zenoenergy_replay_secret_scan.py" in doc_text,
            "receipt and doc record scanner schema, artifacts, and detector rules",
        ),
        _expect_true(
            "replay_secret_scan.source_hooks",
            "SECRET_SCAN_SCHEMA" in source_text
            and "TEXT_RULES" in source_text
            and "SENSITIVE_KEYS" in source_text
            and "secret_scan_manifest_fragment" in source_text
            and "test_secret_scan_rejects_sensitive_json_key" in test_text
            and "test_secret_scan_cli_returns_one_on_findings" in test_text
            and "--secret-scan-report" in manifest_builder_source
            and "secret_scan_manifest_fragment" in manifest_builder_source,
            "scanner source, tests, and manifest builder integration are present",
        ),
        _expect_true(
            "replay_secret_scan.safety_and_limits",
            bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement_or_trade"])
            is False
            and bool(report["safety"]["secret_scanner_authorizes_production"])
            is False
            and "privacy compliance" in limits_lower
            and "full privacy audit" in negative_lower
            and "production promotion decision" in negative_lower,
            "receipt preserves advisory boundary and scanner limits",
        ),
    ]


def _check_replay_coverage_profile(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    test_text: str,
    production_gate_source: str,
) -> list[EvidenceCheck]:
    artifacts = set(str(item) for item in report.get("artifacts", []))
    integrations = set(str(item) for item in report.get("integrations", []))
    thresholds = report.get("thresholds", {})
    upba_thresholds = thresholds.get("upba", {})
    autotrader_thresholds = thresholds.get("autotrader", {})
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_equal(
            "replay_coverage_profile.schema",
            report.get("schema"),
            "zenodex/energy/replay_coverage_profile_receipt/v1",
        ),
        _expect_true(
            "replay_coverage_profile.schemas_thresholds_and_artifacts",
            report.get("profile_schema")
            == "zenodex/energy/replay_coverage_profile/v1"
            and report.get("profile_check_schema")
            == "zenodex/energy/replay_coverage_profile_check/v1"
            and int(upba_thresholds.get("min_pool_count", 0)) >= 3
            and int(upba_thresholds.get("min_hard_negative_family_count", 0)) >= 4
            and int(autotrader_thresholds.get("min_guard_family_count", 0)) >= 4
            and {
                "tools/check_zenoenergy_replay_coverage_profile.py",
                "tests/energy/test_zenoenergy_replay_coverage_profile.py",
                "docs/ZENO_ENERGY_REPLAY_COVERAGE_PROFILE.md",
            }.issubset(artifacts)
            and "zenodex/energy/replay_coverage_profile/v1" in doc_text
            and "zenodex/energy/replay_coverage_profile_check/v1" in doc_text,
            "receipt and doc record coverage profile schemas, thresholds, and artifacts",
        ),
        _expect_true(
            "replay_coverage_profile.source_hooks",
            "MIN_UPBA_POOL_COUNT" in source_text
            and "MIN_UPBA_HARD_NEGATIVE_FAMILY_COUNT" in source_text
            and "MIN_AUTOTRADER_GUARD_FAMILY_COUNT" in source_text
            and "source_report_count_match" in source_text
            and "coverage_profile_summary" in source_text
            and "test_upba_coverage_profile_rejects_thin_hard_negatives" in test_text
            and "test_autotrader_coverage_profile_rejects_source_mismatch" in test_text,
            "checker validates breadth thresholds, source matching, and summary export",
        ),
        _expect_true(
            "replay_coverage_profile.production_hooks",
            {
                "tools/build_zenoenergy_real_replay_report.py",
                "tools/check_zenoenergy_production_promotion.py",
                "tools/build_zenoenergy_production_evidence_bundle.py",
            }.issubset(integrations)
            and "_coverage_profile_check_ok" in production_gate_source
            and "coverage_profile_ok" in production_gate_source
            and "replay coverage profile check" in production_gate_source,
            "production gate requires a passing coverage profile on real reports",
        ),
        _expect_true(
            "replay_coverage_profile.safety_and_limits",
            bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement_or_trade"])
            is False
            and bool(report["safety"]["coverage_profile_authorizes_production"])
            is False
            and "representative" in limits_lower
            and "aggregate batch" in negative_lower
            and "not a production authorization path" in negative_lower,
            "receipt preserves advisory boundary and representativeness limits",
        ),
    ]


def _check_real_replay_report_builder(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    targets = set(str(item) for item in report.get("target_schemas", []))
    artifacts = set(str(item) for item in report.get("artifacts", []))
    doc_lower = doc_text.lower()
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_equal(
            "real_replay_report_builder.schema",
            report.get("schema"),
            "zenodex/energy/real_replay_report_builder_receipt/v1",
        ),
        _expect_true(
            "real_replay_report_builder.targets_and_artifacts",
            {
                "zenodex/energy/upba_real_replay_report/v1",
                "zenodex/energy/autotrader_real_shadow_report/v1",
            }.issubset(targets)
            and report.get("source_manifest_check_schema")
            == "zenodex/energy/replay_source_manifest_check/v1"
            and report.get("coverage_profile_check_schema")
            == "zenodex/energy/replay_coverage_profile_check/v1"
            and {
                "tools/build_zenoenergy_real_replay_report.py",
                "tools/check_zenoenergy_replay_coverage_profile.py",
                "tests/energy/test_zenoenergy_real_replay_report.py",
                "docs/ZENO_ENERGY_REAL_REPLAY_REPORTS.md",
            }.issubset(artifacts)
            and "zenodex/energy/upba_real_replay_report/v1" in doc_text
            and "zenodex/energy/autotrader_real_shadow_report/v1" in doc_text,
            "receipt and doc record both production-gate report schemas",
        ),
        _expect_true(
            "real_replay_report_builder.source_hygiene_hooks",
            "FORBIDDEN_SOURCE_MARKERS" in source_text
            and "--deterministic-replay-ok" in source_text
            and "--no-live-secrets" in source_text
            and "--source-manifest" in source_text
            and "--coverage-profile" in source_text
            and "source_reports" in source_text
            and "source_manifest_summary" in source_text
            and "coverage_profile_summary" in source_text
            and "_canonical_sha256" in source_text
            and "rejects obvious fixture or synthetic source descriptors" in doc_lower
            and "coverage profile check" in doc_lower
            and "test_builder_rejects_autotrader_builtin_fixture_source" in test_text,
            "builder rejects fixture markers and records source hashes, replay/secret attestations, and source manifest checks",
        ),
        _expect_true(
            "real_replay_report_builder.safety_boundary",
            bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement_or_trade"])
            is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and bool(report["safety"]["performance_thresholds_delegated_to_production_gate"])
            is True
            and "cannot independently prove" in limits_lower
            and "synthetic and built-in fixture reports remain research evidence"
            in negative_lower,
            "builder preserves verifier/policy authority and records provenance limits",
        ),
    ]


def _check_production_evidence_bundle(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    artifacts = set(str(item) for item in report.get("artifacts", []))
    output_schemas = set(str(item) for item in report.get("output_schemas", []))
    composed_tools = set(str(item) for item in report.get("composed_tools", []))
    doc_lower = doc_text.lower()
    source_lower = source_text.lower()
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_equal(
            "production_evidence_bundle.schema",
            report.get("schema"),
            "zenodex/energy/production_evidence_bundle_receipt/v1",
        ),
        _expect_true(
            "production_evidence_bundle.artifacts_and_schemas",
            report.get("bundle_schema")
            == "zenodex/energy/production_evidence_bundle/v1"
            and {
                "zenodex/energy/upba_real_replay_report/v1",
                "zenodex/energy/autotrader_real_shadow_report/v1",
                "zenodex/energy/replay_source_manifest_check/v1",
                "zenodex/energy/replay_coverage_profile_check/v1",
                "zenodex/energy/production_promotion_gate/v1",
                "zenodex/energy/production_evidence_bundle/v1",
            }.issubset(output_schemas)
            and {
                "tools/build_zenoenergy_production_evidence_bundle.py",
                "tests/energy/test_zenoenergy_production_evidence_bundle.py",
                "docs/ZENO_ENERGY_PRODUCTION_EVIDENCE_BUNDLE.md",
            }.issubset(artifacts)
            and "zenodex/energy/production_evidence_bundle/v1" in doc_text,
            "receipt and doc record bundle schema, output schemas, and artifacts",
        ),
        _expect_true(
            "production_evidence_bundle.source_hooks",
            {
                "tools/build_zenoenergy_real_replay_report.py",
                "tools/check_zenoenergy_replay_source_manifest.py",
                "tools/check_zenoenergy_replay_coverage_profile.py",
                "tools/check_zenoenergy_production_promotion.py",
            }.issubset(composed_tools)
            and "build_upba_real_replay_report" in source_text
            and "build_autotrader_real_shadow_report" in source_text
            and "validate_replay_source_manifest" in source_text
            and "validate_replay_coverage_profile" in source_text
            and "build_production_gate_report" in source_text
            and "_require_passing_manifest_check" in source_text
            and "source_manifest_checks" in source_text
            and "coverage_profile_checks" in source_text
            and "test_bundle_rejects_source_manifest_hash_mismatch" in test_text
            and "test_cli_writes_bundle_json_and_markdown" in test_text,
            "bundle composes real report builders, source manifest checks, and production gate",
        ),
        _expect_true(
            "production_evidence_bundle.safety_and_limits",
            bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["policy_guards_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement_or_trade"])
            is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and bool(report["safety"]["deterministic_fallback_required"]) is True
            and "advisory ranking" in doc_lower
            and "exits with code `2`" in doc_lower
            and "coverage profiles fail" in doc_lower
            and "cannot prove external data custody" in limits_lower
            and "without passing replay source manifests" in negative_lower
            and "coverage profiles" in negative_lower
            and "outside settlement validity" in source_lower,
            "bundle preserves advisory boundary, fail-closed manifest behavior, and custody limits",
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
        "tiny ensemble uncertainty: diagnostic only",
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
        "tiny ensemble ranker did not beat the gap-weighted default",
    }
    required_sources = {
        "https://cs.nyu.edu/~yann/research/ebm/",
        "https://neurips.cc/virtual/2006/tutorial/3",
        "https://arxiv.org/abs/2101.03288",
        "https://logicalintelligence.com/blog/energy-based-models-for-reasoning",
        "https://papers.nips.cc/paper/6931-deep-sets",
        "https://proceedings.mlr.press/v97/lee19d.html",
        "https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2007-40.pdf",
        "https://papers.neurips.cc/paper/7219-simple-and-scalable-predictive-uncertainty-estimation-using-deep-ensembles",
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
        "tiny ensemble uncertainty",
        "diagnostic only",
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


def _check_dominance_cover(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    summary = report["summary"]
    winner = summary["winner_only"]
    weak = summary["weak_pruned"]
    hand = summary["hand_top1"]
    doc_lower = doc_text.lower()
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_true(
            "dominance_cover.schema",
            report.get("schema")
            == "zenodex/energy/upba_v2_dominance_cover_benchmark/v1"
            and report.get("certificate_schema")
            == "zenodex/energy/upba_v2_dominance_cover_certificate/v1",
            "dominance-cover benchmark and certificate schemas are stable",
        ),
        _expect_true(
            "dominance_cover.winner_only_passes",
            int(winner["count"]) > 0
            and int(winner["ok_count"]) == int(winner["count"])
            and int(winner["structural_verify_ok_count"]) == int(winner["count"])
            and int(winner["max_uncovered_full_count"]) == 0,
            "winner-only certificates pass over the verified full list",
        ),
        _expect_true(
            "dominance_cover.weak_pruned_rejected",
            int(weak["count"]) > 0
            and int(weak["failed_count"]) == int(weak["count"])
            and int(weak["dominance_cover_ok_count"]) == 0
            and int(weak["max_uncovered_full_count"]) > 0
            and "uncovered better verified candidate" in negative_lower,
            "weak pruned negative controls are rejected when better verified candidates are uncovered",
        ),
        _expect_true(
            "dominance_cover.hand_top1_nonvacuous",
            int(hand["count"]) > 0
            and 0 < int(hand["failed_count"]) < int(hand["count"])
            and int(hand["ok_count"]) == int(hand["structural_verify_ok_count"]),
            "hand-energy top-1 pruning is a mixed baseline rather than a vacuous pass",
        ),
        _expect_true(
            "dominance_cover.safety_and_hooks",
            int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and "full_list_complete_for_claim" in source_text
            and "pruned_sound_ok" in source_text
            and "global_claim_ok" in source_text
            and "verify_upba_v2_dominance_cover_certificate" in tool_text
            and "test_weak_pruned_set_fails_when_better_verified_candidate_is_uncovered"
            in test_text
            and "bounded synthetic full lists" in doc_lower
            and "completeness proof" in doc_lower
            and "not a upba v2 bounded-grid optimality verifier" in limits_lower,
            "runtime checker preserves verifier authority and states finite-list scope",
        ),
    ]


def _check_wes_dominance_search(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    summary = report["summary"]
    doc_lower = doc_text.lower()
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_true(
            "wes_dominance_search.schema",
            report.get("schema")
            == "zenodex/energy/zenoenergy_wes_dominance_search/v1"
            and report.get("wes_report_schema") == "wes_generic_policy_comparison.v1"
            and report.get("wes_commit")
            == "5a26bcc1d97c90503bb66e67c7c2a2cf40d41bb6",
            "WES bridge schema and pinned external WES commit are recorded",
        ),
        _expect_true(
            "wes_dominance_search.candidate_corpus",
            int(report["input_candidates"]) == 120
            and int(report["budget"]) == 60
            and int(report["top_k"]) == 25
            and int(summary["input_candidates"]) == int(report["input_candidates"])
            and "external/witnessenergysearch" in tool_text.lower()
            and "WES commit" in doc_text,
            "bounded WES candidate corpus and external source reference are stable",
        ),
        _expect_true(
            "wes_dominance_search.useful_ordering",
            int(summary["model_online_checked"]) == int(report["budget"])
            and int(summary["model_online_useful_at_k"]) >= 24
            and int(summary["declared_priority_useful_at_k"]) >= 24
            and int(summary["model_online_useful_at_k"])
            >= int(summary["random_seeded_useful_at_k"])
            and int(summary["model_online_calls_to_first_useful"]) == 1
            and int(summary["random_seeded_calls_to_first_useful"]) >= 1,
            "WES-ranked policies find useful dominance-cover checks early under the static budget",
        ),
        _expect_true(
            "wes_dominance_search.safety",
            int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["wes_ranks_only"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and int(summary["checker_invalid_accept_count"]) == 0,
            "WES ranks checker calls only and records zero invalid accepts",
        ),
        _expect_true(
            "wes_dominance_search.source_hooks",
            "compare_candidate_search_policies" in tool_text
            and "check_wes_dominance_candidate" in tool_text
            and "verify_candidates_in_order" in tool_text
            and "verify_upba_v2_dominance_cover_certificate" in tool_text
            and "test_wes_dominance_policy_comparison_smoke" in test_text
            and "bounded synthetic" in doc_lower
            and "checker order only" in doc_lower
            and "does not remove the full-list completeness obligation" in negative_lower
            and "not a upba v2 bounded-grid production verifier" in limits_lower,
            "bridge source, tests, and docs preserve WES as an advisory search layer",
        ),
    ]


def _check_dominance_prefix(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    source_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    summary = report["summary"]
    learned = summary["learned"]
    hybrid = summary["hybrid"]
    hand = summary["hand"]
    random = summary["random"]
    doc_lower = doc_text.lower()
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_true(
            "dominance_prefix.schema",
            report.get("schema")
            == "zenodex/energy/upba_v2_dominance_prefix_benchmark/v1"
            and report.get("audit_schema")
            == "zenodex/energy/upba_v2_prefix_dominance_cover_audit/v1"
            and bool(report.get("learned_model_present")) is True,
            "dominance-prefix benchmark and audit schemas are stable",
        ),
        _expect_true(
            "dominance_prefix.safety",
            int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False,
            "prefix audit preserves verifier authority and records zero invalid accepts",
        ),
        _expect_true(
            "dominance_prefix.learned_and_hybrid_cover_first",
            int(learned["count"]) > 0
            and int(learned["ok_count"]) == int(learned["count"])
            and int(hybrid["ok_count"]) == int(hybrid["count"])
            and int(learned["structural_verify_ok_count"]) == int(learned["count"])
            and int(hybrid["structural_verify_ok_count"]) == int(hybrid["count"])
            and float(learned["mean_prefix_checked_count"]) == 1.0
            and float(hybrid["mean_prefix_checked_count"]) == 1.0
            and float(learned["p99_prefix_checked_count"]) == 1.0
            and float(hybrid["p99_prefix_checked_count"]) == 1.0,
            "learned and hybrid prefixes obtain dominance-cover certificates at the first checked candidate",
        ),
        _expect_true(
            "dominance_prefix.beats_controls",
            float(learned["mean_prefix_checked_count"])
            < float(hand["mean_prefix_checked_count"])
            and float(learned["mean_prefix_checked_count"])
            < float(random["mean_prefix_checked_count"])
            and int(random["full_fallback_count"]) > 0
            and int(hand["max_prefix_checked_count"]) > int(learned["max_prefix_checked_count"]),
            "learned prefix cover beats hand and random controls on checked-call count",
        ),
        _expect_true(
            "dominance_prefix.boundary_and_hooks",
            "build_upba_v2_prefix_dominance_cover_audit" in source_text
            and "verify_upba_v2_prefix_dominance_cover_audit" in source_text
            and "PREFIX_DOMINANCE_COVER_SCHEMA" in source_text
            and "scorer_from_linear_model" in tool_text
            and "hard_barrier_energy_from_record" in tool_text
            and "test_prefix_dominance_cover_audit_waits_past_weak_candidate"
            in test_text
            and "offline audit" in doc_lower
            and "unchecked-suffix bound" in doc_lower
            and "no verifier-call savings" in negative_lower
            and "not a upba v2 bounded-grid optimality verifier" in limits_lower,
            "source, tests, and docs preserve offline-prefix and suffix-bound limits",
        ),
    ]


def _check_suffix_bound(
    report: dict[str, Any],
    doc_text: str,
    source_text: str,
    tool_text: str,
    test_text: str,
    lean_text: str,
) -> list[EvidenceCheck]:
    summary = report["summary"]
    learned = summary["learned"]
    hybrid = summary["hybrid"]
    hand = summary["hand"]
    random = summary["random"]
    doc_lower = doc_text.lower()
    limits_lower = " ".join(str(item).lower() for item in report.get("limits", []))
    return [
        _expect_true(
            "suffix_bound.schema",
            report.get("schema") == "zenodex/energy/upba_v2_suffix_bound_benchmark/v1"
            and report.get("certificate_schema")
            == "zenodex/energy/upba_v2_suffix_bound_certificate/v1"
            and bool(report.get("learned_model_present")) is True,
            "suffix-bound benchmark and certificate schemas are stable",
        ),
        _expect_true(
            "suffix_bound.safety",
            int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and bool(report["safety"]["deterministic_suffix_bound_required"]) is True,
            "suffix-bound early stop preserves verifier authority and records zero invalid accepts",
        ),
        _expect_true(
            "suffix_bound.learned_and_hybrid_stop_first",
            int(learned["count"]) > 0
            and int(learned["certificate_ok_count"]) == int(learned["count"])
            and int(hybrid["certificate_ok_count"]) == int(hybrid["count"])
            and int(learned["objective_equiv_accept_count"]) == int(learned["count"])
            and int(hybrid["objective_equiv_accept_count"]) == int(hybrid["count"])
            and float(learned["mean_verifier_calls"]) <= 1.01
            and float(hybrid["mean_verifier_calls"]) <= 1.01
            and float(learned["p99_verifier_calls"]) == 1.0
            and float(hybrid["p99_verifier_calls"]) == 1.0,
            "learned and hybrid suffix-bound certificates stop after roughly one verifier call",
        ),
        _expect_true(
            "suffix_bound.beats_controls",
            float(learned["mean_verifier_calls"]) < float(hand["mean_verifier_calls"])
            and float(learned["mean_verifier_calls"]) < float(random["mean_verifier_calls"])
            and int(random["full_fallback_count"]) > 0
            and float(learned["mean_checked_ratio"]) < 0.05
            and float(hand["mean_checked_ratio"]) < float(random["mean_checked_ratio"]),
            "learned suffix-bound early stop beats hand and random controls on verifier calls",
        ),
        _expect_true(
            "suffix_bound.boundary_and_hooks",
            "build_upba_v2_suffix_bound_certificate" in source_text
            and "verify_upba_v2_suffix_bound_certificate" in source_text
            and "candidate_objective_upper_bound" in source_text
            and "deterministic disqualifier" in source_text
            and "verify_upba_v2_suffix_bound_certificate" in tool_text
            and "test_suffix_bound_certificate_rejects_attractive_unchecked_candidate"
            in test_text
            and "suffix_upper_bound_checked_stop_implies_true_max_concat"
            in lean_text
            and "suffix_upper_bound_checked_stop_with_exact_coverage_implies_global"
            in lean_text
            and "deterministic early-stop certificate" in doc_lower
            and "candidate-family coverage" in doc_lower
            and "candidate-family coverage" in limits_lower,
            "source, tests, Lean theorem, and docs preserve deterministic suffix-bound limits",
        ),
    ]


def _check_suffix_bound_cross_seed(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    summary = report["summary"]
    learned = summary["learned"]
    hybrid = summary["hybrid"]
    hand = summary["hand"]
    random = summary["random"]
    doc_lower = doc_text.lower()
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    return [
        _expect_true(
            "suffix_bound_cross_seed.schema",
            report.get("schema") == "zenodex/energy/upba_v2_suffix_bound_cross_seed/v1"
            and bool(report.get("ok")) is True
            and int(report.get("batches_per_config")) == 60
            and list(report.get("seeds")) == [20260541, 20260542, 20260543]
            and list(report.get("candidate_counts")) == [20, 32, 50],
            "suffix-bound cross-seed stress schema and parameter grid are stable",
        ),
        _expect_true(
            "suffix_bound_cross_seed.safety",
            int(report["safety"]["invalid_accept_count_total"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and bool(report["safety"]["deterministic_suffix_bound_required"]) is True
            and int(learned["invalid_accept_count_total"]) == 0
            and int(hybrid["invalid_accept_count_total"]) == 0,
            "cross-seed suffix-bound stress has zero invalid accepts and keeps verifier authority",
        ),
        _expect_true(
            "suffix_bound_cross_seed.learned_and_hybrid_hold",
            int(learned["configs"]) == 9
            and int(hybrid["configs"]) == 9
            and float(learned["objective_equiv_accept_rate_min"]) == 1.0
            and float(hybrid["objective_equiv_accept_rate_min"]) == 1.0
            and float(learned["suffix_stop_rate_min"]) == 1.0
            and float(hybrid["suffix_stop_rate_min"]) == 1.0
            and float(learned["certificate_ok_rate_min"]) == 1.0
            and float(hybrid["certificate_ok_rate_min"]) == 1.0,
            "learned and hybrid keep complete objective-equivalent acceptance and suffix stops",
        ),
        _expect_true(
            "suffix_bound_cross_seed.beats_controls",
            float(learned["mean_verifier_calls_mean"])
            < float(hand["mean_verifier_calls_mean"])
            and float(hybrid["mean_verifier_calls_mean"])
            < float(hand["mean_verifier_calls_mean"])
            and float(learned["mean_verifier_calls_mean"])
            < float(random["mean_verifier_calls_mean"])
            and int(random["full_fallback_count_total"]) > 0
            and float(learned["p99_verifier_calls_max"]) <= 4.0,
            "learned and hybrid beat hand and random on verifier-call stress metrics",
        ),
        _expect_true(
            "suffix_bound_cross_seed.boundary_and_hooks",
            "stress_suffix_bound" in tool_text
            and "run_suffix_bound_benchmark" in tool_text
            and "synthetic_batches_requested" in tool_text
            and "test_suffix_bound_cross_seed_stress_smoke" in test_text
            and "bounded synthetic evidence" in doc_lower
            and "candidate-family coverage" in doc_lower
            and "does not prove candidate-family coverage" in negative_lower,
            "tool, test, and doc preserve bounded synthetic and coverage limits",
        ),
    ]


def _check_suffix_bound_adversarial(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    summary = report["summary"]
    doc_lower = doc_text.lower()
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    evaluated = int(summary["evaluated_batches"])
    return [
        _expect_true(
            "suffix_bound_adversarial.schema",
            report.get("schema")
            == "zenodex/energy/upba_v2_suffix_bound_adversarial_stress/v1"
            and bool(report.get("ok")) is True
            and int(report.get("batches")) == 120
            and int(report.get("candidates_per_batch")) == 24
            and int(report.get("seed")) == 20260544,
            "suffix-bound adversarial stress schema and parameters are stable",
        ),
        _expect_true(
            "suffix_bound_adversarial.safety",
            int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and bool(report["safety"]["deterministic_suffix_bound_required"]) is True,
            "adversarial suffix stress preserves verifier authority and zero invalid accepts",
        ),
        _expect_true(
            "suffix_bound_adversarial.disqualifier_closes",
            evaluated == 119
            and int(summary["adversary_invalid_count"]) == evaluated
            and int(summary["adversary_disqualified_count"]) == evaluated
            and int(summary["with_disqualifiers_certificate_ok_count"]) == evaluated
            and str(summary["disqualifier_histogram"].get("invariant_violation_flag"))
            == str(evaluated),
            "deterministic disqualifiers close every injected high-output suffix case",
        ),
        _expect_true(
            "suffix_bound_adversarial.declared_output_negative",
            int(summary["without_disqualifiers_certificate_ok_count"]) == 0
            and int(summary["declared_output_only_forced_fail_count"]) == evaluated
            and "declared-output suffix bounds alone fail" in negative_lower,
            "declared-output-only bounds fail on every injected adversarial suffix case",
        ),
        _expect_true(
            "suffix_bound_adversarial.boundary_and_hooks",
            "stress_adversarial_suffix_bound" in tool_text
            and "_mutate_declared_output_above_winner" in tool_text
            and "candidate_objective_upper_bound" in tool_text
            and "test_suffix_bound_adversarial_stress_smoke" in test_text
            and "high-declared-output invalid candidates" in doc_lower
            and "bounded synthetic evidence" in negative_lower,
            "tool, test, and doc preserve adversarial suffix and bounded synthetic limits",
        ),
    ]


def _check_suffix_bound_adversarial_families(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    summary = report["summary"]
    doc_lower = doc_text.lower()
    negative_lower = " ".join(
        str(item).lower() for item in report.get("negative_knowledge", [])
    )
    evaluated = int(summary["evaluated_batches"])
    total_cases = int(summary["total_cases"])
    required_families = set(summary["required_families"])
    family_counts = summary["family_case_counts"]
    histogram = summary["disqualifier_histogram"]
    required_disqualifiers = {
        "all_zero_fill_vector_flag",
        "fill_coverage_violation_flag",
        "invariant_violation_flag",
        "limit_violation_count",
        "negative_reserve_flag",
        "price_objective_violation_flag",
        "schema_policy_mismatch_flag",
    }
    return [
        _expect_true(
            "suffix_bound_adversarial_families.schema",
            report.get("schema")
            == "zenodex/energy/upba_v2_suffix_bound_adversarial_family_stress/v1"
            and bool(report.get("ok")) is True
            and int(report.get("batches")) == 120
            and int(report.get("candidates_per_batch")) == 24
            and int(report.get("seed")) == 20260545,
            "suffix-bound adversarial family stress schema and parameters are stable",
        ),
        _expect_true(
            "suffix_bound_adversarial_families.safety",
            int(report["safety"]["invalid_accept_count"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["scorer_authorizes_settlement"]) is False
            and bool(report["safety"]["model_output_in_state_root"]) is False
            and bool(report["safety"]["deterministic_suffix_bound_required"]) is True,
            "multi-family adversarial suffix stress preserves verifier authority",
        ),
        _expect_true(
            "suffix_bound_adversarial_families.family_coverage",
            evaluated == 118
            and int(summary["family_count"]) == 8
            and total_cases == 944
            and all(int(family_counts[family]) == evaluated for family in required_families)
            and int(summary["observed_disqualifier_count"]) >= 8,
            "eight adversarial families are represented across all evaluated batches",
        ),
        _expect_true(
            "suffix_bound_adversarial_families.disqualifiers_close",
            int(summary["adversary_invalid_count"]) == total_cases
            and int(summary["adversary_disqualified_count"]) == total_cases
            and int(summary["with_disqualifiers_certificate_ok_count"]) == total_cases
            and required_disqualifiers.issubset(set(histogram))
            and int(histogram["all_zero_fill_vector_flag"]) == evaluated
            and int(histogram["fill_coverage_violation_flag"]) == evaluated
            and int(histogram["price_objective_violation_flag"]) == evaluated
            and int(histogram["schema_policy_mismatch_flag"]) == evaluated,
            "deterministic disqualifiers close every multi-family adversarial suffix case",
        ),
        _expect_true(
            "suffix_bound_adversarial_families.declared_output_negative",
            int(summary["high_declared_output_forced_fail_count"])
            == int(summary["high_declared_output_cases"])
            and "high-declared-output suffix adversaries still force failure"
            in negative_lower,
            "declared-output-only bounds still fail on high-output family cases",
        ),
        _expect_true(
            "suffix_bound_adversarial_families.boundary_and_hooks",
            "stress_adversarial_suffix_bound_families" in tool_text
            and "_family_builders" in tool_text
            and "candidate_objective_upper_bound" in tool_text
            and "test_suffix_bound_adversarial_family_stress_smoke" in test_text
            and "several verifier-invalid suffix-candidate families" in doc_lower
            and "bounded synthetic evidence" in negative_lower
            and "not v2 bounded-grid completeness" in negative_lower,
            "tool, test, and doc preserve multi-family bounded synthetic limits",
        ),
    ]


def _check_negative_curriculum(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    weights = report["recommended_disqualifier_sample_weights"]
    proxy = report["bounded_epiplexity_proxy"]
    negative_text = " ".join(str(item) for item in report["negative_knowledge"]).lower()
    return [
        _expect_true(
            "negative_curriculum.schema",
            report.get("schema") == "zenodex/energy/negative_curriculum/v1"
            and bool(report.get("ok")) is True
            and report["source_schema"]
            == "zenodex/energy/upba_v2_suffix_bound_adversarial_family_stress/v1"
            and int(report["evaluated_batches"]) == 118
            and int(report["family_count"]) == 8
            and int(report["total_cases"]) == 944,
            "negative curriculum receipt is tied to the committed adversarial family stress",
        ),
        _expect_true(
            "negative_curriculum.weights",
            float(weights["output_mismatch_count"]) > 3.0
            and float(weights["invariant_violation_flag"]) == 1.0
            and int(report["disqualifier_histogram"]["output_mismatch_count"]) == 20,
            "rare output-mismatch disqualifiers receive the strongest curriculum weight",
        ),
        _expect_true(
            "negative_curriculum.epiplexity_proxy",
            proxy["schema"] == "zenodex/energy/bounded_epiplexity_proxy/v1"
            and proxy["classification"] == "measurable_bounded_structure"
            and float(proxy["score"]) > 0.0
            and float(proxy["policy_separation"]) == 0.375
            and "diagnostic proxy only" in str(proxy["boundary"]).lower(),
            "bounded epiplexity proxy reports measurable structure with a diagnostic-only boundary",
        ),
        _expect_true(
            "negative_curriculum.source_hooks",
            "bounded_epiplexity_proxy" in tool_text
            and "curriculum_weights" in tool_text
            and "julia executable is not available" in test_text
            and "Bounded Epiplexity Proxy" in doc_text
            and "LeCun" in doc_text,
            "Julia tool, test, and doc expose curriculum and academic hooks",
        ),
        _expect_true(
            "negative_curriculum.negative_knowledge",
            "steering signal" in negative_text
            and "correctness certificate" in negative_text
            and "real replay is still required" in negative_text,
            "negative knowledge preserves the boundary around epiplexity and synthetic hard negatives",
        ),
    ]


def _check_curriculum_ranker(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
    trainer_source: str,
) -> list[EvidenceCheck]:
    holdout_baseline = report["holdout"]["baseline"]
    holdout_curriculum = report["holdout"]["curriculum"]
    stress_baseline = report["stress"]["summary"]["baseline_learned"]
    stress_curriculum = report["stress"]["summary"]["curriculum_learned"]
    interpretation = report["interpretation"]
    return [
        _expect_true(
            "curriculum_ranker.schema",
            report.get("schema") == "zenodex/energy/upba_v2_curriculum_ranker_report/v1"
            and int(report["max_train_batches"]) == 1000
            and int(report["train_rows"]) < int(report["train_rows_available"])
            and report["curriculum"].endswith("zenoenergy_negative_curriculum_seed20260545.json"),
            "curriculum ranker receipt records bounded training scope and source curriculum",
        ),
        _expect_true(
            "curriculum_ranker.safety",
            int(stress_curriculum["invalid_accept_count_total"]) == 0
            and int(stress_curriculum["permutation_violation_count_total"]) == 0
            and float(stress_curriculum["top_10_recall_min"]) == 1.0
            and bool(interpretation["safety_clean"]) is True,
            "curriculum ranker preserves safety, permutation, and top-10 fallback evidence",
        ),
        _expect_true(
            "curriculum_ranker.negative_result",
            float(holdout_curriculum["mean_verifier_calls"])
            > float(holdout_baseline["mean_verifier_calls"])
            and float(stress_curriculum["mean_verifier_calls_mean"])
            > float(stress_baseline["mean_verifier_calls_mean"])
            and bool(interpretation["curriculum_improved_cross_seed_mean_calls"]) is False
            and interpretation["promotion_decision"] == "keep_default",
            "rare-disqualifier curriculum does not beat the gap-weighted default",
        ),
        _expect_true(
            "curriculum_ranker.source_hooks",
            "negative_curriculum_weights" in trainer_source
            and "load_negative_curriculum_weights" in trainer_source
            and "max-train-batches" in tool_text
            and "test_curriculum_ranker_receipt_records_negative_result" in test_text,
            "trainer, benchmark, and test expose curriculum weighting and bounded scope",
        ),
        _expect_true(
            "curriculum_ranker.doc_boundary",
            "did not beat the gap-weighted default" in doc_text
            and "promotion_decision: keep_default" in doc_text,
            "doc records the negative result and keeps the default ranker",
        ),
    ]


def _check_data_scaling(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    runs = report["runs"]
    first = runs[0]["metrics"]
    last = runs[-1]["metrics"]
    baseline = report["baselines"]["current_gap_weighted"]
    interpretation = report["interpretation"]
    return [
        _expect_true(
            "data_scaling.schema",
            report.get("schema") == "zenodex/energy/upba_v2_data_scaling_report/v1"
            and int(report["available_train_batches"]) == 10000
            and int(report["available_train_rows"]) == 199860
            and int(report["holdout_rows"]) == 39979
            and len(runs) == 8,
            "data-scaling receipt records the committed synthetic corpus and eight budgets",
        ),
        _expect_true(
            "data_scaling.safety",
            int(report["safety"]["invalid_accept_count_total"]) == 0
            and all(int(row["metrics"]["invalid_accept_count"]) == 0 for row in runs)
            and bool(report["safety"]["verifier_authoritative"]) is True,
            "all scaling budgets preserve zero invalid accepts and verifier authority",
        ),
        _expect_true(
            "data_scaling.quantity_curve",
            float(last["mean_verifier_calls"]) < float(first["mean_verifier_calls"])
            and float(last["top_1_recall"]) > float(first["top_1_recall"])
            and float(last["top_10_recall"]) == 1.0,
            "more same-generator rows improve from the smallest budget",
        ),
        _expect_true(
            "data_scaling.saturates_below_current",
            float(last["mean_verifier_calls"]) >= float(baseline["mean_verifier_calls"])
            and bool(interpretation["best_budget_beats_current_gap_weighted"]) is False
            and bool(interpretation["best_budget_matches_current_gap_weighted_top10"]) is True,
            "full same-generator scaling does not beat the current gap-weighted checkpoint",
        ),
        _expect_true(
            "data_scaling.source_hooks",
            "upba_v2_data_scaling_report/v1" in tool_text
            and "raw volume alone" in test_text
            and "raw volume alone" in doc_text
            and "Repeating the same" in doc_text,
            "tool, test, and doc expose the raw-volume saturation boundary",
        ),
    ]


def _check_best_model_registry(
    root: Path,
    registry: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    models = registry["models"]
    by_id = {str(model["model_id"]): model for model in models}
    upba = by_id.get("gemini_mlp_v6_seed20260519", {})
    upba_linear = by_id.get("gemini_highwinner_seed20260517", {})
    upba_baseline = by_id.get("upba_v2_gap_weighted_default_seed20260517", {})
    autotrader = [
        model
        for model in models
        if model.get("domain") == "autotrader_policy_guard_ordering"
    ]
    expected_autotrader_ids = {
        "autotrader_hard_train20260522_holdout20260523",
        "autotrader_hard_train20260524_holdout20260525",
        "autotrader_hard_train20260526_holdout20260527",
    }
    files_ok = True
    for model in models:
        retained = root / str(model["retained_path"])
        if not retained.exists() or _sha256_file(retained) != model.get("sha256"):
            files_ok = False
            continue
        try:
            payload = _load_json(retained)
        except Exception:
            files_ok = False
            continue
        if payload.get("schema") != model.get("schema"):
            files_ok = False
        if _retained_model_parameter_count(payload) != int(model["parameter_count"]):
            files_ok = False
        if len(payload.get("feature_names", [])) != int(model["feature_dim"]):
            files_ok = False
    return [
        _expect_true(
            "best_model_registry.schema_and_promoted",
            registry.get("schema") == "zenodex/energy/best_model_registry/v1"
            and registry.get("scope") == "advisory_ranking_only"
            and registry["promoted"]["upba_v2"]
            == "gemini_mlp_v6_seed20260519"
            and registry["promoted"]["autotrader_hard_synthetic_best_seed_pair"]
            == "autotrader_hard_train20260526_holdout20260527"
            and set(by_id) == {
                "gemini_mlp_v6_seed20260519",
                "gemini_highwinner_seed20260517",
                "upba_v2_gap_weighted_default_seed20260517",
                *expected_autotrader_ids,
            },
            "best-model registry records the promoted advisory research defaults",
        ),
        _expect_true(
            "best_model_registry.files_and_hashes",
            files_ok,
            "all retained model files exist, match sha256, and match declared schema/dimensions",
        ),
        _expect_true(
            "best_model_registry.upba_default",
            int(upba.get("parameter_count", 0)) == 6273
            and bool(upba["metrics"]["promotion_allowed"]) is True
            and int(upba["metrics"]["holdout_invalid_accept_count"]) == 0
            and int(upba["metrics"]["cross_seed_invalid_accept_count_total"]) == 0
            and int(upba["metrics"]["cross_seed_permutation_violation_count_total"]) == 0
            and float(upba["metrics"]["holdout_top_1_recall"]) > 0.997
            and float(upba["metrics"]["cross_seed_top_1_recall_min"]) >= 0.983
            and float(upba["metrics"]["cross_seed_top_10_recall_min"]) == 1.0
            and float(upba["metrics"]["hard_case_top_1_recall"]) > 0.993
            and int(upba["metrics"]["hard_case_top10_miss_count"]) == 0
            and upba.get("supersedes") == "gemini_highwinner_seed20260517"
            and upba_linear.get("superseded_by") == "gemini_mlp_v6_seed20260519"
            and upba_baseline.get("superseded_by") == "gemini_mlp_v6_seed20260519",
            "retained UPBA model is the promoted v6 MLP checkpoint and keeps the old linear baselines",
        ),
        _expect_true(
            "best_model_registry.autotrader_retained",
            len(autotrader) == 3
            and {str(model["model_id"]) for model in autotrader}
            == expected_autotrader_ids
            and all(int(model["parameter_count"]) == 21 for model in autotrader)
            and all(int(model["metrics"]["invalid_accept_count"]) == 0 for model in autotrader)
            and all(float(model["metrics"]["top_5_recall"]) == 1.0 for model in autotrader)
            and min(float(model["metrics"]["mean_guard_calls"]) for model in autotrader)
            == 1.008,
            "all three AutoTrader hard synthetic cross-seed models are retained",
        ),
        _expect_true(
            "best_model_registry.advisory_boundary",
            bool(registry["safety_contract"]["model_authorizes_settlement"]) is False
            and bool(registry["safety_contract"]["model_authorizes_trade"]) is False
            and bool(registry["safety_contract"]["state_root_dependency"]) is False
            and "zenodex/energy/best_model_registry/v1" in tool_text
            and "test_best_model_registry_pins_current_models" in test_text
            and "Deterministic UPBA verification" in doc_text,
            "registry, docs, test, and tool keep retained models advisory only",
        ),
    ]


def _check_upba_v2_model_leaderboard(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    rows = {str(row["model_id"]): row for row in report["models"]}
    promoted = rows.get("gemini_mlp_v6_seed20260519", {})
    highwinner = rows.get("gemini_highwinner_seed20260517", {})
    gap = rows.get("upba_v2_gap_weighted_default_seed20260517", {})
    objective8 = rows.get("gemini_objective8_seed20260517", {})
    handinit = rows.get("gemini_handinit_seed20260517", {})
    obligation_ids = {str(item["id"]) for item in report["obligations"]}
    required_obligations = {
        "holdout_best_mean_calls",
        "holdout_best_top1",
        "cross_seed_best_mean_calls",
        "cross_seed_best_worst_top1",
        "hard_case_best_top1",
        "hard_case_fewest_top1_misses",
        "safety_counts_clean",
    }
    full_rows = [
        row for row in report["models"] if row["coverage"]["full_three_lane"]
    ]
    return [
        _expect_true(
            "upba_v2_model_leaderboard.schema_and_decision",
            report.get("schema") == "zenodex/energy/upba_v2_model_leaderboard/v1"
            and report.get("scope") == "advisory_ranking_only"
            and report.get("decision") == "promote_v6_research_candidate"
            and report.get("promoted_model_id") == "gemini_mlp_v6_seed20260519"
            and int(report["compared_model_count"]) == 7
            and int(report["full_three_lane_model_count"]) == 6
            and report.get("blocked_reasons") == [],
            "leaderboard promotes the v6 MLP advisory UPBA v2 ranker",
        ),
        _expect_true(
            "upba_v2_model_leaderboard.obligations",
            required_obligations == obligation_ids
            and all(bool(item["passed"]) is True for item in report["obligations"]),
            "all highwinner promotion obligations pass",
        ),
        _expect_true(
            "upba_v2_model_leaderboard.metric_dominance",
            float(promoted["metrics"]["holdout"]["mean_verifier_calls"])
            < float(highwinner["metrics"]["holdout"]["mean_verifier_calls"])
            and float(promoted["metrics"]["holdout"]["mean_verifier_calls"])
            < float(gap["metrics"]["holdout"]["mean_verifier_calls"])
            and float(promoted["metrics"]["holdout"]["mean_verifier_calls"])
            < float(objective8["metrics"]["holdout"]["mean_verifier_calls"])
            and float(promoted["metrics"]["holdout"]["mean_verifier_calls"])
            < float(handinit["metrics"]["holdout"]["mean_verifier_calls"])
            and float(promoted["metrics"]["cross_seed"]["top_1_recall_min"])
            > float(gap["metrics"]["cross_seed"]["top_1_recall_min"])
            and float(promoted["metrics"]["cross_seed"]["mean_verifier_calls_mean"])
            < float(highwinner["metrics"]["cross_seed"]["mean_verifier_calls_mean"])
            and int(promoted["metrics"]["hard_cases"]["top1_miss_count"])
            < int(highwinner["metrics"]["hard_cases"]["top1_miss_count"])
            and int(promoted["metrics"]["hard_cases"]["top1_miss_count"])
            < int(gap["metrics"]["hard_cases"]["top1_miss_count"]),
            "v6 beats the retained linear checkpoints on selected verifier-facing metrics",
        ),
        _expect_true(
            "upba_v2_model_leaderboard.safety_boundary",
            len(full_rows) == 6
            and int(promoted["metrics"]["holdout"]["invalid_accept_count"]) == 0
            and int(
                promoted["metrics"]["cross_seed"]["invalid_accept_count_total"]
            )
            == 0
            and int(
                promoted["metrics"]["cross_seed"][
                    "permutation_violation_count_total"
                ]
            )
            == 0
            and "advisory rankers only" in doc_text
            and "does not authorize settlement" in doc_text,
            "leaderboard keeps safety as verifier-authoritative and advisory only",
        ),
        _expect_true(
            "upba_v2_model_leaderboard.source_hooks",
            "upba_v2_model_leaderboard/v1" in tool_text
            and "test_highwinner_leads_comparable_upba_energy_leaderboard"
            in test_text
            and "gemini_mlp_v6_seed20260519" in doc_text
            and "gemini_highwinner_seed20260517" in doc_text
            and "gemini_handinit_seed20260517" in doc_text,
            "tool, test, and doc pin the comparable model set",
        ),
    ]


def _retained_model_parameter_count(payload: dict[str, Any]) -> int:
    if payload.get("schema") == "zenodex/energy/gemini_mlp/v1":
        return (
            sum(len(row) for row in payload["w1"])
            + len(payload["b1"])
            + len(payload["w2"])
            + 1
        )
    return len(payload.get("weights", [])) + 1


def _check_quality_selection(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    raw = report["runs"]["raw_winner_bearing"]
    quality = report["runs"]["quality_hard_winner_bearing"]
    interpretation = report["interpretation"]
    return [
        _expect_true(
            "quality_selection.schema",
            report.get("schema") == "zenodex/energy/upba_v2_quality_selection_report/v1"
            and int(report["available_train_batches"]) == 10000
            and int(report["winner_bearing_train_batches"]) == 9916
            and int(report["selection"]["excluded_no_winner_train_batches"]) == 84
            and len(raw) == 6
            and len(quality) == 6,
            "quality-selection receipt records winner-bearing filtering and six budgets",
        ),
        _expect_true(
            "quality_selection.safety",
            int(report["safety"]["invalid_accept_count_total"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["model_authorizes_settlement"]) is False
            and all(int(run["metrics"]["invalid_accept_count"]) == 0 for run in raw)
            and all(int(run["metrics"]["invalid_accept_count"]) == 0 for run in quality),
            "all quality-selection policies preserve verifier authority and zero invalid accepts",
        ),
        _expect_true(
            "quality_selection.medium_budget_gain",
            int(interpretation["quality_beats_raw_budget_count"]) == 4
            and float(quality[1]["metrics"]["mean_verifier_calls"])
            < float(raw[1]["metrics"]["mean_verifier_calls"])
            and float(quality[3]["metrics"]["mean_verifier_calls"])
            < float(raw[3]["metrics"]["mean_verifier_calls"]),
            "quality selection improves medium-budget mean verifier calls over raw winner-bearing samples",
        ),
        _expect_true(
            "quality_selection.small_budget_negative",
            int(interpretation["quality_worse_than_raw_budget_count"]) == 1
            and float(quality[0]["metrics"]["mean_verifier_calls"])
            > float(raw[0]["metrics"]["mean_verifier_calls"])
            and "hard-only quality budgets" in interpretation["negative_knowledge"],
            "small hard-only quality budget can overfocus on current-model misses",
        ),
        _expect_true(
            "quality_selection.source_hooks",
            "quality_hard_winner_bearing" in tool_text
            and "test_quality_selection_receipt_records_quality_tradeoff" in test_text
            and "quality better?" in doc_text
            and "winner-bearing" in doc_text,
            "tool, test, and doc expose the quality-selection boundary",
        ),
    ]


def _check_ensemble(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    module_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    modes = report["modes"]
    baseline = report["baselines"]["current_gap_weighted"]
    interpretation = report["interpretation"]
    uncertainty = report["uncertainty"]
    best_auc = float(interpretation["best_uncertainty_auc"])
    return [
        _expect_true(
            "ensemble.schema",
            report.get("schema") == "zenodex/energy/upba_v2_ensemble_report/v1"
            and int(report["ensemble"]["member_count"]) == 6
            and int(report["ensemble"]["total_parameter_count"]) == 582
            and len(modes) == 6,
            "ensemble receipt records six tiny advisory members and six aggregation modes",
        ),
        _expect_true(
            "ensemble.safety",
            int(report["safety"]["invalid_accept_count_total"]) == 0
            and bool(report["safety"]["verifier_authoritative"]) is True
            and bool(report["safety"]["model_authorizes_settlement"]) is False
            and bool(report["safety"]["deterministic_fallback_required"]) is True
            and all(int(mode["invalid_accept_count"]) == 0 for mode in modes.values()),
            "ensemble preserves verifier authority, deterministic fallback, and zero invalid accepts",
        ),
        _expect_true(
            "ensemble.top10_and_default_negative",
            all(float(mode["top_10_recall"]) == 1.0 for mode in modes.values())
            and bool(interpretation["best_ensemble_beats_current_gap_weighted"]) is False
            and float(baseline["mean_verifier_calls"])
            < float(interpretation["best_ensemble_mean_verifier_calls"])
            and "keep the single retained UPBA model" in interpretation["negative_knowledge"],
            "ensemble keeps top-10 recall but does not beat the current gap-weighted default",
        ),
        _expect_true(
            "ensemble.uncertainty_signal",
            best_auc > 0.6
            and float(uncertainty["ensemble_mean_rank"]["top1_uncertainty_miss_mean"])
            > float(uncertainty["ensemble_mean_rank"]["top1_uncertainty_hit_mean"]),
            "rank disagreement has moderate signal for top-1 misses",
        ),
        _expect_true(
            "ensemble.source_hooks",
            "LinearEnergyEnsemble" in module_text
            and "ensemble_rank_std_penalty" in tool_text
            and "test_ensemble_report_records_negative_default_decision" in test_text
            and "Deterministic UPBA verification and fallback remain the authority" in doc_text,
            "module, benchmark, tests, and docs expose the ensemble advisory boundary",
        ),
    ]


def _check_epiplexity_literature(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    check_ids = {str(item["check_id"]) for item in report["checks"]}
    doc_lower = doc_text.lower()
    negative_text = " ".join(str(item) for item in report["negative_knowledge"]).lower()
    required_sources = report["required_source_urls"]
    return [
        _expect_true(
            "epiplexity_literature.schema",
            report.get("schema") == "zenodex/energy/epiplexity_literature_receipt/v1"
            and bool(report.get("ok")) is True
            and int(report["source_count"]) == 6
            and int(report["passed_count"]) == 7
            and int(report["failed_count"]) == 0,
            "epiplexity literature receipt schema and counts are stable",
        ),
        _expect_true(
            "epiplexity_literature.sources",
            all(str(url).startswith("https://arxiv.org/abs/") for url in required_sources.values())
            and "https://arxiv.org/abs/2601.03220" in required_sources.values()
            and "https://arxiv.org/abs/2605.11554" in required_sources.values()
            and "https://arxiv.org/abs/2602.05463" in required_sources.values(),
            "primary epiplexity, proxy counterexample, and companion sources are recorded",
        ),
        _expect_true(
            "epiplexity_literature.task_relevance_gate",
            "mapping.task_relevance_gate" in check_ids
            and "task_metric_improves" in doc_text
            and "mean verifier calls" in doc_lower
            and "top-k" in doc_lower
            and "invalid accepts" in doc_lower,
            "literature note requires task-specific heldout ranking metrics",
        ),
        _expect_true(
            "epiplexity_literature.proxy_boundary",
            "mapping.proxy_boundary" in check_ids
            and "epiplexity_proxy -/-> correctness_certificate" in doc_text
            and "epiplexity_proxy -/-> production_readiness" in doc_text
            and "not a correctness certificate" in negative_text,
            "literature note rejects proxy-as-certificate and proxy-as-production evidence",
        ),
        _expect_true(
            "epiplexity_literature.source_hooks",
            "REQUIRED_SOURCE_URLS" in tool_text
            and "check_epiplexity_literature" in tool_text
            and "test_epiplexity_literature_note_preserves_task_boundary" in test_text
            and report["decision"] == "use_epiplexity_for_training_data_selection_only",
            "checker and test enforce the data-selection-only decision",
        ),
    ]


def _check_synthetic_data_limits(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    check_ids = {str(item["check_id"]) for item in report["checks"]}
    doc_lower = doc_text.lower()
    negative_text = " ".join(str(item) for item in report["negative_knowledge"]).lower()
    required_sources = report["required_source_urls"]
    return [
        _expect_true(
            "synthetic_data_limits.schema",
            report.get("schema") == "zenodex/energy/synthetic_data_limits_receipt/v1"
            and bool(report.get("ok")) is True
            and int(report["source_count"]) == 8
            and int(report["passed_count"]) == 6
            and int(report["failed_count"]) == 0,
            "synthetic-data limits receipt schema and counts are stable",
        ),
        _expect_true(
            "synthetic_data_limits.sources",
            "https://www.nature.com/articles/s41586-024-07566-y"
            in required_sources.values()
            and "https://arxiv.org/abs/2305.17493" in required_sources.values()
            and "https://arxiv.org/abs/2404.01413" in required_sources.values()
            and "https://arxiv.org/abs/1703.06907" in required_sources.values(),
            "model-collapse, accumulation, and simulation-transfer sources are recorded",
        ),
        _expect_true(
            "synthetic_data_limits.verifier_label_boundary",
            "boundary.verifier_labels" in check_ids
            and "model outputs as authoritative labels" in doc_lower
            and "VerifierLabel(ctx, candidate)" in doc_text,
            "note requires verifier or policy labels instead of self-labels",
        ),
        _expect_true(
            "synthetic_data_limits.replay_boundary",
            "boundary.no_real_replay_replacement" in check_ids
            and "do not replace real replay" in doc_lower
            and "real_upba_replay_report_ok" in doc_text
            and "coverage_profile_ok" in doc_text,
            "note keeps real replay and coverage profiles as production-gate requirements",
        ),
        _expect_true(
            "synthetic_data_limits.source_hooks",
            "REQUIRED_SOURCE_URLS" in tool_text
            and "check_synthetic_data_limits" in tool_text
            and "test_synthetic_data_limits_note_preserves_replay_boundary" in test_text
            and report["decision"] == "synthetic_data_research_only_until_real_replay_gate"
            and "not production distribution evidence" in negative_text,
            "checker and test enforce research-only synthetic-data limits",
        ),
    ]


def _check_langevin_discovery(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    negative_text = " ".join(str(item) for item in report["negative_knowledge"]).lower()
    return [
        _expect_true(
            "langevin_discovery.schema",
            report.get("schema")
            == "zenodex/energy/gemini_langevin_discovery_receipt/v1"
            and bool(report.get("ok")) is True
            and int(report["candidate_count"]) == 32,
            "Langevin discovery receipt schema and deterministic seed are stable",
        ),
        _expect_true(
            "langevin_discovery.verifier_selection",
            bool(report["seed_verifier_ok"]) is True
            and bool(report["selected_verifier_ok"]) is True
            and bool(report["accepted_refinement"]) is False
            and bool(report["fallback_to_seed"]) is True,
            "invalid lower-energy refinement falls back to a verifier-backed seed",
        ),
        _expect_true(
            "langevin_discovery.energy_is_not_safety",
            float(report["energy_delta"]) < 0.0
            and bool(report["refined_verifier_ok"]) is False
            and "lower learned energy does not imply verifier acceptance" in negative_text
            and "ZenoGuard is an advisory soft prior" in doc_text,
            "lower energy and ZenoGuard are not treated as safety proof",
        ),
        _expect_true(
            "langevin_discovery.source_hooks",
            "research_only_verifier_checked_proposal" in tool_text
            and "discover_verified" in tool_text
            and "test_langevin_discovery_is_verifier_checked_before_selection"
            in test_text,
            "tool and test enforce verifier-backed Langevin selection",
        ),
    ]


def _check_autotrader_refiner_boundary(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    negative_text = " ".join(str(item) for item in report["negative_knowledge"]).lower()
    return [
        _expect_true(
            "autotrader_refiner_boundary.schema",
            report.get("schema")
            == "zenodex/energy/autotrader_refiner_boundary_receipt/v1"
            and bool(report.get("ok")) is True
            and int(report["evaluated_contexts"]) == 160,
            "AutoTrader refiner boundary receipt schema and deterministic seed are stable",
        ),
        _expect_true(
            "autotrader_refiner_boundary.policy_selection",
            int(report["selected_invalid_count"]) == 0
            and bool(report["policy_guards_authoritative"]) is True
            and bool(report["model_authorizes_trade"]) is False
            and bool(report["refined_proposal_authorizes_trade"]) is False,
            "refined AutoTrader proposals are selected only through policy labels",
        ),
        _expect_true(
            "autotrader_refiner_boundary.synthetic_gain",
            float(report["selected_vs_initial_objective_delta_mean"]) > 0.0
            and float(report["selected_vs_initial_energy_delta_mean"]) < 0.0
            and int(report["accepted_refinement_count"]) > 0,
            "bounded synthetic refiner improves selected objective while lowering advisory energy",
        ),
        _expect_true(
            "autotrader_refiner_boundary.source_hooks",
            "research_only_policy_checked_refinement" in tool_text
            and "refine_trade_checked" in tool_text
            and "test_autotrader_refiner_is_policy_checked_before_selection" in test_text
            and "deterministic policy labels decide selection" in negative_text
            and "AutoTrader refinement is proposal search" in doc_text,
            "tool, doc, and test preserve policy-gated refinement boundary",
        ),
    ]


def _check_jepa_logic_boundary(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
) -> list[EvidenceCheck]:
    negative_text = " ".join(str(item) for item in report["negative_knowledge"]).lower()
    safety = report["safety_contract"]
    jepa = report["jepa"]
    logic = report["zeno_logic"]
    return [
        _expect_true(
            "jepa_logic_boundary.schema",
            report.get("schema")
            == "zenodex/energy/gemini_jepa_logic_boundary_receipt/v1"
            and bool(report.get("ok")) is True
            and report["decision"] == "research_only_future_aware_advisory_score",
            "JEPA/ZenoLogic boundary receipt schema and decision are stable",
        ),
        _expect_true(
            "jepa_logic_boundary.future_score_advisory",
            bool(jepa["future_tension_prefers_balanced"]) is True
            and float(jepa["balanced_action_tension"]) < float(jepa["draining_action_tension"])
            and bool(jepa["model_authorizes_settlement"]) is False,
            "future-tension score ranks proposals but does not authorize settlement",
        ),
        _expect_true(
            "jepa_logic_boundary.logic_negation_warning",
            bool(logic["energy_not_inverts_barrier"]) is True
            and "EnergyNot can invert hard barriers" in doc_text
            and "must not be used over safety predicates" in negative_text,
            "ZenoLogic records the hard-barrier inversion hazard",
        ),
        _expect_true(
            "jepa_logic_boundary.safety_contract",
            bool(safety["deterministic_verifier_authoritative"]) is True
            and bool(safety["deterministic_policy_guards_authoritative"]) is True
            and bool(safety["model_authorizes_settlement"]) is False
            and bool(safety["future_tension_authorizes_settlement"]) is False
            and bool(safety["logic_expression_authorizes_settlement"]) is False,
            "JEPA and ZenoLogic remain advisory scoring surfaces",
        ),
        _expect_true(
            "jepa_logic_boundary.source_hooks",
            "check_gemini_jepa_logic_boundary" in tool_text
            and "ZenoJepaModel" in tool_text
            and "test_jepa_logic_boundary_is_advisory_only" in test_text
            and "advisory scoring surfaces" in doc_text,
            "tool, doc, and test preserve JEPA/ZenoLogic boundary",
        ),
    ]


def _check_autotrader_jepa_ux(
    report: dict[str, Any],
    doc_text: str,
    tool_text: str,
    test_text: str,
    source_text: str,
) -> list[EvidenceCheck]:
    negative_text = " ".join(str(item) for item in report["negative_knowledge"]).lower()
    scenario = report["scenario_scores"]
    future_eval = report["future_aware_evaluation"]
    ranking = report["ranking"]
    safety = report["safety_contract"]
    ux = report["ux"]
    prediction = report["future_risk_prediction"]
    controls = report["control_metrics"]
    warnings = report["warning_metrics"]
    research_inputs = report["research_inputs"]
    efficiency = report["efficiency"]
    correlations = prediction["stress_correlations"]
    return [
        _expect_true(
            "autotrader_jepa_ux.schema",
            report.get("schema")
            == "zenodex/energy/autotrader_jepa_ux_receipt/v1"
            and bool(report.get("ok")) is True
            and report["decision"] == "research_only_future_aware_autotrader_ux",
            "source-level AutoTrader JEPA UX receipt schema and decision are stable",
        ),
        _expect_true(
            "autotrader_jepa_ux.future_tension",
            bool(scenario["future_tension_differentiates_fragility"]) is True
            and float(scenario["fragile_future_tension"])
            > float(scenario["balanced_future_tension"]),
            "future tension distinguishes fragile and balanced proposal scenarios",
        ),
        _expect_true(
            "autotrader_jepa_ux.future_policy_prediction",
            float(prediction["later_policy_failure_auc"]) >= 0.80
            and float(prediction["future_failure_tension_delta_mean"]) > 0.25
            and int(prediction["later_policy_failure_count"]) > 0
            and bool(prediction["model_authorizes_trade"]) is False,
            "future tension separates later policy failures from non-failures",
        ),
        _expect_true(
            "autotrader_jepa_ux.stress_correlations",
            float(correlations["slippage_stress"]) >= 0.55
            and float(correlations["budget_stress"]) >= 0.55
            and float(correlations["drawdown_stress"]) >= 0.55,
            "future tension correlates with slippage, budget, and drawdown stress",
        ),
        _expect_true(
            "autotrader_jepa_ux.counterfactual_controls",
            float(controls["safer_counterfactual_reduction_rate"]) >= 0.95
            and float(controls["suggested_control_best_reduction_rate"]) >= 0.95
            and bool(controls["suggested_control_authority_ok"]) is True
            and bool(controls["model_authorizes_trade"]) is False,
            "safer counterfactual controls and suggested controls reduce future tension",
        ),
        _expect_true(
            "autotrader_jepa_ux.warning_match",
            float(warnings["blocked_status_match_rate"]) == 1.0
            and float(warnings["future_warning_match_rate"]) >= 0.80
            and int(warnings["ux_card_authorizes_trade_count"]) == 0,
            "UX warnings match deterministic guard outcomes and later-risk positives",
        ),
        _expect_true(
            "autotrader_jepa_ux.policy_boundary",
            int(future_eval["invalid_accept_count"]) == 0
            and bool(future_eval["policy_guards_authoritative"]) is True
            and bool(safety["model_authorizes_trade"]) is False
            and bool(safety["future_tension_authorizes_trade"]) is False
            and bool(safety["ux_card_authorizes_trade"]) is False,
            "future-aware UX keeps deterministic policy guards authoritative",
        ),
        _expect_true(
            "autotrader_jepa_ux.ranking_quality",
            future_eval["mode"] == "learned_future_aware"
            and float(ranking["learned_future_top_5_recall"]) >= 0.99
            and float(ranking["learned_future_mean_guard_calls"]) <= 1.10
            and bool(ranking["ranking_guardrail_passed"]) is True,
            "learned+JEPA ranking remains a guardrail with high top-k recall",
        ),
        _expect_true(
            "autotrader_jepa_ux.ux_explanations",
            bool(ux["ux_explains_status_and_controls"]) is True
            and ux["blocked_card"]["status"] == "blocked_by_policy_guard"
            and "stale signal or quote" in ux["blocked_card"]["blocked_reasons"]
            and ux["fragile_card"]["status"]
            in {"needs_risk_review", "policy_valid_with_caution"}
            and any(
                float(effect["future_tension_delta"]) < 0.0
                for effect in ux["fragile_card"]["control_effects"]
            )
            and "warning and proposal-shaping feature" in negative_text,
            "UX cards explain blocked states, future risk, and controls",
        ),
        _expect_true(
            "autotrader_jepa_ux.research_inputs",
            bool(research_inputs["ok"]) is True
            and "experiments_ideas" in research_inputs["artifacts"]
            and "experiments_breakthroughs" in research_inputs["artifacts"]
            and set(research_inputs["artifacts"])
            == {"experiments_ideas", "experiments_breakthroughs"}
            and int(efficiency["parameter_count"]) == 68
            and bool(efficiency["ok"]) is True,
            "ideas, breakthroughs, and a small JEPA profile are linked",
        ),
        _expect_true(
            "autotrader_jepa_ux.source_hooks",
            "check_zenoenergy_autotrader_jepa_ux" in tool_text
            and "build_autotrader_advisory_card" in source_text
            and "default_autotrader_jepa_model" in source_text
            and "project_autotrader_future_stress" in source_text
            and "autotrader_control_effect" in source_text
            and "test_autotrader_jepa_ux_receipt_preserves_authority_boundary"
            in test_text
            and "test_autotrader_future_stress_tracks_later_policy_failures"
            in test_text
            and "deterministic policy guards remain authoritative" in doc_text,
            "tool, source, doc, and tests preserve the source-level JEPA UX boundary",
        ),
    ]


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
    replay_source_manifest = payloads["replay_source_manifest"]
    replay_source_manifest_builder = payloads["replay_source_manifest_builder"]
    replay_secret_scan = payloads["replay_secret_scan"]
    replay_coverage_profile = payloads["replay_coverage_profile"]
    real_replay_builder = payloads["real_replay_report_builder"]
    production_evidence_bundle = payloads["production_evidence_bundle"]
    sota_decision_map = payloads["sota_decision_map"]
    autotrader = payloads["autotrader_energy_hard_cross_seed"]
    autotrader_aggregate = autotrader["aggregate"]
    autotrader_shadow = payloads["autotrader_energy_shadow_bridge"]
    dominance_cover = payloads["dominance_cover"]
    wes_dominance_search = payloads["wes_dominance_search"]
    dominance_prefix = payloads["dominance_prefix"]
    suffix_bound = payloads["suffix_bound"]
    suffix_bound_cross_seed = payloads["suffix_bound_cross_seed"]
    suffix_bound_adversarial = payloads["suffix_bound_adversarial"]
    suffix_bound_adversarial_families = payloads[
        "suffix_bound_adversarial_families"
    ]
    negative_curriculum = payloads["negative_curriculum"]
    curriculum_ranker = payloads["curriculum_ranker"]
    data_scaling = payloads["data_scaling"]
    quality_selection = payloads["quality_selection"]
    ensemble = payloads["ensemble"]
    best_model_registry = payloads["best_model_registry"]
    upba_v2_model_leaderboard = payloads["upba_v2_model_leaderboard"]
    energy_order_alone_formal = payloads["energy_order_alone_formal"]
    epiplexity_literature = payloads["epiplexity_literature"]
    synthetic_data_limits = payloads["synthetic_data_limits"]
    langevin_discovery = payloads["langevin_discovery"]
    autotrader_refiner_boundary = payloads["autotrader_refiner_boundary"]
    jepa_logic_boundary = payloads["jepa_logic_boundary"]
    autotrader_jepa_ux = payloads["autotrader_jepa_ux"]
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
        "energy_order_alone_formal": {
            "schema": energy_order_alone_formal["schema"],
            "formal_target": energy_order_alone_formal["formal_target"],
            "formal_names": energy_order_alone_formal["formal_names"],
            "claim": energy_order_alone_formal["claim"],
            "negative_knowledge": energy_order_alone_formal["negative_knowledge"],
        },
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
        "replay_source_manifest": {
            "source_manifest_schema": replay_source_manifest[
                "source_manifest_schema"
            ],
            "source_manifest_check_schema": replay_source_manifest[
                "source_manifest_check_schema"
            ],
            "supported_status": replay_source_manifest["supported_status"],
            "negative_knowledge": replay_source_manifest["negative_knowledge"],
            "claim": replay_source_manifest["claim"],
        },
        "replay_source_manifest_builder": {
            "builder_schema": replay_source_manifest_builder["builder_schema"],
            "output_schema": replay_source_manifest_builder["output_schema"],
            "check_schema": replay_source_manifest_builder["check_schema"],
            "negative_knowledge": replay_source_manifest_builder["negative_knowledge"],
            "claim": replay_source_manifest_builder["claim"],
        },
        "replay_secret_scan": {
            "secret_scan_schema": replay_secret_scan["secret_scan_schema"],
            "scanner_rules": replay_secret_scan["scanner_rules"],
            "negative_knowledge": replay_secret_scan["negative_knowledge"],
            "claim": replay_secret_scan["claim"],
        },
        "replay_coverage_profile": {
            "profile_schema": replay_coverage_profile["profile_schema"],
            "profile_check_schema": replay_coverage_profile["profile_check_schema"],
            "thresholds": replay_coverage_profile["thresholds"],
            "negative_knowledge": replay_coverage_profile["negative_knowledge"],
            "claim": replay_coverage_profile["claim"],
        },
        "real_replay_report_builder": {
            "target_schemas": real_replay_builder["target_schemas"],
            "supported_status": real_replay_builder["supported_status"],
            "negative_knowledge": real_replay_builder["negative_knowledge"],
            "claim": real_replay_builder["claim"],
        },
        "production_evidence_bundle": {
            "bundle_schema": production_evidence_bundle["bundle_schema"],
            "supported_status": "supported",
            "negative_knowledge": production_evidence_bundle["negative_knowledge"],
            "claim": production_evidence_bundle["claim"],
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
        "dominance_cover": {
            "schema": dominance_cover["schema"],
            "evaluated_batches": dominance_cover["evaluated_batches"],
            "winner_only_ok_count": dominance_cover["summary"]["winner_only"][
                "ok_count"
            ],
            "winner_only_count": dominance_cover["summary"]["winner_only"]["count"],
            "weak_pruned_failed_count": dominance_cover["summary"]["weak_pruned"][
                "failed_count"
            ],
            "weak_pruned_count": dominance_cover["summary"]["weak_pruned"]["count"],
            "hand_top1_ok_count": dominance_cover["summary"]["hand_top1"][
                "ok_count"
            ],
            "hand_top1_failed_count": dominance_cover["summary"]["hand_top1"][
                "failed_count"
            ],
            "invalid_accept_count": dominance_cover["safety"][
                "invalid_accept_count"
            ],
            "negative_knowledge": dominance_cover["negative_knowledge"],
        },
        "wes_dominance_search": {
            "schema": wes_dominance_search["schema"],
            "wes_commit": wes_dominance_search["wes_commit"],
            "input_candidates": wes_dominance_search["input_candidates"],
            "budget": wes_dominance_search["budget"],
            "top_k": wes_dominance_search["top_k"],
            "model_online_useful_at_k": wes_dominance_search["summary"][
                "model_online_useful_at_k"
            ],
            "model_frozen_useful_at_k": wes_dominance_search["summary"][
                "model_frozen_useful_at_k"
            ],
            "declared_priority_useful_at_k": wes_dominance_search["summary"][
                "declared_priority_useful_at_k"
            ],
            "random_seeded_useful_at_k": wes_dominance_search["summary"][
                "random_seeded_useful_at_k"
            ],
            "checker_invalid_accept_count": wes_dominance_search["summary"][
                "checker_invalid_accept_count"
            ],
            "negative_knowledge": wes_dominance_search["negative_knowledge"],
        },
        "dominance_prefix": {
            "schema": dominance_prefix["schema"],
            "evaluated_batches": dominance_prefix["evaluated_batches"],
            "model_path": dominance_prefix["model_path"],
            "learned_mean_prefix_checked_count": dominance_prefix["summary"][
                "learned"
            ]["mean_prefix_checked_count"],
            "learned_p99_prefix_checked_count": dominance_prefix["summary"][
                "learned"
            ]["p99_prefix_checked_count"],
            "hybrid_mean_prefix_checked_count": dominance_prefix["summary"][
                "hybrid"
            ]["mean_prefix_checked_count"],
            "hand_mean_prefix_checked_count": dominance_prefix["summary"]["hand"][
                "mean_prefix_checked_count"
            ],
            "random_mean_prefix_checked_count": dominance_prefix["summary"][
                "random"
            ]["mean_prefix_checked_count"],
            "random_full_fallback_count": dominance_prefix["summary"]["random"][
                "full_fallback_count"
            ],
            "invalid_accept_count": dominance_prefix["safety"][
                "invalid_accept_count"
            ],
            "negative_knowledge": dominance_prefix["negative_knowledge"],
        },
        "suffix_bound": {
            "schema": suffix_bound["schema"],
            "evaluated_batches": suffix_bound["evaluated_batches"],
            "model_path": suffix_bound["model_path"],
            "learned_mean_verifier_calls": suffix_bound["summary"]["learned"][
                "mean_verifier_calls"
            ],
            "learned_p99_verifier_calls": suffix_bound["summary"]["learned"][
                "p99_verifier_calls"
            ],
            "hybrid_mean_verifier_calls": suffix_bound["summary"]["hybrid"][
                "mean_verifier_calls"
            ],
            "hand_mean_verifier_calls": suffix_bound["summary"]["hand"][
                "mean_verifier_calls"
            ],
            "random_mean_verifier_calls": suffix_bound["summary"]["random"][
                "mean_verifier_calls"
            ],
            "random_full_fallback_count": suffix_bound["summary"]["random"][
                "full_fallback_count"
            ],
            "invalid_accept_count": suffix_bound["safety"]["invalid_accept_count"],
            "limits": suffix_bound["limits"],
        },
        "suffix_bound_cross_seed": {
            "schema": suffix_bound_cross_seed["schema"],
            "batches_per_config": suffix_bound_cross_seed["batches_per_config"],
            "seeds": suffix_bound_cross_seed["seeds"],
            "candidate_counts": suffix_bound_cross_seed["candidate_counts"],
            "synthetic_batches_requested": suffix_bound_cross_seed[
                "synthetic_batches_requested"
            ],
            "synthetic_candidates_requested": suffix_bound_cross_seed[
                "synthetic_candidates_requested"
            ],
            "learned_mean_verifier_calls": suffix_bound_cross_seed["summary"][
                "learned"
            ]["mean_verifier_calls_mean"],
            "learned_p99_verifier_calls_max": suffix_bound_cross_seed["summary"][
                "learned"
            ]["p99_verifier_calls_max"],
            "hybrid_mean_verifier_calls": suffix_bound_cross_seed["summary"][
                "hybrid"
            ]["mean_verifier_calls_mean"],
            "hand_mean_verifier_calls": suffix_bound_cross_seed["summary"]["hand"][
                "mean_verifier_calls_mean"
            ],
            "random_mean_verifier_calls": suffix_bound_cross_seed["summary"][
                "random"
            ]["mean_verifier_calls_mean"],
            "random_full_fallback_count": suffix_bound_cross_seed["summary"][
                "random"
            ]["full_fallback_count_total"],
            "invalid_accept_count_total": suffix_bound_cross_seed["safety"][
                "invalid_accept_count_total"
            ],
            "negative_knowledge": suffix_bound_cross_seed["negative_knowledge"],
        },
        "suffix_bound_adversarial": {
            "schema": suffix_bound_adversarial["schema"],
            "batches": suffix_bound_adversarial["batches"],
            "evaluated_batches": suffix_bound_adversarial["summary"][
                "evaluated_batches"
            ],
            "candidates_per_batch": suffix_bound_adversarial["candidates_per_batch"],
            "seed": suffix_bound_adversarial["seed"],
            "adversary_invalid_count": suffix_bound_adversarial["summary"][
                "adversary_invalid_count"
            ],
            "adversary_disqualified_count": suffix_bound_adversarial["summary"][
                "adversary_disqualified_count"
            ],
            "with_disqualifiers_certificate_ok_count": suffix_bound_adversarial[
                "summary"
            ]["with_disqualifiers_certificate_ok_count"],
            "without_disqualifiers_certificate_ok_count": suffix_bound_adversarial[
                "summary"
            ]["without_disqualifiers_certificate_ok_count"],
            "declared_output_only_forced_fail_count": suffix_bound_adversarial[
                "summary"
            ]["declared_output_only_forced_fail_count"],
            "disqualifier_histogram": suffix_bound_adversarial["summary"][
                "disqualifier_histogram"
            ],
            "negative_knowledge": suffix_bound_adversarial["negative_knowledge"],
        },
        "suffix_bound_adversarial_families": {
            "schema": suffix_bound_adversarial_families["schema"],
            "batches": suffix_bound_adversarial_families["batches"],
            "evaluated_batches": suffix_bound_adversarial_families["summary"][
                "evaluated_batches"
            ],
            "candidates_per_batch": suffix_bound_adversarial_families[
                "candidates_per_batch"
            ],
            "seed": suffix_bound_adversarial_families["seed"],
            "family_count": suffix_bound_adversarial_families["summary"][
                "family_count"
            ],
            "total_cases": suffix_bound_adversarial_families["summary"][
                "total_cases"
            ],
            "adversary_invalid_count": suffix_bound_adversarial_families[
                "summary"
            ]["adversary_invalid_count"],
            "adversary_disqualified_count": suffix_bound_adversarial_families[
                "summary"
            ]["adversary_disqualified_count"],
            "with_disqualifiers_certificate_ok_count": (
                suffix_bound_adversarial_families["summary"][
                    "with_disqualifiers_certificate_ok_count"
                ]
            ),
            "without_disqualifiers_certificate_ok_count": (
                suffix_bound_adversarial_families["summary"][
                    "without_disqualifiers_certificate_ok_count"
                ]
            ),
            "high_declared_output_forced_fail_count": (
                suffix_bound_adversarial_families["summary"][
                    "high_declared_output_forced_fail_count"
                ]
            ),
            "observed_disqualifier_count": suffix_bound_adversarial_families[
                "summary"
            ]["observed_disqualifier_count"],
            "family_case_counts": suffix_bound_adversarial_families["summary"][
                "family_case_counts"
            ],
            "disqualifier_histogram": suffix_bound_adversarial_families["summary"][
                "disqualifier_histogram"
            ],
            "negative_knowledge": suffix_bound_adversarial_families[
                "negative_knowledge"
            ],
        },
        "negative_curriculum": {
            "schema": negative_curriculum["schema"],
            "source_schema": negative_curriculum["source_schema"],
            "evaluated_batches": negative_curriculum["evaluated_batches"],
            "family_count": negative_curriculum["family_count"],
            "total_cases": negative_curriculum["total_cases"],
            "output_mismatch_weight": negative_curriculum[
                "recommended_disqualifier_sample_weights"
            ]["output_mismatch_count"],
            "bounded_epiplexity_proxy": negative_curriculum[
                "bounded_epiplexity_proxy"
            ],
            "negative_knowledge": negative_curriculum["negative_knowledge"],
        },
        "curriculum_ranker": {
            "schema": curriculum_ranker["schema"],
            "max_train_batches": curriculum_ranker["max_train_batches"],
            "train_rows": curriculum_ranker["train_rows"],
            "train_rows_available": curriculum_ranker["train_rows_available"],
            "baseline_holdout_mean_calls": curriculum_ranker["holdout"]["baseline"][
                "mean_verifier_calls"
            ],
            "curriculum_holdout_mean_calls": curriculum_ranker["holdout"][
                "curriculum"
            ]["mean_verifier_calls"],
            "baseline_stress_mean_calls": curriculum_ranker["stress"]["summary"][
                "baseline_learned"
            ]["mean_verifier_calls_mean"],
            "curriculum_stress_mean_calls": curriculum_ranker["stress"]["summary"][
                "curriculum_learned"
            ]["mean_verifier_calls_mean"],
            "promotion_decision": curriculum_ranker["interpretation"][
                "promotion_decision"
            ],
            "negative_knowledge": curriculum_ranker["interpretation"][
                "negative_knowledge"
            ],
        },
        "data_scaling": {
            "schema": data_scaling["schema"],
            "available_train_rows": data_scaling["available_train_rows"],
            "holdout_rows": data_scaling["holdout_rows"],
            "first_budget_mean_calls": data_scaling["runs"][0]["metrics"][
                "mean_verifier_calls"
            ],
            "full_budget_mean_calls": data_scaling["runs"][-1]["metrics"][
                "mean_verifier_calls"
            ],
            "current_gap_weighted_mean_calls": data_scaling["baselines"][
                "current_gap_weighted"
            ]["mean_verifier_calls"],
            "best_budget_beats_current_gap_weighted": data_scaling[
                "interpretation"
            ]["best_budget_beats_current_gap_weighted"],
            "negative_knowledge": data_scaling["interpretation"][
                "negative_knowledge"
            ],
        },
        "quality_selection": {
            "schema": quality_selection["schema"],
            "winner_bearing_train_batches": quality_selection[
                "winner_bearing_train_batches"
            ],
            "excluded_no_winner_train_batches": quality_selection["selection"][
                "excluded_no_winner_train_batches"
            ],
            "quality_beats_raw_budget_count": quality_selection["interpretation"][
                "quality_beats_raw_budget_count"
            ],
            "quality_worse_than_raw_budget_count": quality_selection[
                "interpretation"
            ]["quality_worse_than_raw_budget_count"],
            "best_quality_mean_verifier_calls": quality_selection["interpretation"][
                "best_quality_mean_verifier_calls"
            ],
            "best_quality_matches_or_beats_current_gap_weighted": quality_selection[
                "interpretation"
            ]["best_quality_matches_or_beats_current_gap_weighted"],
            "negative_knowledge": quality_selection["interpretation"][
                "negative_knowledge"
            ],
        },
        "ensemble": {
            "schema": ensemble["schema"],
            "member_count": ensemble["ensemble"]["member_count"],
            "best_ensemble_mode": ensemble["interpretation"][
                "best_ensemble_mode"
            ],
            "best_ensemble_mean_verifier_calls": ensemble["interpretation"][
                "best_ensemble_mean_verifier_calls"
            ],
            "baseline_mean_verifier_calls": ensemble["interpretation"][
                "baseline_mean_verifier_calls"
            ],
            "best_ensemble_beats_current_gap_weighted": ensemble[
                "interpretation"
            ]["best_ensemble_beats_current_gap_weighted"],
            "best_uncertainty_auc": ensemble["interpretation"][
                "best_uncertainty_auc"
            ],
            "negative_knowledge": ensemble["interpretation"][
                "negative_knowledge"
            ],
        },
        "best_model_registry": {
            "schema": best_model_registry["schema"],
            "scope": best_model_registry["scope"],
            "model_count": len(best_model_registry["models"]),
            "promoted": best_model_registry["promoted"],
            "safety_contract": best_model_registry["safety_contract"],
        },
        "upba_v2_model_leaderboard": {
            "schema": upba_v2_model_leaderboard["schema"],
            "decision": upba_v2_model_leaderboard["decision"],
            "promoted_model_id": upba_v2_model_leaderboard["promoted_model_id"],
            "compared_model_count": upba_v2_model_leaderboard[
                "compared_model_count"
            ],
            "full_three_lane_model_count": upba_v2_model_leaderboard[
                "full_three_lane_model_count"
            ],
            "blocked_reasons": upba_v2_model_leaderboard["blocked_reasons"],
        },
        "epiplexity_literature": {
            "schema": epiplexity_literature["schema"],
            "source_count": epiplexity_literature["source_count"],
            "passed_count": epiplexity_literature["passed_count"],
            "decision": epiplexity_literature["decision"],
            "proxy": epiplexity_literature["proxy"],
            "negative_knowledge": epiplexity_literature["negative_knowledge"],
        },
        "synthetic_data_limits": {
            "schema": synthetic_data_limits["schema"],
            "source_count": synthetic_data_limits["source_count"],
            "passed_count": synthetic_data_limits["passed_count"],
            "decision": synthetic_data_limits["decision"],
            "negative_knowledge": synthetic_data_limits["negative_knowledge"],
        },
        "langevin_discovery": {
            "schema": langevin_discovery["schema"],
            "decision": langevin_discovery["decision"],
            "energy_delta": langevin_discovery["energy_delta"],
            "seed_verifier_ok": langevin_discovery["seed_verifier_ok"],
            "refined_verifier_ok": langevin_discovery["refined_verifier_ok"],
            "selected_verifier_ok": langevin_discovery["selected_verifier_ok"],
            "accepted_refinement": langevin_discovery["accepted_refinement"],
            "fallback_to_seed": langevin_discovery["fallback_to_seed"],
        },
        "autotrader_refiner_boundary": {
            "schema": autotrader_refiner_boundary["schema"],
            "decision": autotrader_refiner_boundary["decision"],
            "evaluated_contexts": autotrader_refiner_boundary["evaluated_contexts"],
            "accepted_refinement_count": autotrader_refiner_boundary[
                "accepted_refinement_count"
            ],
            "selected_invalid_count": autotrader_refiner_boundary[
                "selected_invalid_count"
            ],
            "selected_vs_initial_objective_delta_mean": autotrader_refiner_boundary[
                "selected_vs_initial_objective_delta_mean"
            ],
            "selected_vs_initial_energy_delta_mean": autotrader_refiner_boundary[
                "selected_vs_initial_energy_delta_mean"
            ],
            "negative_knowledge": autotrader_refiner_boundary["negative_knowledge"],
        },
        "jepa_logic_boundary": {
            "schema": jepa_logic_boundary["schema"],
            "decision": jepa_logic_boundary["decision"],
            "balanced_action_tension": jepa_logic_boundary["jepa"][
                "balanced_action_tension"
            ],
            "draining_action_tension": jepa_logic_boundary["jepa"][
                "draining_action_tension"
            ],
            "future_tension_prefers_balanced": jepa_logic_boundary["jepa"][
                "future_tension_prefers_balanced"
            ],
            "energy_not_inverts_barrier": jepa_logic_boundary["zeno_logic"][
                "energy_not_inverts_barrier"
            ],
            "negative_knowledge": jepa_logic_boundary["negative_knowledge"],
        },
        "autotrader_jepa_ux": {
            "schema": autotrader_jepa_ux["schema"],
            "decision": autotrader_jepa_ux["decision"],
            "mean_guard_calls": autotrader_jepa_ux["future_aware_evaluation"][
                "mean_guard_calls"
            ],
            "top_5_recall": autotrader_jepa_ux["future_aware_evaluation"][
                "top_5_recall"
            ],
            "invalid_accept_count": autotrader_jepa_ux["future_aware_evaluation"][
                "invalid_accept_count"
            ],
            "balanced_future_tension": autotrader_jepa_ux["scenario_scores"][
                "balanced_future_tension"
            ],
            "fragile_future_tension": autotrader_jepa_ux["scenario_scores"][
                "fragile_future_tension"
            ],
            "later_policy_failure_auc": autotrader_jepa_ux[
                "future_risk_prediction"
            ]["later_policy_failure_auc"],
            "stress_correlations": autotrader_jepa_ux["future_risk_prediction"][
                "stress_correlations"
            ],
            "safer_counterfactual_reduction_rate": autotrader_jepa_ux[
                "control_metrics"
            ]["safer_counterfactual_reduction_rate"],
            "suggested_control_best_reduction_rate": autotrader_jepa_ux[
                "control_metrics"
            ]["suggested_control_best_reduction_rate"],
            "blocked_status_match_rate": autotrader_jepa_ux["warning_metrics"][
                "blocked_status_match_rate"
            ],
            "future_warning_match_rate": autotrader_jepa_ux["warning_metrics"][
                "future_warning_match_rate"
            ],
            "ux_explains_status_and_controls": autotrader_jepa_ux["ux"][
                "ux_explains_status_and_controls"
            ],
            "negative_knowledge": autotrader_jepa_ux["negative_knowledge"],
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


def _sha256_file(path: Path) -> str:
    return "sha256:" + sha256(path.read_bytes()).hexdigest()


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


if __name__ == "__main__":
    raise SystemExit(main())
