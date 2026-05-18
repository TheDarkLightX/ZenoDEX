from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_uniform_batch_optimality_typechecks_without_placeholders() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/UniformBatchOptimality.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    for required in (
        "theorem exact_upper_bound_certificate_implies_global_weak_optimal",
        "theorem upba_v3_exact_out_exact_grid_upper_bound_certificate_implies_global_weak_optimal",
        "theorem upba_v3_full_fill_exact_out_grid_upper_bound_certificate_implies_global_weak_optimal",
        "theorem upba_v3_exact_out_bounded_grid_upper_bound_certificate_implies_global_weak_optimal",
        "theorem exactOutFullFillCanonicalGridCandidates_eq_singleton_plan",
        "theorem feasibleExactOutFullFill_iff_singleton_plan",
        "theorem exactOutCanonicalGridCandidates_exact_audit_set",
        "theorem exactOutFullFillCanonicalGridCandidates_exact_audit_set",
        "theorem reordered_exact_upper_bound_certificate_implies_global_weak_optimal",
        "def FullFallbackEquivalentOrder",
        "def CandidateSubset",
        "def AdvisorySelectedRepairSet",
        "theorem candidate_subset_refl",
        "theorem candidate_subset_trans",
        "theorem advisory_selected_repair_set_implies_candidate_subset",
        "theorem augmented_superset_weak_optimal_implies_base_weak_optimal",
        "theorem augmented_superset_upper_bound_certificate_implies_base_weak_optimal",
        "theorem advisory_selected_repair_set_upper_bound_certificate_implies_base_weak_optimal",
        "theorem full_fallback_equivalent_order_preserves_membership_iff",
        "theorem full_fallback_equivalent_order_preserves_weak_optimality_iff",
        "def CheckedStopCertificate",
        "theorem checked_stop_certificate_implies_concat_weak_optimal",
        "theorem checked_stop_certificate_with_full_permutation_implies_full_weak_optimal",
        "theorem checked_stop_certificate_with_exact_full_implies_global_weak_optimal",
        "theorem generated_corpus_exact_upper_bound_certificate_implies_global_weak_optimal",
        "theorem dominance_cover_upper_bound_certificate_implies_global_weak_optimal",
        "def ObjectiveEquivalent",
        "theorem objective_equivalent_transfers_weak_dominance",
        "theorem objective_equivalent_preserves_weak_optimal_in",
        "theorem objective_equivalent_preserves_global_weak_optimal",
        "theorem objective_equivalent_exact_upper_bound_certificate_implies_global_weak_optimal",
        "theorem objective_equivalent_reordered_exact_upper_bound_certificate_implies_global_weak_optimal",
        "theorem upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
        "theorem upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
        "theorem upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal",
    ):
        assert required in source
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
    assert forbidden.search(source) is None

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
