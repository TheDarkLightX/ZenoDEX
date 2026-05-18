# ZenoEnergy Fallback And Checked-Stop Formal Boundary

Receipt:
`data/upba_energy/upba_v2_fallback_checked_stop_formal_receipt.json`

Formal target:
`lean-mathlib/Proofs/UniformBatchOptimality.lean`

Commands:

```bash
cd lean-mathlib && lake env lean Proofs/UniformBatchOptimality.lean
pytest -q tests/formal/test_lean_uniform_batch_optimality.py
```

Both commands passed for this receipt.

## Boundary

Full deterministic fallback is order-equivalent when the ranked order is a
permutation of the exact finite candidate list. The model may change order, but
the verifier still checks the same candidate family.

Checked early stop needs a verifier-facing certificate:

```text
winner in checked
WeaklyOptimalIn(winner, checked)
WeaklyOptimalIn(winner, unchecked_suffix)
(checked ++ unchecked_suffix).Perm(full)
ExactAuditSet(full, Feasible)
```

Those premises lift a checked-prefix winner to global weak optimality over the
finite exact candidate family represented by `full`.

## Lean Names

```text
def FullFallbackEquivalentOrder
theorem full_fallback_equivalent_order_preserves_membership_iff
theorem full_fallback_equivalent_order_preserves_weak_optimality_iff
def CheckedStopCertificate
theorem checked_stop_certificate_implies_concat_weak_optimal
theorem checked_stop_certificate_with_full_permutation_implies_full_weak_optimal
theorem checked_stop_certificate_with_exact_full_implies_global_weak_optimal
theorem reordered_exact_upper_bound_certificate_implies_global_weak_optimal
theorem upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
theorem upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
theorem upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
```

## Runtime Evidence

The 200-batch fallback permutation audit reports:

```text
learned top_10_recall: 1.0
learned checked_stop_top_k_rate: 1.0
learned permutation_violation_count: 0
invalid_accept_count: 0
```

The holdout top-k sweep reports:

```text
learned k=2 checked_stop_top_k_rate: 1.0
learned k=2 false_exclusion_rate: 0.0
random k=10 false_exclusion_rate: 0.4931921331316188
```

## Limits

These theorems are finite-candidate-family certificates. They do not prove that
synthetic generation is globally complete unless the exact-audit-set premises
are supplied. The checked-stop rates are offline audits over verified suffix
labels. Online early stop still needs a deterministic suffix-bound certificate
or full fallback.
