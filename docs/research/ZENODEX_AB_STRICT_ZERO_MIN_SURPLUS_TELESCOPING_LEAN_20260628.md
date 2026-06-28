# ZenoDEX AB Strict Zero-Min Surplus Telescoping Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof ladder with the
final reserve-out to surplus connection.

For a fixed exact-in suffix, the sum of per-step outputs equals the drop in
output reserve from the suffix start to the suffix end:

```lean
theorem runOutputAfterSuffix_eq_reserveOut_sub_finalReserveOut
    (reserveIn reserveOut : Nat)
    (steps : List ExactInStep) :
    runOutputAfterSuffix reserveIn reserveOut steps =
      reserveOut - runReserveOutAfterSuffix reserveIn reserveOut steps

theorem zeroMinSuffixSurplus_eq_reserveOut_sub_finalReserveOut
    (reserveIn reserveOut : Nat)
    (steps : List ExactInStep) :
    zeroMinSuffixSurplus reserveIn reserveOut steps =
      reserveOut - runReserveOutAfterSuffix reserveIn reserveOut steps
```

Since every strict zero-min swap has `min_amount_out = 0`, per-step surplus is
the per-step output in this model. The theorem ties the pruning objective to the
same reserve-out order used by the existing suffix dominance and record-set
pruning lemmas.

## Value

- Discharges the final reserve-out to surplus proof component for fixed strict
  zero-min suffixes.
- Converts the representative-dominance proof from a reserve-order statement
  into the economic objective used by AB compression research.
- Adds a telescoping identity that is independent of search implementation
  details.

## Scope

Proved in Lean:

- a fixed strict exact-in suffix cannot increase output reserve;
- total suffix output equals initial output reserve minus final output reserve;
- zero-min suffix surplus equals the same final reserve-out drop;
- concrete non-vacuity witness for the telescoping identity.

Non-claims:

- no formal strict executability predicate;
- no sender-balance proof;
- no canonical tie-order proof;
- no nonzero `min_amount_out` coverage;
- no kernel domain-failure proof;
- no subset-mask induction proof;
- no full Python subset-DP refinement proof;
- no production ordering or settlement authority.

## Replay

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
```

## Verification

- `lake env lean Proofs/ABStrictZeroMinMonotone.lean`: pass
- `lake build Proofs.ABStrictZeroMinMonotone`: pass
- `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py`: pass
- proof placeholders: none
