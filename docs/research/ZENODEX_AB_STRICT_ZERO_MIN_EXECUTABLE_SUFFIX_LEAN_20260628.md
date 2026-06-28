# ZenoDEX AB Strict Zero-Min Executable Suffix Lean Proof - 2026-06-28

## Executive Result

This artifact extends the AB strict executable zero-min proof ladder with an
explicit executable-step and executable-suffix predicate for the abstract fixed
suffix model.

```lean
def strictStepExecutable (reserveIn reserveOut : Nat) (step : ExactInStep) : Prop

def suffixExecutable (reserveIn reserveOut : Nat) : List ExactInStep -> Prop

theorem suffixExecutable_finalReserveOut_pos
    {reserveIn reserveOut : Nat}
    {steps : List ExactInStep}
    (hout : 0 < reserveOut)
    (hexec : suffixExecutable reserveIn reserveOut steps) :
    0 < runReserveOutAfterSuffix reserveIn reserveOut steps
```

The predicate records positive input reserve, positive output reserve, positive
gross input, positive net input, `netIn <= grossIn`, and positive CPMM output
for each step. The suffix theorem proves that an executable suffix keeps final
output reserve positive.

## Value

- Makes the strict executable scope explicit in Lean.
- Separates executable-suffix assumptions from the reserve monotonicity and
  telescoping arithmetic.
- Narrows the remaining full compression proof gap to subset-mask induction and
  Python refinement.

## Scope

Proved in Lean:

- positive reserves imply CPMM output is strictly less than output reserve;
- a strict executable step leaves positive output reserve;
- a strict executable step strictly decreases output reserve;
- a strict executable suffix leaves positive final output reserve;
- suffix input reserve remains positive from a positive initial input reserve;
- concrete non-vacuity witness for a two-step executable suffix.

Non-claims:

- no sender-balance proof;
- no canonical tie-order proof;
- no nonzero `min_amount_out` coverage;
- no full kernel domain-failure model;
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
