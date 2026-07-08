# ZenoDEX AB Strict Zero-Min Economic Key Bridge Lean Proof - 2026-06-29

## Executive Result

This artifact adds the Lean economic-key layer for the AB strict executable
zero-min proof ladder. It formalizes the supported research key:

```text
(executed_input, surplus)
```

as:

```text
structure ZeroMinEconomicKey where
  executedInput : Nat
  surplus : Nat
```

The key deliberately excludes canonical tie order. Lean proves that a recursive
range-step winner certificate bounds this economic key when the executed-input
component is fixed:

```text
rangeStepPathWinnerCertificate parent winner children bitCount masks initialReserveOut suffix
  -> fullFrontierZeroMinEconomicKey executedInput initialReserveOut children suffix
     is dominated by selectedZeroMinEconomicKey executedInput initialReserveOut winner suffix
```

It also adds a strict executable wrapper:

```text
strictRangeStepPathEconomicCertificate :=
  rangeStepPathWinnerCertificate
  and suffixExecutable winner.selected.processedReserveIn winner.selected.reserveOut suffix
```

The endpoint proves bounded child coverage, economic-key dominance, and carries
the compressed-winner suffix executability assumption.

## New Lean Surface

File:

```text
lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Added definitions and theorems:

```text
structure ZeroMinEconomicKey
def zeroMinEconomicKeyDominated
def selectedZeroMinEconomicKey
def fullFrontierZeroMinEconomicKey
theorem rangeStepPathWinnerCertificate_bounds_zeroMinEconomicKey
def strictRangeStepPathEconomicCertificate
theorem strictRangeStepPathEconomicCertificate_covers_bounds_and_executes
theorem witness_strictRangeStepPathEconomicCertificate_covers_bounds_and_executes
```

The proof composes the recursive range-step certificate endpoint with a fixed
executed-input component. This matches the supported strict zero-min economic
surface while keeping tie order out of the formal claim.

## ZenoDEX Value

Previous Lean artifacts reached a recursive range-step coverage and winner
dominance certificate. This artifact connects that certificate to the AB
economic key used by the counterexample-salvage evidence: executed input first,
then surplus.

The immediate value is a cleaner verifier-facing proof object: a certificate can
state the fixed executed input, prove the selected winner is executable for the
strict suffix, and recover both bounded mask coverage and economic-key
dominance. The remaining work is construction/refinement: prove that the Python
compressed DP emits this certificate and that the fixed executed-input component
matches the concrete batch.

## Non-Claims

This artifact does not prove the full strict compressed-DP theorem. It does not
construct the recursive path, child frontier, mask family, winner, or executed
input. It does not define canonical tie order. It does not prove that the Python
implementation emits these certificates. It does not prove Lean-to-Python
refinement. It does not cover nonzero `min_amount_out`. It does not prove host
bitset equivalence. It does not authorize settlement, state roots, production
promotion, governance actions, or any consensus-critical path.

## Replay

Expected replay commands:

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 -m json.tool generated/zenodex_ab_strict_zero_min_economic_key_bridge_lean_20260629/report.json >/dev/null
rg -n "\b(sorry|admit|axiom|unsafe|sorryAx)\b" lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

The final `rg` command should exit with status 1 because no forbidden proof
placeholder is present.

## Research-Kernel Atom

Suggested atom id:

```text
atom_ab_strict_zero_min_economic_key_bridge_lean_20260629
```

Suggested parents:

```text
atom_ab_strict_zero_min_subset_mask_induction_frontier_20260628
atom_ab_strict_zero_min_range_step_path_bridge_lean_20260629
atom_ab_strict_zero_min_step_induction_bridge_lean_20260628
```

Suggested status after replay:

```text
SUPPORTED
```
