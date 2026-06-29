# ZenoDEX AB Strict Zero-Min Range-Path Host Table Lean Bridge - 2026-06-29

## Executive Result

The AB strict zero-min subset-induction ladder now has a Lean bridge from
recursive pruned range-step reachability to the finite host-table dominance
endpoint.

Research-only proof evidence; no settlement, state-root, production, or
governance authority.

## What Changed

The prior host-table bridge required direct assumptions for every retained mask:

```text
allBitsBelowSet mask.maskId bitCount
maskPruningInvariant mask
```

The new `StrictSubsetInductionRangePathTable` replaces those direct assumptions
with a recursive range-step family condition:

```text
reachablePrunedRangeStepPathListInFamily parent masks bitCount masks
```

For each retained mask, this condition supplies a pruned recursive path over
`List.range bitCount`. Lean derives both bounded bit coverage and local pruning
from that path, then reuses the direct host-table theorem.

## Theorem Endpoint

`strictSubsetInductionRangePathTable_validates` proves:

- the interpreted `StrictSubsetInductionHostTable` is valid;
- packet-hash bound, no-authority-effect, and winner-membership rails are
  present;
- the winner covers every bit below `bitCount`;
- the full finite mask family is economically dominated by the selected winner
  at fixed executed input;
- the selected winner executes the suffix.

The dominance endpoint remains:

```text
zeroMinEconomicKeyDominated
  (fullFrontierZeroMinEconomicKey executedInput initialReserveOut masks suffix)
  (selectedZeroMinEconomicKey executedInput initialReserveOut winner suffix)
```

## Value

This reduces one assumption class in the proof ladder. The host table no longer
needs to assert coverage and pruning directly for every mask if it supplies
recursive pruned range-step reachability. That is closer to the full
subset-mask induction frontier, where the remaining hard part is constructing
and refining the finite family from the concrete Python DP emitter.

## Theorems And Definitions Added

- `StrictSubsetInductionRangePathTable`
- `strictSubsetInductionRangePathTableHost`
- `strictSubsetInductionRangePathTableValid`
- `strictSubsetInductionRangePathTable_validates`
- `witness_strictSubsetInductionRangePathTable_validates`

## Replay Commands

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
python3 tools/check_claims_registry.py
```

## Verification Receipts

- Lean file check: pass
- Formal pytest guard: pass, `1 passed`
- Proof-placeholder scan: pass, `No proof placeholders found.`
- Lean module build: pass
- Claims registry: pass, `ok`

## Non-Claims

- This does not construct the finite mask family from the Python DP table.
- This does not prove Python-to-Lean refinement.
- This does not define canonical tie order.
- This does not cover nonzero `min_amount_out` batches.
- This does not turn bounded evidence into exhaustive state coverage.
- This does not authorize settlement, state roots, production deployment, or
  governance execution.
