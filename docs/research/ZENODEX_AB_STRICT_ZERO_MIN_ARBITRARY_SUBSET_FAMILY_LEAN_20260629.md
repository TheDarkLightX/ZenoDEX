# ZenoDEX AB Strict Zero-Min Arbitrary Subset-Family Lean Bridge - 2026-06-29

## Executive Result

The AB strict zero-min proof ladder now has a Lean bridge for arbitrary finite
subset-mask families. This theorem matches the aggregation shape checked by the
bounded host oracle over reachable subset masks.

Research-only proof evidence; no settlement, state-root, production, or
governance authority.

## What The Bridge Fixes

Earlier host-table bridges required every retained mask to satisfy:

```text
allBitsBelowSet mask.maskId bitCount
```

That is a full-range coverage assumption. It is useful for final full-mask
certificates, but it is too strong for arbitrary reachable subset masks.

`StrictSubsetFamilyHostTable` removes that assumption. It requires only local
record-set pruning for every retained mask:

```text
forall mask in masks, maskPruningInvariant mask
```

Given a selected-family winner, fixed suffix, suffix executability, and
data-only rails, Lean proves the finite family dominance endpoint.

## Theorem Endpoint

`strictSubsetFamilyHostTable_validates` proves:

- packet-hash bound rail is present;
- no-authority-effect rail is present;
- winner-membership bound rail is present;
- the full finite subset family is economically dominated by the selected
  winner at fixed executed input;
- the selected winner executes the suffix.

The dominance endpoint is:

```text
zeroMinEconomicKeyDominated
  (fullFrontierZeroMinEconomicKey executedInput initialReserveOut masks suffix)
  (selectedZeroMinEconomicKey executedInput initialReserveOut winner suffix)
```

## Relationship To The Host Oracle

The bounded host oracle checks 180 strict cases, 4,464 reachable masks, 85,284
records, and 212,760 executable suffix completions. This Lean theorem now
matches the arbitrary reachable-mask aggregation shape of that checker, while
keeping Python-to-Lean refinement as a separate open obligation.

## Theorems And Definitions Added

- `StrictSubsetFamilyHostTable`
- `strictSubsetFamilyHostTableValid`
- `strictSubsetFamilyHostTable_validates`
- `witness_strictSubsetFamilyHostTable_validates`

## Replay Commands

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
python3 tools/check_claims_registry.py
```

## Non-Claims

- This does not construct the finite mask family from the Python DP table.
- This does not prove Python-to-Lean refinement.
- This does not define canonical tie order.
- This does not cover nonzero `min_amount_out` batches.
- This does not prove full-mask coverage for arbitrary reachable subset masks.
- This does not turn bounded evidence into exhaustive state coverage.
- This does not authorize settlement, state roots, production deployment, or
  governance execution.

## Value For ZenoDEX

This closes a specification mismatch in the proof ladder. Full-range bridge
theorems remain useful for final full-mask certificates, while arbitrary
reachable subset-mask aggregation now has its own Lean endpoint with weaker and
more accurate assumptions.
