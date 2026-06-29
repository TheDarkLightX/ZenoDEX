# ZenoDEX AB Strict Zero-Min Aggregate Host-Table Lean Bridge

## Summary

This artifact adds a machine-checked Lean host-table endpoint for aggregate
winner evidence in the AB strict zero-min subset-mask proof ladder.

The previous aggregate-winner bridge showed that a scalar fold-max bound is
equivalent to the universal selected-family winner predicate. This artifact
lifts that bridge to the host-table layer:

- `strictSubsetInductionAggregateRangePathTableValid` accepts a recursive
  range-path table with `selectedFamilyAggregateWinner`;
- `strictSubsetInductionAggregateRangePathTable_to_rangePathTableValid` converts
  it into the existing recursive range-path table validity predicate;
- `strictSubsetInductionAggregateRangePathTable_validates` inherits the existing
  subset-induction host-table endpoint.

Research-only formal proof component; no settlement, state-root, production,
routing, matching, or governance authority.

## New Lean Surface

- `strictSubsetInductionAggregateRangePathTableValid`
- `strictSubsetInductionAggregateRangePathTable_to_rangePathTableValid`
- `strictSubsetInductionAggregateRangePathTable_validates`

## Proof Role

The proof reduces host packet burden: a host witness can carry one selected
family aggregate winner bound while Lean recovers the existing range-path and
host-table endpoints.

This advances the subset-mask induction ladder by making the host-emitter
boundary smaller and closer to a replayable fold-max certificate.

## Verification

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Observed result:

- Lean target file: pass
- Focused formal pytest: `1 passed in 10.04s`
- Proof placeholder scan: pass
- Lean module build: pass
- JSON validation: pass
- Public claim scope check: ok
- Claims registry check: ok
- Diff whitespace check: pass

## Artifact Hashes

- `lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean`:
  `7fdc5adcbbaf6256c4100a8d5416f464e672f964ca1dc1eb7c15c4f8d9a8cf08`
- `tests/formal/test_lean_ab_strict_zero_min_monotone.py`:
  `ce54bcfff369890bd4a79406955990c55cd5efec3c7e70cf53df3017fdbca6ec`

## Non-Claims

- This proof does not construct a subset DP table.
- This proof does not prove Python-to-Lean refinement.
- This proof does not prove JSON canonicalization or packet-hash computation in
  Lean.
- This proof does not define canonical tie order or choose among tied winners.
- This proof is restricted to the abstract strict executable same-pool,
  same-direction, exact-in, zero-min proof surface already modeled in
  `ABStrictZeroMinMonotone.lean`.
- This proof does not cover nonzero `min_amount_out` behavior.
- This proof has no settlement, state-root, production, routing, matching, or
  governance authority.
