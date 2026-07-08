# ZenoDEX AB Strict Zero-Min Observed Summary Lean Bridge

## Summary

This artifact adds a machine-checked Lean observed-summary certificate for the
AB strict zero-min subset-mask proof ladder.

The previous range-path and aggregate-winner endpoints validate a supplied
finite table. This bridge adds a host-visible summary shell that binds:

```text
(observedMaskCount, observedWinnerMaskId, observedExecutedInput, observedInitialReserveOut)
```

to the validated recursive range-path table, then inherits the aggregate
range-path economic endpoint.

Research-only formal proof component; no settlement, state-root, production,
routing, matching, or governance authority.

## New Lean Surface

- `StrictSubsetInductionObservedSummary`
- `strictSubsetInductionObservedSummaryValid`
- `strictSubsetInductionObservedSummaryFullKey`
- `strictSubsetInductionObservedSummarySelectedKey`
- `strictSubsetInductionObservedSummary_to_aggregateRangePathTableValid`
- `strictSubsetInductionObservedSummary_validates`
- `witness_strictSubsetInductionObservedSummary_validates`

## Proof Role

This closes a checker-boundary gap in the monotone-reserve proof ladder:

1. a host-visible summary names the observed mask count and economic-key
   metadata;
2. the summary validity predicate binds those fields to the Lean table fields;
3. the table must satisfy the aggregate recursive range-path predicate;
4. therefore validation recovers count/key bindings, packet rails, winner
   full-mask coverage, zero-min economic-key dominance, and selected suffix
   executability.

This remains a checker endpoint. It does not construct the host table or prove
that a Python emitter generated the table.

## Verification

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
python3 tools/check_public_claim_scope.py --root . --json
python3 tools/check_claims_registry.py
```

Observed result:

- Lean target file: pass
- Focused formal pytest: `1 passed in 8.90s`
- Proof placeholder scan: pass
- Lean module build: pass
- JSON validation: pass
- Public claim scope check: ok
- Claims registry check: ok
- Diff whitespace check: pass

## Artifact Hashes

- `lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean`:
  `0d9787f60b655a59c5ab3f6395eebf013d7827b3e5f51c974c180cfe3a1ae1e6`
- `tests/formal/test_lean_ab_strict_zero_min_monotone.py`:
  `eb9e1af42c1e854baf73fb2f892dd4466c5730d81529d7788ac1f4746c9ba081`

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
