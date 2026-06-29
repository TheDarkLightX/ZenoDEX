# ZenoDEX AB Strict Zero-Min Aggregate Winner Lean Bridge

## Summary

This artifact adds a machine-checked Lean bridge for a host-emitter-friendly
winner certificate in the AB strict zero-min subset-mask proof ladder.

The existing proof surface used `selectedFamilyOutputWinner`, a universal
predicate requiring the supplied winner to dominate every retained selected
representative. The new surface adds `selectedFamilyAggregateWinner`, which
uses one scalar aggregate bound:

```text
bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix
  <= maskSelectedSuffixOutput initialReserveOut winner suffix
```

Together with explicit winner membership, this aggregate predicate is equivalent
to the universal selected-family winner predicate. This lets a future host
packet carry a fold-max-style aggregate bound while reusing the existing Lean
endpoints.

Research-only formal proof component; no settlement, state-root, production,
routing, matching, or governance authority.

## New Lean Surface

- `selectedFamilyAggregateWinner`
- `selectedFamilyAggregateWinner_to_selectedFamilyOutputWinner`
- `selectedFamilyOutputWinner_to_selectedFamilyAggregateWinner`
- `selectedFamilyOutputWinner_iff_aggregateWinner`
- `aggregateRangeStepPathWinnerCertificate`
- `aggregateRangeStepPathWinnerCertificate_to_rangeStepPathWinnerCertificate`

## Proof Role

The bridge converts a scalar selected-family aggregate proof into the existing
universal winner predicate and then into the existing recursive range-step
winner certificate endpoint.

This is useful for host evidence because a packet can record one fold-max bound
rather than one inequality per retained mask, while Lean still receives the
same proof obligation at the old endpoint.

## Verification

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Observed result:

- Lean target file: pass
- Focused formal pytest: `1 passed in 9.18s`
- Proof placeholder scan: pass
- Lean module build: pass
- JSON validation: pass
- Public claim scope check: ok
- Claims registry check: ok
- Diff whitespace check: pass

## Artifact Hashes

- `lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean`:
  `6619b88752c36c079f954bdf9236865dcd9b5dd3c98a1bb4861bf0ae65448fff`
- `tests/formal/test_lean_ab_strict_zero_min_monotone.py`:
  `12ac54a370f58bf147a1ab0dd9ae8451ad7e87531e2b42e4e669cb82bb49f9c3`

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
