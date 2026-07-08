# ZenoDEX AB Strict Zero-Min Range-Step Transfer Lean Bridge

## Summary

This artifact adds a machine-checked Lean bridge between two existing AB strict
zero-min proof-certificate surfaces:

- recursive range-step path evidence;
- range-mask and compressed-winner certificate evidence.

The result is a representation-transfer component for the subset-mask induction
ladder. A later host emitter can provide recursive path-shaped evidence and
reuse endpoints that consume the earlier range-mask/compressed-winner surface.

Research-only formal proof component; no settlement, state-root, production,
routing, matching, or governance authority.

## New Lean Surface

- `reachablePrunedStepPath_to_reachablePrunedRangeMask`
- `reachablePrunedRangeStepPathInFamily_to_reachablePrunedFullMaskInFamily`
- `reachablePrunedRangeStepPathListInFamily_to_reachablePrunedFullMaskListInFamily`
- `rangeStepPathWinnerCertificate_to_compressedWinnerCertificate`

## Proof Role

The previous ladder already had:

- `reachablePrunedRangeMask` and `reachablePrunedFullMaskListInFamily` endpoints;
- recursive `reachablePrunedStepPath` and `rangeStepPathWinnerCertificate`
  endpoints;
- strict host-table endpoints over explicit finite mask families.

This bridge proves that recursive range-step evidence can be consumed by the
older compressed-winner certificate layer without changing the winner, children,
mask family, suffix, or economic parameters.

## Verification

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Observed result:

- Lean target file: pass
- Focused formal pytest: `1 passed in 11.94s`
- Proof placeholder scan: pass

## Artifact Hashes

- `lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean`:
  `f885fab2d2e40abb67f82b804f8e33fd02e49cc740c69585c0a3086faeb5420f`
- `tests/formal/test_lean_ab_strict_zero_min_monotone.py`:
  `49f34abd1e33c94ce74d4268fee50a950a2b43cc14813fc0f08c176659f5ff40`

## Non-Claims

- This proof does not construct a subset DP table.
- This proof does not prove Python-to-Lean refinement.
- This proof does not prove JSON canonicalization or packet-hash computation in
  Lean.
- This proof does not define canonical tie order or preserve order-id history.
- This proof is restricted to the abstract strict executable same-pool,
  same-direction, exact-in, zero-min proof surface already modeled in
  `ABStrictZeroMinMonotone.lean`.
- This proof does not cover nonzero `min_amount_out` behavior.
- This proof has no settlement, state-root, production, routing, matching, or
  governance authority.
