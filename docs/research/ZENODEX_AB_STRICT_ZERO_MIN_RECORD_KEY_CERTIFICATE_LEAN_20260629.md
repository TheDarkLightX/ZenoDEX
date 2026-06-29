# ZenoDEX AB Strict Zero-Min Record-Key Certificate Lean Bridge

## Summary

This artifact adds a machine-checked Lean record-set economic-key certificate
for the AB strict zero-min subset-mask proof ladder.

The previous record pruning theorem bounded scalar suffix output. This bridge
lifts that result into the actual strict zero-min economic objective:

```text
(executedInput, zeroMinSurplus)
```

It also adds a proof-carrying finite record-set certificate that carries the
selected representative's suffix executability.

Research-only formal proof component; no settlement, state-root, production,
routing, matching, or governance authority.

## New Lean Surface

- `recordZeroMinEconomicKey`
- `minReserveRecord_dominates_zeroMinEconomicKey`
- `bestRecordSetZeroMinEconomicKey`
- `bestRecordSetZeroMinEconomicKey_dominated_by_selected`
- `strictRecordSetPruningCertificate`
- `strictRecordSetPruningCertificate_validates`

## Proof Role

This closes a local gap in the monotone-reserve proof ladder:

1. all records in a finite processed-subset record set share the selected
   representative's processed input reserve;
2. the selected representative has minimum output reserve;
3. the selected representative's suffix is executable;
4. therefore the best full record-set economic key is weakly dominated by the
   selected representative's economic key, and selected suffix executability is
   preserved.

This is still a record-level certificate. It does not construct the subset DP
table or connect Lean records to Python host records.

## Verification

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
```

Observed result:

- Lean target file: pass
- Focused formal pytest: `1 passed in 9.08s`
- Proof placeholder scan: pass
- Lean module build: pass
- JSON validation: pass
- Public claim scope check: ok
- Claims registry check: ok
- Diff whitespace check: pass

## Artifact Hashes

- `lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean`:
  `7910a6708cf7ff77e3ca7c7a53f7acd012b1523a142f960d9efa4f3a22a4d115`
- `tests/formal/test_lean_ab_strict_zero_min_monotone.py`:
  `76aafdc2629d7cb3fc57e9121b1eb783ce3215e9f0b12e841fa02254e5ab280e`

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
