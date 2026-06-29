# ZenoDEX AB Strict Zero-Min Subset-Induction Host Table Lean Bridge - 2026-06-29

## Executive Result

The AB strict zero-min subset-induction work now has a Lean bridge theorem for
the bounded host table endpoint.

Research-only proof evidence; no settlement, state-root, production, or
governance authority.

## What The Lean Bridge Proves

`StrictSubsetInductionHostTable` packages a finite family of observed subset
masks, a selected winner, a fixed suffix, and data-only rails:

```text
packetHashBound = true
noAuthorityEffect = true
winnerMembershipBound = true
```

If every mask covers the declared bit range and satisfies local pruning, and if
the supplied winner dominates the selected family for the fixed suffix, then
`strictSubsetInductionHostTable_validates` proves:

- packet-hash bound rail is present;
- no-authority-effect rail is present;
- winner-membership bound rail is present;
- the winner covers every bit below `bitCount`;
- the full finite mask family is economically dominated by the selected winner
  at fixed executed input;
- the selected winner executes the suffix.

The dominance endpoint is:

```text
zeroMinEconomicKeyDominated
  (fullFrontierZeroMinEconomicKey executedInput initialReserveOut masks suffix)
  (selectedZeroMinEconomicKey executedInput initialReserveOut winner suffix)
```

The selected compressed winner has the same executed input and weakly better
zero-min final reserve-out key than the full finite frontier represented by the
host table.

## Relationship To The Host Oracle

The host oracle in
`tools/check_ab_strict_zero_min_subset_induction_witness.py` generated bounded
evidence over 180 strict cases, 4,464 masks, 85,284 records, and 212,760 suffix
checks. This Lean bridge consumes the same shape of evidence as assumptions:
finite mask family, local pruning, winner selection, suffix executability, and
authority rails.

This moves the evidence chain from a bounded Python witness toward a formal
endpoint theorem. The host checker still supplies the finite tables; Lean now
checks what follows from those tables.

## Theorems And Definitions Added

- `StrictSubsetInductionHostTable`
- `strictSubsetInductionHostTableValid`
- `strictSubsetInductionHostTable_validates`
- `witness_strictSubsetInductionHostTable_validates`

## Replay Commands

```bash
cd lean-mathlib && lake env lean Proofs/ABStrictZeroMinMonotone.lean
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_strict_zero_min_monotone.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABStrictZeroMinMonotone.lean
cd lean-mathlib && lake build Proofs.ABStrictZeroMinMonotone
```

## Verification Receipts

- Lean file check: pass
- Formal pytest guard: pass, `1 passed`
- Proof-placeholder scan: pass, `No proof placeholders found.`
- Lean module build: pass, `Build completed successfully (3076 jobs).`

## Non-Claims

- This is not a full Lean construction of the subset DP table.
- This does not prove Python-to-Lean refinement.
- This does not define canonical tie order.
- This does not cover nonzero `min_amount_out` batches.
- This does not turn the bounded stress corpus into exhaustive state coverage.
- This does not authorize settlement, state roots, production deployment, or
  governance execution.

## Value For ZenoDEX

The bridge narrows the highest-value AB-ordering breakthrough into a reusable
verification pattern: host search can enumerate finite certificates, while Lean
checks the economic dominance endpoint under explicit assumptions. That gives
ZenoDEX a clearer route from expensive brute-force exploration to certificate-
carrying exact solvers.
