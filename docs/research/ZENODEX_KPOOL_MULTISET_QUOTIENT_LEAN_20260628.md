# ZenoDEX k-Pool Multiset Quotient Lean Proof

Date: 2026-06-28

## Summary

This artifact adds a Lean proof component for the k-pool multiset DP research
oracle. The oracle groups duplicate exact-in intent amounts and tracks
per-amount usage counts instead of a full identity bitmask.

The checked proof formalizes the identity-erasure condition:

```text
same (amount, allocation) trace -> same abstract final state and reward
```

For the modeled k-pool oracle, a transition may depend on current state, exact-in
amount, and k-way allocation. It may not depend on the identity of the intent.
Under that interface, swapping identities inside an equal-amount class preserves
the abstract run.

## Proved Component

The checked Lean file is:

```text
lean-mathlib/Proofs/KPoolMultisetQuotient.lean
```

Main theorem:

```text
runTrace_congr_sameStepKeys:
  SameStepKeys xs ys ->
  runTrace next reward state xs = runTrace next reward state ys
```

Supporting theorems:

- `equalAmount_identity_swap`: swapping only the identities of two equal-amount
  adjacent steps preserves the run.
- `identityErasure_preserves_trace`: final state and accumulated reward are both
  preserved.
- `witness_equalAmount_identity_swap`: non-vacuity witness for identity erasure.
- `witness_allocation_position_matters`: boundary witness showing allocation
  position is load-bearing.

## Why It Matters

The current k-pool multiset DP implementation already has bounded replay
evidence:

- k-pool subset DP vs k-pool multiset DP parity on duplicate-heavy cases.
- k-pool multiset DP vs brute force on small cases.
- Measured reductions in states, transitions, and ordering upper bound.

This Lean proof discharges the core representation-change obligation behind the
quotient: equal-amount intent identity does not affect an amount/allocation-only
transition trace.

## Non-Claims

This artifact does not prove the full Python implementation. It also does not
formalize:

- CPMM reserve arithmetic;
- split feasibility;
- per-user balances;
- heterogeneous `min_out` or deadlines;
- exact-out requests;
- canonical settlement materialization;
- production routing, settlement, governance, state-root, or promotion authority.

The proof is a reusable research component for the oracle model.

## Verification Receipts

Commands run from the repository root:

```bash
cd lean-mathlib && lake env lean Proofs/KPoolMultisetQuotient.lean
cd lean-mathlib && lake build Proofs.KPoolMultisetQuotient
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_kpool_multiset_quotient.py
python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/KPoolMultisetQuotient.lean
```

Expected result:

```text
Lean typecheck: pass
Lean module build: pass
pytest: pass
placeholder scan: no proof placeholders
```
