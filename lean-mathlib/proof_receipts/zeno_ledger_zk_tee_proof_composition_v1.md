# ZenoLedger ZK/TEE Proof Composition V1 Receipt

Date: 2026-05-15

## Accepted Artifact

`lean-mathlib/Proofs/ZenoLedgerZkTeeProofComposition.lean`

## Main Theorems

```text
ZenoLedgerZkTeeProofComposition.accepted_metadata_binds_header_roots
ZenoLedgerZkTeeProofComposition.accepted_metadata_unique_under_digest_injective
ZenoLedgerZkTeeProofComposition.apply_chunks_perm_invariant
```

The accepted theorem set covers three deterministic proof-composition facts:

- accepted proof metadata exposes the same pre-state, post-state, transaction,
  evidence, and body roots as the ZenoLedger header;
- two proof metadata objects bound to the same header are equal when the metadata
  digest is injective;
- pairwise-commuting proof chunks can be reordered without changing the final
  state.

The digest-injectivity premise is explicit. In the runtime, that premise is the
cryptographic and serialization obligation supplied by canonical metadata bytes
and hash collision resistance.

## Aristotle Review

Aristotle project:

```text
374e1b9f-402b-4465-958e-5d64de73e787
```

Returned status:

```text
COMPLETE_WITH_ERRORS
```

The returned `AristotleTask.lean` checked locally and had a clean Lean placeholder
scan. I accepted the recursive-chain witness theorem and chunk permutation
invariance structure, then strengthened the local repo artifact with the missing
runtime-style proof metadata binding and kind-specific fail-closed theorems.

## Replay

```bash
cd lean-mathlib
lake build Proofs.ZenoLedgerZkTeeProofComposition
lake build Proofs
```

Result: both passed locally on 2026-05-15.

Runtime replay for the corresponding metadata gate:

```bash
pytest -q tests/integration/test_zeno_ledger_v0.py tests/integration/test_zeno_ledger_verify_cli.py
```

Result: `70 passed in 665.62s` locally on 2026-05-15.

Trust scan:

```bash
rg -n '\b(sorry|admit|axiom|unsafe|sorryAx)\b' \
  lean-mathlib/Proofs/ZenoLedgerZkTeeProofComposition.lean \
  internal/aristotle_results/zenodex_zk_tee_math_v1/unpacked/zenodex_zk_tee_math_v1_aristotle/AristotleTask.lean
```

Result: no matches.

## Boundaries

This proof does not claim:

- RISC Zero, SP1, or any zkVM proof-system soundness;
- TEE hardware confidentiality or vendor attestation soundness;
- hash collision resistance;
- equivalence between the Rust guest and the full Python ZenoDEX runtime;
- complete privacy for settlement inputs;
- production validator-network readiness.

The in-repo claim is deterministic composition around public roots, metadata
binding, kind-specific fail-closed fields, and commuting chunk schedules.
