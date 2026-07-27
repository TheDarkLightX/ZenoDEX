# M5-P4B0 Test Matrix

Every ID below requires an executable test. Property tests must use fixed,
reported seeds. Mutation tests must recompute artifact hashes after mutation so
semantic validation, rather than the outer hash, kills the mutant.

| Test ID | Requirement | Required evidence |
| --- | --- | --- |
| `P4B0-INPUT-001` | P4B0-001 | Exact baseline, differential, source, command, state, and context hashes are retained in each typed observation. |
| `P4B0-PARSE-001` | P4B0-002 | Duplicate keys, BOM, trailing bytes, whitespace/key-order aliases, floats, exponent numbers, negative zero, and invalid Unicode reject. |
| `P4B0-PARSE-002` | P4B0-002 | Accepted bytes consume fully and satisfy `encode(decode(b)) == b`. |
| `P4B0-ADMIT-001` | P4B0-003 | Every observation is admitted by `admit(declared_schema, value, path, context)`. |
| `P4B0-ADMIT-002` | P4B0-003 | Static mutation inserts hand-written parallel validation; contract checker rejects it. |
| `P4B0-IMMUT-001` | P4B0-004 | Caller mutation, subclass substitution, nested `object.__setattr__`, and retained-alias attacks cannot alter admitted observations or witnesses. |
| `P4B0-POLICY-001` | P4B0-005 | Policy registry is closed, source-owned, uniquely keyed, versioned, and hash-bound. |
| `P4B0-POLICY-002` | P4B0-005 | Artifact-supplied policy, wildcard path, or constructor selector rejects. |
| `P4B0-INPUT-002` | P4B0-006 | Mutate command bytes/hash, pre-state bytes/root, or context bytes/hash on one side only; each rejects before refinement. |
| `P4B0-RESULT-001` | P4B0-007 | Accept/reject mismatch returns a stable `MismatchV1`, independent of iteration order. |
| `P4B0-REJECT-001` | P4B0-008 | Every frozen rejection fixture exercises an explicit code, phase, precedence, path, and reason mapping. |
| `P4B0-REJECT-002` | P4B0-008 | Change code/path/precedence/reason or add any committable output to exact rejection; each mutation fails. |
| `P4B0-STATE-001` | P4B0-009 | Accepted legacy and FCIS semantic projections compare all eight state fields. |
| `P4B0-STATE-002` | P4B0-009 | Mutate each state field separately while retaining or recomputing the outer root; every mutation fails. |
| `P4B0-ECON-001` | P4B0-010 | Mutate ordered fills/events, balances, reserves, LP changes, fees, dust, fee allocation, or nonce result; every mutation fails. |
| `P4B0-PATCH-001` | P4B0-011 | Applying the exact patch to the exact pre-state produces the exact successor projection. |
| `P4B0-PATCH-002` | P4B0-011 | Stale expected-old, duplicate key, reordered op, missing op, extra op, and partial application fail atomically. |
| `P4B0-BUNDLE-001` | P4B0-012 | Receipt and bundle roots are recomputed and bind all candidate components. |
| `P4B0-BUNDLE-002` | P4B0-012 | Cross-candidate substitution for state, plan, receipt, replay, outbox, or cached root fails. |
| `P4B0-OUTBOX-001` | P4B0-013 | Reorder, delete, duplicate, or mutate an outbox record or idempotency key; every mutation fails. |
| `P4B0-REPLAY-001` | P4B0-013 | Replay/nullifier changes equal the accepted command set and successor nonce state. |
| `P4B0-VERSION-001` | P4B0-014 | Every accepted version delta is an exact entry in the source-owned policy and witness. |
| `P4B0-VERSION-002` | P4B0-014 | Unknown algorithm/schema/codec/snapshot/support/policy version fails closed. |
| `P4B0-UNKNOWN-001` | P4B0-015 | Unknown command, reject code, field, status, or observation variant returns `InvalidEvidenceV1`. |
| `P4B0-UNKNOWN-002` | P4B0-015 | Duplicate or omitted registry entry fails the structural checker. |
| `P4B0-BUDGET-001` | P4B0-016 | Boundary values at limit and limit plus one for every resource bound. |
| `P4B0-BUDGET-002` | P4B0-016 | Cyclic, deep, wide, and oversized evidence rejects with stable typed codes and no partial witness. |
| `P4B0-DETERMINISM-001` | P4B0-017 | Two clean generations at one head produce byte-identical artifacts and policy hashes. |
| `P4B0-MUTANTS-001` | P4B0-018 | Named mutation ledger records every mutant above as killed by a specific test ID. |
| `P4B0-NOMOUNT-001` | P4B0-019 | Diff from required ancestor contains no mounted runtime, configuration, verifier, Rust, Tau, or proof-guest changes. |
| `P4B0-NOMOUNT-002` | P4B0-019 | New modules have no import path from `src/core/dex.py` or mounted integration dispatch. |
| `P4B0-GATE-001` | P4B0-020 | Structurally valid artifact with mismatches passes normal validation and reports `BLOCKED`. |
| `P4B0-GATE-002` | P4B0-020 | `--require-all-refine` fails unless every frozen fixture refines; it never switches authority. |

## Mandatory independent attacks

The reviewer will run these without using the implementor's helper mutations:

1. Swap exact observations between two fixtures while retaining fixture IDs.
2. Change one context byte and recompute its hash.
3. Change a rejection code while preserving its public reason.
4. Change effects while retaining next-state bytes and root.
5. Change one semantic state field and recompute the representation root.
6. Apply a patch from decision A to pre-state B.
7. Substitute receipt A into bundle B and recompute the cached bundle root.
8. Reorder outbox records and recompute the outbox root.
9. Add a wildcard entry to the policy registry.
10. Add one new `IntentKind` without a refinement registry entry.
11. Mark one mismatch `RefinesV1` only in the generated JSON.
12. Modify `src/core/dex.py` after evidence generation.
