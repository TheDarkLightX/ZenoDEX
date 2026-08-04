# FCIS M6 Task J07 Plan

TASK_ID: J07
BASE_SHA: 225e99f9fe862cb06818515c53666352a031ee5d
SOURCE_HEAD_SHA: cd29859c3c8604279c80fec5956f8dc9595ab359
SOURCE_HEAD_TREE: 75165d79a31a9d69066eec7e7b6b2677b8a8db28

## Objective

Implement an isolated authority-switch relation that consumes the J06
QUIESCED gate and a freshly used F06 migration authorization, then emits one
canonical successor with target-only writer authority and stale-token
rejection. Bind the live Tau writer-profile refinement through one independently
verified admission context and one complete V3 token.

## Scope

The slice covers:

- verifier-owned J07 pre/post authority contexts;
- exact phase and epoch transition from QUIESCED to AUTHORITY_SWITCH;
- canonical authority, snapshot, and head root derivation;
- unchanged current-state and deployment roots;
- explicit post-context carry-forward and pre/post predecessor binding;
- independently verified promotion, source-language, policy, verifier, and
  evidence coordinates;
- verifier-owned V3 writer tokens with point-of-use provenance checks;
- an exact Tau-profile receipt and writer-binding refinement into J07;
- hard 8,192-live-value admission/token registry capacities and weak-reference
  snapshot reclamation;
- bounded typed rejection paths;
- F06 migration authorization revalidation at switch use;
- independent switch and Tau writer-authority vectors, focused tests,
  deterministic property tests, and typed negative witnesses.

## Acceptance

The implementation must report `J07_AUTHORITY_SWITCH_MATCH`, the public
builder must reproduce both checked vectors, and the target writer must be the
only accepted post-switch profile. An old writer token, forged dependency,
mutated registered value, verifier-time context mutation, exhausted provenance
registry, or rejecting external verifier must fail closed with a typed result.

## Nonclaims

J07 does not implement a production transaction, database lock, process
barrier, runtime writer middleware, external verifier, rollback, accounting,
backing, cryptographic verifier authenticity, datastore currentness, or zUSD
safety theorem. M6 remains research-only, unmounted, and non-promotable.
