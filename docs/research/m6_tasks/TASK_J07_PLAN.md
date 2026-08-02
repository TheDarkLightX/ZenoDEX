# FCIS M6 Task J07 Plan

TASK_ID: J07
BASE_SHA: 1d6f4441ada8baec64c8768985e552b97ee6dc65
SOURCE_HEAD_SHA: 006e2507748d0de0525d636fdbb648b1f7f2f1e9
SOURCE_HEAD_TREE: 676590e5899ef150ed8aae476d66305023f92f58

## Objective

Implement an isolated authority-switch relation that consumes the J06
QUIESCED gate and a freshly used F06 migration authorization, then emits one
canonical successor with target-only writer authority and stale-token
rejection.

## Scope

The slice covers:

- verifier-owned J07 pre/post authority contexts;
- exact phase and epoch transition from QUIESCED to AUTHORITY_SWITCH;
- canonical authority, snapshot, and head root derivation;
- unchanged current-state and deployment roots;
- verifier-owned writer tokens with point-of-use provenance checks;
- F06 migration authorization revalidation at switch use;
- independent vector, focused tests, deterministic property tests, and typed
  negative witnesses.

## Acceptance

The implementation must report `J07_AUTHORITY_SWITCH_MATCH`, the public
builder must reproduce the checked vector, and the target writer must be the
only accepted post-switch profile. An old writer token, forged dependency,
mutated registered value, or rejecting external verifier must fail closed.

## Nonclaims

J07 does not implement a production transaction, database lock, process
barrier, runtime writer middleware, external verifier, rollback, accounting,
backing, or zUSD safety theorem. M6 remains research-only, unmounted, and
non-promotable.
