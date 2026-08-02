# FCIS M6 Task J07 Plan

TASK_ID: J07
BASE_SHA: c8a861119e59701c96c9106ff4ba154f7b4650a2
SOURCE_HEAD_SHA: d40e2d7bc028d93c5f38f24b158567a9fff752fc
SOURCE_HEAD_TREE: 3e1c984da840c02854e7846362bcffc340e7981b

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
- explicit post-context carry-forward and pre/post predecessor binding;
- verifier-owned writer tokens with point-of-use provenance checks;
- bounded typed rejection paths;
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
