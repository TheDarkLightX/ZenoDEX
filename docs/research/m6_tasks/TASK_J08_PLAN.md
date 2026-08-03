# FCIS M6 Task J08 Plan

TASK_ID: J08
BASE_SHA: b72aa9d997e7cfb5db49e8ea91dcebba2a1f2193
SOURCE_HEAD_SHA: d92c98fd9911741c2be6a3a1af9d7d1ff1bccbb3
SOURCE_HEAD_TREE: f409c5381210827160a016f9eec78755b3f4690c

## Objective

Define a verifier-gated rollback relation that restores a complete authorized
state without erasing history or reviving the pre-switch authority token.

## Scope

The slice covers:

- verifier-owned complete state aggregates;
- source and pre-switch anchor binding to J07;
- preservation of state, deployment, residual, nullifier, outbox, and effect
  identity roots;
- append-only rollback history commitment;
- exact authority epoch advance and POST_SWITCH_VALIDATION target;
- empty target writer set and fresh-authorization latch;
- typed rejection of balance-only, partial, stale, malformed, and unbounded
  rollback inputs;
- independent vector, focused tests, deterministic property tests, and
  negative witnesses.

## Acceptance

The implementation must report `J08_ROLLBACK_MATCH`, reproduce the public
vector, restore every complete-state root from the anchor, change the history
root through a canonical rollback commitment, advance the authority epoch
once, and expose no value-moving capability.

## Nonclaims

J08 does not implement a production rollback transaction, datastore recovery,
filesystem durability, external complete-state authentication, runtime writer
middleware, deployment migration, accounting, backing, or zUSD safety. M6
remains research-only, unmounted, and non-promotable.
