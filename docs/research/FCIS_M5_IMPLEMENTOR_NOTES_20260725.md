# FCIS M5 Implementor Notes

**Contract:** `zenodex/fcis-m5-atomic-mount/v2`  
**Date:** 2026-07-25  
**Validated source checkpoint:** `8f8e313bb951800a1d18ee221168a3935ab3f4ad`  
**Pull request:** #488  
**Outcome:** `M5_PREREQUISITE_CHECKPOINT_ONLY`  
**Mount status:** `M5_BLOCKED_NO_AUTHORITY_SWITCH`

## What was completed

This checkpoint closes the missing M5 authority substrate without changing the
mounted runtime authority:

- exact immutable `AcceptV1 | RejectV1 | CommittedFailureV1` alternatives;
- an exact eight-field committed DEX state aggregate;
- canonical candidate, receipt, commit-plan, and commit-bundle roots;
- same-candidate binding across state, patch, plan, receipt, replay, and outbox;
- ordinary rejection with no successor, plan, replay, or outbox fields;
- receipt-derived deterministic outbox idempotency identities;
- an immutable expected-pre-root compare-and-swap reference interpreter;
- exact no-publication behavior for stale, malformed, duplicate, and injected
  pre-linearization crash paths;
- replay updates retained as per-bundle publication batches;
- a dedicated locked-dependency CI gate.

## Files

- `src/core/fcis_atomic_mount_values.py`
- `src/core/fcis_atomic_mount_codec.py`
- `src/integration/fcis_atomic_commit_reference.py`
- `tests/core/test_fcis_atomic_mount.py`
- `.github/workflows/fcis-m5-atomic.yml`
- `docs/research/FCIS_M5_P0_DRIFT_AUDIT_20260725.md`

## Selected design

The checkpoint uses a closed deterministic decision algebra in the functional
core and a root-bound transactional-outbox compare-and-swap command at the
shell boundary.

The core owns only exact immutable values and deterministic encoders. It does
not call storage, dispatch messages, consult time, allocate random identities,
or repair incomplete outputs. The reference shell revalidates the complete
bundle, compares `expected_pre_root`, and constructs one complete immutable
successor containing state, receipt, replay batches, and outbox rows.

The reference model intentionally proves only functional semantics. It does not
claim production database linearizability, WAL durability, crash recovery,
external exactly-once delivery, or multi-process safety.

## Validation

GitHub Actions run `30160353798`, job `89684561981`:

- locked development dependencies: pass;
- Ruff: pass;
- mypy: pass;
- `tests/core/test_fcis_atomic_mount.py`: pass.

The source checkpoint was also mergeable as a stacked draft against
`agent/fcis-pr454-reviewed-port-20260723`.

## Why authority was not switched

The reviewed handoff requires a stop when any mount prerequisite is incomplete.
The current support-root v5 profile is not promotion-ready because it does not
yet prove complete explicit presence/absence semantics and complete touched
state coverage for all spot actions. Fee-accumulator/context support, verifier
and proof-guest migration, golden vectors, exact Python/Rust refinement, and a
real datastore implementation with crash evidence also remain open.

No changes were made to the mounted `DexState`, production evaluator, support
root version, verifier authority, or runtime publication path.

## Next required closure work

1. Replace sparse omission with an explicit presence/absence support encoding.
2. Complete recipient and LP-cell support for swap, create-pool, and
   remove-liquidity paths.
3. Commit every consulted fee/context cell or remove the dependency.
4. Build the exact M4-evaluator-to-M5-decision adapter.
5. Implement canonical M5 bundle/decision codecs in Rust and prove parity.
6. Migrate verifiers/proof guests and publish golden vectors.
7. Implement one real transactional commit port and produce stale-root,
   rollback, crash-recovery, concurrency, and retry evidence.
8. Repeat independent adversarial review before any authority switch.

## Final checkpoint statement

`M5_PREREQUISITE_CHECKPOINT_ONLY`

The M5 design is materially implemented and validated, but production authority
remains deliberately unchanged until the remaining proof and persistence
obligations are closed.
