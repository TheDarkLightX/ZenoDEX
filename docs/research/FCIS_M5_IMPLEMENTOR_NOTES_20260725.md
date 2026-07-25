# FCIS M5 Implementor Notes

**Contract:** `zenodex/fcis-m5-atomic-mount/v2`  
**Date:** 2026-07-25  
**Validated source checkpoint:** `77a73c93dbd23729b743aa2fb46f0d62554c7578`  
**Pull request:** #488  
**Outcome:** `M5_PREREQUISITE_CHECKPOINT_ONLY`  
**Mount status:** `M5_BLOCKED_NO_AUTHORITY_SWITCH`

## What was completed

This checkpoint closes the missing M5 authority substrate without changing the
mounted runtime authority:

- exact immutable `AcceptV1 | RejectV1 | CommittedFailureV1` alternatives;
- an exact eight-field committed DEX state aggregate;
- canonical candidate, receipt, commit-plan, and commit-bundle roots;
- candidate identity that commits the pre-root, context, command, successor,
  patch, value plan, replay updates, receipt body, and raw outbox effects;
- same-candidate binding across state, patch, plan, receipt, replay, and outbox;
- ordinary rejection with no successor, plan, replay, or outbox fields;
- receipt-derived deterministic outbox idempotency identities whose receipt
  root is itself bound to every candidate artifact;
- defensive revalidation of nested root-bound payloads before publication,
  including hostile `frozen=True` bypass attempts;
- an immutable expected-pre-root compare-and-swap reference interpreter;
- replay compare-and-replace validation against both pre-state and successor;
- exact no-publication behavior for stale, malformed, duplicate, inconsistent
  replay, and injected pre-linearization crash paths;
- replay updates retained as per-bundle publication batches;
- a dedicated locked-dependency CI gate.

## Files

- `src/core/fcis_atomic_mount_values.py`
- `src/core/fcis_atomic_mount_codec.py`
- `src/integration/fcis_atomic_commit_reference.py`
- `tests/core/test_fcis_atomic_mount.py`
- `tests/core/test_fcis_atomic_mount_binding.py`
- `.github/workflows/fcis-m5-atomic.yml`
- `docs/research/FCIS_M5_P0_DRIFT_AUDIT_20260725.md`

## Selected design

The checkpoint uses a closed deterministic decision algebra in the functional
core and a root-bound transactional-outbox compare-and-swap command at the
shell boundary.

The core owns only exact immutable values and deterministic encoders. It does
not call storage, dispatch messages, consult time, allocate random identities,
or repair incomplete outputs. The reference shell revalidates the complete
bundle, compares `expected_pre_root`, validates replay compare-and-replace
preconditions, and constructs one complete immutable successor containing
state, receipt, replay batches, and outbox rows.

Candidate identity is deliberately broader than successor-state identity. Two
computations that reach the same state but produce different patches, plans,
receipts, replay updates, or outbox payloads receive different candidate roots.
This prevents cross-plan substitution and prevents different effect payloads
from sharing a receipt-derived idempotency key.

The reference model intentionally proves only functional semantics. It does not
claim production database linearizability, WAL durability, crash recovery,
external exactly-once delivery, or multi-process safety.

## Validation

GitHub Actions run `30160824360`, job `89685743943`, at source checkpoint
`77a73c93dbd23729b743aa2fb46f0d62554c7578`:

- locked development dependencies: pass;
- Ruff: pass;
- mypy: pass;
- base atomic-authority laws: pass;
- same-state artifact-substitution laws: pass;
- hostile nested-mutation revalidation: pass;
- replay compare-and-replace and repeated-account batch laws: pass.

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
