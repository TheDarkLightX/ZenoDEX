# ZRPF Atomic Settlement Store V1 CBC Specification

Date: 2026-07-12

Status: atomic transaction mechanics implemented and tested;
`settlement_authority=false`

## Scoped positive claim

`SQLiteZrpfAtomicSettlementStoreV1` demonstrates that one local SQLite
`BEGIN IMMEDIATE` transaction can atomically couple:

- the existing release-bound authenticated recursive-root replay admission;
- replay indexes for root, slot, child claims, receipts, and messages;
- one canonical `SettlementEffectPlanV1` commitment and canonical bytes;
- the plan pre-state and post-state roots;
- economic action IDs;
- ledger cell-write rows;
- asset-effect rows;
- action-binding authorization nullifiers;
- action-independent grant-spend nullifiers;
- message, carry, and reward rows;
- replay and settlement metadata compare-and-swap cursors.

The store has durable global unique indexes for economic actions, asset effects,
authorization nullifiers, grant-spend nullifiers, message IDs, carry IDs, and
reward IDs. A new plan requires exact caller-observed replay and settlement
cursors plus equality between its pre-state root and the settlement state root
read inside the serialized transaction.

This is transaction-kernel evidence. Every persisted metadata and plan row fixes:

```text
settlement_authority = false
authority_blocked_reason =
  semantic_v2_missing_exact_settlement_effect_plan_binding
```

SQLite constraints, typed receipts, and restart validation reject any attempt
to change those fields in V1.

## Missing proof-binding seam

The current Semantic Epoch V2 proposal authenticates:

```text
proof_tree_root
leaf_records_root
pre_state_roots_root
post_state_roots_root
transaction_roots_root
effect_roots_root
asset_delta_roots_root
source_claim_ids_root
semantic_source_ids_root
task_ids_root
dependency_manifest_root
semantic_epoch_root
```

It does not authenticate the exact Python settlement-plan commitment or these
plan-specific roots:

```text
economic_action_ids_root
ledger_cell_writes_root
authorization_nullifiers_root
authorization_grant_spend_nullifiers_root
message_effects_root
carry_effects_root
reward_effects_root
```

There is also no verified deterministic mapping from the current generic leaf
roots to the complete plan rows. Binding an arbitrary host plan to the existing
semantic receipt would create settlement authority from unauthenticated host
data.

`_bind_authenticated_settlement_commit_v1` therefore rejects every call with
the stable missing-binding reason. Production source defines no mint for the
sealed `_AuthenticatedSettlementCommitV1`. The dedicated test module alone uses
the private seal to construct `settlement_authority=false` inputs. Those markers
are manually minted fixtures, not independently verified receipt outputs.

## Authority flow

Current evidence flow:

```text
release-bound _AuthenticatedRecursiveStarkRootFacts
  + canonical SettlementEffectPlanV1
  + private test-only seal
    -> validate currently comparable root, epoch, policy, and message fields
    -> _AuthenticatedSettlementCommitV1(authority=false)
    -> BEGIN IMMEDIATE
    -> replay conflict evaluation
    -> expected replay cursor equality
    -> expected settlement cursor equality
    -> plan pre-state equals locked settlement state
    -> global economic-action and nullifier conflict evaluation
    -> persist replay rows and all plan rows
    -> replay metadata CAS
    -> settlement metadata CAS
    -> COMMIT
    -> data-only atomicity receipt(authority=false)
```

Required future authority flow:

```text
verified Semantic V3 receipt
  -> exact authenticated settlement-plan binding facts
  -> independently reconstruct SettlementEffectPlanV1
  -> exact plan commitment and every root equality
  -> sealed production settlement capability
  -> same atomic transaction kernel
```

The proof-neutral plan cannot call the mutating store path. The store exposes no
public `commit` or `commit_settlement` method. Its private transaction method
requires the exact sealed type and release-bound recursive-root provenance.

## Database profile

The combined evidence database uses its own application ID and schema. This
keeps the existing replay-only store, schema version, genesis hash, deterministic
vectors, and public claims unchanged. It reuses the replay planner and row
engine inside the same database transaction.

Every connection asserts:

```sql
PRAGMA foreign_keys = ON;
PRAGMA journal_mode = DELETE;
PRAGMA synchronous = EXTRA;
PRAGMA trusted_schema = OFF;
PRAGMA busy_timeout = 5000;
```

The governed settlement genesis state root is supplied when the store is
created, persisted separately from the replay-index genesis, and must match on
every reopen. The settlement cursor is:

```text
(revision, state_root, plan_count)
```

with `revision == plan_count`. Each successful new plan increments the replay
cursor and settlement cursor in one transaction. Exact retries recover the
original admission and settlement receipts without writing.

`COMMIT` precedes recovery of the data-only response. A process or response
failure in that interval can report an error after SQLite committed. The
recovery contract requires an exact retry; the stored root provenance and plan
commitment then return `IDEMPOTENT_REPLAY` with the original receipts.

The combined profile permits no admission-only history. Replay revision, root
count, settlement revision, and plan count must remain equal. Every plan stores
the corresponding admission revision, and startup plus each locked transaction
requires a one-to-one root-and-revision linkage. A split history fails closed
before conflict evaluation or new row insertion.

## Transaction ordering

Reject precedence for a new transaction is:

1. authenticated recursive-root policy and replay conflicts;
2. exact idempotent root, verifier provenance, and plan commitment recovery;
3. expected replay cursor equality;
4. expected settlement cursor equality;
5. plan pre-state equality with the locked settlement state;
6. duplicate economic action;
7. duplicate action-binding authorization nullifier;
8. duplicate grant-spend nullifier;
9. duplicate asset, message, carry, or reward effect identity;
10. row persistence and both metadata compare-and-swap updates.

Every planned rejection explicitly rolls back and returns both unchanged
cursors. Primary and unique constraints remain commit-time backstops.

## Restart validation

Store initialization takes `BEGIN EXCLUSIVE` and validates one stable snapshot.
It runs the existing full replay-history validator, then streams settlement plans
in dense revision order. For every plan it:

- verifies the previous-state link;
- rejects excessive JSON nesting, duplicate keys, floats, non-finite numbers,
  unknown fields, and noncanonical JSON bytes;
- reconstructs every typed V1 record and reruns the complete pure plan
  validator;
- recomputes every derived record ID, collection root, and the domain-separated
  plan commitment;
- compares every stored header root with the canonical plan;
- requires dense action and record ordinals;
- requires one settlement plan at the identical revision for every admission;
- compares every persisted canonical record with its plan record;
- compares stored record identifiers with canonical record identifiers;
- requires the final replayed post-state and count to equal settlement metadata;
- requires authority to remain false with the exact blocked reason.

This detects same-count mutation of plan bytes, record rows, state links, and
metadata on restart. It does not provide an external authenticity anchor or
rollback-resistant storage.

## Executed evidence requirements

The focused suite covers:

- one transaction containing every row family;
- persisted authority-false status and blocked reason;
- deterministic production-binding rejection;
- forged private-seal rejection before I/O;
- no public commit method;
- exact idempotent replay across restart;
- lost-response-after-commit recovery with a freshly constructed sealed test
  input;
- POSIX process exit after `COMMIT` and before response recovery, followed by
  exact idempotent retry;
- replay-cursor, settlement-cursor, and pre-state rejection as no-ops;
- global duplicate economic-action rejection;
- global duplicate grant-spend rejection across distinct actions;
- two SQLite writers from one version, with exactly one commit;
- injected failure after each of six transaction stages, with total rollback;
- restart rejection after canonical-plan, record-row, and metadata tampering;
- startup and locked-commit rejection of admission-only split history;
- stable typed rejection of malformed public receipt lookup input;
- a deterministic state-machine sequence with restart validation after every
  action;
- an architecture scan restricting private seal and constructor use to their
  definition and the dedicated test module.

## Explicit non-claims

This V1 kernel does not establish:

- a receipt-authenticated settlement-plan commitment;
- a production settlement capability;
- semantic correctness or canonical derivation of economic actions;
- proof that cell writes produce the post-state root;
- balance non-negativity or application-specific state validity;
- complete cross-language plan parity;
- data availability, schedule validity, carry continuity, or remote delivery;
- a deployed ZenoLedger state-tree update;
- hostile same-interpreter or same-UID resistance;
- storage rollback resistance;
- settlement, release, public, privacy, or production authority.

## Next promotion gate

Semantic V3 must journal the exact settlement-plan commitment and every
authority-relevant root, or journal enough canonical data for the guest and
outer verifier to derive those values without host discretion. A sealed
production binder may be added only after an actual receipt verifies that
surface under a governed program identity and manifest. The transaction kernel
must then apply or verify a ledger-native state-transition witness proving that
the committed cell writes transform the authenticated pre-state root into the
post-state root.
