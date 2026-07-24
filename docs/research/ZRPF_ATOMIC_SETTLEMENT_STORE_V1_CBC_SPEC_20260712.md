# ZRPF Atomic Settlement Store V1 CBC Specification

Date: 2026-07-12

Status: atomic transaction mechanics and the source-opened Spot V6 association
implemented and tested; final retained V6 proof evidence pending;
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

## Source-opened Spot V6 extension

The schema V4 extension closes the receipt-to-plan association for one bounded
source-opened ordinary Spot profile. The implemented authenticated path is:

```text
exact settlement receipt bytes + exact settlement guest-input bytes
  -> pinned Rust verifier executes once
  -> settlement image, profile, manifest, and journal authenticate
  -> exact guest input independently recomposes the expected journal
  -> strict Python decoder checks the same ZRPFSAV1 frame
  -> private _AuthenticatedSourceOpenedSpotV6SettlementV1
  -> one BEGIN IMMEDIATE transaction
```

That transaction persists the exact settlement receipt, guest input,
settlement-admission journal, reconstructed source-opened replay blob,
full-blob content certificate, settlement certificate, effect plan, governed
program identities, receipt-security identities, Python execution projection,
projection binding, and all replay and nullifier rows. Restart validation
rehashes and redecodes those artifacts and rederives their associations.

The V6 journal authenticates the exact settlement certificate and exact effect
plan used by this singleton ordinary Spot profile. This closes the former
host-selected-plan seam for that profile only. It does not prove that a live
ZenoLedger balance tree was read or mutated, and every durable result continues
to fix `settlement_authority=false`.

## Legacy Semantic V2 proof-binding seam

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

The source-opened Spot V6 path does not use this legacy binder. Its dedicated
settlement guest derives the plan and commits it inside the fixed admission
journal, and its sealed Rust and Python verifiers reconstruct that journal from
the exact guest input. Other profiles remain blocked until they obtain an
equivalent receipt-authenticated mapping.

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

Implemented bounded V6 flow:

```text
verified source-opened Spot settlement V6 receipt
  -> exact guest-input recomposition
  -> authenticated ZRPFSAV1 certificate-and-plan journal
  -> private Python V6 association
  -> atomic exact-artifact, replay, projection, and effect-plan persistence
  -> data-only receipt(settlement_authority=false)
```

The proof-neutral plan cannot call the mutating store path. The store exposes no
public `commit` or `commit_settlement` method. Its legacy private transaction
method requires the exact sealed type and release-bound recursive-root
provenance. The V6 private method additionally requires the exact sealed
source-opened verifier result and its receipt, guest-input, admission-journal,
content-certificate, replay, and projection bindings.

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

Schema V4 also maintains a monotonic source-opened association count. Migration
to V4 rejects any database with prior certificate history because that history
cannot be retroactively associated with exact receipt and guest-input bytes.
New V6 rows must preserve a one-to-one association among the receipt, admission
journal, replay blob, content certificate, certificate, plan, projection, and
the admitted root.

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

The V6 extension additionally covers exact external-verifier request and
response framing, independent admission-journal decoding, projection binding,
concurrent commit behavior, exact retry, restart reconstruction, deletion
downgrade rejection, and mutation of every persisted proof-association
artifact. These tests establish local transactional and binding behavior. The
final retained real-proof evidence remains a separate promotion gate.

## Explicit non-claims

This V1 kernel and its V4 source-opened extension do not establish:

- a receipt-authenticated settlement-plan commitment for profiles other than
  the bounded source-opened ordinary Spot V6 profile;
- a production settlement capability;
- semantic correctness or canonical derivation of economic actions;
- proof that the persisted cell writes mutate a live ledger from the committed
  pre-state root to the committed post-state root;
- balance non-negativity or application-specific state validity;
- complete cross-language plan parity;
- provider retrievability, externally governed data availability, schedule
  validity, carry continuity, or remote delivery;
- a deployed ZenoLedger state-tree update;
- hostile same-interpreter or same-UID resistance;
- storage rollback resistance;
- external finality or governed release authorization;
- settlement, release, public, privacy, or production authority.

## Next promotion gate

Every additional semantic profile must journal the exact settlement-plan
commitment and every authority-relevant root, or journal enough canonical data
for the guest and outer verifier to derive those values without host
discretion. The source-opened Spot V6 profile implements that bounded binding;
its checked retained proof record remains pending. Promotion to settlement
authority additionally requires a ledger-native transition that atomically
applies or verifies the committed cell writes against the live authenticated
pre-state, advances the live post-state, consumes live authorization grants,
and binds governed release and external finality policy.
