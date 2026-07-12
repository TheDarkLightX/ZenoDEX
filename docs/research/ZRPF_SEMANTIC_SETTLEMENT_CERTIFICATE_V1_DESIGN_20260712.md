# ZRPF Semantic Settlement Certificate V1 Design

Date: 2026-07-12

Status: proof-neutral action batch and SettlementEffectPlanV2 implemented and
host-tested; proof-neutral ordinary Spot effect projection implemented; guest,
receipt, and ledger authority pending

## Goal and bounded domain

The target is one authority-bearing receipt for at most 64 canonical economic
actions represented by one bounded ZRPF semantic root. The receipt must bind
the exact action identities, grant-spend nullifiers, application-state
transition, conserved asset effects, messages, carry records, rewards, proof
program, receipt-security profile, and release manifest required by the atomic
ZenoLedger commit.

The initial bounded profile is:

```text
economic actions              1..=64
cell writes                   1..=8,192
asset effects                 1..=8,192
messages, carries, rewards    0..=8,192 each
amount arithmetic             checked u128
epoch and authorization nonce u64
```

## Candidate ranking

1. A separate settlement-certificate guest verifies one exact Semantic V2 or
   Value V4 receipt, decodes canonical economic actions and strictly ordered
   settlement rows, recomputes every root, and emits one settlement
   certificate. This keeps the established structural and semantic receipts
   stable and gives the ledger one exact authority object.
2. Extending the existing Semantic V2 journal with settlement fields creates a
   smaller proof stack, while coupling structural aggregation, value semantics,
   and ledger effect semantics into one guest revision. Existing V2 receipts
   and source-built evidence would all change.
3. A host-only binder cannot establish authority. Semantic V2 does not commit
   the action batch, grant-spend set, exact writes, messages, carries, rewards,
   or complete plan commitment.

Candidate 1 is selected. Candidate 3 is forbidden as a settlement path.

## Required proof-neutral objects

### EconomicActionBatchV1

The implemented batch supplies:

```text
application_id
chain_or_domain_id
epoch_id
pre_state_root
action_ids_root
authorized_actions_root
action_authorization_bindings_root
authorization_grant_spends_root
effect_commitments_root
consumed_object_ids_root
batch_commitment
```

It rejects duplicate actions, grant-and-nonce spends, and consumed objects
repeated anywhere within the proposed batch before that batch exists. Durable
cross-batch uniqueness remains a ledger obligation.

### SettlementEffectPlanV2

V2 supplies a cross-language deterministic order and canonical byte encoding
for one already-selected typed row set. The existing Python
`SettlementEffectPlanV1` remains an authority-neutral reference until it is
replaced by a byte-for-byte mirror of V2. V2 does not yet normalize distinct
row partitions that represent the same application-level effect.

V2 contains the exact `EconomicActionBatchV1`, derives its application,
domain, epoch, pre-state, action identities, action-bound authorization
identities, and grant-spend identities from that batch, and accepts only these
additional fields:

```text
source_semantic_journal_hash
public_policy_hash
post_state_root
strictly ordered ledger cell writes
strictly ordered asset effects
strictly ordered cross-domain messages
strictly ordered carry records
strictly ordered reward records
```

Caller-supplied duplicate projections of application, domain, action,
authorization, or pre-state are prohibited.

Referenceable row identifiers must be derived from every semantic field using
fixed-width domain-separated SHA-256. Exact bounded Postcard decoding must
reject trailing bytes, nonminimal encodings, oversized sequence claims,
unknown fields, invalid enums, and any derived-root substitution.

The constructor must establish:

```text
all rows reference one batch action
every action has at least one write and one asset effect
one cell key is written at most once
ordinary transfers carry no supply authority material
mint, burn, and reward rows use the action's exact authorization binding
one authorization binding backs at most one authorized effect
per-asset debit + authorized mint = credit + authorized burn
message and carry rows pair exactly and use dedicated balanced ordinary-transfer
backing effects whose debit and credit both equal the message amount
reward rows pair exactly with one typed funded effect and recipient write
all u128 accumulation is checked
pre_state_root comes from the batch
post_state_root is nonzero and different
```

The plan commitment binds the complete encoded plan, every collection root,
and the exact economic-action batch commitment.

### Canonicality and effect-commitment boundary

Current canonicality is syntactic and order-level:

```text
same header + economic-action batch + validated typed row multiset
  -> same strict row order
  -> same collection roots
  -> same exact Postcard bytes and plan commitment
```

It does not currently establish semantic normal form. In particular:

- one ordinary row of ten atoms and two ordinary rows of four and six atoms
  can encode the same aggregate flow with different plan commitments;
- one fixed `EconomicActionBatchV1` can be paired with more than one internally
  valid settlement row set;
- an action record's opaque `effect_commitment` is committed by the batch, but
  V2 does not derive it from or compare it with the action's settlement rows.

The last point cannot be closed by hashing the existing rows generically:
settlement rows reference `economic_action_id`, while that action ID already
contains `effect_commitment`. A generic derivation would be circular. Each
authority-bearing application profile must instead define a non-circular
effect projection or normal form, prove that it matches the authenticated
action semantics, and reject alternative row partitions. Until that profile
exists, effect-commitment correspondence and semantic row normalization remain
settlement blockers.

The ordinary Spot V1 projection is the first closed application profile. It
derives one aggregate action, one lane-state write, and one balanced ordinary
effect per asset from an exact Value Aggregate V5 proposal. It rejects
issuance, destruction, messages, carries, and rewards. Supply-changing and
cross-domain profiles remain separate obligations.

Construction remains proof-neutral. V2 does not establish that applying the
cell writes to an authenticated state tree produces `post_state_root`, that a
recipient cell encodes the stated reward amount, that an authorization grant
exists in governed policy, that an action's `effect_commitment` matches its
settlement rows, that equivalent row partitions have one semantic normal form,
or that any source semantic receipt authenticated the plan. Those are
certificate-guest, application-profile, and ledger obligations.

The implemented V2 profile uses fixed-width domain-separated SHA-256 for every
referenceable record, collection root, and plan commitment. It uses a bounded
exact Postcard codec. The retained ordinary-transfer fixture derives:

```text
settlement_effect_plan_v2 =
da34e94f4a45ca88957e1a403d36c650b3addbf901e0aa2a785d19ffb706bd75
```

## Settlement-certificate guest

The guest authority progression is:

```text
bounded raw input
  -> verify exact governed semantic/value receipt assumption
  -> decode its exact canonical journal
  -> decode SettlementEffectPlanV2
  -> obtain and revalidate its embedded EconomicActionBatchV1
  -> require plan source hash, scope, epoch, pre/post/effect roots to match the
     authenticated semantic/value journal under one explicit profile adapter
  -> derive governed release/program manifest
  -> emit SettlementEpochCertificateV1
```

The guest must verify the receipt before decoding or interpreting its journal.
The source-profile adapter must be a closed enum. An unrecognized semantic
profile rejects without fallback.

## SettlementEpochCertificateV1

The proof-neutral journal contains:

```text
certificate_version
application_id
chain_or_domain_id
epoch_id
semantic_profile_id
semantic_journal_hash
semantic_claim_binding
proof_tree_root
semantic_epoch_root or value_subtree_root
economic_action_batch_commitment
economic_action_ids_root
action_authorization_bindings_root
authorization_grant_spends_root
consumed_object_ids_root
settlement_effect_plan_commitment
pre_state_root
post_state_root
cell_writes_root
asset_effects_root
messages_root
carries_root
rewards_root
public_policy_hash
data_availability_certificate_root
schedule_certificate_root
carry_continuity_certificate_root
dependency_manifest_root
```

Runtime program identity remains outside this proof-neutral journal. The sealed
host verifier attaches the actual verified image ID, receipt-security profile,
verifier parameters, and full governed program manifest after cryptographic
verification.

## Ledger authority boundary

Only a sealed `VerifiedSettlementEpochReceiptV1` may mint the private
settlement-commit capability. The SQLite/ZenoLedger transaction then requires:

```text
current state version and root == certificate pre-state
governed epoch progression
unique semantic/root receipt identities
unique economic action IDs
unique action-bound authorization identities
unique grant-spend nullifiers
unique consumed objects and message IDs
exact plan commitment and resulting post-state root
```

One serializable transaction commits replay indexes, cell writes, value
effects, messages, carries, rewards, and the new state/version. Any uniqueness,
CAS, storage, or effect failure rolls back the complete transaction.

## Proof obligations and negative controls

Required negatives include:

1. valid semantic receipt with a substituted action batch;
2. valid action batch with a substituted settlement plan;
3. two encodings of one action;
4. one grant nonce reused by two distinct actions;
5. one consumed object reused across subtrees;
6. one-atom conservation failure;
7. pre-state, post-state, policy, epoch, or domain relabeling;
8. wrong semantic image, profile, manifest, or receipt-security parameters;
9. exact settlement receipt seal mutation;
10. two concurrent ledger commits from one pre-state;
11. failure injection after every persistence stage;
12. DA, schedule, or carry certificate omission and substitution.

Each mutation must reject at its named boundary and must not advance ledger
state.

## Performance targets

The reference implementation remains bounded and direct. Measure:

```text
encoded action-batch bytes
encoded plan bytes
guest cycles and peak memory
receipt generation and verification latency
certificate bytes
SQLite commit latency
64-action worst-case row counts
```

The first acceptance target is one full 64-action certificate within declared
memory and byte limits. Recursive accumulator replacement is a later scaling
profile and cannot weaken this direct reference oracle.

## Explicit non-claims

This design document supplies no receipt, image ID, proof, ledger authority,
DA result, schedule result, carry-continuity result, action-to-effect
correspondence, semantic row-normalization result, source finality, release
authority, settlement authority, privacy claim, throughput result, or
production claim.

Promotion requires the implemented protocol and guest, current-image proof
evidence, sealed verifier, atomic ledger tests, governed release binding, and
the exact negative controls above.

## Executed protocol evidence

The proof-neutral implementation currently covers deterministic ordering and
canonical bytes for a fixed row set, independent hash-preimage reconstruction,
within-batch action and consumed-object duplicate rejection, authorization
matching, mint and burn shape, reward binding, checked per-asset conservation,
dedicated balanced ordinary-transfer message/carry pairing, permutation
invariance, exact codec rejection, oversized declared row sets, and record-level
decode revalidation. Minimized tests retain the detached action-effect
commitment and row-partition alias cases as explicit pending non-authority
evidence.

Run from `zk/zrpf_protocol`:

```bash
cargo +1.94.1 fmt --all -- --check
cargo +1.94.1 test --locked --offline --all-targets
cargo +1.94.1 clippy --locked --offline --all-targets -- -D warnings
cargo +1.94.1 test --locked --offline --doc
```

These commands establish deterministic host behavior for the proof-neutral
types. They do not establish guest execution or receipt authority.
