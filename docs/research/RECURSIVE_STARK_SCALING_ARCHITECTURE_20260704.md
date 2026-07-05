# Recursive STARK Scaling Architecture

Date: 2026-07-04
Status: experimental design specification

## Claim Scope

This note specifies a target architecture for using recursive proof aggregation
to scale ZenoDEX and ZenoLedger. It is a design artifact, not an implementation
claim.

Existing repo artifacts already cover local pieces:

- `config/proof_profiles/zeno_ledger_profiles.json` names
  `recursive_block_v1`.
- `docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json` lists
  `recursive_epoch_real_proof` as an explicit gap.
- `docs/research/SHARDED_SETTLEMENT_CERTIFICATE_20260701.md` defines a
  shard-level certificate shape.
- `docs/research/CROSS_SHARD_GLOBAL_CONSERVATION_RECEIPT_20260701.md` defines
  a deterministic global conservation receipt.
- `lean-mathlib/Proofs/CrossShardAtomicSettlement.lean` models atomic
  cross-shard settlement.
- `docs/zenodex_spot_state_proof_risc0_v1.md` defines the current spot Risc0
  state-proof lane.

The missing layer is a proof tree that turns many local receipts into one root
proof whose public journal is cheap enough for Tau/ZenoLedger validators and
wallet light clients to check.

## Goal

Scale verification from:

```text
verify many shard/batch/market proofs
```

to:

```text
verify one recursive root proof
```

without weakening the authority boundary:

```text
Local proofs prove local transitions.
Recursive aggregation proves proof validity and composition.
ZenoLedger/Tau accepts only the root journal if every public binding matches.
```

## Non-Goals

This design does not solve:

- data availability by itself;
- production validator finality;
- sequencer fairness or censorship resistance;
- oracle truth;
- cross-chain bridge finality;
- prover decentralization economics;
- complete spot/perps/zUSD proof coverage.

Those must remain explicit profile gaps until separately implemented.

## Architecture

```text
             shard / market execution
                     |
        +------------+-------------+
        |                          |
  Leaf proof 0                Leaf proof n
  spot/perps/oracle/...       spot/perps/oracle/...
        |                          |
        +------------+-------------+
                     |
              aggregation proof
          verifies child proofs and
          composes their journals
                     |
              recursive root proof
                     |
           ZenoLedger / Tau verifier
```

The root proof does not re-execute every transaction. It verifies child proofs
and checks that their public outputs compose into one globally valid epoch or
block transition.

## Correct-By-Construction Circuit Quality

Circuit quality is a statement-construction problem. Reviews, tests, and proof
smokes are evidence layers; they are not the primary defense. The primary
defense is to make unsupported proof statements impossible to express in the
production profile.

Every recursive proof lane must follow this contract:

```text
TypedStatement
  -> deterministic witness builder
  -> guest verifier checks the witness
  -> canonical journal
  -> host/Tau/ZenoLedger verifies proof, image ID, journal hash, and metadata
```

The host may propose witnesses. The guest must verify every claim-relevant
witness field. A witness field is acceptable only if it is:

- checked inside the guest;
- committed in the journal and checked by an outer verifier;
- domain-separated and included in a public root;
- irrelevant to the public statement by a documented proof obligation.

Any other private witness field is an unconstrained input and must be rejected
from the production profile.

### Construction Rules

Use typed statement objects instead of ad hoc JSON or loosely interpreted
metadata. The statement type for a leaf or recursive node must include:

- `domain_separator`;
- `schema_version`;
- `chain_id`;
- `epoch_id` or bounded height range;
- `proof_profile`;
- expected RISC0 image ID or verifier ID;
- feature, policy, dependency, and toolchain lock hashes;
- pre-state and post-state roots;
- input roots, evidence roots, receipt roots, and data-availability roots;
- bounded row counts for deltas, messages, receipts, and children.

The constructor for that statement type must reject:

- unknown critical fields;
- missing required roots;
- all-zero image IDs or verifier IDs;
- ambiguous defaults;
- unsorted rows;
- duplicate IDs;
- row counts above the configured bound;
- cross-domain replay attempts;
- proof-profile mismatches.

If a field affects acceptance, ordering, conservation, authority, or replay, it
must be part of the statement hash or a root committed by the statement hash.

### RISC0-Specific Gates

RISC0 proof generation is not verification. The production verifier must check:

```text
receipt.verify(expected_image_id)
journal.risc0_image_id == expected_image_id
hash(canonical_journal) == expected_journal_hash
proof_profile == expected_profile
metadata roots == journal roots == block/header roots
```

Recursive composition must verify child proofs in the guest. The intended RISC0
shape is:

```text
host:  add child receipts as assumptions
guest: env::verify(child_image_id, child_journal_digest)
guest: decode child journal only after verification
guest: compose EffectSummaryV1 values
guest: commit RecursiveEpochJournalV1
```

Child journal bytes without in-guest receipt verification are only data. They do
not carry proof authority.

The production profile must forbid:

- RISC0 dev mode;
- placeholder ELF or all-zero image IDs;
- implicit default prover options;
- unversioned receipt kinds;
- accepting a `Composite`, `Succinct`, or `Groth16` receipt under the wrong
  declared profile;
- proving under one method ID and reporting another;
- root aggregation over child proofs whose verifier IDs are absent from
  `verifier_set_root`.

The receipt profile should be explicit at the CLI and metadata boundary:

```text
composite: fast local development and large local receipts
succinct: recursive aggregation and constant-size STARK receipt lane
groth16: on-chain EVM-style verifier target, if used by an adapter
```

### Verifier/Prover Separation

Keep the prover path and verifier path separate.

The prover path may:

- search schedules;
- build witnesses;
- choose shard partitions;
- produce child proofs;
- build recursive assumptions.

The verifier path must:

- parse bounded typed statements;
- verify proof/image/journal bindings;
- recompute all public roots;
- enforce conservation, exact-once, and authority rules;
- reject unsupported shapes with stable typed reasons;
- leave state unchanged on reject.

No host-side witness builder may be the only place where a safety property is
checked. If the guest cannot check it, the journal must expose a certificate
that an outer deterministic verifier checks before admission.

### Circuit Quality Test Matrix

Every circuit, journal, verifier, or CLI parser change must add focused
negative tests for the relevant rows below.

| Bug class | Required reject test |
| --- | --- |
| wrong method | proof generated with unexpected image ID |
| journal swap | valid proof paired with another journal hash |
| stale verifier | child verifier ID absent from `verifier_set_root` |
| profile confusion | receipt kind does not match declared profile |
| dev profile leak | dev-mode or placeholder proof accepted |
| cross-domain replay | correct proof under wrong chain/config/domain |
| stale epoch | child epoch differs from root epoch |
| missing child | recursive proof claims children but omits one receipt |
| child substitution | one child proof replaced by another valid proof |
| duplicate receipt | same accepted receipt appears twice |
| duplicate message | same cross-shard message appears twice |
| unbalanced asset delta | aggregate debit/credit equality fails |
| unauthorized mint/burn | nonzero mint/burn without allowed authority root |
| unavailable data | DA root missing or certificate policy rejects |
| metadata drift | block/header/body roots differ from root journal |
| reject mutation | rejected proof path mutates state |

At least one mutation-resistance test should target each new conservation or
binding rule: remove the rule, invert the condition, or replace the checked root
with a sibling root, then confirm the test fails.

### Formal Obligations Before Promotion

Before `recursive_epoch_real_proof` can be promoted from gap to implemented, the
following obligations need local evidence:

1. **Statement binding**

```text
accepted_recursive_proof
-> proof image, journal hash, proof profile, policy hash, and metadata roots
   all match the expected typed statement
```

2. **Guest-authority boundary**

```text
accepted_child_summary
-> child receipt verified in guest under an allowed verifier ID
```

3. **Reject-is-no-op**

```text
reject(statement, state) -> state' = state
```

4. **Composition conservation**

```text
all accepted child summaries balanced
AND cross-shard messages cancel or carry exactly once
-> root summary balanced
```

5. **Associative aggregation**

```text
compose(compose(A, B), C) = compose(A, compose(B, C))
```

under canonical sort order, unique identities, and the same carry-queue mode.

## Core Abstraction: Effect Summary

Every child proof must output a canonical `EffectSummaryV1`.

```text
EffectSummaryV1 {
  domain_separator
  schema_version
  chain_id
  epoch_id
  height_range
  shard_id_or_lane_id
  lane_kind
  proof_profile
  program_id
  verifier_id
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  accepted_receipts_root
  rejected_receipts_root
  asset_delta_root
  cross_shard_outbox_root
  cross_shard_inbox_root
  write_set_root
  dependency_lock_hash
  toolchain_lock_hash
  feature_suite_hash
  public_policy_hash
}
```

`EffectSummaryV1` is the unit of recursive composition. It must be canonical:

- fields are append-only;
- roots are fixed-width hex digests;
- asset rows are sorted by `asset_id`;
- message rows are sorted by `message_id`;
- no implicit defaults except explicitly versioned zero roots;
- every digest is domain separated.

## Asset Delta Rows

Each leaf publishes a sorted root over asset delta rows:

```text
AssetDeltaRowV1 {
  asset_id
  debit_atoms
  credit_atoms
  authorized_mint_atoms
  authorized_burn_atoms
  authority_root
}
```

Global conservation at an aggregation node requires, for each asset:

```text
sum(debit_atoms) + sum(authorized_burn_atoms)
  = sum(credit_atoms) + sum(authorized_mint_atoms)
```

Rows with nonzero mint or burn require an authority root from an allowed policy:

```text
allowed_authority_root in root_journal.allowed_authority_roots
```

For ordinary spot settlement, the expected authority root is zero and mint/burn
must be zero.

## Cross-Shard Messages

Cross-shard effects are represented as messages, not as direct remote writes.

```text
CrossShardMessageV1 {
  message_id
  epoch_id
  source_shard_id
  destination_shard_id
  asset_id
  amount_atoms
  sender_scope_hash
  recipient_scope_hash
  source_receipt_hash
  deadline_epoch
}
```

`message_id` is:

```text
H("zenodex.cross_shard_message.v1",
  epoch_id,
  source_shard_id,
  destination_shard_id,
  asset_id,
  amount_atoms,
  sender_scope_hash,
  recipient_scope_hash,
  source_receipt_hash,
  deadline_epoch)
```

Aggregation requires exact cancellation:

```text
multiset(outbox messages) = multiset(inbox messages)
```

or an explicit carry queue transition:

```text
pre_carry_queue_root + outbox - inbox = post_carry_queue_root
```

The carry-queue mode is required for asynchronous cross-shard settlement. The
strict equality mode is required for synchronous atomic settlement.

## Leaf Proof Statements

Each leaf proof must prove one local transition class.

### Spot Shard Leaf

```text
Given:
  pre_state_root
  tx_root
  route_quote_receipt_roots
  policy_hash

Prove:
  deterministic spot transition execution
  no negative balances
  nonce sequencing
  accepted/rejected receipt roots
  quote receipt binding
  local conservation except declared cross-shard messages
  post_state_root

Output:
  EffectSummaryV1
```

### Perps Market Leaf

```text
Prove:
  funding application
  liquidation/ADL transition
  margin and insurance bounds
  oracle epoch binding
  no unauthorized cross-market mutation
  post_state_root

Output:
  EffectSummaryV1
```

### Oracle Leaf

```text
Prove:
  reporter set root binding
  Byzantine median or accepted aggregation rule
  freshness window
  source quorum policy
  output price packet root

Output:
  EffectSummaryV1
```

### zUSD / Vault / Proof-Market Leaf

Each additional lane uses the same `EffectSummaryV1`, with lane-specific
transition obligations and authority roots for any mint, burn, slash, or reward
effect.

## Aggregation Node Statement

An aggregation proof verifies a list of child proof descriptors:

```text
ChildProofDescriptorV1 {
  child_proof_commitment
  child_journal_hash
  child_effect_summary_hash
  child_program_id
  child_verifier_id
  child_profile
}
```

The aggregation circuit proves:

```text
for every child:
  verify_child_proof(child_proof_commitment, child_verifier_id)
  decode_child_journal(child_journal_hash)
  H(child_effect_summary) = child_effect_summary_hash
  child profile is allowed by verifier_set_root

all children:
  share chain_id, epoch_id, public_policy_hash, feature_suite_hash
  have unique lane/shard identity unless ordered by a conflict schedule
  have sorted, unique receipt IDs
  have sorted, unique cross-shard message IDs per inbox/outbox root
  have compatible dependency/toolchain locks

composition:
  pre_state_vector_root = root(child.pre_state_root by shard/lane)
  post_state_vector_root = root(child.post_state_root by shard/lane)
  global asset deltas conserve
  cross-shard messages cancel or advance carry queue
  no receipt appears twice
  no write-set conflict is unaccounted for
```

The aggregation node outputs its own `EffectSummaryV1`, where:

```text
pre_state_root      = pre_state_vector_root
post_state_root     = post_state_vector_root
tx_root             = root(child.tx_root)
evidence_root       = root(child.evidence_root)
receipt_root        = root(child.receipt_root)
asset_delta_root    = aggregate_asset_delta_root(children)
outbox_root/inbox_root/carry roots = composed message roots
```

This makes the aggregation operation associative:

```text
aggregate(aggregate(A, B), aggregate(C, D))
  = aggregate(A, B, C, D)
```

up to the canonical tree shape and root hash. This associativity is the core
scaling property because it allows parallel proving.

## Root Journal

The root proof journal must be small and verifier-oriented:

```text
RecursiveEpochJournalV1 {
  journal_version
  proof_type = "risc0.zenodex_recursive_epoch.v1"
  chain_id
  epoch_id
  proof_profile = "recursive_block_v1"
  recursive_statement_hash
  verifier_set_root
  child_verification_claims_root
  child_journals_root
  child_effect_summaries_root
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  accepted_receipts_root
  rejected_receipts_root
  asset_delta_root
  carry_queue_pre_root
  carry_queue_post_root
  conflict_schedule_hash
  data_availability_root
  data_availability_certificate_root
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
}
```

`child_verification_claims_root` must be nonzero for
`proof_kind = recursive_epoch_v0`. The RISC0 guest verifies child claims as
`(child_image_id, child_journal_bytes)`. Exact serialized child receipt hashes
are host audit metadata; they are not a guest-verifiable root unless a separate
receipt-hash adapter proves that binding.

The committed verifier set is a set of derived verifier IDs, not arbitrary
labels. Each child verifier ID is computed from `(child_image_id,
child_profile)`, so membership in `verifier_set_root` authorizes the same image
ID that the RISC0 `env::verify` call checks.

This repo includes `risc0.zenodex_recursive_summary_leaf.v1` as a dedicated
summary-leaf image for recursive plumbing and smoke tests. It accepts only the
`recursive_summary_leaf_test_v1` profile and enforces bounded summary inputs
(4096-byte postcard cap, 128-byte summary text fields). It is useful for testing
real assumption-based recursion, but it is not a production transition leaf
because it does not derive the summary from spot, perps, zUSD, oracle, or ledger
semantics.

This repo also includes `risc0.zenodex_recursive_spot_leaf.v1`, the first
transition-specific recursive leaf. It executes the existing checked spot
transition and derives a recursive summary from `StateProofJournalV1`. The v1
profile is intentionally local: recursive accepted/rejected receipt ID sets,
asset-delta rows, and cross-shard messages are empty, while the native spot
accepted-receipts root is committed as `receipt_root`. This proves local spot
app-state transitions under recursion; it does not claim cross-shard settlement
or native ledger balance deltas.

The repeatable smoke helper is
`zk/state_proof_risc0/cli/examples/recursive_summary_leaf_smoke.rs`. It builds a
summary-leaf or spot-leaf proof request, then builds a recursive root proof
request that uses that leaf receipt as a child proof assumption. The 2026-07-04
summary-leaf and spot-leaf local smokes both verified one-child root receipts
with `{"ok":true}`. The spot-leaf smoke is transition evidence for the scoped
local spot profile; the summary-leaf smoke remains plumbing evidence only.

## ZenoLedger / Tau Acceptance Algorithm

The block verifier must not accept recursive metadata by itself. It accepts only
after this sequence:

```text
1. Validate proof_metadata_v0.
2. Require proof_kind == "recursive_epoch_v0".
3. Require proof_profile == "recursive_block_v1".
4. Verify the recursive root proof under program_id/verifier_id.
5. Decode RecursiveEpochJournalV1.
6. Require journal.child_verification_claims_root ==
   metadata.child_verification_claims_root.
7. Require journal.pre_state_root == header.pre_state_root.
8. Require journal.post_state_root == header.post_state_root.
9. Require journal.tx_root == body.tx_root.
10. Require journal.evidence_root == metadata.evidence_root.
11. Require journal.conflict_schedule_hash == metadata.conflict_schedule_hash.
12. Require journal.feature_suite_hash == metadata.feature_suite_hash.
13. Require journal.dependency_lock_hash == metadata.dependency_lock_hash.
14. Require journal.toolchain_lock_hash == metadata.toolchain_lock_hash.
15. Require DA certificate root to satisfy the active DA policy.
16. Accept the block transition.
```

Any mismatch is a typed reject and must be no-op.

## Data Availability Contract

Recursive proofs compress verification. They do not make transaction data
available.

The root journal therefore binds:

```text
data_availability_root
data_availability_certificate_root
```

The active DA policy decides whether the certificate is:

- full blob inclusion;
- committee signature quorum;
- erasure-coded sampling receipt;
- local public-testnet replay bundle;
- Tau-native availability envelope.

The proof only claims:

```text
the computation used data committed by data_availability_root
```

It does not claim:

```text
users can retrieve that data
```

unless the DA certificate verifier also accepts.

## Scheduler Contract

The recursive architecture needs a scheduler that partitions work into leaves.
The scheduler is advisory until its output is committed by the proof.

The scheduler emits:

```text
ScheduleCertificateV1 {
  epoch_id
  shard_partition_root
  conflict_graph_root
  conflict_schedule_hash
  assigned_leaf_root
  dependency_edges_root
}
```

The root proof must bind `conflict_schedule_hash`. Leaves with disjoint
write-set roots can be proven in parallel. Leaves with overlapping write sets
must either:

- be ordered by the schedule; or
- be rejected as conflicts.

## Disaster States Minimized

This design targets the following disaster states:

| Disaster state | Required rejection or proof obligation |
| --- | --- |
| child proof from wrong chain | `chain_id` mismatch reject |
| child proof from wrong feature set | `feature_suite_hash` mismatch reject |
| child proof using stale verifier | `verifier_set_root` reject |
| metadata claims recursive proof without children | nonzero `child_verification_claims_root` required |
| valid child proofs from different epochs mixed | `epoch_id` mismatch reject |
| missing shard hidden by aggregation | expected shard set or partition root required |
| cross-shard debit without credit | message multiset/carry-queue check |
| duplicated cross-shard message | sorted unique `message_id` check |
| duplicated accepted receipt | sorted unique receipt check |
| unbalanced aggregate asset deltas | per-asset conservation check |
| unauthorized mint/burn | authority root check |
| write conflict hidden inside parallel leaves | write-set/conflict schedule check |
| proof verifies unavailable data | DA certificate requirement |
| recursive proof replayed across domain | domain separator and chain/config binding |
| block header not bound to proof | header/body/journal equality checks |

## Throughput Model

Let:

```text
N = number of leaves
C_leaf = cost to prove one local leaf
C_rec(k) = cost to aggregate k children
D = tree depth
```

Without recursion, validators verify `N` proofs or replay `N` transitions.
With recursion, validators verify one root proof.

Parallel proving latency is approximately:

```text
max(C_leaf over leaves) + D * C_rec(k)
```

for branching factor `k`. Total prover work increases by aggregation overhead,
but validator and light-client verification cost becomes essentially constant
per root block/epoch.

This matters for UX:

- stable verification cost;
- lower light-client sync burden;
- one receipt for a large batch;
- clearer failure causes at the leaf level;
- ability to shard execution without asking users to reason about shards.

## Implementation Plan

### Phase 0: Metadata and Checker Skeleton

Artifacts:

- `docs/recursive_epoch_proof_v1.md`
- `src/core/recursive_effect_summary.py`
- tests for canonical roots, unknown fields, duplicate rows, and mismatch
  rejects.

Gate:

```bash
python3 -m py_compile src/core/recursive_effect_summary.py
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/core/test_recursive_effect_summary.py
```

### Phase 1: Non-ZK Recursive Composition Checker

Implement a deterministic host checker that consumes child
`EffectSummaryV1` objects and emits `RecursiveEpochJournalV1`.

This proves the composition contract before investing in circuit work.

Negative tests:

- wrong chain;
- wrong epoch;
- missing shard;
- duplicated receipt;
- duplicated cross-shard message;
- unbalanced deltas;
- unauthorized mint;
- stale verifier ID;
- DA certificate missing.

### Phase 2: RISC0 / STARK Leaf Adapters

Extend current Risc0 journals or equivalent STARK leaf journals to emit
`EffectSummaryV1`.

The first leaf should be spot-only, because current Risc0 coverage already has
the most concrete smoke path.

### Phase 3: Recursive Aggregation Prototype

Build a root proof that verifies child proofs and the Phase 1 composition
checker inside the proving system.

The backend may be:

- a recursive STARK pipeline;
- Risc0 recursion if selected for local continuity;
- an external SHARP/S-two-style Cairo/STARK aggregation lane;
- a proof-system-neutral prototype that commits to the same root journal.

The ZenoLedger/Tau contract must see the same `RecursiveEpochJournalV1`.

### Phase 4: ZenoLedger Admission

Wire `proof_kind = recursive_epoch_v0` into block admission:

- require real root proof verification;
- require nonzero `child_verification_claims_root`;
- require root journal/header/body equality;
- require DA policy acceptance;
- emit a recursive block receipt for wallet/explorer display.

### Phase 5: Tau Semantic Contract

Lower the root-journal acceptance rules into Tau-compatible semantic contracts.

The Tau contract should validate bounded public fields and delegate cryptographic
proof verification to the active verifier adapter.

## Formal Obligations

The first Lean/SMT targets should be:

1. **Associativity of effect aggregation**

```text
compose(compose(A, B), C) = compose(A, compose(B, C))
```

under sorted canonical roots and disjoint child identities.

2. **Per-asset conservation preservation**

```text
forall children, balanced(children) -> balanced(compose(children))
```

3. **Cross-shard exact-once theorem**

```text
sorted_unique(outbox) AND sorted_unique(inbox)
AND multiset(outbox) = multiset(inbox)
-> every message consumed exactly once
```

4. **Header binding soundness**

```text
accepted_recursive_block
-> header.pre = journal.pre
AND header.post = journal.post
AND body.tx_root = journal.tx_root
```

5. **No partial visible commit**

For synchronous mode:

```text
accepted_root -> all child cross-shard messages matched in same epoch
```

For asynchronous mode:

```text
accepted_root -> carry_queue_post = carry_queue_pre + outbox - inbox
```

## Proof Profile Update Required

When implemented, update:

- `config/proof_profiles/zeno_ledger_profiles.json`
- `docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json`
- `docs/ZENO_LEDGER_PROOF_PROFILES.md`
- `docs/claims_registry.yaml`

The matrix must keep `recursive_epoch_real_proof` as a gap until a real root
proof smoke exists and the verifier rejects malformed root journals.

## Minimum Real-Proof Smoke

The first credible smoke should prove:

```text
leaf 0: spot shard A, one accepted swap
leaf 1: spot shard B, one accepted swap
root: aggregate both leaves
```

Required negative smokes:

- swap child proofs from different epochs;
- tamper child verification-claim root;
- tamper child journal bytes;
- tamper post state root;
- duplicate receipt ID;
- unbalanced asset delta row;
- wrong verifier ID;
- missing DA certificate root;
- child proof from wrong chain.

## Product Consequence

If implemented, a user-facing receipt can show:

```text
Recursive block verified
  leaf count: N
  markets: spot/perps/oracle/...
  accepted receipts: M
  rejected receipts: R
  global conservation: verified
  cross-shard messages: exact-once or carried
  DA policy: accepted
```

This is a UX improvement because the wallet can verify one compact object while
still exposing precise failure causes when a shard, market, or cross-shard
message fails.

## Non-Claims

This spec does not claim:

- the recursive RISC0 lane is production-ready;
- the summary-leaf test image proves any value-moving transition;
- current spot child journals already expose chain-bound `EffectSummaryV1`
  summaries without an adapter;
- the current `recursive_block_v1` profile is production-ready;
- all spot/perps/zUSD/oracle transitions have leaf proofs;
- DA is solved by proof recursion;
- Tau mainnet accepts this proof format;
- any throughput number.

## Next Frontier

The highest-value next step after the recursive root guest/CLI lane is a
summary-adapter proof for existing spot journals, so spot children can produce
chain-bound `EffectSummaryV1` journals without weakening the root verifier.
