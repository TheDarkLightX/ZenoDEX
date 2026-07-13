# ZRPF Settlement Effect Plan V1 CBC Specification

Date: 2026-07-12

Status: pure deterministic core implemented and host-tested; proof binding,
durable application, and settlement authority pending

## Scoped claim

`SettlementEffectPlanV1` is a frozen, bounded, canonical value object for
proposing one set of ZenoLedger cell writes and aligned asset, authorization,
message, carry, and reward effects. Its constructor independently establishes:

- exact field shapes and unsigned integer bounds;
- order-independent canonicalization with duplicate rejection;
- semantic-field-derived effect, message, carry, and reward IDs;
- proof-system-neutral action and grant-spend authorization nullifiers;
- exact mint and burn row shape plus matching authorization consumption;
- authorization consumption for every reward effect;
- checked per-asset conservation;
- action-to-write and action-to-asset-effect coverage;
- exact message-to-carry and reward-to-write/effect alignment;
- explicit pre-state and post-state root commitment;
- one canonical SHA-256 plan commitment.

The constructor performs no I/O and accepts no verification Boolean. The
result is a self-consistent data proposal. It is not an authentication
capability and cannot establish that a receipt, semantic guest, or ledger
authorized its contents.

## Authority boundary

```text
untrusted ProposedSettlementEffectPlanV1
  -> validate bounded typed rows
  -> sort by canonical identity
  -> recompute every referenceable row identity
  -> reject every duplicate identity
  -> bind every record to a declared economic action
  -> recompute authorization nullifiers
  -> bind authorization pre-state to the plan pre-state
  -> reject duplicate grant-and-nonce spends across actions
  -> require authority consumption for mint, burn, and reward
  -> checked u128 flow accumulation
  -> per-asset conservation
  -> exact message/carry and reward references
  -> canonical SettlementEffectPlanV1
  -> domain-separated plan commitment
  -> no proof or ledger authority
```

A later authority-bearing entry point must obtain the plan from authenticated
semantic facts, bind it to the verified program/profile manifest, and commit it
with the replay indexes and application-state update in one serializable
transaction.

## Bounded value objects

Every identity and commitment is canonical lowercase `0x`-prefixed 32-byte
hex. Counts are bounded to 8,192 entries per collection. Epochs and
authorization nonces are unsigned 64-bit integers. Asset amounts and all
intermediate flow sums are unsigned 128-bit integers.

### LedgerCellWriteV1

```text
economic_action_id
cell_key
pre_value_hash
post_value_hash
```

The cell key and action ID are nonzero. A zero value hash is the V1 absence
sentinel. Pre and post value hashes must differ. Cell keys are globally unique
inside the plan.

### AssetEffectV1

```text
effect_id = derived
kind = ordinary_transfer | authorized_mint | authorized_burn | authorized_reward
economic_action_id
asset_id
debit_atoms: u128
credit_atoms: u128
authorized_mint_atoms: u128
authorized_burn_atoms: u128
authority_scope_id
authorization_nullifier
```

`effect_id` is a domain-separated hash of every other field and is never
accepted from the caller. All-zero rows reject. Ordinary rows require zero
authority scope and zero authorization nullifier. A row cannot combine mint
and burn.

Mint has the exact shape:

```text
debit_atoms = 0
credit_atoms = authorized_mint_atoms > 0
authorized_burn_atoms = 0
authority_scope_id != 0
authorization_nullifier != 0
```

Burn has the exact shape:

```text
credit_atoms = 0
debit_atoms = authorized_burn_atoms > 0
authorized_mint_atoms = 0
authority_scope_id != 0
authorization_nullifier != 0
```

Each supply-changing row references one matching authorization consumption
with the same economic action and authority scope.

An authorized reward is a funded transfer with:

```text
debit_atoms = credit_atoms > 0
authorized_mint_atoms = authorized_burn_atoms = 0
authority_scope_id != 0
authorization_nullifier != 0
```

### AuthorizationConsumptionV1

```text
application_id
chain_or_domain_id
economic_action_id
authorization_subject_id
authorization_grant_id
authorization_scope_id
authorization_nonce: u64
action_pre_state_root
authorization_nullifier
authorization_grant_spend_nullifier = derived
```

The plan recomputes the nullifier. It also requires the application and domain
to equal the plan header. Authorization nullifiers are globally unique in the
plan. Every authorization consumption must be used by exactly one authorized
asset effect. Reusing one consumption for two effects rejects. The action
pre-state must equal the V1 plan pre-state.

The V1 nullifier preimage is:

```text
u16_be(domain_byte_length)
"zenodex.zrpf.authorization_consumption_nullifier.v1"
u16_be(version = 1)
application_id[32]
chain_or_domain_id[32]
economic_action_id[32]
authorization_subject_id[32]
authorization_grant_id[32]
authorization_scope_id[32]
u64_be(authorization_nonce)
action_pre_state_root[32]
```

```text
authorization_nullifier = SHA256(preimage)
```

The identity intentionally excludes proof program/image identity, receipt
encoding and bytes, intent salt, signature representation, relayer, and prover.
Equivalent proof or signature encodings therefore cannot create fresh
authorization-consumption identities.

The second nullifier prevents one grant and nonce from being freshened by
changing action or pre-state material:

```text
u16_be(domain_byte_length)
"zenodex.zrpf.authorization_grant_spend_nullifier.v1"
u16_be(version = 1)
application_id[32]
chain_or_domain_id[32]
authorization_grant_id[32]
u64_be(authorization_nonce)
```

It intentionally excludes action, effect, pre-state, subject, and scope. Both
authorization nullifiers are committed. Grant-spend nullifiers must be unique
inside the plan.

### MessageEffectV1 and CarryEffectV1

A message binds its action, asset effect, source domain, destination domain,
asset, amount, and either `outbox_enqueue` or `inbox_consume`. Source and
destination must differ. Outbox source or inbox destination must equal the plan
domain. The referenced asset effect must match the action and asset; outbox
amount equals its debit and inbox amount equals its credit. One carry row must
exist for each message:

```text
outbox_enqueue <-> lock
inbox_consume  <-> release
```

Action, message, asset, and amount must match exactly. This is a local plan
alignment rule. It does not establish remote delivery or queue continuity.
Message and carry IDs are derived from every semantic field and cannot be
chosen by the caller.

### RewardEffectV1

A reward binds:

```text
reward_id
economic_action_id
asset_effect_id
recipient_cell_key
asset_id
amount_atoms
authority_scope_id
authorization_nullifier
```

The referenced asset effect and recipient cell write must exist. Action and
asset IDs must match. The asset effect must have kind `authorized_reward`; its
scope and authorization nullifier must equal the reward fields. Its credit must
equal the reward amount. One asset effect cannot back multiple rewards inside
the same plan. Reward IDs are derived from every semantic field.

## Economic action coverage

The proposal supplies sorted-unique canonical economic action IDs after
normalization. Every row must reference one declared action. Every declared
action must have at least:

- one ledger cell write; and
- one asset effect.

The plan publishes `economic_action_ids_root`,
`authorization_nullifiers_root`, and
`authorization_grant_spend_nullifiers_root`. Derivation of each economic action
ID from canonical action semantics is a separate protocol obligation.

## Conservation

For each asset, V1 accumulates all four columns with checked `u128` addition.
Overflow rejects before comparison.

```text
sum(debit_atoms) + sum(authorized_mint_atoms)
  = sum(credit_atoms) + sum(authorized_burn_atoms)
```

Each side addition is also checked. Equality uses ordinary integer arithmetic,
not field-modular arithmetic.

## State-root binding

The plan requires nonzero, different `pre_state_root` and `post_state_root` and
commits both with every cell write and effect row. Every authorization action
pre-state must equal the plan pre-state. This closes the V1 in-plan root-alias
path; an upstream authenticated economic-action record must still prove that
the action ID binds that pre-state. The plan establishes transcript binding
only. It does not prove that applying the cell writes to an
authenticated state tree produces the post-state root. A later admission lane
must verify exact sparse-Merkle or ledger-native transition witnesses.

## Canonical roots and plan commitment

Input row order has no effect on the result. Canonical sort keys are:

| Collection | Key |
| --- | --- |
| economic actions | action ID |
| cell writes | cell key |
| asset effects | effect ID |
| authorizations | authorization nullifier |
| messages | message ID |
| carries | carry ID |
| rewards | reward ID |

Effect, message, carry, and reward IDs are recomputed from their complete
semantic records before they are used as keys. This closes label-renaming and
duplicate-under-new-label escapes. All duplicates reject before construction.
Each collection root uses canonical JSON with a distinct `zenodex:` domain
separator. The plan commitment binds the header, canonical rows, collection
roots, action root, action-binding authorization root, and grant-spend root:

```text
plan_commitment = SHA256(
  domain_sep("zrpf_settlement_effect_plan", 1)
  || canonical_json(plan)
)
```

The retained test vector has:

```text
canonical plan bytes = 4,429
plan commitment =
  0x62b5fe3f2f5772273c36d58a77c139bd91e8d6b6f216be6a85c29669a1d7f854
authorization nullifier =
  0x04da42ae3e508ff068a07e03a186250155dc3145d9d28320b0f90b83d1baa3b3
```

The shared Rust/Python nullifier vector uses repeated-byte identifiers,
economic action ID
`0x8613bdc85d4618ed79c0d927c107b4682423091f8d1856251ad9e355a6525143`,
grant byte `0x09`, and derives:

```text
0x03c908ee0fd74c394865c11453a51a0b059bfb35ceb62956beb00c00d49ff913
```

The shared Rust/Python grant-spend vector derives:

```text
0x1f5970f7f3ba7ec6dd111b488f0229256aa683c032111f950e08293c7ac63c38
```

## Stable rejection surface

The constructor raises `SettlementEffectPlanValidationError` with a typed
`SettlementEffectPlanRejectCodeV1`. Covered classes include invalid shape,
capacity, duplicates, unknown or uncovered actions, nullifier mismatch,
grant-and-nonce reuse, pre-state mismatch, detached or missing authorization,
derived-ID mismatch, invalid typed effect shape, arithmetic overflow, asset
imbalance, state-root no-change, message/carry mismatch, and reward mismatch.

Every aggregate rejection occurs before a plan is returned. Inputs are frozen,
and rejection leaves the exact proposal and nested rows unchanged.

## Executed evidence

The focused test suite covers:

- canonical construction and retained hash vectors;
- tuple-permutation invariance;
- pre/post root commitment sensitivity;
- one-atom conservation failure;
- checked u128 overflow;
- missing, detached, mismatched, and cross-domain authorization;
- action-pre-state alias and cross-action grant-and-nonce replay rejection;
- mint/burn and ordinary-row authority shape;
- derived-ID mutation and duplicate-under-renamed-ID rejection;
- action coverage;
- exact message/carry pairing;
- authorized reward binding;
- duplicate action rejection;
- reject-is-no-op;
- Boolean-as-integer rejection;
- sensitivity of the nullifier to every included identity field;
- absence of proof/signature representation fields from authorization identity.

Commands executed for this scoped implementation are recorded in the commit
handoff. The required focused gates are pytest, Ruff, and mypy over the new
core and test modules.

## Explicit non-claims

This profile does not establish:

- origin of the proposal from a verified RISC0 receipt;
- authenticity or semantic correctness of any economic action ID;
- complete cross-language economic-action record parity beyond the shared
  authorization-nullifier vectors;
- cross-language parity for the Python V1 effect, message, carry, reward, and
  complete plan commitments;
- membership of authorization grants and scopes in an authenticated policy
  registry;
- equivalence across all possible economic action encodings;
- sparse-Merkle or ledger-native proof that cell writes produce the post root;
- proof that a reward recipient cell transition encodes the stated credit;
- authenticated reward entitlement, purpose, recipient, asset, epoch, or cap;
- balance non-negativity after applying writes;
- collateral, liquidation, oracle, or market-specific validity;
- global authorization-cap accounting across multiple plans;
- durable cross-epoch or cross-plan action, authorization, and grant-spend
  uniqueness;
- data availability, source finality, schedule validity, or carry continuity;
- remote message delivery;
- atomic SQLite or ZenoLedger application;
- crash-consistent coupling of replay indexes and economic effects;
- settlement, release, public, privacy, or production authority.

## Next promotion

The next compatible layer must consume an authenticated Semantic V2 authority
pair and an independently reconstructed `SettlementEffectPlanV1`, require exact
agreement on application, domain, epoch, source journal, policy, economic
action, authorization, state, and effect roots, then commit:

```text
replay indexes
+ application cell writes
+ authorization nullifiers
+ authorization grant-spend nullifiers
+ value effects
+ carry/message effects
+ reward effects
+ resulting application-state root
```

in one serializable transaction guarded by a state-version compare-and-swap and
durable unique indexes.
