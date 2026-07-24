# PR #478 Command, Settlement, and Effect Schema

This file is normative for the PR #478 repair after it is rebased on the final
reviewed #477 head.

## 1. Ownership slice within the authority pipeline

```text
existing canonical parser output or exact mounted builder
  -> OwnedIntentV1
  -> existing signature/authentication stage binds canonical command identity
  -> existing authorization stage consumes that identity
  -> candidate OwnedSettlementV1
  -> validated OwnedDexEffectsV1
```

PR #478 changes only ownership at these mounted boundaries. It does not replace
the raw-byte parser, authentication, authorization, nonce commitment, receipt,
outbox, or atomic-commit stages. Every phase wrapper must preserve the same
canonical command identity/hash and canonical bytes. Python object identity
across wrappers is irrelevant. A later stage never re-reads a mutable builder.

## 2. Bounded owned JSON

Some compatibility fields currently carry JSON-shaped data. They use this
closed grammar:

```text
OwnedJsonValueV1 =
    None
  | exact bool
  | exact bounded int
  | exact bounded canonical string
  | tuple[OwnedJsonValueV1, ...]
  | OwnedMapV1[str, OwnedJsonValueV1]
```

Rules:

- no floats, `NaN`, infinity, negative zero, bytes, bytearray, enum, set,
  dataclass, arbitrary object, numeric string, or subclass;
- depth at most 64;
- total nodes at most 200,000;
- canonical encoded bytes at most 4,000,000 unless a narrower transport bound
  already applies;
- strings at most 4,096 characters and the field's narrower UTF-8 limit;
- object keys are exact canonical strings and iterate in canonical order;
- cycles reject;
- source arrays are exact lists at decoder output; owned arrays are tuples;
- source objects are exact dicts; owned objects are exact `OwnedMapV1`;
- duplicate keys reject in the raw-byte decoder before a Python dict can erase
  them;
- an accepted decoded value must re-encode byte-for-byte to the original
  authority bytes.

`project_owned_json` accepts only an exact `OwnedJsonValueV1` and returns a
fresh ephemeral builtin JSON projection. It has no `Any` input, no fallback,
and no copy protocol. A source dict cannot call it directly.

## 3. Intent record

### Owned output

```text
OwnedIntentV1 {
  module: "TauSwap"
  version: "0.1"
  kind: exact OwnedEnumV1 admitted from exact IntentKind
  intent_id: canonical 32-byte lowercase 0x hex
  sender_pubkey: canonical 48-byte lowercase 0x hex
  deadline: exact nonnegative int
  salt: None | exact bounded canonical string
  fields: OwnedMapV1[str, kind-indexed owned value]
}
```

It is a distinct frozen/slotted data type and does not inherit `Intent` or any
mutable intent class. It has no `set_field` method.

### Accepted source types

The conversion registry may accept only exact known parser/builder types:

```text
Intent
SwapIntent
RouteIntent
CreatePoolIntent
ValidatedIntent
OwnedIntentV1
```

Each source type is listed explicitly because it is already mounted. Exact
field extraction ignores source methods and uses the same kind-indexed schema.
Any new intent class fails the registry-drift test. Production ingress must use
the parser-normalized variant; direct builder admission is a compatibility
surface and receives identical full validation.

### Common field registry

Use one leaf registry imported by parser, owner, encoder, and tests. Do not
duplicate the key sets from `src/integration/operations.py`.

| Field | Rule |
| --- | --- |
| `nonce` | optional exact int, `1..0xffffffff` |
| `recipient` | optional exact canonical non-empty string, current 512-character limit |
| `submission_order` | optional exact nonnegative int |
| `quote_receipt_hash` | optional canonical 32-byte hash under the mounted receipt rule |
| `quote_pool_fingerprint` | optional exact canonical string under current receipt rule |
| `quote_receipt_leg_index` | optional exact nonnegative int |
| `oracle_authorization` | optional bounded `OwnedJsonObjectV1`; typed Oracle authorization remains a separate refinement obligation |

Unknown common fields reject.

### Kind-indexed fields

The exact key set is `common keys + keys for kind`. Required/optional status and
bounds mirror the mounted parser and domain constants.

#### SWAP_EXACT_IN

```text
pool_id         exact canonical non-empty string
asset_in        exact canonical non-empty string
asset_out       exact canonical non-empty string, different from asset_in
amount_in       exact int, 1..DEX_SWAP_AMOUNT_MAX
min_amount_out  exact int, 0..DEX_SWAP_AMOUNT_MAX
```

#### SWAP_EXACT_OUT

```text
pool_id        exact canonical non-empty string
asset_in       exact canonical non-empty string
asset_out      exact canonical non-empty string, different from asset_in
amount_out     exact int, 1..DEX_SWAP_AMOUNT_MAX
max_amount_in  exact int, 1..DEX_SWAP_AMOUNT_MAX
```

#### CREATE_POOL

```text
asset0       exact canonical non-empty string
asset1       exact canonical non-empty string; pair already in canonical order
fee_bps      exact int, 0..10_000
amount0      exact int, 1..DEX_LP_AMOUNT_MAX
amount1      exact int, 1..DEX_LP_AMOUNT_MAX
created_at   optional exact nonnegative int
curve_tag    optional exact canonical curve-registry string
curve_params optional exact canonical curve-registry string
```

The owner validates canonical form and does not normalize it.

#### ADD_LIQUIDITY

```text
pool_id          exact canonical non-empty string
amount0_desired  exact int, 1..DEX_LP_AMOUNT_MAX
amount1_desired  exact int, 1..DEX_LP_AMOUNT_MAX
amount0_min      exact int, 0..DEX_LP_AMOUNT_MAX
amount1_min      exact int, 0..DEX_LP_AMOUNT_MAX
```

#### REMOVE_LIQUIDITY

```text
pool_id      exact canonical non-empty string
lp_amount    exact int, 1..DEX_LP_SUPPLY_MAX
amount0_min  exact int, 0..DEX_POOL_RESERVE_MAX
amount1_min  exact int, 0..DEX_POOL_RESERVE_MAX
```

#### ROUTE_EXACT_IN

```text
asset_in              exact canonical non-empty string
asset_out             exact canonical non-empty string, different from asset_in
leg_indices           exact non-empty list at source -> owned tuple; exact
                      nonnegative strictly increasing integers
total_amount_in       exact int, 1..DEX_SWAP_AMOUNT_MAX
total_min_amount_out  exact int, 0..DEX_SWAP_AMOUNT_MAX
route_legs            reserved compatibility field; bounded JSON and rejected
                      by the mounted witness gate when user-supplied
route_pool_fingerprints same rule as route_legs
```

#### ROUTE_EXACT_OUT

```text
asset_in             exact canonical non-empty string
asset_out            exact canonical non-empty string, different from asset_in
leg_indices          exact non-empty list at source -> owned tuple; exact
                     nonnegative strictly increasing integers
total_amount_out     exact int, 1..DEX_SWAP_AMOUNT_MAX
total_max_amount_in  exact int, 0..DEX_SWAP_AMOUNT_MAX under current behavior
route_legs and route_pool_fingerprints as above
```

Opposite exact-in/exact-out fields reject. Missing required fields reject.

### Batch

`admit_intent_batch` accepts an exact list or tuple only at the declared API
edge, checks at most 256 items, admits in source order, and returns
`tuple[OwnedIntentV1, ...]`. The returned order is protocol order and is never
sorted by object identity, hash, or worker timing.

## 4. Signed and authenticated envelope ownership

`SignedIntentV1` contains:

```text
intent: exact OwnedIntentV1
signature: exact canonical fixed-width signature bytes/string under the
           mounted BLS encoding
signed_message_hash: hash of the exact canonical OwnedIntentV1 bytes
```

Construction order:

1. admit/own intent;
2. canonical-encode owned intent;
3. validate exact canonical signature representation;
4. compute or verify signed-message hash;
5. construct signed value.

Before implementation, the mounted envelope inventory must also cover quote
receipt payloads, transaction sender and authentication mode, the chain/domain
signature frame, and every settlement proof, Oracle, certificate, grid, and
auxiliary field. An omitted mounted field blocks implementation.

The relayer, verifier, nonce checker, preview, and executor consume the same
owned value and bytes. A mutable `Intent` is never retained by `SignedIntentV1`.

Type names such as `AuthenticatedIntent` may be used only when a verifier-owned
witness binds signer, signature, chain/domain, command hash, and relevant
pre-state/policy. A caller-constructible frozen record is not authentication.

## 5. Settlement source and owned normal form

### Source

The legacy ingress accepts exact `Settlement` or exact `OwnedSettlementV1` and
returns exact `OwnedSettlementV1`. All mutable fields are admitted before
validator execution. Authority validators and transition functions accept only
the exact owned settlement.

### Owned settlement

```text
OwnedSettlementV1 {
  module: exact "TauSwap"
  version: exact mounted version string
  batch_ref: exact bounded canonical string
  included_intents: tuple[OwnedIncludedIntentV1, ...]
  fills: tuple[OwnedFillV1, ...]
  balance_deltas: tuple[OwnedBalanceDeltaV1, ...]
  reserve_deltas: tuple[OwnedReserveDeltaV1, ...]
  lp_deltas: tuple[OwnedLPDeltaV1, ...]
  events: None | tuple[OwnedJsonObjectV1, ...]
}
```

No owned record inherits its mutable source record. There is no dataclass seal
field. Cache/index data is private, non-dataclass metadata and never enters the
schema or encoder.

### Included intent

```text
intent_id  exact canonical 32-byte ID
action     exact OwnedEnumV1 admitted from exact FillAction
```

At most 256 entries. Intent IDs are unique. Order is the declared batch order.

### Fill

| Field | Rule |
| --- | --- |
| `intent_id` | exact canonical 32-byte ID |
| `action` | exact `OwnedEnumV1` admitted from exact `FillAction` |
| `reason` | `None` or exact bounded string |
| `amount_in_filled` | `None` or exact nonnegative bounded amount |
| `amount_out_filled` | same |
| `fee_paid` | same |
| `protocol_fee_paid` | same |
| `amount0_used` | same |
| `amount1_used` | same |
| `lp_minted` | same |
| `amount0_out` | same |
| `amount1_out` | same |
| `lp_burned` | same |
| `reserve_in_before` | same |
| `reserve_out_before` | same |

At most 256 fills. Action-specific presence and conservation rules remain in
the strong settlement validator and must run over the same owned candidate.

### Deltas

```text
OwnedBalanceDeltaV1(pubkey, asset, delta_add, delta_sub)
OwnedReserveDeltaV1(pool_id, asset, delta_add, delta_sub)
OwnedLPDeltaV1(pubkey, pool_id, delta_add, delta_sub)
```

Identifiers are exact canonical strings. Delta components are exact
nonnegative integers under the existing domain bounds. Net delta is derived;
it is not stored independently.

The total settlement JSON graph remains inside the 200,000-node and
4,000,000-byte profiles. A tighter per-delta-list bound may be promoted only
after deriving it from all mounted intent and route variants.

### Events

For this compatibility PR, each event is a bounded `OwnedJsonObjectV1`. This
closes mutation and representation aliasing while preserving current event
payloads. It does not establish a typed event semantics. `EVENT-TYPING-001`
remains an explicit blocker for the full FCIS profile; a later source-derived
tagged event registry must replace the JSON carrier.

### Settlement invariants

After exact field admission, enforce:

- unique included intent IDs;
- unique fill IDs;
- every fill belongs to an included intent;
- every `FILL` action has exactly one matching fill record;
- no extra `FILL` record;
- stable list order;
- current strong settlement conservation and proof-carrying checks;
- final owned candidate is the exact value used to build effects.

## 6. Pure settlement transition

Settlement validation, application, and effect construction consume the same
exact `OwnedSettlementV1`. Application computes immutable balance, reserve, LP,
nonce, and event patches and returns a new committed candidate. There is no
public `to_scratch_settlement`, mutable settlement projection, or second
reconstruction of command meaning after authentication.

A leaf implementation may allocate a private builtin work buffer from admitted
immutable values. It remains inside one pure function and is tested
differentially against the return-new reference relation.

## 7. Effect plan and result

```text
OwnedDexEffectsV1 {
  settlement: exact OwnedSettlementV1
  total_swap_fees: exact nonnegative int
  fee_split: None | exact owned FeeSplitResult
}
```

`total_swap_fees` must be derived from the same owned fills stored in
`settlement`. The constructor re-derives and checks equality or the transition
constructs the total once and passes the same semantic value to both invariant
and effect construction. No mutable dictionary is the authoritative effect
plan.

`DexStepResult` becomes the exhaustive aggregate result required by E10:

```text
Accept
  -> exact DexState + exact OwnedDexEffectsV1 + canonical receipt
Reject
  -> no successor + no authoritative effects + canonical rejection receipt
CommittedFailure
  -> exact DexState + exact OwnedDexEffectsV1 + canonical failure receipt
```

PR #478 owns these values and their canonical projection. Atomic root-bound
publication, receipt storage, replay updates, and outbox-record commitment are
the later shell contract; they are never modeled as a post-commit best-effort
receipt write.

## 8. Canonical projection

Canonical encoders accept exact owned types only. Projection order is declared
by record field order and owned-map canonical entries. Implementation-only
metadata, private indexes, Python class names, and insertion history are
excluded.

Required round trips:

```text
decode_authority_bytes(encode_owned(x)) = x

decode_authority_bytes(b) = x
and accepted(b)
implies encode_owned(x) = b
```

Golden vectors must be shared with every Rust/proof-guest implementation that
claims the same boundary.

## 9. Observable compatibility

For every canonical valid input accepted before the ownership repair:

```text
signed_message_bytes_before == signed_message_bytes_after
nonce_result_before          == nonce_result_after
settlement_accept_before     == settlement_accept_after
settlement_bytes_before      == settlement_bytes_after
effect_bytes_before          == effect_bytes_after
state_root_before            == state_root_after
```

New rejections are limited to values named by this packet: malformed exact
types, subclasses, aliases, cycles, over-limit values, unregistered variants,
noncanonical encodings, and old pseudo-frozen objects.
