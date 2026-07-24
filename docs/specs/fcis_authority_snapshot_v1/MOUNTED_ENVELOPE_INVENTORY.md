# Mounted DEX Authority Envelope Inventory V1

Status: **normative inventory for the unmounted authority-graph review unit**

This inventory satisfies erratum E4. It records every authority-bearing value
currently mounted around DEX intent and settlement ownership. Its purpose is to
prevent an ownership repair from silently dropping a field or promoting an
owned value into an authentication witness.

The inventory has two implementation scopes:

```text
authority graph in the current review unit
  = exact owned intent, settlement, fill, delta, event, and bounded-JSON values

later phase and atomic-mount work
  = signature policy, outer sender, chain/domain context, proof and certificate
    verification, nonce/replay updates, receipts, outbox, and publication
```

Owning a payload preserves its bytes and prevents alias mutation. Ownership
does not verify a signature, authorize a sender, validate a proof, consume a
nonce, or make an external certificate authoritative.

## 1. Mounted operation-group carriers

### Operation group `"2"`: signed-intent entries

The mounted parser is `src/integration/operations.py:parse_signed_intents`.
Each entry currently accepts one of these transport shapes:

```text
intent object
[intent object]
[intent object, signature string]
[intent object, quote-receipt object]
[intent object, signature string, quote-receipt object]
```

The object form may also carry `signature` and `quote_receipt` members. A
member and positional carrier supplied together reject as ambiguous. The
parser removes both transport members before constructing the intent fields.

The parser result is the legacy frozen outer record:

```text
SignedIntentEnvelope {
  intent: mutable Intent graph
  signature: None | string
  quote_receipt: None | mutable JSON object
}
```

The current authority-graph review unit replaces retained aliases with owned
values. It does not declare this record authenticated.

### Operation group `"3"`: settlement envelope

The mounted parser is `src/integration/operations.py:parse_settlement_envelope`.
The settlement object has these auxiliary members removed before construction:

```text
proof | zk_proof                       mutually exclusive aliases
oracle_authorization
uniform_batch_certificate
uniform_batch_optimality_certificate
uniform_batch_v2_bounded_grid
uniform_batch_v3_exact_out_grid
```

Every present auxiliary member must currently be a JSON object. The parser
result is:

```text
SettlementEnvelope {
  settlement: mutable Settlement graph
  proof: None | mutable JSON object
  oracle_authorization: None | mutable JSON object
  uniform_batch_certificate: None | mutable JSON object
  uniform_batch_optimality_certificate: None | mutable JSON object
  uniform_batch_v2_bounded_grid: None | mutable JSON object
  uniform_batch_v3_exact_out_grid: None | mutable JSON object
}
```

The current authority-graph review unit may own these auxiliary objects as
bounded `OwnedJsonObjectV1` carriers. Their existing typed verifiers remain the
authority for their meaning.

## 2. Intent command identity

The canonical intent command contains:

```text
module
version
kind
intent_id
sender_pubkey
deadline
optional salt
kind-indexed fields object
```

The exact common and kind-indexed field registry is normative in
`PR478_AUTHORITY_EFFECT_SCHEMA.md`. Parser, owner, encoder, and drift tests must
import one leaf registry. Transport-only `signature` and `quote_receipt` are
never intent fields.

The signing projection nests kind-indexed values under `fields`, includes
`salt` only when present, and uses the same canonical identifier spellings
consumed by execution. `OwnedIntentV1` must encode to this same logical signing
projection. It remains an owned parsed command, not an authenticated command.

## 3. Signature, sender, authentication policy, and domain frame

These values jointly decide intent authentication and therefore remain a
single later phase contract:

| Value | Mounted source | Current rule | Ownership disposition |
| --- | --- | --- | --- |
| intent signature | `SignedIntentEnvelope.signature` | optional parser string up to 4,096 characters; verifier decodes exactly 96 bytes | later exact canonical signature value |
| declared signer | `intent.sender_pubkey` | verifier decodes exactly 48 bytes | owned inside `OwnedIntentV1` |
| outer sender | `apply_ops(tx_sender_pubkey=...)` | `None` or shell-verified sender; bypass comparison decodes exactly 48 bytes | explicit later execution-context value |
| require signatures | `DexEngineConfig.require_intent_signatures` | exact configuration boolean | explicit later policy value |
| allow sender bypass | `DexEngineConfig.allow_unsigned_intents_if_tx_sender_matches` | exact configuration boolean | explicit later policy value |
| chain | `DexEngineConfig.chain_id` | nonempty deployment string | explicit later execution-context value |
| algorithm frame | `domain_sep_bytes(..., version=1)` | label is `dex_intent_sig:{chain_id}` | versioned later signature-frame value |
| message body | canonical intent signing JSON | canonical JSON bytes | derived only from exact `OwnedIntentV1` |
| verified message | SHA-256 of domain frame plus body | BLS `G2Basic.Verify(pubkey, digest, signature)` | verifier-owned witness output |

The mounted policy has three observable modes derived from the two booleans and
signature presence:

```text
per-intent signature required
per-intent signature or matching outer sender
matching outer sender only
```

An `AuthenticatedIntentV1` may be constructed only by the verifier that checks
the exact owned command bytes together with all table values above. A public
frozen constructor is forbidden.

## 4. Quote-receipt payload

The attached quote receipt has the outer shape:

```text
{
  "body": { ... },
  "receipt_hash": string
}
```

The body is committed with domain `zenodex.route_quote_receipt/v1` and contains:

```text
schema = "zenodex/route_quote_receipt/v1"
kind = "exact_in" | "exact_out"
asset_in
asset_out
amount_in
amount_out
legs: nonempty ordered list of {
  amount_in,
  amount_out,
  hops: nonempty ordered list of {
    pool_id, asset_in, asset_out, amount_in, amount_out
  }
}
pools: pool_id -> pool-state fingerprint
optional quote_epoch
optional canonical_route_certificate for exact-in only
```

The mounted verifier checks the receipt hash, route endpoints and totals, pool
fingerprints, hop continuity, per-hop AMM replay, optional quote epoch, and the
optional canonical-route certificate. The intent binds receipt identity and
coverage through `quote_receipt_hash`, `quote_pool_fingerprint`,
`quote_receipt_leg_index`, and route fields.

The authority graph owns the complete receipt as bounded JSON. Verification
and construction of a quote-bound authorization witness remain later phases.

## 5. Intent-level Oracle authorization

`intent.fields["oracle_authorization"]` is mounted for protected single-pool
swap intents. It is JSON-shaped at parser ownership time. The typed Oracle
checker accepts either a direct authorization object or an envelope with:

```text
authorization
optional receipt_graph
optional economic_envelope
```

The authorization record includes:

```text
consumer_module, action_kind, action_id, action_facts_hash,
pre_state_hash, profile_id, query_id,
value_e8, value_hash, confidence_e8, deviation_bps,
observed_epoch, expires_at_epoch, feed_id,
feed_registry_root, query_policy_root, source_registry_root,
reporter_registry_root, evidence_class,
economic_envelope_id, receipt_graph_root
```

The mounted protected-swap checker binds those values to the actual intent,
verified quote receipt, runtime epoch, quote value, and pool snapshot. The
authority graph owns the input object only. Typed Oracle authorization remains
a verifier-owned witness and an explicit refinement obligation.

## 6. Settlement graph

The exact settlement ownership graph contains:

```text
module = "TauSwap"
version = "0.1"
batch_ref
included_intents: ordered pairs of (intent_id, FillAction)
fills: ordered Fill records
balance_deltas: ordered BalanceDelta records
reserve_deltas: ordered ReserveDelta records
lp_deltas: ordered LPDelta records
events: None | 1..200,000 ordered bounded JSON objects
```

`FillAction` is admitted to a fresh `OwnedEnumV1`; no source enum singleton is
retained. All identifiers, optional fill fields, amount bounds, uniqueness,
coverage, and order rules are defined in `PR478_AUTHORITY_EFFECT_SCHEMA.md`.
Events remain bounded owned JSON under the open `EVENT-TYPING-001` obligation.
An empty event sequence is not an owned normal form; E14 requires `None` for
absence because the mounted encoder omits both source spellings.

## 7. Proof payload

The settlement proof carrier is bounded by the mounted proof-verifier byte
limit. When verification is enabled it must bind:

```text
pre_state_commitment
batch_commitment
```

The optional `scheme` string selects currently supported verifier behavior.
Additional proof members are verifier-specific bounded JSON. The engine sends
a small verifier payload containing schema/version, the owned proof payload,
and the independently computed pre-state and batch commitments.

Owning the proof prevents alias mutation. Only the configured verifier can
produce a proof-accepted witness.

## 8. Settlement-level Oracle authorization

`SettlementEnvelope.oracle_authorization` uses the same Oracle envelope grammar
listed in section 5. The critical-settlement checker additionally binds:

```text
exact settlement hash
exact pre-state root
price_curr from the configured three-price history
runtime epoch
critical-settlement query and profile IDs
```

The authority graph owns the input object. It does not replace this typed
consumer check.

## 9. Uniform-batch certificate payloads

### Uniform batch certificate

The certificate object has the exact keys:

```text
schema, policy_id, price_objective_id,
pool_id, base_asset, quote_asset,
pool_state_hash, intent_set_hash,
price_num, price_den,
fills: ordered list of {intent_id, executed_in, executed_out}
```

Supported schema/policy pairs are the declared UPBA v1, v2, and v3 profiles.
The fill list is bounded at 256.

### Optimality certificate

The exact keys are:

```text
schema, objective_id, candidate_set_hash, winner_id,
volume_upper, surplus_upper_at_winner_volume,
candidates: ordered list of {
  candidate_id, volume, surplus, optional fill_vector_hash
}
```

The candidate list is bounded at 256. Its verifier checks the finite candidate
set, winner binding, objective, and policy-specific evidence.

### V2 bounded-grid evidence

The mounted engine consumes:

```text
max_price_num
max_price_den
fill_vectors
optional table_root
```

Each fill vector is a bounded sequence of uniform-batch fill objects. The
verifier reconstructs the accepted candidate table and checks its optional
root plus the optimality certificate.

### V3 exact-out grid evidence

The mounted engine accepts exactly:

```text
max_price_num
max_price_den
```

The verifier reconstructs the exact-out candidate set and checks the bound
optimality certificate. V2 and V3 grid payloads are mutually exclusive and
both require the uniform-batch and optimality certificates.

These four objects may be owned as bounded JSON in the authority graph. Their
typed certificate parsers and semantic verifiers continue to decide validity.

## 10. Review-unit closure and nonclaims

The authority-graph review unit may close only when:

```text
all owned domain records use the single state admission profile
all JSON carriers use the closed BoundedJsonValue algebra
all accepted source types are exact and exhaustively registered
all source aliases can be mutated without changing owned bytes or behavior
the authority-graph structural checker is green
the legacy parser/validator parity corpus is green
```

It does not close authentication, authorization, nonce/replay commitment,
proof validity, Oracle validity, certificate optimality, receipt persistence,
outbox delivery, or atomic publication. Those claims require the later phase
and atomic-mount review units.
