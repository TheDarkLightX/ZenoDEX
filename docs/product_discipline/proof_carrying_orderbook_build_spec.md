# Proof-Carrying Orderbook Build Spec

This spec defines a product/API build plan for a ZenoDEX orderbook surface that
is usable by bots while preserving the trustless-hosting bar:

```text
ClientAccepts(result) :=
  checkpoint_chain_verified
  and proof_receipt_verified
  and journal_bound_to_header_root
  and verifier_identity_pinned
  and rulebook_hash_pinned_or_validly_upgraded
```

The first product goal is a clean order lifecycle API. The security goal is that
no state-changing result is labeled final until a client can verify the matching
receipt, root binding, verifier identity, and rulebook pin.

## Goals

- Provide a bot-compatible REST API for order submission, cancellation, status,
  fills, market data, and proof retrieval.
- Separate request acknowledgement, execution, replay verification, and proof
  finality in every response.
- Support idempotent order submission through `client_order_id`.
- Make base-unit precision, market version, and rulebook hash visible to clients.
- Define proof endpoints early, even while proof production is async or pending.
- Keep transport authentication separate from authority-bearing trade signatures.

## Non-Goals

- This spec does not claim a complete CLOB proof is implemented.
- This spec does not promote any assurance matrix column.
- This spec does not replace existing CPMM/settlement paths.
- This spec does not require the first implementation to prove the full matching
  law. It requires honest labels until that proof exists.

## Status Model

Use these statuses consistently across REST, SDK, and UI:

```text
received
sequenced
executed
replay_verified
proof_pending
proof_verified
rejected
expired
cancelled
```

Only `proof_verified` means the client verified proof material and can treat the
result as final under the trustless acceptance rule.

## API Surface

### System

```text
GET /time
GET /health
GET /proof-policy
```

`/proof-policy` returns the active proof mode, accepted verifier ids, accepted
rulebook hash, latest proven height, and non-claim labels.

### Markets

```text
GET /markets
GET /markets/{market_id}
GET /markets/{market_id}/book
GET /markets/{market_id}/trades
GET /markets/{market_id}/candles
GET /markets/{market_id}/stats/24h
```

Each market response should include:

```text
market_id
base_asset
quote_asset
base_decimals
quote_decimals
price_tick_size
quantity_step_size
min_order_size
fee_rule_hash
matching_rule_hash
market_version
book_root
latest_height
latest_proven_height
data_status
```

### Orders

```text
POST   /orders
GET    /orders
GET    /orders/{order_id}
DELETE /orders/{order_id}
DELETE /orders
GET    /orders/{order_id}/fills
GET    /orders/{order_id}/receipt
GET    /orders/{order_id}/proof
```

`POST /orders` request fields:

```text
market_id
client_order_id
side
order_type
price
quantity
quote_quantity
time_in_force
expires_at
nonce
deadline
agent_key_id
signature
```

Rules:

- Amounts and prices are base-unit strings.
- `client_order_id` is unique per signer and market.
- Repeating the same semantic request is idempotent.
- Repeating a `client_order_id` with different semantics fails closed.
- `signature` covers the canonical order intent, including nonce and deadline.
- The API returns an immediate request receipt hash even when proof finality is
  pending.

### Fills

```text
GET /fills
GET /fills/{fill_id}
GET /fills/{fill_id}/receipt
GET /fills/{fill_id}/proof
```

Fill receipts should include:

```text
fill_id
maker_order_id
taker_order_id
market_id
price
quantity
maker_fee
taker_fee
pre_book_root
post_book_root
order_event_log_root
matching_rule_hash
fee_rule_hash
state_root_before
state_root_after
height
status
proof_status
```

### Proof Bundles

```text
GET /blocks/{height}/proof-bundle
GET /markets/{market_id}/proof-bundle?height=...
GET /proofs/{proof_id}
```

Proof bundle fields:

```text
proof_id
proof_type
verifier_id
image_id
rulebook_hash
header
body
journal
proof_receipt
proof_metadata
pre_state_root
post_state_root
tx_root
event_log_root
data_availability_root
client_verification_status
non_claims
```

The client SDK must fail closed on missing or mismatched `verifier_id`,
`image_id`, `rulebook_hash`, `post_state_root`, or proof receipt.

### Withdrawals

```text
POST /withdrawals
GET  /withdrawals
GET  /withdrawals/{withdrawal_id}
GET  /withdrawals/{withdrawal_id}/claim
```

Claim responses should include proof material, root identity, verifier identity,
chain id, bridge contract, destination, and proof status.

## Matching-Law Roadmap

### Stage 0: Product Skeleton

Build the REST shape, canonical request schemas, response statuses, and SDK
types. All proof fields may return `proof_pending` or `not_available`, but no
response may imply trustless finality.

Acceptance criteria:

- Order submit/list/detail/cancel endpoints exist.
- Market metadata exposes precision and rule hashes.
- `client_order_id` idempotency is tested.
- SDK labels proof-finality separately from execution.
- Unknown proof status fails closed in SDK finality helpers.

### Stage 1: Deterministic Replay Receipts

Implement deterministic local replay receipts for order events and fills.

Acceptance criteria:

- Replay recomputes book roots and fill receipts.
- Reordered fills fail replay.
- Skipped better prices fail replay.
- Fee drift fails replay.
- Duplicate nonce/order-event replay fails.

### Stage 2: Proof-Carrying Matching Law

Prove a bounded matching law:

```text
No higher-priority eligible order was skipped for any accepted fill.
```

Initial scope may be one market, limit orders, price-time priority, no hidden
order types, and bounded event batches.

Acceptance criteria:

- Guest proves pre-book root, event log root, fills, fees, and post-book root.
- Journal binds matching rule hash and fee rule hash.
- Proof metadata binds journal to ledger header `post_state_root`.
- Client verifier rejects bad image id, bad rulebook hash, bad root, bad
  receipt, reordered fill, skipped order, and fee drift.

### Stage 3: Trustless Client Finality

Wire proof verification into the client acceptance path.

Acceptance criteria:

- SDK exposes `verifyOrderProof`, `verifyFillProof`, and `verifyBlockProofBundle`.
- SDK finality helpers return final only on `proof_verified`.
- Browser/client pinset rejects unexpected verifier ids and rulebook hashes.
- Mutating proof, journal, header root, image id, or rulebook hash makes the SDK
  reject.

## Test Plan

### API Tests

- Place limit order.
- Place market order.
- Cancel order.
- Cancel all orders in a market.
- Duplicate `client_order_id` with identical payload returns same receipt.
- Duplicate `client_order_id` with changed payload rejects.
- Expired deadline rejects.
- Bad nonce rejects.
- Bad agent signature rejects.
- Bad precision rejects.

### Replay Tests

- Recompute order event log root.
- Recompute pre/post book root.
- Recompute fill receipt hash.
- Reject skipped higher-priority order.
- Reject crossed-book inconsistency.
- Reject fee schedule mismatch.
- Reject market-rule hash mismatch.

### Proof/Client Tests

- Reject missing proof when strict finality requested.
- Reject proof with wrong `image_id`.
- Reject proof with wrong `verifier_id`.
- Reject proof with wrong `rulebook_hash`.
- Reject journal `post_state_root` mismatch.
- Reject proof metadata/header mismatch.
- Reject receipt that verifies but is not bound to the requested order or fill.

## Product Milestones

1. Orderbook API skeleton and typed SDK responses.
2. Idempotent order submission with agent-key signatures.
3. Market data with book roots and proof-status labels.
4. Replay receipts for fills and book transitions.
5. Proof bundle schema and strict client verifier stubs.
6. Bounded matching-law proof for one market.
7. Client refuse-by-default finality path.

## Open Design Questions

- Which order types are in the first proof scope: limit only, or limit plus
  market IOC?
- Is cancellation sequenced as an order event in the same event log?
- What is the first batch bound for proof feasibility?
- Do we expose per-fill proofs, per-block proofs, or recursive rollups first?
- Which SDK is first: browser, Python bot, or TypeScript bot?
- Does the first matching-law proof live in RISC0, SP1, or an intermediate
  deterministic replay verifier before ZK?

