# Orderbook API Patterns

This note records useful public product patterns from modern order-book APIs and
adapts them to ZenoDEX's proof-carrying architecture.

## Reusable Product Patterns

### Bot-Compatible Authentication

Useful pattern:

- Headless wallet sign-in for first API-key creation.
- API key plus HMAC for private REST requests.
- Short replay window on signed requests.
- Per-device trading keys so bots do not need the main wallet online for every
  order.

ZenoDEX adaptation:

- Keep transport auth separate from authority-bearing trade signatures.
- Use agent keys for order submission, cancellation, transfer, and withdrawal
  requests.
- Bind every state-changing request to a nonce, deadline, client order id, and
  canonical signing payload.
- Make server time available for clients, but never make local wall-clock
  agreement an assurance claim.

### Order Lifecycle Endpoints

Useful pattern:

```text
POST   /orders
GET    /orders
GET    /orders/{id}
DELETE /orders/{id}
DELETE /orders
GET    /orders/{id}/trades
GET    /orders/{id}/average-price
GET    /orders/{id}/transaction
```

ZenoDEX adaptation:

```text
POST   /orders
GET    /orders
GET    /orders/{id}
DELETE /orders/{id}
DELETE /orders
GET    /orders/{id}/fills
GET    /orders/{id}/receipt
GET    /orders/{id}/proof
GET    /fills/{id}/proof
GET    /blocks/{height}/proof-bundle
```

Submit acknowledgement and proof finality should be different states. An order
can be received, sequenced, matched, settled, and proof-finalized at different
times.

### Market Data Endpoints

Useful pattern:

```text
GET /markets
GET /markets/{ticker}
GET /markets/{ticker}/order-book
GET /markets/{ticker}/trades
GET /markets/{ticker}/price
GET /markets/{ticker}/24hr
GET /markets/{ticker}/candles
```

ZenoDEX adaptation:

- Include base-unit precision fields and formatted fields.
- Include market version and rulebook hash for any market with proof-carrying
  semantics.
- Expose the current canonical book root and latest proven height.
- Label data freshness clearly: live preview, replay-verified, proof-finalized.

### Client Order IDs

Useful pattern:

- Client-supplied order identifiers for bot reconciliation.
- Duplicate submissions return the existing order instead of creating an
  unintended second order.

ZenoDEX adaptation:

- Bind `client_order_id` to signer, market, side, quantity, price, nonce, and
  expiry in the canonical request hash.
- Return a deterministic request receipt hash immediately.
- A duplicate request with different semantics must fail closed.

### Withdrawal Claim Proofs

Useful pattern:

```text
POST /withdrawals
GET  /withdrawals
GET  /withdrawals/{id}
GET  /withdrawals/{id}/claim
```

Modern bridge-style APIs often expose local and global exit-proof fields for
asynchronous withdrawal claims.

ZenoDEX adaptation:

- Use the same async shape for withdrawal, trade, settlement, and block proof
  bundles.
- A claim endpoint should return proof material plus the exact root and verifier
  identity the client must check.
- The SDK must refuse a claim whose proof, root, verifier id, or rulebook hash
  does not match the client's accepted pinset.

## Proof-Carrying Orderbook Shape

For a proof-carrying order book, every accepted fill should eventually have:

```text
fill_receipt
order_event_log_root
pre_book_root
post_book_root
matching_rule_hash
fee_rule_hash
state_root_before
state_root_after
zk_receipt_or_recursive_proof
client_verification_report
```

The client acceptance rule should be:

```text
ClientAcceptsFill :=
  checkpoint_chain_verified
  and proof_receipt_verified
  and journal_bound_to_header_root
  and image_id_pinned
  and rulebook_hash_pinned_or_validly_upgraded
  and matching_law_verified
```

The matching law target:

```text
No higher-priority eligible order was skipped for this fill.
```

This gives ZenoDEX a stronger product claim than a generic "ZK order book":
the user receives a client-verifiable proof that the host followed the matching
law.

## Status Labels

Use these labels in API responses and UI:

- `received`: request accepted by an API edge.
- `sequenced`: request included in a canonical event sequence.
- `executed`: host produced an execution result.
- `replay_verified`: result passed deterministic local replay.
- `proof_pending`: proof not ready yet.
- `proof_verified`: client verified proof, root binding, and rulebook pins.
- `rejected`: request or proof failed.

Only `proof_verified` can support a trustless acceptance claim.

## Non-Claims

- This note does not assert that any external project satisfies these properties.
- API surface alone does not prove matching fairness, solvency, custody safety,
  or privacy.
- HMAC/API-key authentication is operational security, not consensus validity.
- A withdrawal Merkle proof is not a proof of order matching fairness.
- A ZK receipt proves the program identified by its verifier identity executed;
  the client still needs semantic pinning for which program is accepted.
