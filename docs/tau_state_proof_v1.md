# Tau Net State Proof (v1): DHT-bound, optional

## Goal

Enable **optional, per-block “verified computation” proofs** (e.g. Risc0) without changing Tau Testnet’s block format or consensus hash rules.

This v1 design:

- Stores **proof artifacts in the DHT** (large payload).
- Binds a proof to a block by using the block’s committed `state_hash` as the DHT key suffix.
- Allows **fail-closed enforcement** behind an explicit opt-in flag.

## Background (current Tau Testnet behavior)

Tau Testnet’s PoA pipeline commits to state via `header.state_hash` and uses the DHT for snapshot distribution:

- `tau_state:<state_hash>`: JSON payload containing Tau rules text plus hashes:
  - `rules`: Tau program text (utf-8 string)
  - `accounts_hash`: 32-byte hex (sha256 of accounts snapshot)
  - `app_hash` (optional): 32-byte hex (sha256 of canonical app snapshot)
- `state:<block_hash>`: accounts snapshot for that block.
- `app_state:<app_hash>`: canonical application snapshot bytes (optional, via the app bridge).

Secondary nodes can validate a new block by fetching these snapshots from the DHT and checking internal hash consistency, without re-executing all transactions.

## New DHT record: `state_proof:<state_hash>`

### Key

`state_proof:<state_hash>`

- `<state_hash>` is the exact 64-hex `header.state_hash` committed in the block.
- This binds the proof to the committed block state without requiring a new consensus field.

### Value (proof envelope)

The value is UTF-8 JSON bytes with a small, generic envelope:

```json
{
  "schema": "tau_state_proof",
  "schema_version": 1,
  "state_hash": "<64-hex>",
  "proof_type": "<string>",
  "proof": "<base64>",
  "meta": { "optional": "object" }
}
```

Notes:

- `state_hash` MUST equal the suffix in `state_proof:<state_hash>`.
- `proof_type` identifies the proving system and circuit/program (example: `"risc0.dex_transition.v1"`).
- `proof` is base64-encoded proof bytes (receipt).
- `meta` is optional debugging metadata (keep small; treat as untrusted).

## Publishing flow (miner / block producer)

After executing a block and computing `state_hash`, a miner MAY:

1. Generate a proof artifact for the block/state (implementation-specific).
2. Wrap it in the `tau_state_proof` envelope.
3. Publish it to the DHT under `state_proof:<state_hash>`.

Proof generation is **not** required by default.

### Generator command interface (recommended)

To keep Tau Testnet generic, proof generation should be delegated to an external command (Rust/Python/etc).

**Input (stdin):**

```json
{
  "schema": "tau_state_proof_request",
  "schema_version": 1,
  "state_hash": "<64-hex>",
  "block": { "...": "block dict (optional)" },
  "tau_state": { "rules": "...", "accounts_hash": "...", "app_hash": "..." },
  "context": { "...": "optional, implementation-specific proof context" }
}
```

**Output (stdout):** a `tau_state_proof` envelope JSON object.

## Verification flow (validators / followers)

This v1 protocol is **opt-in**:

- Default: do not require or verify proofs.
- Opt-in: require a proof for each block and **fail-closed** if missing/invalid.

Recommended enforcement algorithm for a follower processing a new block:

1. Read `expected_state_hash = block.header.state_hash`.
2. Fetch `tau_state:<expected_state_hash>` and verify its internal commitment.
3. Fetch `state_proof:<expected_state_hash>`.
4. Run a configured verifier over the proof envelope.
5. Reject the block if proof is missing or verification fails.

### Verifier command interface (recommended)

**Input (stdin):**

```json
{
  "schema": "tau_state_proof_verify",
  "schema_version": 1,
  "state_hash": "<64-hex>",
  "proof": { "...": "tau_state_proof envelope as object" },
  "block": { "...": "optional block dict (for tx binding)" },
  "tau_state": { "...": "optional tau_state dict (for expected app_hash, etc.)" },
  "context": { "...": "optional, implementation-specific proof context" }
}
```

**Output (stdout):**

```json
{ "ok": true }
```

On failure:

```json
{ "ok": false, "error": "reason" }
```

## Configuration (v1)

The reference implementation (Tau Testnet patch) uses env flags:

- Mining / publishing:
  - `TAU_STATE_PROOF_GENERATE_CMD`: if set, runs a generator command and publishes `state_proof:<state_hash>`.
  - `TAU_STATE_PROOF_GENERATE_REQUIRE=1`: fail block creation if proof generation/publish fails.
- Validation / enforcement:
  - `TAU_STATE_PROOF_REQUIRE=1`: require and verify `state_proof:<state_hash>` when processing new blocks.
  - `TAU_STATE_PROOF_VERIFY_CMD`: verifier command; fail-closed if missing when `TAU_STATE_PROOF_REQUIRE=1`.

## Upgrade path (future)

If the network wants stronger anti-equivocation guarantees, a future version can:

- Content-address proof blobs (`state_proof:<proof_hash>`) and
- Commit `proof_hash` into consensus (e.g. extend the `state_hash` computation or add a header field).

That would be consensus-affecting and should be introduced only with explicit versioning and rollout coordination.
