---
title: zenodex_spot_state_proof_risc0_v1
type: note
permalink: autonomous-tau-dex-review/docs/zenodex-spot-state-proof-risc0-v1
---

# ZenoDEX Spot Risc0 State Proof (v1)

## Legacy quarantine

This proof type is retained as historical regression source. Its workspace
resolves Risc0 1.2.6, which is affected by `GHSA-jqq4-c7wq-36h7`. The workspace
has authority `NONE` and is ineligible for governed release, settlement, claim
promotion, or production admission. The current proof-toolchain gate exits
nonzero while this quarantine remains.

This document specifies the concrete **Risc0 proof type** used by this repo’s
legacy ZenoDEX spot integration, carried in the generic Tau Testnet
`state_proof:<state_hash>` envelope (see `docs/tau_state_proof_v1.md`).

## Proof type

- `proof_type`: `risc0.zenodex_spot_transition.v1`
- Guest program (source): `zk/state_proof_risc0/methods/guest`
- Generator/verifier CLI: `zk/state_proof_risc0/cli` (binary `tau-state-proof-risc0-cli`)

## Proof metadata bindings

ZenoLedger proof metadata carries `toolchain_lock_hash`, computed from the
repo-local proof toolchain manifest by default. The manifest binds the Python
hash lockfiles, Docker build files, Lean toolchain/lake manifests, Risc0 Cargo
workspace lockfiles, and the Rust TEE attestation verifier lockfiles into the
metadata hash committed by `header.proof_journal_hash`.

Operators may pass `--toolchain-lock-hash` to the Risc0 or TEE metadata adapters
when replaying against an externally approved lock manifest.

The legacy Risc0 metadata adapter can also require the spot proof's `post_app_hash` to
match `header.post_state_root`. When `pre_app_hash` is present, it can require
that value to match `header.pre_state_root`. Empty pre-state proofs bind the
absence bit into the public-input hash and journal hash.

## Statement (what is proven)

Given:
- `state_hash` (32 bytes) for the block,
- the block’s app-relevant transaction list (bound via `txs_commitment`),
- the previous DEX `app_hash` (optional; empty for “no app state yet”),
- the current block’s expected DEX `app_hash`,

the prover shows that executing the ZenoDEX spot transition rules over the
committed transactions produces exactly the expected `app_hash`.

### Public outputs (Risc0 journal)

The journal is `StateProofJournalV1` from `zk/state_proof_risc0/shared/src/lib.rs`:

- `journal_version = 1`
- `state_hash`
- `txs_commitment`
- `ingress_commitment`
- `pre_nonce_root`
- `post_nonce_root`
- `accepted_receipts_root`
- `pre_app_hash_present`, `pre_app_hash`
- `post_app_hash`

## Transaction binding (`txs_commitment`)

`txs_commitment` is a SHA-256 digest over a deterministic binary encoding of the per-tx app ops (not the Tau Testnet merkle root).

- Domain prefix: ASCII `tau_state_proof_txs_v1:`
- Encoding: see `txs_commitment_v1(...)` in `zk/state_proof_risc0/shared/src/lib.rs`

Verifier flow:
1. Parse the block’s `transactions` into the typed `TauTxV1` list.
2. Compute `txs_commitment_v1(txs)`.
3. Require it equals the journal `txs_commitment`.

## Nonce and accepted-receipt binding

Each non-empty transaction in the Risc0 proof lane must carry `nonce`. The guest
builds `TxIngressFactV1 { sender_pubkey, nonce }` facts in transaction order,
checks per-sender nonce sequencing from `context.pre_nonces` (default empty),
and emits:

- `ingress_commitment`: commitment to the ordered ingress facts;
- `pre_nonce_root`: root of the starting per-sender next-nonce map;
- `post_nonce_root`: root after applying the accepted transaction nonces;
- `accepted_receipts_root`: commitment to ordered accepted transaction receipt
  facts over `(index, sender, nonce, accepted, tx_commitment)`.

The host verifier recomputes these values from the supplied block and
`context.pre_nonces`. This closes nonce sequencing for the successful spot v1
proof lane. Rejected transaction receipts are still out of scope for this proof
type, because the current guest aborts the proof on invalid transitions.

## Transition semantics (v1 scope)

This v1 guest proves the ZenoDEX spot state transition for a restricted but
useful subset:

- Supported intent kinds:
  - `CREATE_POOL`
  - `SWAP_EXACT_IN`
  - `ADD_LIQUIDITY`
  - `REMOVE_LIQUIDITY`
- Faucet op:
  - `operations["4"].mint` is supported (test/dev only; must not mint native)
- DoS / safety constraints (fail-closed):
  - at most **1 intent per transaction** (`operations["2"]`)
  - **native asset is rejected** in intents (v1 does not model per-tx native sync)
- Native mirror behavior:
  - after applying all txs in the block, the guest performs a final native sync using `context.chain_balances_post` to match the app-bridge’s “final sync” behavior.

The swap, liquidity, and pool-id derivation rules match the Python implementation:
- Pool id: `sha256(b"TauSwapPool" || asset0 || asset1 || str(fee_bps) || "CPMM" || "")`
- Fee: `ceil(amount_in * fee_bps / 10_000)`
- Output: `floor(reserve_out * net_in / (reserve_in + net_in))`
- Reserves: input reserve increases by **full** `amount_in` (fees stay in pool)
- Add liquidity:
  - chooses ratio-preserving used amounts with the v7 exact
    cross-multiplication branch rule;
  - mints `min(floor(amount0_used * lp_supply / reserve0),
    floor(amount1_used * lp_supply / reserve1))`;
  - rejects zero LP mint, inactive pools, empty pools, insufficient balances,
    native-asset pools, and minimum-bound violations.
- Remove liquidity:
  - returns `floor(lp_amount * reserve0 / lp_supply)` and
    `floor(lp_amount * reserve1 / lp_supply)`;
  - rejects inactive pools, zero or oversupply burns, insufficient LP balance,
    native-asset pools, and minimum-bound violations.

`TauSwapPool` is a legacy hash-domain prefix. It remains part of the pool-id
derivation so existing deterministic fixtures and state roots do not change.

## Real-proof smoke coverage

`tools/zeno_ledger_risc0_real_proof_smoke.py --case all` now requires real
Risc0 receipts for:

- `empty`
- `faucet_mint`
- `create_pool`
- `swap_exact_in`
- `add_liquidity`
- `remove_liquidity`
- `spot_block_liquidity_cycle`

The `spot_block_liquidity_cycle` case proves one multi-transaction block that
creates a pool, adds liquidity, swaps exact-in, removes liquidity, and binds the
pre-app hash, transaction commitment, post-app hash, state hash, and block
timestamp through the host verifier.

For each case, the smoke also emits a synthetic ZenoLedger v0 body, a bound
header, and Risc0 proof metadata. With `--require-proof-files`, the archive
checker loads those artifacts and requires:

- the generated metadata hash equals `header.proof_journal_hash`;
- the header/body roots validate;
- `post_app_hash` equals `header.post_state_root`;
- present `pre_app_hash` values equal `header.pre_state_root`;
- Risc0 metadata rebuild binds `ingress_commitment`, `pre_nonce_root`,
  `post_nonce_root`, and `accepted_receipts_root`;
- the proof, body, header, and metadata artifact files exist when
  `--require-proof-files` is used.

## Generator/verifier request `context` (Tau Testnet subprocess I/O)

The Tau Testnet `state_proof.py` patch forwards `context` into the subprocess JSON request.

The Risc0 generator requires:

```json
{
  "context": {
    "block_timestamp": 123,
    "app_state_pre": "<canonical json string or empty>",
    "app_hash_pre": "<64-hex or empty>",
    "chain_balances_post": { "<pubkey>": 12345 }
  }
}
```

The verifier additionally accepts (recommended):
- `block`: used to recompute `txs_commitment`
- `tau_state.app_hash`: used to check `post_app_hash`
- `context.app_hash_pre`: used to check `pre_app_hash`

## Upgrade path

Planned v2 extensions:
- multi-intent settlement / batch clearing proofs
- native-asset support by including per-tx `chain_balances` views (or an explicit commitment to them)
- optional signature checks in-guest where appropriate (likely still prefer “verify off-chain, prove transition”)
- rejected receipt execution when the proof scope moves from successful
  transition execution to full production ingress semantics
