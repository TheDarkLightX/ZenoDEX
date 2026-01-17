# TauSwap Risc0 State Proof (v1)

This document specifies the concrete **Risc0 proof type** used by this repo’s TauSwap DEX integration, carried in the generic Tau Testnet `state_proof:<state_hash>` envelope (see `docs/tau_state_proof_v1.md`).

## Proof type

- `proof_type`: `risc0.tauswap_transition.v1`
- Guest program (source): `zk/state_proof_risc0/methods/guest`
- Generator/verifier CLI: `zk/state_proof_risc0/cli` (binary `tau-state-proof-risc0-cli`)

## Statement (what is proven)

Given:
- `state_hash` (32 bytes) for the block,
- the block’s app-relevant transaction list (bound via `txs_commitment`),
- the previous DEX `app_hash` (optional; empty for “no app state yet”),
- the current block’s expected DEX `app_hash`,

the prover shows that executing the TauSwap transition rules over the committed transactions produces exactly the expected `app_hash`.

### Public outputs (Risc0 journal)

The journal is `StateProofJournalV1` from `zk/state_proof_risc0/shared/src/lib.rs`:

- `journal_version = 1`
- `state_hash`
- `txs_commitment`
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

## Transition semantics (v1 scope)

This v1 guest proves the TauSwap DEX state transition for a restricted but useful subset:

- Supported intent kinds:
  - `CREATE_POOL`
  - `SWAP_EXACT_IN`
- Faucet op:
  - `operations["4"].mint` is supported (test/dev only; must not mint native)
- DoS / safety constraints (fail-closed):
  - at most **1 intent per transaction** (`operations["2"]`)
  - **native asset is rejected** in intents (v1 does not model per-tx native sync)
- Native mirror behavior:
  - after applying all txs in the block, the guest performs a final native sync using `context.chain_balances_post` to match the app-bridge’s “final sync” behavior.

The swap math and pool-id derivation match the Python implementation:
- Pool id: `sha256(b"TauSwapPool" || asset0 || asset1 || str(fee_bps) || "CPMM" || "")`
- Fee: `ceil(amount_in * fee_bps / 10_000)`
- Output: `floor(reserve_out * net_in / (reserve_in + net_in))`
- Reserves: input reserve increases by **full** `amount_in` (fees stay in pool)

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

