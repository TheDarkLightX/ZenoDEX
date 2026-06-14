---
title: PROOF_MINING_OPERATOR_API
type: note
permalink: autonomous-tau-dex-review/docs/proof-mining-operator-api
---

# Proof Mining Operator API

This API is for operators who want a live, fail-closed proof-mining status check before submitting a reward claim.
The HTTP route rejects client-submitted proof contexts; use the local CLI mode for the context-bound submit-ready check.

## Endpoint

`POST /api/dex/proof_mining_status`

The endpoint is advisory and mirrors the plugin's fail-closed shape checks before a `ZenoProofMining.submit_proof` operation is sent on-chain.
It does not accept `proof_mining_context` over HTTP, because the API server cannot distinguish a client-fabricated context from one emitted by the verified DEX execution path.

## CLI preflight

Use the shell wrapper in local mode when you have a verified DEX proof context and want the context-bound submit-ready check:

```bash
python3 tools/permissionless_proof_mining_status.py \
  --claim ./proof_claim.json \
  --proof-mining-context ./proof_context.json \
  --chain-balances ./chain_balances.json \
  --tx-sender-pubkey 0x<sender-pubkey> \
  --expected-proposal-hash sha256:<proposal_hash>
```

To call a running API server instead of evaluating locally, omit `--proof-mining-context`.
The HTTP preflight can confirm claim shape and live balances, then it fails closed with `claimable=false` until the claim reaches the plugin path with a verified execution context:

```bash
python3 tools/permissionless_proof_mining_status.py \
  --api-url http://127.0.0.1:8080 \
  --claim ./proof_claim.json \
  --chain-balances ./chain_balances.json \
  --tx-sender-pubkey 0x<sender-pubkey> \
  --expected-proposal-hash sha256:<proposal_hash>
```

The command exits `0` when the selected mode reports the claim is submit-ready and nonzero when the claim is not claimable or the API call fails.

## Request body

```json
{
  "app_state_json": "{...}",
  "chain_balances": {
    "0x<reward-pool-pubkey>": 20,
    "0x<sender-pubkey>": 123
  },
  "claim": {
    "body": { "...": "proof mining claim artifact" },
    "claim_hash": "sha256:..."
  },
  "tx_sender_pubkey": "0x<48-byte-pubkey>",
  "expected_proposal_hash": "sha256:..."
}
```

## Required environment

- `TAU_DEX_PROOF_MINING_POOL_PUBKEY`

Without that env var, the endpoint returns `enabled=false` and `claimable=false`.

## Response shape

```json
{
  "ok": true,
  "status": {
    "enabled": true,
    "claimable": false,
    "error": "proof mining claim requires verified DEX proof context",
    "reward_pool_pubkey": "0x...",
    "proposal_hash": "sha256:...",
    "reward_amount": 4,
    "reward_pool_before": 20,
    "reward_pool_after": 16,
    "checks": {
      "reward_pool_configured": true,
      "sender_valid": true,
      "claim_valid": true,
      "winner_matches_sender": true,
      "proposal_hash_matches_context": true,
      "verified_context_present": false,
      "reward_pool_balance_non_negative": true,
      "runtime_state_present": false,
      "reward_pool_pubkey_matches_state": false,
      "reward_pool_balance_matches_state": false,
      "runtime_apply_ok": false
    }
  }
}
```

If the endpoint can parse the request but the claim should not be submitted, it still returns `200` with `claimable=false` and a concrete `error` string.

Malformed requests return `400`.
Requests containing `proof_mining_context` return `400` with `proof_mining_context_not_accepted`.

## What it checks

The endpoint mirrors the runtime path in `src/integration/tau_testnet_dex_plugin.py`:

- reward-pool env is configured
- sender pubkey is canonical
- claim artifact passes validation
- `winner.miner_id` matches `tx_sender_pubkey`
- `claim.proposal_hash` matches `expected_proposal_hash`
- no client-supplied proof context was provided over HTTP
- reward-pool chain balance is non-negative
- wrapped proof-mining runtime state, if present, matches the configured reward pool
- wrapped proof-mining runtime state, if present, matches the live reward-pool balance
- the bounded proof-mining manager still accepts the claim

## Intended use

Use the local CLI mode before building the final operation bundle:

1. run the DEX proof-verification path off-chain and get `proposal_hash`
2. persist the verified proof context emitted by that DEX execution path
3. build the proof-mining claim artifact
4. call `tools/permissionless_proof_mining_status.py` without `--api-url`
5. only submit `ZenoProofMining.submit_proof` if `claimable=true`

Use `/api/dex/proof_mining_status` as a live balance and claim-shape preflight.
It is not a replacement for the on-chain/plugin checks, and it cannot make a context-bound submit-ready claim by itself.
