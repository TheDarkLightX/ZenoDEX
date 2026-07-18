---
title: PROOF_MINING_OPERATOR_API
type: note
permalink: autonomous-tau-dex-review/docs/proof-mining-operator-api
---

# Proof Mining Operator API

This API is for operators who already have a verified DEX proof context and want to know whether a proof-mining claim is currently submit-ready.

## Endpoint

`POST /api/dex/proof_mining_status`

The endpoint is advisory and mirrors the plugin's fail-closed checks before a `ZenoProofMining.submit_proof` operation is sent on-chain.

## CLI preflight

Use the shell wrapper if you want the same check without hand-crafting HTTP requests:

```bash
python3 tools/permissionless_proof_mining_status.py \
  --claim ./proof_claim.json \
  --proof-mining-context ./proof_context.json \
  --chain-balances ./chain_balances.json \
  --tx-sender-pubkey 0x<sender-pubkey> \
  --expected-proposal-hash sha256:<proposal_hash>
```

To call a running API server instead of evaluating locally:

```bash
python3 tools/permissionless_proof_mining_status.py \
  --api-url http://127.0.0.1:8080 \
  --claim ./proof_claim.json \
  --proof-mining-context ./proof_context.json \
  --chain-balances ./chain_balances.json \
  --tx-sender-pubkey 0x<sender-pubkey> \
  --expected-proposal-hash sha256:<proposal_hash>
```

The command exits `0` when the claim is submit-ready and nonzero when the claim is not claimable or the API call fails.

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
  "proof_mining_context": {
    "...": "verified DEX proof context"
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
    "claimable": true,
    "error": null,
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
      "recipient_differs_from_reward_pool": true,
      "proposal_hash_matches_context": true,
      "verified_context_present": true,
      "chain_balance_identity_unambiguous": true,
      "reward_pool_balance_non_negative": true,
      "runtime_state_present": false,
      "reward_pool_pubkey_matches_state": false,
      "reward_pool_balance_matches_state": false,
      "runtime_apply_ok": true
    }
  }
}
```

If the endpoint can parse the request but the claim should not be submitted, it still returns `200` with `claimable=false` and a concrete `error` string.

Malformed requests return `400`.

## What it checks

The endpoint mirrors the runtime path in `src/integration/tau_testnet_dex_plugin.py`:

- reward-pool env is configured
- sender pubkey is canonical
- claim artifact passes validation
- `winner.miner_id` matches `tx_sender_pubkey`
- the reward recipient differs from the internal reward-pool principal
- `claim.proposal_hash` matches `expected_proposal_hash`
- a verified DEX proof context is present and matches the claim binding
- every Tau chain-balance principal has one unambiguous exact spelling
- reward-pool chain balance is non-negative
- wrapped proof-mining runtime state, if present, matches the configured reward pool
- wrapped proof-mining runtime state, if present, matches the live reward-pool balance
- the bounded proof-mining manager still accepts the claim

Self-payment is rejected with `proof mining reward recipient must differ from reward pool`.
This check is enforced by both the preview endpoint and the authoritative app bridge.
Raw 96-hex Tau balance keys are resolved to canonical `0x`-prefixed principals.
Supplying both spellings of the same principal rejects before state application.

## Intended use

Use this before building the final operation bundle:

1. run the DEX proof-verification path off-chain and get `proposal_hash`
2. persist the verified proof context emitted by that DEX execution path
3. build the proof-mining claim artifact
4. call `/api/dex/proof_mining_status`
5. only submit `ZenoProofMining.submit_proof` if `claimable=true`

This is not a replacement for the on-chain/plugin checks. It is a preflight surface so operators can fail early and avoid sending obviously bad claims.
