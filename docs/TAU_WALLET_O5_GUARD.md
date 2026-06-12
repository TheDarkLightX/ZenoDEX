---
title: TAU_WALLET_O5_GUARD
type: note
permalink: autonomous-tau-dex-review/docs/tau-wallet-o5-guard
---

# Tau Wallet `o5` Guard

This repo includes a sender-scoped outbound guard built around Tau Testnet's
user-policy output `o5`.

## Purpose

Use `o5` as a hard veto bit for wallet and auto-trader safety policy:

- `o5 = 0`: block
- `o5 = 1`: allow
- missing `o5`: neutral / no user-policy veto

The control-plane pattern is:

- built-in transfer validity stays in `o1`
- custom user policy writes to `o5`
- effective allow is `o1 && (o5 != 0)`

## Repo Artifacts

- Tau replay spec:
  [autotrader_wallet_outbound_guard_v1.tau](../src/tau_specs/recommended/autotrader_wallet_outbound_guard_v1.tau)
- Python adapter:
  [strategy_wallet_outbound_guard_v1_adapter.py](../src/kernels/python/strategy_wallet_outbound_guard_v1_adapter.py)
- ESSO kernel:
  [strategy_wallet_outbound_guard_v1.yaml](../src/kernels/dex/strategy_wallet_outbound_guard_v1.yaml)
- Tau witness builder:
  [tau_witness.py](../src/integration/tau_witness.py)
- Raw Tau Testnet rule generator:
  [tau_user_policy.py](../src/integration/tau_user_policy.py)
- Local node demo:
  [tau_testnet_o5_wallet_policy_demo.py](../tools/tau_testnet_o5_wallet_policy_demo.py)

## Semantics

The repo-local formal guard is sender-scoped and fail-closed:

- disabled rule is neutral and allows
- sender mismatch is neutral and allows
- matching sender must satisfy:
  - amount cap
  - destination allowed
  - session active
  - policy hash match

That sender-scoped neutrality matters because `o5` is shared: one user's rule must
not block another user's transfers.

## Local Tau Testnet Demo

If a local Tau Testnet node is running and supports `o5` user-policy output:

```bash
python3 tools/tau_testnet_o5_wallet_policy_demo.py \
  --amount 150 \
  --max-amount 100 \
  --mine
```

This tool:

1. derives the sender pubkey from the provided private key
2. looks up or creates the Tau numeric sender id in the local node DB
3. builds a raw Tau rule that blocks matching-sender transfers above the cap
4. submits a signed transfer with that rule in operation `0`
5. optionally mines a block

The generated rule shape is:

```tau
always (
  o5[t] = { 1 }:bv <-> ((!(i3[t]:bv = { sender_id }:bv)) || (i1[t]:bv <= { max_amount }:bv))
).
```

That means:

- if `i3` is not the scoped sender, allow
- if `i3` is the scoped sender, only allow when `i1 <= max_amount`

## Inputs

For the repo-local replay spec:

- `i1`: amount
- `i2`: max outbound amount
- `i3`: sender id
- `i4`: scoped sender id
- `i5`: destination allowed
- `i6`: session active
- `i7`: policy hash ok
- `i8`: enabled

Final allow/block output:

- `o5`: outbound allowed

## Why This Matters

This is the intended use of Tau for the wallet and auto-trader:

- Tau is the hard veto / control plane
- the local executor remains the fast path
- no per-trade Tau round trip is required for hot execution
- Tau still enforces caps, revocation, session policy, and destination restrictions
