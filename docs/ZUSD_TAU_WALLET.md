---
title: ZUSD_TAU_WALLET
type: note
permalink: autonomous-tau-dex-review/docs/zusd-tau-wallet
---

## zUSD Tau wallet / transport replay

This document describes a not-yet-published wallet/transport lane. It is not part of the current public replay contract.

If and when this lane is published, the repo should expose a wallet-facing CLI for Tau-native zUSD token transport:

```bash
python3 tools/zusd_tau_wallet.py transfer \
  --sender-pubkey <sender-pubkey> \
  --recipient-pubkey <recipient-pubkey> \
  --sender-balance-before 400 \
  --recipient-balance-before 50 \
  --amount 100 \
  --deadline 99 \
  --last-used-nonce 0 \
  --total-supply-before 1000 \
  --pretty
```

Supported subcommands:

- `transfer`
- `mint`
- `burn`

What it produces:

- a deterministic Tau token operation on stream `9`
- nonce progression derived from the token sender namespace
- Tau witness steps for:
  - `zusd_transfer_guard_v1.tau` on transfers
  - `protocol_token_v1.tau` on all token actions
- optional signed Tau transaction payloads when signing inputs are supplied

What it does not do:

- it does not change the zUSD monetary kernel itself
- it does not bypass Tau validation
- it does not authorize arbitrary minting; mint/burn remain actor-scoped and proof-bound

Proposed replay / assurance lane once published coherently:

```bash
bash tools/run_zusd_evidence.sh
python3 tools/permissionless_assurance.py replay zusd
```

The intended zUSD lane would cover:

- core monetary state-machine tests
- multi-vault redemption and liquidation tests
- Tau gate tests
- Tau transport helper tests
- wallet CLI tests
- Tau spec traces for the recommended zUSD guards
- ESSO `verify-multi` for `src/kernels/dex/protocol_token_v1.yaml`
