---
title: AUTOTRADER_POLICY_COMPILE
type: note
permalink: autonomous-tau-dex-review/docs/autotrader-policy-compile
---

# Auto-Trader Policy Compile

`tools/autotrader_policy_compile.py` is the deterministic frontend for turning
bounded policy text into the repo's `StrategyIR`.

It is intentionally not a free-form "LLM decides trades" interface. The tool
only accepts:

- controlled DCA sentences
- explicit `key: value` policy documents

Everything compiles through the same bounded policy compiler in
[`src/agents/policy_compiler.py`](../src/agents/policy_compiler.py).

## Supported Forms

Controlled sentence form:

```text
dca 100 zUSD into BTC every 4 epochs until epoch 20 max slippage 25 bps per window max 300 lifetime max 900 backend tau max live orders 2
```

Explicit `key: value` form:

```text
template: dca
strategy_id: dca.kv.1
owner_pubkey: owner.pubkey.1
backend: local
asset_in: zUSD
asset_out: BTC
fixed_order_size: 100
cadence_epochs: 4
per_order_max: 100
per_window_max: 500
lifetime_max: 1000
valid_from_epoch: 1
valid_until_epoch: 100
```

## Output

The CLI emits JSON with:

- the normalized candidate payload
- compiled `StrategyIR`
- local-policy document
- Tau compile-contract receipt for replay against
  `autotrader_compile_contract_v1.tau`
- optional advisory KRR output

Schema: `zenodex/autotrader-policy-compile/v1`

## Trust Boundary

- Text input is untrusted.
- The parser is deterministic and bounded.
- Unsupported text fails closed.
- KRR is advisory only and never bypasses the compiler.
- The compiled policy still has to pass shell/controller guards before any
  intent can be emitted.

## Usage

Inline text:

```bash
python3 tools/autotrader_policy_compile.py \
  --text "dca 100 zUSD into BTC every 4 epochs until epoch 20 backend tau" \
  --owner-pubkey owner.pubkey.1 \
  --pretty
```

Policy file:

```bash
python3 tools/autotrader_policy_compile.py \
  --text-file /path/to/policy.txt \
  --owner-pubkey owner.pubkey.1 \
  --krr-backend off
```