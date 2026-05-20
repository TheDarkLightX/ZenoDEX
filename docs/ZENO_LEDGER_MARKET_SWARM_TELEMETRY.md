# ZenoLedger Market Swarm Telemetry

`tools/zeno_ledger_market_swarm.py` drives deterministic synthetic agents against
the live Docker testnet. It is meant for stress testing and model-data capture,
not for production trading.

The swarm submits real testnet writes:

```text
bootstrap faucet funding
momentum swaps
mean-reversion swaps
noise swaps
large whale swaps
liquidity add/remove churn
high min-output unfilled probes
malformed tx probes
readonly-node rejection probes
```

Every row carries the request hash, target node, agent id, action family,
receipt status, expected-valid flag, and context features such as pool reserves
and trade stress. Receipts remain authoritative; telemetry is only observation
data for WES, energy models, dashboards, and offline learning.

## Run

```bash
python3 tools/zeno_ledger_market_swarm.py \
  --writer-url http://127.0.0.1:8787 \
  --forwarder-url http://127.0.0.1:8788 \
  --readonly-url http://127.0.0.1:8789 \
  --token "${ZENO_LEDGER_WRITER_TOKEN:-local-multidocker-token}" \
  --seed zenodex-market-swarm-v0 \
  --agents 16 \
  --steps 500 \
  --out-dir artifacts/market_swarm/run-001
```

Outputs:

```text
artifacts/market_swarm/run-001/report.json
artifacts/market_swarm/run-001/telemetry.jsonl
```

## Node Telemetry API

Each node can reconstruct live trade telemetry from its canonical live ledger
artifacts:

```bash
curl 'http://127.0.0.1:8787/telemetry/trades?limit=1000'
curl 'http://127.0.0.1:8787/telemetry/summary?limit=10000'
```

The row schema is:

```text
zenodex.zeno_ledger.node_trade_telemetry_row.v0
```

Important fields:

```text
height
time_ms
node_id
node_role
tx_id
tx_hash
intent_kind
pool_id
asset_in
asset_out
amount_in
min_amount_out
accepted
error_code
receipt_hash
features.stress_bps
features.reserve_skew_bps
context.pre_pool
context.post_pool
```

Because the API reconstructs from ledger bodies, receipts, headers, and
snapshots, it is suitable for model training without introducing another trusted
logger. Models can rank, summarize, or learn from the rows; they cannot change
checker verdicts.

## Model Use

Good first labels:

```text
accepted
rejected
error_code
stress_bps
reserve_skew_bps
action_family
invalid_accepted
```

Useful first objectives:

```text
predict rejected high-stress candidates
rank near-miss probes for WES
estimate checker/runtime cost from action family and pool context
detect action sequences that lead to high slippage or LP churn
```

Keep train/test splits by `run_id` and `seed`, not random rows, so models must
generalize across market episodes.
