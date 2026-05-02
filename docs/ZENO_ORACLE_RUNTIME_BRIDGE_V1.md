# Zeno Oracle Runtime Bridge V1

Status: first concrete ZenoDEX consumer hook.

The Oracle receipt chain is useful only if runtime actions refuse to treat raw
oracle-looking data as authority. The first runtime bridge is now wired into the
isolated perps `settle_epoch` path.

## Perps Settlement Hook

`PerpEngineConfig` exposes two Oracle bridge controls:

```python
oracle_adapter_bridge_verifier: Optional[Callable[[Mapping[str, Any]], Any]]
require_oracle_adapter_for_isolated_settle_epoch: bool
```

When a `settle_epoch` op carries `oracle_adapter_bridge`, the engine:

1. requires the bridge to be a JSON object;
2. requires a configured verifier;
3. runs the verifier before settlement state changes;
4. requires verifier status `accepted`;
5. requires the verified bridge to bind to:

```text
consumer_module = "zenodex.perps"
action_kind     = "settle_epoch"
```

6. requires the verified bridge `action_id` to equal the deterministic runtime
   action ID for the exact settlement state.

The runtime action ID is the SHA-256 content hash of:

```text
schema = "zenodex.oracle.perps_runtime_action_id.v1"
chain_id
consumer_module = "zenodex.perps"
action_kind = "settle_epoch"
market_id
quote_asset
now_epoch
clearing_price_epoch
clearing_price_e8
index_price_e8
oracle_last_update_epoch
```

If `require_oracle_adapter_for_isolated_settle_epoch` is true, a settlement op
without `oracle_adapter_bridge` is rejected. If the bridge is present but no
verifier is configured, settlement is rejected even when the requirement flag is
false.

This prevents the first wired perps path from accepting a receipt minted for a
different consumer, action, market, epoch, clearing price, or oracle snapshot,
or accepting a decorative bridge field that no runtime verifier checked.

## CI Coverage

The Oracle MVP gate runs:

```bash
pytest -q tests/integration/test_perp_engine.py -k oracle_adapter
```

Those tests cover:

- required bridge missing;
- bridge present with no verifier;
- verifier rejection;
- accepted bridge for the wrong action;
- accepted bridge for the wrong runtime action ID;
- accepted bridge bound to `zenodex.perps / settle_epoch`.

## Non-Claims

This hook does not yet claim:

- clearinghouse perps settlement is Oracle-bridge gated;
- zUSD, routing, trigger, or liquidation consumers are runtime-wired;
- the external Oracle network is live;
- the verifier callback is automatically configured by deployment tooling.

The current claim is narrower: the isolated perps settlement engine now has a
fail-closed runtime bridge point that can require an accepted aggregate-derived
Oracle receipt before settlement proceeds.
