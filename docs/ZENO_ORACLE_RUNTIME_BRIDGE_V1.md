# Zeno Oracle Runtime Bridge V1

Status: first concrete ZenoDEX perps and zUSD consumer hooks.

The Oracle receipt chain is useful only if runtime actions refuse to treat raw
oracle-looking data as authority. The first runtime bridges are now wired into
perps settlement paths and critical zUSD API actions.

## Perps Settlement Hook

`PerpEngineConfig` exposes two Oracle bridge controls:

```python
oracle_adapter_bridge_verifier: Optional[Callable[[Mapping[str, Any]], Any]]
require_oracle_adapter_for_isolated_settle_epoch: bool
require_oracle_adapter_for_clearinghouse_settle_epoch: bool
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

For isolated perps, the runtime action ID is the SHA-256 content hash of:

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

For clearinghouse perps, the runtime action ID uses:

```text
schema = "zenodex.oracle.perps_clearinghouse_runtime_action_id.v1"
chain_id
consumer_module = "zenodex.perps"
action_kind = "settle_epoch"
market_kind
market_id
quote_asset
participant_pubkeys
now_epoch
clearing_price_epoch
clearing_price_e8
index_price_e8
oracle_last_update_epoch
```

If `require_oracle_adapter_for_isolated_settle_epoch` is true, a settlement op
without `oracle_adapter_bridge` is rejected on isolated perps. If
`require_oracle_adapter_for_clearinghouse_settle_epoch` is true, a settlement op
without `oracle_adapter_bridge` is rejected on 2-party and 3-party clearinghouse
perps. If the bridge is present but no verifier is configured, settlement is
rejected even when the requirement flag is false.

This prevents the wired perps settlement paths from accepting a receipt minted
for a different consumer, action, market, market kind, participant set, epoch,
clearing price, or oracle snapshot, or accepting a decorative bridge field that
no runtime verifier checked.

## zUSD API Hook

The zUSD development API now gates the critical `mint_zusd` and `liquidate`
commands when `ZUSD_ORACLE_ADAPTER_REQUIRED` is enabled, and also verifies any
`oracle_adapter_bridge` supplied on those commands even when the requirement flag
is disabled.

The verified bridge must bind to:

```text
consumer_module = "zenodex.zusd"
action_kind     = "mint" | "liquidate_vault"
```

The zUSD runtime action ID is the SHA-256 content hash of:

```text
schema = "zenodex.oracle.zusd_runtime_action_id.v1"
consumer_module = "zenodex.zusd"
action_kind
mode = "single" | "multi"
tag
args
now_epoch
price_e8
price_pending_e8
oracle_last_update_epoch
```

This prevents a zUSD mint/liquidation request from borrowing a receipt for a
different command, mode, argument set, active oracle price, pending oracle price,
or oracle update epoch.

The Oracle MVP gate also runs:

```bash
pytest -q tests/integration/test_zusd_api.py -k oracle_adapter
```

The zUSD hook does not claim that the zUSD API is the production chain
transaction path; `src/integration/zusd_api.py` remains a demo/development API.

## CI Coverage

The Oracle MVP gate runs:

```bash
pytest -q tests/integration/test_perp_engine.py -k oracle_adapter
pytest -q tests/integration/test_perp_engine_clearinghouse_2p.py -k oracle_adapter
pytest -q tests/integration/test_perp_engine_clearinghouse_3p_transfer.py -k oracle_adapter
pytest -q tests/integration/test_zusd_api.py -k oracle_adapter
```

Those tests cover:

- required bridge missing;
- bridge present with no verifier;
- verifier rejection;
- accepted bridge for the wrong action;
- accepted bridge for the wrong runtime action ID;
- accepted bridge bound to the intended consumer/action.

## Non-Claims

This hook does not yet claim:

- routing or trigger consumers are runtime-wired;
- the zUSD demo API is the production chain transaction path;
- the external Oracle network is live;
- verifier callbacks are automatically configured by deployment tooling.

The current claim is narrower: perps settlement and critical zUSD demo API
actions now have fail-closed runtime bridge points that can require an accepted
aggregate-derived Oracle receipt before execution proceeds.
