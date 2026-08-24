# Zeno Oracle Runtime Bridge V1

Status: first concrete ZenoDEX perps, zUSD, and routing consumer hooks.

The Oracle receipt chain is useful only if runtime actions refuse to treat raw
oracle-looking data as authority. The first runtime bridges are now wired into
perps settlement paths, critical zUSD API actions, and guarded routing quote
APIs.

## Perps Settlement Hook

`PerpEngineConfig` exposes separate adapter, typed-authorization, and
verifier-selected-root controls for settlement:

```python
oracle_adapter_bridge_verifier: Optional[Callable[[Mapping[str, Any]], Any]]
require_oracle_adapter_for_isolated_settle_epoch: bool
require_oracle_adapter_for_clearinghouse_settle_epoch: bool
require_oracle_authorization_for_isolated_settle: bool
require_oracle_authorization_for_clearinghouse_settle_epoch: bool
oracle_authorization_receipt_graph_root: Optional[str]
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
query_id        = sha256("zenodex.oracle.query.perps.index_price_e8")
profile_id      = published O3 / 2-epoch perps settle profile
```

6. requires the verified bridge `action_id` to equal the deterministic runtime
   action ID for the exact settlement state;
7. requires the bridge value and action epoch to equal the exact price and
   epoch consumed by settlement;
8. when typed authorization is required, verifies the action facts, pre-state,
   price, epoch, profile, query, and terminal receipt graph against the
   configured root.

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
without `oracle_adapter_bridge` is rejected on 2-party, 3-party, and N-party
clearinghouse perps. The corresponding typed-authorization controls require
`oracle_authorization`. A required authorization also requires a
verifier-selected receipt graph root. If the bridge is present but no verifier
is configured, settlement is rejected even when the requirement flag is false.

This prevents the wired perps settlement paths from accepting a receipt minted
for a different consumer, action, query, profile policy, market, market kind,
participant set, epoch, clearing price, or oracle snapshot, or accepting a
decorative bridge field that no runtime verifier checked.

The wallet and Tau-testnet adapters can bind these controls through:

```text
TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_SETTLE_EPOCH
TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_ISOLATED_SETTLE
TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH
TAU_DEX_PERP_ORACLE_AUTHORIZATION_RECEIPT_GRAPH_ROOT
```

The wallet adapter copies a supplied `oracle_authorization` into an owned
canonical JSON object before constructing the engine operation. Typed
authorization remains disabled by default on these development adapters until
an authorization producer and verifier-selected root are configured. The
`zeno_oracle_fail_closed_perp_config` helper forces both typed-authorization
controls on for fail-closed profiles.

## zUSD API Hook

The zUSD development API now gates the critical `mint_zusd` and `liquidate`
commands when `ZUSD_ORACLE_ADAPTER_REQUIRED` is enabled, and also verifies any
`oracle_adapter_bridge` supplied on those commands even when the requirement flag
is disabled.

When `ZUSD_ORACLE_AUTHORIZATION_REQUIRED` is enabled, the same critical
`mint_zusd` and `liquidate` commands also require typed `oracle_authorization`.
The authorization is checked against the runtime action kind (`mint` or
`liquidate_vault`), the per-action zUSD profile, the runtime action ID,
action-facts hash, pre-state hash, query ID, active or pending oracle price, and
current epoch. This keeps the O3 adapter receipt and the runtime-consumed typed
authorization bound to the same zUSD action surface.

The verified bridge must bind to:

```text
consumer_module = "zenodex.zusd"
action_kind     = "mint" | "liquidate_vault"
query_id        = sha256("zenodex.oracle.query.zusd.collateral_price_e8")
profile_id      = published zUSD mint/liquidation profile
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
different command, query, profile policy, mode, argument set, active oracle
price, pending oracle price, or oracle update epoch.

The Oracle MVP gate also runs:

```bash
pytest -q tests/integration/test_zusd_api.py -k oracle_adapter
pytest -q tests/integration/test_zusd_api.py -k oracle_authorization
```

The zUSD hook does not claim that the zUSD API is the production chain
transaction path; `src/integration/zusd_api.py` remains a demo/development API.

## Routing Guarded-Quote Hooks

The DEX API now gates these endpoints when
`DEX_ROUTING_ORACLE_ADAPTER_REQUIRED` is enabled, and also verifies any
`oracle_adapter_bridge` supplied on those requests even when the requirement
flag is disabled:

- `/api/dex/quote_exact_in_route_guarded`
- `/api/dex/quote_exact_out_many_pool_guarded`

The verified bridge must bind to:

```text
consumer_module = "zenodex.routing"
action_kind     = "guarded_quote"
query_id        = sha256("zenodex.oracle.query.routing.reference_price_e8")
profile_id      = published O3 / 4-epoch routing guarded-quote profile
```

The routing runtime action ID is the SHA-256 content hash of:

```text
schema = "zenodex.oracle.routing_runtime_action_id.v1"
consumer_module = "zenodex.routing"
action_kind = "guarded_quote"
path = "/api/dex/quote_exact_in_route_guarded"
quote_kind = "exact_in"
asset_in
asset_out
amount_in
split_search_profile
enable_mixed_direct_twohop_split
binding_ok
pool_snapshot_hash
```

For the exact-out many-pool guarded quote endpoint, the runtime action ID uses
the same schema with:

```text
path = "/api/dex/quote_exact_out_many_pool_guarded"
quote_kind = "exact_out_many_pool"
asset_in
asset_out
amount_out_total
max_legs
max_candidate_pools
max_candidates
max_iters
window
brute_force_max
max_enumerated_candidates
pool_snapshot_hash
```

The pool snapshot hash commits to the ordered pool snapshots used by the
request. This prevents a guarded quote request from borrowing a receipt for a
different route query, profile policy, asset pair, amount, route policy, binding
flag, or pool snapshot.

The Oracle MVP gate also runs:

```bash
pytest -q tests/integration/test_api_server_dex_api.py -k oracle_adapter
```

The routing hooks are currently limited to the exact-in guarded quote endpoint
and the exact-out many-pool guarded quote endpoint. They do not claim every
quote, packet-build, advisory, or verification endpoint is runtime-wired.

## CI Coverage

The Oracle MVP gate runs:

```bash
pytest -q tests/integration/test_perp_engine.py -k oracle_adapter
pytest -q tests/integration/test_perp_engine_clearinghouse_2p.py -k oracle_adapter
pytest -q tests/integration/test_perp_engine_clearinghouse_3p_transfer.py -k oracle_adapter
pytest -q tests/integration/test_zusd_api.py -k oracle_adapter
pytest -q tests/integration/test_zusd_api.py -k oracle_authorization
pytest -q tests/integration/test_api_server_dex_api.py -k oracle_adapter
pytest -q tests/integration/test_zeno_oracle_trigger_authorization.py
bash tools/run_runtime_shell_assurance_gate.sh
python3 tools/check_runtime_shell_assurance_manifest.py
```

Those tests cover:

- required bridge missing;
- bridge present with no verifier;
- verifier rejection;
- accepted bridge for the wrong action;
- accepted bridge for the wrong query;
- accepted bridge for the wrong runtime action ID;
- accepted bridge bound to the intended consumer/action.
- isolated perps v3 `settle_epoch` rejection when the Oracle snapshot is
  missing, zero-priced, stale, or from the same epoch.

## Non-Claims

This hook does not yet claim:

- every routing endpoint is runtime-wired;
- the zUSD demo API is the production chain transaction path;
- the external Oracle network is live;
- verifier callbacks are automatically configured by deployment tooling.

The current claim is narrower: perps settlement, critical zUSD demo API actions,
trigger execution, and guarded routing quote APIs now have fail-closed runtime
bridge points that can require an accepted aggregate-derived Oracle receipt
before execution proceeds. zUSD, trigger execution, protected swap, isolated
perps settlement, and critical settlement also have typed authorization tests.
