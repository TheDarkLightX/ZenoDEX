# Zeno Oracle Runtime Bridge V1

Status: first concrete ZenoDEX perps, zUSD, and routing consumer hooks.

The Oracle receipt chain is useful only if runtime actions refuse to treat raw
oracle-looking data as authority. The first runtime bridges are now wired into
perps settlement paths, critical zUSD API actions, and guarded routing quote
APIs.

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
query_id        = sha256("zenodex.oracle.query.perps.index_price_e8")
profile_id      = published O3 / 2-epoch perps settle profile
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
for a different consumer, action, query, profile policy, market, market kind,
participant set, epoch, clearing price, or oracle snapshot, or accepting a
decorative bridge field that no runtime verifier checked.

## zUSD Production Gap

The unsigned in-memory zUSD API was deleted. Its former adapter and typed
authorization checks do not transfer release credit to the production monetary
path. `src/integration/zusd_monetary_bridge.py` must commit and verify the full
`mint` and `liquidate_vault` Oracle lifecycle before those two catalog profiles
can move out of the blocked set. Audit replay scaffolds are evidence tools, not
transaction authority.

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
- zUSD mint or liquidation is Oracle-authorized on the production monetary path;
- the external Oracle network is live;
- verifier callbacks are automatically configured by deployment tooling.

The current claim is narrower: perps settlement, trigger execution, guarded
routing quote APIs, protected swaps, and critical settlement have fail-closed
runtime bridge or typed-authorization coverage. The two zUSD profiles remain
explicitly blocked.
