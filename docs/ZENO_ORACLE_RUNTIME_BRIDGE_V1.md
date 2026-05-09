# Zeno Oracle Runtime Bridge V1

Status: concrete ZenoDEX perps, zUSD, routing, protected swap, trigger, and
critical-settlement consumer hooks.

The Oracle receipt chain is useful only if runtime actions refuse to treat raw
oracle-looking data as authority. The first runtime bridges are now wired into
perps settlement paths, critical zUSD API actions, and guarded routing quote
APIs, with typed authorization checks for protected swaps, zUSD, guarded
quotes, isolated perps settlement, and critical settlement.

## Perps Settlement Hook

`PerpEngineConfig` exposes two Oracle bridge controls:

```python
oracle_adapter_bridge_verifier: Optional[Callable[[Mapping[str, Any]], Any]]
require_oracle_adapter_for_isolated_settle_epoch: bool
require_oracle_adapter_for_clearinghouse_settle_epoch: bool
require_oracle_authorization_for_isolated_settle_epoch: bool
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

If `require_oracle_authorization_for_isolated_settle_epoch` is true, isolated
settlement also requires a typed `oracle_authorization` bound to the runtime
action facts and current oracle snapshot. The older internal spelling
`require_oracle_authorization_for_isolated_settle` remains accepted as an alias.

This prevents the wired perps settlement paths from accepting a receipt minted
for a different consumer, action, query, profile policy, market, market kind,
participant set, epoch, clearing price, or oracle snapshot, or accepting a
decorative bridge field that no runtime verifier checked.

## zUSD API Hook

The zUSD development API now gates the critical `mint_zusd` and `liquidate`
commands when `ZUSD_ORACLE_ADAPTER_REQUIRED` is enabled, and also verifies any
`oracle_adapter_bridge` supplied on those commands even when the requirement flag
is disabled.

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

## Protected Swap Authorization Hook

`DexEngineConfig.require_oracle_authorization_for_protected_swaps` makes
quote-receipt-bound exact-in and exact-out swaps require a typed
`oracle_authorization`. The runtime derives protected-swap action facts from the
intent, quote receipt, quoted leg, pool snapshot, amount constraint, query id,
and block epoch, then checks the authorization against those facts before nonce
application and settlement computation.

The production-candidate network config gate requires this control in
`runtime_controls` and binds the enabled-control set into the
`runtime_controls_attestation` receipt.

The protected swap hook rejects missing authorization when configured,
non-object authorization payloads, missing quote receipt witnesses, quote-leg
drift, wrong runtime value, wrong receipt context, and expired authorization.

## Trigger Execution Hooks

Trigger execution uses the catalog action identity `execute_trigger` for both
the O3 adapter bridge and typed Oracle authorization. The trigger command facts
still carry the local command action `execute`, but the Oracle-facing action
facts hash now records that local command under `trigger_action_kind` and records
`action_kind = "execute_trigger"` for the consumer profile boundary.

`check_trigger_execute_oracle_adapter_bridge(required=True)` rejects missing
bridges, wrong consumer/action/query/profile, and action-id drift.
`check_trigger_execute_oracle_authorization` rejects legacy `execute`
authorization aliases, wrong value, wrong pre-state context, below-O3 evidence,
expired authorization, unsatisfied trigger conditions, and catalog-profile
drift.

The production-candidate network config gate requires
`trigger_oracle_authorization_required` in `runtime_controls` and binds that
enabled control into the `runtime_controls_attestation` receipt.

## CI Coverage

The Oracle MVP gate runs:

```bash
pytest -q tests/integration/test_perp_engine.py -k oracle_adapter
pytest -q tests/integration/test_perp_engine_clearinghouse_2p.py -k oracle_adapter
pytest -q tests/integration/test_perp_engine_clearinghouse_3p_transfer.py -k oracle_adapter
pytest -q tests/integration/test_zusd_api.py -k oracle_adapter
pytest -q tests/integration/test_api_server_dex_api.py -k oracle_adapter
pytest -q tests/integration/test_zeno_oracle_trigger_authorization.py
```

Those tests cover:

- required bridge missing;
- bridge present with no verifier;
- verifier rejection;
- accepted bridge for the wrong action;
- accepted bridge for the wrong query;
- accepted bridge for the wrong runtime action ID;
- accepted bridge bound to the intended consumer/action.

## Non-Claims

This hook does not yet claim:

- every routing endpoint is runtime-wired;
- the zUSD demo API is the production chain transaction path;
- the external Oracle network is live;
- verifier callbacks are automatically configured by deployment tooling.

The current claim covers perps settlement, critical zUSD demo API actions,
guarded routing quote APIs, protected swaps, trigger execution helpers, and
critical-settlement authorization helpers. Production deployment still has to
enable the required runtime controls and provide the attestation receipt.
