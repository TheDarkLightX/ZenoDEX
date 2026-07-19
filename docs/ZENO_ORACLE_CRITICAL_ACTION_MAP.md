# Zeno Oracle Critical Action Map

Status: machine-checked runtime wiring map for the current local Oracle MVP
branch.

The consumer-profile catalog defines seven first-shell critical profiles. The
runtime checker compares that catalog against the integration modules that
currently consume Oracle adapter bridges and typed authorizations:

```bash
python3 tools/check_zeno_oracle_critical_action_map.py
```

Current expected receipt:

```text
catalog_profile_count = 7
runtime_wired_count = 5
design_only_backlog_count = 2
status = accepted
```

## Runtime-Wired Profiles

| Consumer | Action | Runtime path | Required control |
| --- | --- | --- | --- |
| `zenodex.perps` | `settle_epoch` | `src/integration/perp_engine.py` | `require_oracle_adapter_for_isolated_settle_epoch`, `require_oracle_adapter_for_clearinghouse_settle_epoch` |
| `zenodex.perps` | `liquidate_account` | `src/integration/perp_engine.py` | `require_oracle_adapter_for_isolated_partial_liquidate` |
| `zenodex.routing` | `guarded_quote` | `src/integration/api_server.py` | `DEX_ROUTING_ORACLE_ADAPTER_REQUIRED` |
| `zenodex.settlement` | `critical_settlement` | `src/integration/dex_engine.py` | `require_oracle_authorization_for_critical_settlements` |
| `zenodex.trigger` | `execute_trigger` | `src/integration/zeno_oracle_trigger_authorization.py` | `check_trigger_execute_oracle_adapter_bridge(required=True)`, `check_trigger_execute_oracle_authorization` |

The checker verifies that each runtime-wired surface still agrees with the
catalog query ID, catalog profile ID, expected consumer module, expected action
kind, and runtime action-ID binding. For routing it checks both exact-in and
exact-out guarded quote paths. For perps it checks isolated settlement, the two
clearinghouse settlement variants, and isolated partial liquidation under the
`liquidate_account` profile. For critical settlements it checks the typed
`OracleAuthorization` binding in `dex_engine` against the normalized settlement,
pre-state root, current settlement price, and settlement freshness controls. For
triggers it checks the existing typed trigger action facts against both an O3
adapter bridge result and the typed `OracleAuthorization` checker for the
cataloged `execute_trigger` profile.

## Blocked Profiles

The catalog retains `zenodex.zusd:mint` and
`zenodex.zusd:liquidate_vault`, but neither receives runtime-wired credit. The
production path is `src/integration/zusd_monetary_bridge.py`, which does not yet
commit a complete typed Oracle-authorization lifecycle for either action. The
deleted unsigned API and audit replay scaffolds are not runtime evidence. Both
profiles therefore remain fail-closed promotion blockers.

## CI Gate

The devnet alpha gate runs the map checker:

```bash
bash scripts/check_zeno_oracle_devnet_alpha.sh
```

That gate now executes:

- the Oracle MVP verifier/chaos gate;
- `tools/check_zeno_oracle_critical_action_map.py`;
- service-level devnet tests;
- the 17-case devnet disaster harness;
- the devnet alpha completion audit.

## Non-Claims

This map does not claim:

- design-only backlog profiles are runtime-wired;
- optional runtime adapter flags are enabled by default;
- a production Oracle network is live;
- every future ZenoDEX feature already has an Oracle adapter profile.
