# Zeno Oracle Critical Action Map

Status: machine-checked runtime wiring map for the current local Oracle MVP
branch.

The consumer-profile catalog defines six first-shell critical profiles. The
runtime checker compares that catalog against the integration modules that
currently consume Oracle adapter bridges and typed `OracleAuthorization`
bundles:

```bash
python3 tools/check_zeno_oracle_critical_action_map.py
```

Current expected receipt:

```text
catalog_profile_count = 6
runtime_wired_count = 4
design_only_backlog_count = 2
status = accepted
```

## Runtime-Wired Profiles

| Consumer | Action | Runtime path | Required control |
| --- | --- | --- | --- |
| `zenodex.perps` | `settle_epoch` | `src/integration/perp_engine.py` | `require_oracle_adapter_for_isolated_settle_epoch`, `require_oracle_adapter_for_clearinghouse_settle_epoch`, `require_oracle_authorization_for_isolated_settle_epoch` |
| `zenodex.zusd` | `mint` | `src/integration/zusd_api.py` | `ZUSD_ORACLE_ADAPTER_REQUIRED`, `ZUSD_ORACLE_AUTHORIZATION_REQUIRED` |
| `zenodex.zusd` | `liquidate_vault` | `src/integration/zusd_api.py` | `ZUSD_ORACLE_ADAPTER_REQUIRED`, `ZUSD_ORACLE_AUTHORIZATION_REQUIRED` |
| `zenodex.routing` | `guarded_quote` | `src/integration/api_server.py` | `DEX_ROUTING_ORACLE_ADAPTER_REQUIRED`, `DEX_ROUTING_ORACLE_AUTHORIZATION_REQUIRED` |

The checker verifies that each runtime-wired surface still agrees with the
catalog query ID, catalog profile ID, expected consumer module, expected action
kind, and runtime action-ID binding. For routing it checks both exact-in and
exact-out guarded quote paths. For perps it checks isolated settlement plus the
two clearinghouse settlement variants. It also ratchets the typed authorization
wiring for the currently implemented adapters: zUSD, guarded routing quotes,
and isolated perps settlement must bind action facts, pre-state, and the
runtime oracle value consumed by the action.

## Design-Only Backlog Profiles

| Consumer | Action | Why Not Runtime-Wired Yet |
| --- | --- | --- |
| `zenodex.perps` | `liquidate_account` | Reserved for a future standalone liquidation adapter. Current perps liquidation is reached through `settle_epoch`. |
| `zenodex.trigger` | `execute_trigger` | The profile exists in the first-shell catalog, but no trigger runtime module is wired in this checkout. |

These are explicit backlog items, not covered runtime guarantees.

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
