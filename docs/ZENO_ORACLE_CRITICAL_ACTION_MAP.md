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
runtime_wired_count = 7
design_only_backlog_count = 0
status = accepted
```

## Runtime-Wired Profiles

| Consumer | Action | Runtime path | Required control |
| --- | --- | --- | --- |
| `zenodex.perps` | `settle_epoch` | `src/integration/perp_engine.py` | isolated/clearinghouse adapter controls plus isolated/clearinghouse typed-authorization controls |
| `zenodex.perps` | `liquidate_account` | `src/integration/perp_engine.py` | `require_oracle_adapter_for_isolated_partial_liquidate` |
| `zenodex.zusd` | `mint` | `src/integration/zusd_api.py` | `ZUSD_ORACLE_ADAPTER_REQUIRED`, `ZUSD_ORACLE_AUTHORIZATION_REQUIRED` |
| `zenodex.zusd` | `liquidate_vault` | `src/integration/zusd_api.py` | `ZUSD_ORACLE_ADAPTER_REQUIRED`, `ZUSD_ORACLE_AUTHORIZATION_REQUIRED` |
| `zenodex.routing` | `guarded_quote` | `src/integration/api_server.py` | `DEX_ROUTING_ORACLE_ADAPTER_REQUIRED` |
| `zenodex.settlement` | `critical_settlement` | `src/integration/dex_engine.py` | `require_oracle_authorization_for_critical_settlements` |
| `zenodex.trigger` | `execute_trigger` | `src/integration/zeno_oracle_trigger_authorization.py` | `check_trigger_execute_oracle_adapter_bridge(required=True)`, `check_trigger_execute_oracle_authorization` |

The checker verifies that each runtime-wired surface still agrees with the
catalog query ID, catalog profile ID, expected consumer module, expected action
kind, runtime action-ID binding, exact value and epoch binding, and the
verifier-selected receipt graph root. For routing it checks both exact-in and
exact-out guarded quote paths. For perps it checks isolated settlement, the two
fixed clearinghouse settlement variants, N-party run/settlement, and isolated
partial liquidation under the `liquidate_account` profile. For zUSD
mint/liquidation it checks both the O3
adapter bridge binding and the typed `OracleAuthorization` binding to the
runtime action kind, per-action profile, action facts hash, pre-state hash, and
runtime oracle price. For critical settlements it checks the typed
`OracleAuthorization` binding in `dex_engine` against the normalized settlement,
pre-state root, current settlement price, and settlement freshness controls. For
triggers it checks the existing typed trigger action facts against both an O3
adapter bridge result and the typed `OracleAuthorization` checker for the
cataloged `execute_trigger` profile.

## Design-Only Backlog Profiles

The first-shell profile catalog has no design-only backlog entries in this
checkout. Future critical consumers still need their own profiles and runtime
checks before they become covered guarantees.

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
