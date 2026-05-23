# ZenoOracle MVP Completion Audit

Updated: 2026-05-03

This note records the current ZenoOracle MVP state on the
`codex/zeno-oracle-mvp-hardening` branch. It is a completion audit, not a
production certification.

## Current Implementation

ZenoOracle now has a local MVP shell:

- CLI entry points in `tools/zenodex_oracle.py` and `tools/zenodex-oracle`
- release bundle builder in `tools/build_zenodex_oracle_release.py`
- local dashboard components under `tools/dex-ui/src/components/ZenoOracleDashboard.*`
- canonicalization vectors in `docs/zeno_oracle/canonicalization_vectors_v1.json`
- typed runtime authorization checks in `src/integration/zeno_oracle_authorization.py`
- routing, settlement, and trigger authorization adapters in `src/integration/zeno_oracle_*_authorization.py`

The critical runtime object is `OracleAuthorization`. It binds:

```text
consumer action
+ action facts hash
+ pre-state hash
+ query/profile
+ decoded value_e8
+ freshness/uncertainty
+ registry roots
+ economic envelope
+ terminal receipt graph root
```

This removes the weakest earlier shape: a consumer accepting an opaque
`action_id` or `value_hash` without checking that the live runtime value and
pre-state are the same facts authorized by the oracle receipt.

## Hardened Surfaces

The current branch contains replayable checks for these Oracle/DEX composition
shapes:

- wrong runtime value rejected
- wrong action facts hash rejected
- wrong pre-state hash rejected
- wrong query/profile/consumer rejected
- stale authorization rejected
- insufficient evidence class rejected for critical consumers
- missing terminal receipt graph rejected for critical consumers
- terminal graph value/root/freshness/registry mismatch rejected
- fake graph diversity rejected by recomputing report leaf reporter/source/control-group counts
- disputed report inclusion rejected
- canonicalization vector drift rejected by a checked vector file

The core safety rule is:

```text
valid oracle artifact + wrong runtime context -> reject before state mutation
```

The implementation now makes that rule executable for zUSD, perps, protected
routing, critical settlement, and trigger authorization surfaces on this
feature branch.

## Evidence

Recent commits on this branch:

- `8c7f24a feat: add ZenoOracle MVP CLI and dashboard`
- `02da883 feat: bind oracle authorizations to runtime facts`
- `af7d672 test: add oracle runtime binding vectors`
- `ad8c1e8 fix: require terminal oracle receipt graphs`
- `902f3e8 test: reject fake oracle graph diversity`

Focused gates already run on the branch:

```text
tests/integration/test_zenodex_oracle_cli.py
tests/tools/test_check_zeno_oracle_canonicalization_vectors.py
tests/integration/test_zenodex_oracle_release_bundle.py
tests/integration/test_oracle_authorization_semantic_binding.py
tests/integration/test_zusd_api.py
tests/integration/test_perp_engine_oracle_authorization.py
tests/integration/test_dex_engine_protected_routing_oracle_authorization.py
tests/integration/test_dex_engine_critical_settlement_oracle_authorization.py
tests/integration/test_zeno_oracle_trigger_authorization.py
```

Latest focused result recorded during implementation:

```text
107 passed in 7.86s
```

The dashboard build and lint also passed earlier in the same branch cycle.

## Not Yet Complete

ZenoOracle is not production-complete yet. The remaining blockers are:

- clean integration into `origin/main`; this branch has no clean merge base and
  cherry-picking revealed real conflicts with the existing oracle adapter bridge
- preserving both main's adapter-bridge path and this branch's typed
  `OracleAuthorization` path instead of choosing one
- production feed/reporter registries with live persisted reporter lifecycle,
  sequence, bond, slash, withdrawal, and dispute state
- production O3 read path wired from live reports rather than only the local MVP
  shell
- terminal receipt DAG replay over feed policy, query policy, reporter/source
  registries, aggregate receipts, disputes, and economic envelopes as one
  coherent graph
- release binaries and installer flow for non-developer oracle users
- whitepaper/product documentation that separates MVP, O3, O4/ZK, and O5 claims
- Lean/ESSO/SMT proof lanes for the strongest invariant claims

## Next Merge Plan

The next branch should be cut from `origin/main` and integrate the Oracle stack
deliberately:

1. Keep main's `oracle_adapter_bridge` compatibility path.
2. Add typed `OracleAuthorization` as the stricter critical-action gate.
3. Preserve main's newer perps submission field-selector logic.
4. Re-run the Oracle focused gate and the affected zUSD/perps/routing tests.
5. Only then open or update the PR.

Until that integration is done, this branch is valuable as a hardened Oracle MVP
work branch, but it should not be described as merged production state.
