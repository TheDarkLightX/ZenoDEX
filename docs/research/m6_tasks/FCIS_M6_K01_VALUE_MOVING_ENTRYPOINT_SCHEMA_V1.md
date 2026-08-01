# FCIS M6 K01 value-moving entrypoint inventory

K01 records candidate command, authority, datastore, migration, recovery,
legacy, proof, and external-effect entrypoints. Every row carries the fields
needed for the R12 no-bypass audit:

```text
publisher_id
kind
symbol_path
caller
input_type
state_effect_touched
required_anf_commit_port_call
legacy_status
runtime_reachability_evidence
value_moving
authority_sink
source_paths
```

The builder hashes the exact configuration, deployment/build source paths, and
entrypoint source paths. It constructs the typed inventory without accepting a
candidate topology root, runtime certificate, authority grant, or instance
root as input. The inventory root is derived from the complete canonical
payload.

## Closed language

The supported surface kinds are API, CLI, administrator, migration worker,
recovery worker, proof verifier, legacy runtime, background outbox worker,
direct datastore adapter, and explicitly out-of-scope zUSD, perps, and
autotrader surfaces.

The required publisher IDs inherited from D05 are:

```text
api_http_ingress
background_outbox_delivery
durable_recovery_worker
durable_state_adapter
entitlement_migration_worker
governance_administrator
legacy_fcis_runtime
operator_cli
proof_verifier
```

The proof verifier is typed as non-value-moving. A legacy path must carry the
post-switch rejection requirement and unverified legacy reachability. A
value-moving row cannot use the proof-only requirement.

## Completeness boundary

The generated status is `reviewed_source_set_only`. K01 proves exactness and
canonicality relative to its reviewed input. It does not prove that the input
contains every production publisher or that a deployment, image, worker,
credential, process, or runtime call graph reaches the listed symbols. Those
are K03, K04, K06, and K07 obligations. No M6 caller, datastore authority,
runtime switch, or value-moving path is mounted by this packet.
