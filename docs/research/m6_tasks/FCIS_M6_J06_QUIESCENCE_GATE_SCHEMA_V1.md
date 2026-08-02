# FCIS M6 J06 quiescence gate schema

J06 is a bounded research model for the final migration replay/current-head
comparison. The gate is valid only at `QUIESCED`, binds the J04 manifest,
complete replay-evidence root, K01 entrypoint root, J02 authority epoch, both
writer-profile roots, and equal current/replay head and durable-snapshot roots.

The covered writer set is the exact in-scope value-moving subset of K01:

```text
api_http_ingress
background_outbox_delivery
durable_recovery_worker
durable_state_adapter
entitlement_migration_worker
governance_administrator
legacy_fcis_runtime
operator_cli
outbox_lease_worker
```

The gate also carries the J04 quiescence markers and the J02 authority epoch.
Its root is the canonical hash of every field except the self-reference. Gate
and admission-result construction is verifier-owned in this model; ordinary
callers cannot mint a self-consistent witness by choosing roots directly.

## Admission contract

For every typed writer attempt `x` presented to a valid gate `g`:

```text
reject_writer_v1(g, x).accepted = false
reject_writer_v1(g, x).state_unchanged = true
post_head_root = pre_head_root = g.current_head_root
post_authority_state_root = pre_authority_state_root = g.authority_state_root
post_snapshot_root = pre_snapshot_root = g.current_snapshot_root
```

An attempt outside the covered K01 set, with a stale authority epoch/root,
foreign expected head, or wrong activation sequence receives its own closed
rejection code. A correctly bound attempt receives
`quiesced_writer_rejected`.

## Boundary

The model does not provide a production mutex, database lock, transaction
isolation proof, process barrier, fresh replay execution, runtime call-graph
proof, or deployment reachability proof. The equal head and snapshot values
are configured/derived model premises. Those remain J07 and K-wave
implementation obligations. M6 remains unmounted and non-promotable.
