# I07 plan: outbox disaster matrix

Status: implemented and tested as a fail-closed ten-scenario matrix;
research-only and unmounted. I08 and the later migration/no-bypass work remain
pending.

## Objective

Record the exact durable and external result for each required outbox failure
family:

```text
delivery before local commit
orphan outbox row
payload collision under the same effect ID
foreign receipt acknowledgment
acknowledgment before delivery
lost lease
worker crash before send
worker crash after send
worker crash after acknowledgment write
migration during delivery
```

The checker requires an exact ten-member registry, exact nested durable and
external state fields, nonempty preconditions, named invariants, evidence
references, and per-scenario unmounted nonclaims. It also rejects impossible
effect/attempt combinations and missing semantic invariant anchors.

## Evidence boundary

I07 supplies a machine-checked scenario registry and negative structural
witnesses. It connects the I02-I06 research models by reference and states the
expected behavior that a future worker, datastore, and migration refinement
must satisfy. It does not execute a production worker, prove destination
delivery, prove filesystem durability, mount migration authority, establish
no-bypass reachability, or prove accounting, backing, or zUSD safety. M6
remains unmounted and non-promotable.
