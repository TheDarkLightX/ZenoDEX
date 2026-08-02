# FCIS M6 F02 canonical history encoder

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F02 consumes one complete `F02AuthorizedHistoryV1` and materializes one
`F02DurableLayoutV1`. The public `encode_history` function is the sole row
materializer. It emits these related families from the same source value:

```text
header
authority_rows
history_rows
evidence_rows
nullifier_rows
outbox_rows
ack_rows
```

Each history row retains the complete canonical F01 atom bytes and its atom
root. Each publication emits eight ordered evidence rows for ANF,
proof-context, response, receipt, decision, bundle, replay, and outbox roots.
Nullifier and outbox rows retain the complete typed F01 projections. Acks are
checked against their committed outbox ancestor, destination, payload,
adapter, idempotency, commit, and response roots.

The layout header records exact counts for every parallel family. Canonical
row ordering is sequence order, atom/kind order, or atom/ordinal order as
appropriate. The layout root is:

```text
layoutRoot = SHA256(domain_sep("zenodex/fcis/m6/f02/layout-root", 1)
                    || canonical_json_bytes(all layout rows and header))
```

The complete layout codec includes the root as a checked cache field. Any
missing, surplus, reordered, crossed, or stale row fails construction or root
recomputation.

## Boundary

F02 is a typed research encoder and layout contract. It does not write a
database, prove transaction atomicity, reopen a physical store, authenticate a
caller, verify external proofs, deliver effects, mount migration authority,
cover no-bypass reachability, or establish accounting, backing, zUSD safety,
or value movement. F03 owns total fail-closed reopen and exact fixed-point
recovery.
