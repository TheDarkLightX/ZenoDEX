# FCIS M6 F04A prior-state acknowledgment progress

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F04A is the narrow companion to the F04 whole-layout fixed-point gate. F04
correctly accepts a canonical layout with an unacknowledged outbox effect when
the current F02 schema permits pending delivery. F04A adds the prior-state
evidence needed to classify acknowledgment deletion and mutation.

The relation accepts an ack-only update when:

```text
prior and current are independent F04 fixed points
non-ack history is identical
authority/evidence/nullifier/outbox projections are identical
every prior ack remains byte-identical
new acks are F02-provenanced
```

It reports either `pending` or `acked` and lists added and still-pending effect
identities. It rejects:

```text
prior ack deletion
prior ack mutation
non-ack history change
malformed prior/current layouts
```

## Boundary

F04A closes the prior-state ambiguity for acknowledgment-only progress. It does
not claim that a current layout with no acknowledgment is corrupt when no
prior state or explicit R10 ack-obligation policy is available. The original
F04 packet remains a GAP for that stronger current-only theorem.

The relation does not authenticate a destination receipt, write a datastore,
or mount an effect worker. It is a research value relation only.
