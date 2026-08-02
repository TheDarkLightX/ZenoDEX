# FCIS M6 F04 whole-layout fixed-point gate

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_GAP_UNMOUNTED`

F04 is the narrow gate that callers use for canonical F02 durable-layout
bytes:

```text
check_whole_layout_fixed_point(bytes) -> complete history/layout | typed reject
```

The gate first applies the F03 partial reopen relation. It then independently
materializes the accepted history through F02 and requires:

```text
encode_history(reopen(layout)) == layout
encode_layout_v1(layout) == supplied_bytes
```

A selected `layout_root` is checked as a cache and never stands in for the
complete row set. The success value contains the complete typed history and
layout. Rejection retains the F03 source code when available.

## Mutation boundary

The deterministic campaign covers missing, extra, duplicate, reordered, and
crossed mutations across authority, history, evidence, nullifier, outbox, and
ack row families. The layout root is recomputed after each mutation. Twenty
five invalid cases reject.

One case is intentionally preserved as a semantic witness:

```text
ack_rows:missing -> accepted pending-delivery layout
```

F02 permits an outbox with no durable acknowledgment while delivery is pending.
The current fixed-point equation cannot distinguish deletion of an existing ack
from a legitimate current history with no ack. That distinction requires a
prior-state commitment or an explicit ack-obligation policy. F04 therefore
remains a gap for the stronger universal “every missing row rejects” claim.

## Boundary

F04 does not read a physical datastore, authenticate the source history, prove
WAL/fsync or crash recovery, grant restart authority, deliver effects, mount a
runtime caller, or establish accounting, backing, zUSD safety, or value
movement.
