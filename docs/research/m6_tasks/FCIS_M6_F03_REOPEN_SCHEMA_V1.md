# FCIS M6 F03 total fail-closed reopen

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F03 reopens the F02 durable layout through a partial relation:

```text
reopen_layout_bytes(bytes) -> complete history | typed reject
```

The decoder enforces this order:

1. exact input type and bounded byte length;
2. UTF-8, duplicate-key, JSON, and canonical-byte checks;
3. exact envelope and row fields;
4. nested authority, atom, nullifier, outbox, evidence, and ack decoding;
5. complete F02 history reconstruction;
6. state-chain, context, authority, nullifier, outbox, and acknowledgment
   projection checks;
7. canonical re-encoding through F02 `encode_history`;
8. exact whole-layout fixed-point equality.

The success result contains one complete `F02AuthorizedHistoryV1`, the layout
root, and canonical layout bytes. Every failure returns
`F03ReopenRejectV1` with a stable code and path. No partial history is exposed.

## Boundary

F03 is an executable reopen reference. It does not read a physical datastore,
prove filesystem/WAL/fsync durability, handle a process crash, mint fresh
post-restart authorization, mount a runtime caller, deliver effects, or prove
accounting, backing, zUSD safety, or value movement. Production recovery still
requires an adapter refinement and crash-injection evidence.
