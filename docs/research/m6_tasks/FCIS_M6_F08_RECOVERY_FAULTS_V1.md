# FCIS M6 F08 reopen and corruption fault semantics

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

F08 defines the crash/reopen observation boundary over the F04 fixed-point
relation. It validates two distinct canonical durable layouts:

```text
PRE  = exact bytes before publication
POST = exact bytes after publication
```

An observed payload can produce only:

```text
PRE
POST
REJECTED_LOCKED
```

The rejected outcome exposes no layout root or partial history. Every outcome
requires fresh authorization, and the model never exposes value-moving
capability.

## Fault surface

The independent campaign injects missing, surplus, duplicate, reordered, and
crossed rows across authority, history, evidence, nullifier, outbox, and
acknowledgment collections. It also mutates the state header, selected layout
root, truncates the byte string, and supplies invalid UTF-8. A valid third F04
fixed point is tested separately and is rejected as neither PRE nor POST.

The campaign contains 31 observed faults. All 31 return `REJECTED_LOCKED`.

## Authority boundary

F08 is an abstract observation relation. It does not claim that a physical
database or filesystem has atomic PRE/POST behavior. A production adapter must
refine this model with transaction boundaries, WAL or equivalent durability,
fsync behavior, process-death injection, and post-crash canonical reopen.

## Nonclaims

F08 does not implement a datastore adapter, crash injector, runtime command
gate, fresh external authorization verifier, or value movement. It does not
promote R07/R09 or close M6.
