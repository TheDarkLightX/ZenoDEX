# J02 plan: writer matrix

Status: implemented as an executable checker over the research authority
state; tested, research-only, and unmounted. J03-J09 remain pending.

## Objective

Enforce the exact writer relation:

```text
LEGACY / SHADOW_REPLAY / DUAL_CHECK -> legacy writer only
QUIESCED                            -> no value-moving writer
AUTHORITY_SWITCH and later          -> target writer only
```

The checker derives the writer set from every lifecycle phase, rejects dual
writer sets and quiesced writers, verifies active-profile agreement, and
checks that a legacy writer is absent after the authority switch.

## Evidence boundary

J02 checks the bounded `AuthorityStateV1` writer relation. It does not audit
real API, CLI, admin, migration, recovery, verifier-callback, worker, or
datastore entrypoints, and it does not implement stale-token transaction
refinement. Runtime writer exclusion, no-bypass coverage, accounting,
backing, and zUSD safety remain open. M6 remains unmounted and
non-promotable.
