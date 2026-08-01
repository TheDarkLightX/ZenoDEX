# J01 plan: exact migration lifecycle

Status: implemented as an executable checker over the existing closed
`MigrationPhaseV1` and `advance_authority_state` research boundary; tested,
research-only, and unmounted. J02-J09 remain pending.

## Objective

Freeze the only accepted authority lifecycle:

```text
LEGACY
-> SHADOW_REPLAY
-> DUAL_CHECK
-> QUIESCED
-> AUTHORITY_SWITCH
-> POST_SWITCH_VALIDATION
-> LEGACY_DISABLED
```

The checker verifies exact enum membership and order, valid one-edge
transitions, epoch monotonicity, transition-root construction, terminal
behavior, and rejection of skipped, reversed, repeated, unknown, or
caller-selected ad hoc phases.

## Evidence boundary

J01 verifies the bounded research lifecycle already represented in
`src/core/fcis_durable_retraction.py`. It does not implement the real
migration switch, writer exclusion, stale-token rejection, state/evidence
transport, rollback, datastore migration, runtime mounting, no-bypass
coverage, accounting, backing, or zUSD safety. M6 remains unmounted and
non-promotable.
