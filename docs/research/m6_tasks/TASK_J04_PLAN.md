# J04 plan: root- and sequence-bound migration manifest

Status: implemented as a canonical, fail-closed migration manifest; tested,
research-only, and unmounted. J05-J09 remain pending.

## Objective

Bind the migration decision to source and target roots, transport checker IDs
and roots, activation sequence, rollback rules, complete quiescence evidence,
and a complete replay evidence root. The manifest root is the SHA-256 of the
canonical manifest body without its self-reference.

The checker rejects root-width/type failures, source/target profile drift,
missing transport obligations, incomplete quiescence evidence, invalid
activation or rollback windows, missing complete-history rollback rules, and a
stale manifest root.

## Evidence boundary

J04 validates a manifest shape and binding relation. Its transport and replay
roots are deterministic research identifiers and do not constitute completed
proofs. It does not implement migration, state transport, writer exclusion,
rollback, datastore behavior, runtime mounting, no-bypass coverage,
accounting, backing, or zUSD safety. M6 remains unmounted and
non-promotable.
