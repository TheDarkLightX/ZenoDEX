# J03 plan: migration artifact transport map

Status: implemented as a fail-closed eight-artifact migration map; tested,
research-only, and unmounted. J04-J09 remain pending.

## Objective

Make every migration artifact decision explicit. The map covers state,
configuration, residual fee history, proof contexts, receipts, nullifiers,
history, and outbox effects. Each row states whether the artifact is preserved,
recomputed, transported through a proved map, invalidated and regenerated, or
forbidden, together with source/target profile policy, roots/checker
requirements, acceptance gate, and nonclaims.

The checker rejects missing artifact classes, reordered or duplicate rows,
profile-boundary mappings that do not match the frozen policy, transport rows
without checker/root obligations, preservation without a condition, and
missing unmounted boundaries.

## Evidence boundary

J03 is a migration obligation registry. It does not prove any state, fee,
receipt, nullifier, history, proof-context, configuration, or outbox transport
relation. It does not implement migration, writer exclusion, rollback,
datastore behavior, runtime mounting, no-bypass coverage, accounting,
backing, or zUSD safety. M6 remains unmounted and non-promotable.
