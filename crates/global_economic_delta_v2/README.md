# Global Economic Delta V2

This standalone research crate implements the event-level delta shapes declared
by the G1 semantic inventory. It supplies typed decoding, deterministic
validation, canonical bytes, and a domain-separated root. Source bindings are
declarative inputs committed by the plan.

## Projection-role extension

The closed V2 event language includes `reserve_transfer`, `fee_allocation`,
and `reward`. Each variant owns both economic locations, the exact positive
amount, and one economic-event root. Reserve direction is a closed enum. Fee
and reward events also bind the policy root that gives the allocation meaning.
This keeps those effects distinguishable from an ordinary internal transfer
and prevents a caller from attaching an unbound fee or reward label later.

The supplemental Python/Rust vector is
`tests/data/global_economic_delta_v2_projection_events.json`, with canonical
root
`sha256:64663ff48b10b511cdaec74d47634d656a9c083d95c76c13ba652ba37d762a4b`.
It retains mutants for an unknown direction, aliased source/destination, and
invalid policy roots.

This is an additive research-language change. Existing accepted bytes retain
their roots. No active release selects this implementation; a future release
must use a new content-derived release identity and prove runtime projection
before activation. The G1 mapping records structural candidates only. It does
not establish that the current five-field M6 delta entry can represent these
events.

The source-history V2 statement adds exact chain, deployment, profile, writer
epoch, history root and height, source occurrence coordinates, finality anchor,
and consumption-nullifier bindings. It checks source root, kind, asset, and
amount against the structural plan. The opaque
`VerifiedSourceHistoryDeltaPlanV2` can only be constructed through a sealed,
release-and-image-pinned proof backend. This crate exports no concrete backend,
so no downstream caller can currently construct that witness.

It does not implement all 33 commands, verify proofs, select policy, publish
state, mount a writer, prove source inclusion/finality/nullifier absence, or
grant settlement or production authority. The Python source-history module is
an independent canonicalization and semantic-drift oracle only.
