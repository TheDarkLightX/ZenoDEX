# Global Economic Delta V2

This standalone research crate implements the event-level delta shapes declared
by the G1 semantic inventory. It supplies typed decoding, deterministic
validation, canonical bytes, and a domain-separated root. Source bindings are
declarative inputs committed by the plan.

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
