# Semantic-Drift Controls

> **Differential conformance is necessary, but it can certify the same bug
> twice.** Two implementations translated from the same flawed mental model
> agree with each other, so a Python/Rust equality check stays green while both
> are wrong.

This document is the lesson from the fee-router asset-scoping defect, written
down so the same class of mistake is not repeated as the Rust surface widens
(Phases 6–9 of `RUST_RUNTIME_MIGRATION_PLAN.md`).

## What happened (the motivating bug)

The first fee router used a single global accumulator while `route_fee` accepted
an `asset`. That let a rounding remainder cross token units and fee-policy
streams: routing `1 zUSD` left `dust=1`, then routing `9999 AGRS` consumed that
zUSD dust and emitted a `10000`-unit AGRS receipt; a DEX remainder could be
re-split under the redemption table. Python and Rust agreed exactly, so:

* the differential conformance suite passed,
* per-call conservation (`amount + dust_in == buckets + dust_out`) held,
* every golden-trace step matched.

The bug was an **abstraction** error (the accumulator was not keyed by routing
context), invisible to all of the above. Fixed by keying dust per
`(source, asset)` and cumulative buckets per `asset`.

## Why differential testing missed it

| Check | What it proves | What it cannot prove |
|-------|----------------|----------------------|
| Python/Rust differential | the two runtimes **agree** | that either is **correct** |
| Per-call conservation | value isn't created/destroyed *within a call* | value isn't **misattributed across calls/streams** |
| Golden traces | recorded behavior is **stable** | the recorded behavior is **intended** |

## The control: independent semantic invariants

For every runtime surface we add **semantic invariants** — properties derived
from the *intended meaning*, asserted against **each runtime independently**
(Python property tests + Rust `proptest`), never as a cross-implementation
diff. A bug present identically in both runtimes still fails an intent invariant.

The invariant that catches this whole class is **no cross-key interference**:

> A logical stream's outputs depend only on that stream's own sub-sequence of
> inputs. Interleaving unrelated streams must not change them.

* fee router — stream key = `(source, asset)`
  (`tests/runtime/test_fee_router_semantic_invariants.py`)
* replay guard — stream key = `sender`
  (`tests/runtime/test_replay_guard_semantic_invariants.py`)
* Rust mirrors live in each module's `proptest!` block.

These fail on the buggy global-state model and pass on the keyed model.

## Layered defense (in order of strength)

1. **One authoritative semantics.** Python is authoritative; Rust is a shadow
   until promotion (Phase 9). They are never independently authoritative.
2. **Independent semantic invariants per surface**, run on each runtime alone
   (the control above). At minimum: per-key conservation, **no cross-key
   interference**, key/unit coherence, no-op-on-reject, and any
   domain/policy-specific invariant.
3. **Golden traces include a cross-key regression case** (mixed assets/sources,
   mixed senders), not only single-stream happy paths.
4. **Shadow replay rebuilds the Rust CLI** before comparing, so review never
   diffs Python against a stale binary (`tools/runtime/rust_shadow_replay.py`).
5. **Differential conformance** (static + randomized) — necessary, not
   sufficient; it pins agreement once correctness is established by (2).
6. **Formal obligations** (Tau / ESSO / Lean) for surfaces that have them must
   stay green as a promotion gate.

## Checklist for a new runtime surface (Phase 6+)

- [ ] Identify the **stream key** (the dimension state must be partitioned by).
- [ ] Python authoritative reference returning `Result`-style accept/reject with
      stable codes; conform to any existing authoritative module (do not invent
      a second semantics).
- [ ] Rust shadow mirroring validation **order** and canonical encoding.
- [ ] Golden trace: happy + every rejection code + **a cross-key case**.
- [ ] **Semantic invariants** (Python + Rust), including no cross-key
      interference and no-op-on-reject.
- [ ] Property tests + rejection tests.
- [ ] Differential conformance (static smoke + randomized).
- [ ] Update `RUNTIME_TRUSTED_CORE_BOUNDARY.md` and the migration plan.

## Surfaces with these controls today

| Surface | Stream key | Invariants | Differential |
|---------|-----------|------------|--------------|
| `fee_router` | `(source, asset)` dust, `asset` buckets | ✅ Python + Rust | ✅ static + 400-case |
| `replay_guard` | `sender` | ✅ Python + Rust | ✅ static + 400-case |
