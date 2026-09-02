# Tau ADT ABI V1 — slice 1 report (2026-09-02)

Result: 7/7 parity between the real Python transition and Tau-recomputed
transition_ok over frozen bv[16]+sbf ADT vectors (2 accepts + 5 reject classes:
SELF_TRANSFER, ZERO_AMOUNT, FEE_LIMIT_EXCEEDED, INSUFFICIENT_BALANCE,
DISABLED_ASSET), with the reject-is-noop contract conjoined into every program.
Falsification self-test proves the harness can return F (wrong expectation) and
FAIL_CLOSED (broken program) — verdicts are earned, not defaulted.

## The three-way claim - now DIRECT (slice 3)

The target invariant Python == Rust == Tau holds directly over the frozen
vector set: the Rust leg (experiments/tau_adt_abi/rust_leg, a small binary
linking the real zk crate) replays the EXACT same vectors through
transition_asset_transfer_v1 and reports 15/15 agreement with the Python
oracle, additionally asserting the noop contract inside the leg
(pre_state_root == post_state_root and effects.is_empty() on every reject).
Combined with the 15/15 Python == Tau parity, all three implementations agree
vector-for-vector on the same inputs - one structured state transition, three
independently replayable implementations, one deterministic oracle. The
earlier transitivity argument is superseded.

## What Tau actually recomputes

Guard precedence for the five covered reject classes mirrored from the Python
transition (disabled -> self -> zero -> fee-limit -> insufficient -> accept),
over ADT literals with frozen member order (ABI rule 1); every Result member is
explicitly constrained in every accepting disjunct (ABI rule 2 - no member ever
defaults to its algebra's zero). The reject-code space is a bv[4] token
dictionary frozen per vector set. Identities and roots stay host-side tokens.

## Known limits (deliberate)

- Bounded shadow domain bv[16]; no u128 arithmetic, hashing, signatures.
- The row-ceiling class (POST_STATE_RESOURCE_BOUND_EXCEEDED) is not yet
  covered: its real ceiling (4096 rows) is outside the bounded domain, so it
  will enter as a CONTRACT-tier check (Tau validates reject_is_noop over the
  host-produced result record) in a later slice, clearly labeled as weaker
  than the recompute tier.
- Guard precedence in Tau is hand-mirrored, not derived from the Python source;
  a precedence-drift between the implementations would surface as a parity F
  only for vectors that distinguish the orders. Boundary vectors targeting each
  adjacent precedence pair are queued.
- Single machine, single binary (upstream 3c24bad9), alpha toolchain.

## Slice 2 addendum (same day)

15/15 parity after adding four guard-edge boundary vectors (fee at limit /
one over; balance exact / one short) and four precedence discriminators where
two guards both want to fire (disabled+self, self+zero, zero+fee,
fee+insufficient). The discriminators take their expected code from the
Python oracle at build time, so a precedence drift between implementations
surfaces as a Tau parity F rather than a fixture edit. The hand-mirroring
limit from slice 1 is now bounded: every adjacent pair in the mirrored
precedence chain has a distinguishing vector.

Research-only; no authority of any kind is granted or implied.

## Slice 4 addendum (2026-09-02, review repairs P1-1 / P1-2)

The per-vector program is now UNIVERSAL: `ex s:St ex c:Cmd ( bindings && all r:Res ( chain(s,c,r) -> expected(r) ) )`
plus a separate NON-VACUITY program `ex r:Res ( chain )`. The earlier existential form conjoined the expected
result with the chain, so a chain weakened to admit every result could still answer T (P1-1); the universal
form answers F for that weakening (selftest probe 2) and F for a wrong expectation (probe 1). noop and
effects_empty are taken from the REAL rejected value (`pre_state_root == post_state_root`,
`effects.is_empty`), not re-derived host-side (P1-2). Identity comparison (sender/recipient) and `enabled`
are recomputed in Tau over bv[4] identity tokens and an sbf member rather than folded to Python literals.
Result at upstream 3c24bad9: 15/15 vectors T on both programs; selftest v2 ok.

Grammar fact (verified): quantified ADT variables whose members are accessed must be single letters
(`s.bal` parses; `st.bal`, `sx.bal`, `state.bal` fail with `Syntax Error: Unexpected '='`).
