# Tau ADT ABI V1 — slice 1 report (2026-09-02)

Result: 7/7 parity between the real Python transition and Tau-recomputed
transition_ok over frozen bv[16]+sbf ADT vectors (2 accepts + 5 reject classes:
SELF_TRANSFER, ZERO_AMOUNT, FEE_LIMIT_EXCEEDED, INSUFFICIENT_BALANCE,
DISABLED_ASSET), with the reject-is-noop contract conjoined into every program.
Falsification self-test proves the harness can return F (wrong expectation) and
FAIL_CLOSED (broken program) — verdicts are earned, not defaulted.

## The three-way claim, stated honestly

The target invariant is Python == Rust == Tau over the frozen bounded domain.
This slice proves the Python == Tau leg directly. The Rust == Python leg is NOT
re-proved here: it is carried by the repository's existing differential surface
(the transfer golden/parity suites and the compiled-Rust totality replay,
tests/formal/test_o008_transition_resource_bound_rust_replay.py), which pin the
same transition over a superset of this domain. Three-way equality follows by
transitivity ONLY where those suites and this harness share domain and
semantics; a dedicated Rust leg replaying these exact seven vectors is the
honest upgrade and is queued as slice 2.

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

Research-only; no authority of any kind is granted or implied.
