# Tau ADT ABI V1 — design (2026-09-02, upstream 3c24bad9)

Goal: one structured state transition, three independently replayable implementations, one
deterministic oracle:  Python semantics == Rust semantics == Tau ADT semantics over a frozen
bounded test domain. First demonstration target: the NEW-6 totalization contract at the
semantic-object level (Reject(r) => r.post_root == r.pre_root AND r.effects == empty).

Upstream capabilities this builds on (all verified live at 3c24bad9): ADT
functions/predicates/recurrences (demos 4.2-4.3), whole-ADT definition arguments via
parse-time flattening (demo 4.4), mixed-algebra tuples (bv + sbf members), bv min/max
builtins with cvc5 + blasting (4437dad2), simultaneous type-safe substitution (3c24bad9).
Wrong-TYPE definition calls fail closed (787abef6); ARITY mismatches persist unexpanded —
the F8 fail-closed harness discipline (match verdicts exactly; treat unexpanded
applications as failure) is mandatory and inherited from experiments/tau_adt.

## ABI rules (frozen as part of the contract)

1. MEMBER ORDER AND FLATTENED ARITY ARE ABI. Every ADT freezes its member order; a
   definition over a record declares exactly one parameter per flattened member. A tool
   (renderer) derives both from one source of truth; drift is a failing test, not a comment.
2. NO IMPLICIT PARTIAL OUTPUTS. Value-bearing records never rely on a member defaulting to
   its algebra's zero: every member of every emitted record is explicitly constrained in
   every accepting formula, and the harness rejects a solve/normalize result that leaves any
   member unconstrained.
3. BOUNDED SHADOW DOMAIN. Tau carries bv[W] amounts (start W=16); the oracle runs Python
   and Rust over the SAME bounded domain with the SAME width semantics via an explicit
   domain adapter, and every vector certifies in-band-ness (no value near 2^W unless the
   vector is an overflow-path vector, in which case all three implementations must agree on
   the reject). The u128<->bv[W] bridge is a first-class obligation, never implicit.
4. QUANTITATIVE + LOGICAL SPLIT PER RECORD: amounts/nonces are bv members; authority /
   enabled / binding flags are sbf members (mixed-algebra tuples), one record, no parallel
   representations.

## V1 scope (narrow on purpose)

Types: EconomicCommandV1 (kind, asset, sender, recipient, amount, max_fee),
AssetTransferContextV1 (subset: release, subject), AssetTransferStateV1 (bounded: <= 3
balances, 1 policy, 1 supply), AssetTransferResultV1 (accepted:sbf, reject_code:bv[4],
pre_root/post_root as opaque equality tokens, effects_empty:sbf). Identities and roots are
NOT hashed in Tau: they are small enumerated tokens (bv[4]) under a frozen vector-local
dictionary; hashing/crypto stays host-side (per the study partition).

Predicates (whole-ADT arguments, flattened arity frozen):
  reject_is_noop(result...)          := accepted=0 -> (post_root=pre_root && effects_empty=1)
  fee_policy_ok(command..., policy...)
  balance_covers(command..., state...)
  transition_ok(context..., state..., command..., result...)

Harness: a Python renderer maps each frozen vector (built by the REAL Python transition,
mirrored by the REAL Rust transition via the existing parity suites) into one Tau program
per vector asserting transition_ok over the vector's literal members; the runner requires
an exact `T`/`F` verdict per program (F8 discipline), compares against the Python outcome,
and reports the three-way parity table. Overflow/boundary vectors include the NEW-6 class:
a transfer that would grow the post-state past the (bounded) row ceiling must yield the
typed reject with noop roots and empty effects in all three implementations.

## Non-goals for V1

No tables (not on main; the UPBA landing pad waits for them), no hashing, no signatures, no
u128 arithmetic, no recurrence-over-epochs (V2 candidate), no authority claims of any kind.
Research-only.
