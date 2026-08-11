# M6 Research Program: Frozen 13-Problem Scope

Date: 2026-07-30

Status: FROZEN_OPEN

This document is the repository-local freeze of the M6 research program. It
defines exactly thirteen hard problems. It does not promote any theorem,
implementation, runtime mount, or production claim.

## Overall theorem

The M6 target is the following refinement chain:

    RuntimeAccept
      -> authenticated command
      -> authenticated current state and context
      -> deterministic kernel evaluation
      -> authorized candidate
      -> exact receipt and bundle lineage
      -> atomic publication
      -> recoverable committed state
      -> committed outbox effects only
      -> no alternate acceptance path

The program is closed only when every item in the frozen registry has the
appropriate PROVED, IMPLEMENTED, MOUNTED, and TESTED evidence, with no
unresolved authority or effect gap.

## Freeze rules

1. The only M6 problem identifiers are M6-R01 through M6-R13.
2. The assurance gates are named FormalGate, RuntimeRefinementGate, and
   MountedAuthorityGate. They are separate from the advisory A--F score and
   from the M6-R requirement identifiers.
3. LEAP owns representation changes, new invariants, certificate languages,
   impossibility boundaries, and intervention algebras.
4. Ordinary implementation defects stay in the engineering lane.
5. Research tools, models, simulations, subagents, and retrieval systems
   propose candidates. Deterministic checkers, proofs, replay receipts, and
   runtime gates decide claims.
6. The allocator-selection search is frozen for now. SRGD and AGQE are treated
   as the same allocator kernel. ZAG may search for a competing selector only
   after an existing candidate fails the M6-R02 requirement.
7. A failing gate produces a minimized falsifier and preserves the negative
   evidence after repair.

## Frozen registry

| ID | Hard problem | Wave | Primary lane | Freeze status |
| --- | --- | ---: | --- | --- |
| M6-R01 | Canonical fee-occurrence semantics | 1 | LEAP | FROZEN_OPEN |
| M6-R02 | Complete SRGD/AGQE adaptive-policy theorem | 1 | Lean + Aristotle | FROZEN_OPEN |
| M6-R03 | Entitlement identity, policy rotation, and migration | 1 | LEAP | FROZEN_OPEN |
| M6-R04 | Concrete LineageCube composition theorem | 1 | LEAP | FROZEN_OPEN |
| M6-R05 | Authenticated nonce and replay concurrency | 2 | ESSO + ZenoFCIS | FROZEN_OPEN |
| M6-R06 | Complete evidence recomputation | 2 | LEAP | FROZEN_OPEN |
| M6-R07 | Authorized history, nullifiers, and reopen | 2 | LEAP + ESSO | FROZEN_OPEN |
| M6-R08 | Authenticated proof-context binding | 2 | LEAP + verifier lane | FROZEN_OPEN |
| M6-R09 | Atomic publication and crash refinement | 3 | LEAP + ESSO | FROZEN_OPEN |
| M6-R10 | Outbox delivery and acknowledgment semantics | 3 | LEAP + ESSO | FROZEN_OPEN |
| M6-R11 | Migration and authority-switch state machine | 3 | LEAP + ESSO | FROZEN_OPEN |
| M6-R12 | Mounted no-bypass theorem | 4 | Engineering and audit | FROZEN_OPEN |
| M6-R13 | ZUSD-P0 whole-system invariant | 4 | LEAP + formal arithmetic | FROZEN_OPEN |

No additional problem may be added under the M6 identifier without a new
program decision that explicitly supersedes this freeze.

## Wave 1: representation, allocation, identity, and lineage

### M6-R01: Canonical fee-occurrence semantics

Decide exactly what constitutes one allocator invocation:

- raw fill;
- settlement witness;
- same-key group within one transition;
- whole-transition aggregate.

Required result:

    settlement replay
      -> one unique ordered allocator-occurrence stream

First falsifier:

    one occurrence of 867
      !=
    two occurrences of 493 and 374

The evidence lane is LEAP, Morph, ESSO partition and reordering search, Lean
fold proofs, and ATDD. This is the immediate executable target because every
stream-level fairness theorem depends on the occurrence boundary.

Exit evidence must identify the canonical occurrence key, order, grouping
rule, replay encoding, and reject behavior for ambiguous or duplicate
occurrences.

### M6-R02: Complete SRGD/AGQE adaptive-policy theorem

Prove, for every valid sequence of amounts and policies:

- sum of allocations equals the amount;
- zero weight gives zero allocation;
- local quota holds;
- sum of deficits equals zero;
- -D < deficit_i < D;
- cumulative discrepancy is less than one atom;
- fixed-role tie-breaking is deterministic.

Then prove that the Python and Rust implementations refine the theorem over the
full U256 domain.

First falsifiers:

- a short adaptive sequence reaches abs(deficit_i) >= D;
- a zero-weight role receives an atom;
- Python and Rust select different roles;
- an intermediate arithmetic operation overflows;
- grouping semantics differ from M6-R01.

The evidence lane is Lean, Aristotle, ESSO, Kani/SMT, and differential testing.
ZAG searches only if the existing kernel fails one of these gates.

The selector search is closed as a research direction for the current kernel:
SRGD and AGQE identify the same kernel. The remaining work is theorem
completion, domain refinement, and falsification.

### M6-R03: Entitlement identity, policy rotation, and migration

Freeze the state identity carrying rounding history:

    distribution domain
    asset
    semantic algorithm profile
    fixed role order

Prove that destination changes, custody changes, and ordinary policy rotation
cannot reset residual state. Define the SRGD-to-AGQE relation as:

    sigma_i = -d_i

First falsifier:

    rename SRGD as AGQE
      -> initialize sigma = 0
      -> erase accumulated entitlement history

The evidence lane is LEAP fibered quotients, Morph, ESSO rotation sequences,
the Lean migration proof, and authority-bound ATDD.

### M6-R04: Concrete LineageCube composition theorem

Instantiate the generic LineageCube with actual ZenoDEX artifacts:

    canonical bytes
    command
    current state
    context
    evaluation candidate
    authorization decision
    receipt
    commit bundle
    durable state
    outbox event

Every semantic, authority, and durability face must commute and retain one
lineage identity.

First falsifier:

    decision refines command C1
    receipt authorizes command C2
    post-state comes from candidate K1
    outbox comes from candidate K2

The evidence lane is LEAP for abstraction, Morph for edge obligations,
Lean/Aristotle for commuting faces, ZenoFCIS for immutable values and the face
checker, and ATDD for crossed-lineage mutants.

This is the highest-impact M6 research target. R05 through R11 should use the
concrete vocabulary established here.

## Wave 2: replay, evidence, history, and proof context

### M6-R05: Authenticated nonce and replay concurrency

Required relation:

    authenticated sender
    and current nonce = n
    and command nonce = n + 1
    and evaluation succeeds
      -> exactly one atomic commit

Exact retries must distinguish:

    newly committed
    already committed
    stale state
    definite rejection
    indeterminate transport outcome

First falsifier: two concurrent commands using the same sender and nonce both
commit.

The evidence lane is ESSO, TLA, the ZenoFCIS transactional shell, concurrency
tests, and Lean for the abstract retry classifier.

### M6-R06: Complete evidence recomputation

Persisted evidence must equal the entire freshly recomputed evidence set.
Reject:

- a missing row;
- an extra row;
- a duplicate row;
- wrong order when order matters;
- foreign context;
- stale algorithm;
- a correct digest attached to the wrong transition.

First falsifier: add one valid-looking surplus row while retaining the selected
digest and still obtain acceptance.

The evidence lane is LEAP verifier-first synthesis, Morph, an exact
deterministic checker, counterexample-basis search, property tests, and
mutation tests.

### M6-R07: Authorized history, nullifiers, and reopen

Required invariant:

    authorized genesis
    and strict replay of every committed transition
    and reconstructed state = stored current state
    and one nullifier per consumed authorization
    and no orphan transition or nullifier

First falsifiers:

- a nullifier exists without its transition;
- a transition exists without its nullifier;
- truncated history is accepted;
- reopened state accepts a command before reauthorization.

The evidence lane is LEAP, ESSO history exploration, Lean replay folds,
authenticated-state structures from ZenoFCIS, and crash tests.

### M6-R08: Authenticated proof-context binding

The proof context must commit to at least:

- chain and deployment;
- state/configuration root;
- protocol and language version;
- verifier identity;
- verification-key digest;
- statement and public-input schema;
- algorithm profile;
- history/genesis authority;
- epoch or expiry rules.

First falsifier: a valid proof for deployment A, an old configuration, or a
retired verification key is accepted under deployment B's current state.

The evidence lane is LEAP theorem-carrying schema dimensions, Morph, Tau, Lean,
RISC0 verifier tests, and ATDD substitution mutants.

## Wave 3: publication, delivery, and authority switching

### M6-R09: Atomic publication and crash refinement

One transaction must publish:

    successor state
    authority header
    history
    nullifiers
    receipt
    decision
    bundle
    replay data
    outbox rows

Recovery must expose exactly:

    PRE
    or
    POST

First falsifier: any crash point leaves a durable mixture, such as successor
state without its receipt or nullifier.

The evidence lane is LEAP Intervention-Closed Shell Algebra, ESSO, TLA,
ZenoFCIS SQLite refinement, and deterministic fault injection.

### M6-R10: Outbox delivery and acknowledgment semantics

Required guarantees:

- no external effect without a committed outbox row;
- every committed effect remains recoverably deliverable;
- stable idempotency identity;
- lost acknowledgment does not create a new semantic effect;
- delivery acknowledgment preserves provenance.

The contract is atomic enqueue plus at-least-once delivery with an idempotent
effect identity.

First falsifier: a crash after external delivery and before acknowledgment
causes a second semantically distinct transfer.

The evidence lane is LEAP, ESSO intervention words, the ZenoFCIS outbox, and
BDD recovery scenarios.

### M6-R11: Migration and authority-switch state machine

Freeze the exact lifecycle:

    LEGACY
      -> SHADOW_REPLAY
      -> DUAL_CHECK
      -> QUIESCED
      -> AUTHORITY_SWITCH
      -> POST_SWITCH_VALIDATION
      -> LEGACY_DISABLED

Every phase requires authenticated source and target roots, complete replay
evidence, allowed writers, rollback rules, and promotion evidence.

First falsifiers:

- V1 state is published through the V2 transition family;
- an old writer commits after authority switch;
- rollback restores balances while losing configuration or residual history;
- mixed V1/V2 evidence passes publication.

The evidence lane is LEAP, ESSO, TLA, Lean migration projections, and ZenoFCIS
shell tests.

## Wave 4: mounting and whole-system closure

### M6-R12: Mounted no-bypass theorem

Inventory every value-moving entrypoint:

    API
    CLI
    recovery
    administrator
    migration
    legacy runtime
    proof verifier
    background worker
    direct datastore adapter

Each path must produce the same checked lineage or reject.

First falsifier: one entrypoint changes balances, nonces, configuration,
history, or outbox state without a verified commit bundle.

The evidence lane is reachability analysis, mutation testing, ATDD,
production-boundary checking, and runtime integration tests. LEAP may generate
bypass classes; the primary work is engineering and audit.

### M6-R13: ZUSD-P0 whole-system invariant

Define authoritative total debt and backing, then cover every command that can
change either quantity:

    mint
    burn
    liquidation
    settlement
    funding
    fee transfer
    migration
    recovery
    administrative transition

Prove integer-width, rounding, and Oracle-freshness refinement from stored
quantities to the mathematical theorem.

First falsifier: one debt-changing path bypasses the invariant gate or uses a
stale observation.

The evidence lane is LEAP for invariant reformulation, Morph for accounting
equivalences, Lean/Aristotle, Kani/SMT, differential vectors, and mounted
no-bypass evidence.

## Workflow ownership

| Lane | Ownership |
| --- | --- |
| LEAP | Representation changes, new invariants, certificate languages, impossibility boundaries, intervention algebras |
| Morph | Equivalences, quotients, source/target refinement obligations |
| ZAG | Competing algorithms or schedulers after an existing candidate fails |
| ESSO | Bounded stateful sequences, crashes, retries, rotations, and counterexamples |
| Lean + Aristotle | General theorems after the statement survives falsification |
| Research Kernel | Claims, dependencies, contradictions, counterexamples, and promotion status |
| ZenoFCIS | Candidate, receipt, bundle, authenticated-state, commit, and outbox substrate |
| ATDD/BDD | Executable behavior contracts and permanent negative mutants |
| TLA/Tau/SMT/Kani | Concurrency, temporal authority, bounded arithmetic, and implementation safety |

No lane may promote another lane's result without the relevant local evidence.

## Execution order

### Wave 1

M6-R01, M6-R02, M6-R03, and M6-R04 establish occurrence semantics,
apportionment, residual identity, and concrete lineage. M6-R02 through M6-R04
may proceed in parallel once M6-R01's boundary is frozen.

### Wave 2

M6-R05, M6-R06, M6-R07, and M6-R08 use the common LineageCube vocabulary.
They may proceed independently against that vocabulary.

### Wave 3

M6-R09, M6-R10, and M6-R11 close atomic publication, delivery, and authority
switching.

### Wave 4

M6-R12 and M6-R13 close mounted reachability and the whole-system zUSD
invariant. The final M6 composition review follows both.

## Frozen stop list

The following directions have existing counterexamples or insufficient
semantics and receive no new M6 research cycles:

- scalar phase alone under adaptive policy rotation;
- fixed-policy schedule selection as the final dynamic-policy solution;
- minimal residual period exactly equal to D;
- a weight-free stabilization quotient;
- deficit-only selection that omits the current quota remainder;
- treating AGQE and SRGD as separate allocator kernels;
- assuming tests, carriers, roots, or proofs automatically establish runtime
  mounting.

The remaining B1B-1 Rust structural-checker and packet-gate defects are
ordinary engineering problems. They require item-aware Rust parsing, mutation
tests, and exact-head CI. LEAP is outside that lane.

## Evidence and non-claims

This freeze records research scope and decision boundaries. It does not claim
that any M6 problem is proved, implemented, mounted, or tested. In particular,
the following are open until their named evidence lanes produce replayable
artifacts:

- the canonical occurrence stream;
- the full-U256 adaptive allocation theorem and Python/Rust refinement;
- residual-preserving identity and migration;
- concrete LineageCube commutation;
- nonce, evidence, history, proof-context, publication, outbox, and migration
  refinement;
- no-bypass mounting;
- the whole-system zUSD debt/backing theorem.

Adjacent FCIS and zUSD research notes may supply vocabulary or candidate
obligations. They do not discharge an M6 problem until the problem's local
falsifier, evidence lane, and runtime boundary are checked.

## Promotion gate

Use the following fail-closed predicate for the final M6 composition review:

    M6Promote
      iff
        exact_problem_ids = [M6-R01, ..., M6-R13]
        and every problem has its appropriate
            PROVED + IMPLEMENTED + MOUNTED + TESTED evidence
        and no problem retains an unresolved GAP or UNKNOWN
            at an authoritative state, liability, effect, or entrypoint
        and RuntimeAccept has no alternate acceptance path

The proof, checker, replay, and runtime evidence must bind to the same command,
state, context, candidate, decision, receipt, bundle, durable state, and
outbox lineage. A passing inventory or unit test cannot satisfy the mounting
condition by itself.

The immediate next experiment is M6-R01. The central M6 research target is
M6-R04. M6-R09 through M6-R12 form the decisive production-closure sequence.
