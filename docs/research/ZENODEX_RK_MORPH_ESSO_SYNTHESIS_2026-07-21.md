# ZenoDEX Research Kernel, Morph, and ESSO synthesis

Date: 2026-07-21  
Parent theorem-ledger PR: #471 at `3c5ee8b7487048a2dd0a370a64eeb1c294cd9c04`

## Executive conclusion

Using the three tools changes the next research priority.

The immediate obstacle to value-moving deterministic parallel execution is not a
lack of scheduling algorithms. It is the absence of a proved refinement from
concrete commands to complete, sound `ReadSet`, `WriteSet`, and `ContextSet`
values, followed by one atomic publication boundary for state, effects, receipts,
nonces, and outbox rows.

The strongest sequence supported by the combined evidence is:

```text
one canonical typed grammar per authority surface
→ immutable owned pre-state
→ pure commands with sound footprints
→ independent patch algebra over one snapshot
→ canonical rejection/effect/receipt join
→ one expected-root atomic candidate commit
→ bounded lifecycle closure for zUSD
→ cross-language and proof-guest refinement
```

Matching, flow, equilibrium, and accelerated parallel solvers remain outside the
trusted core. They may propose candidates only after the finite candidate domain,
objective, normalization, and tie-break are protocol values, and the sequential
core can replay the candidate exactly.

## Evidence binding rule

The synthesis ledger is not satisfied by hashes that merely have the right
length. Its validator pins the exact parent head, tool repositories, tool source
commits, study commits, pull-request numbers, workflow-run identifiers,
workflow conclusions, artifact digests, stable result hashes, and ESSO model
fingerprints used for this result. A same-width SHA or digest substitution is a
failed evidence check, even when every other field remains structurally valid.

This is still local release evidence rather than a proof supplied by the remote
tools. Research Kernel, Morph, and ESSO results enter the assurance case only
through the exact recorded artifacts and the explicit nonclaims below.

## What each tool was allowed to establish

### Research Kernel

Research Kernel was used as a deterministic evidence graph and promotion gate,
not as a theorem prover. The successful exact-head run:

- promoted the narrowly scoped claim that typed deterministic parsing is useful
  only together with concrete bounded full-consumption and exact re-encoding
  refinement;
- retained explicit nonclaims that runtime parser refinement is incomplete;
- refuted two overbroad claims with concrete witnesses;
- ranked the remaining frontier.

The two refuted claims are important:

1. **Disjoint write sets are sufficient for deterministic parallelism.**

   Counterexample: Task A reads `x` and writes `y := x`; Task B writes `x := 1`.
   The write sets `{y}` and `{x}` are disjoint, but the order changes `y`.

2. **Any deterministic matching algorithm produces a canonical settlement.**

   Counterexample: `K₂,₂` has two cardinality-optimal perfect matchings. Two
   deterministic implementations using different vertex orderings can return
   different valid matchings unless the protocol supplies a unique total key.

Research Kernel’s highest-priority open item was the incomplete zUSD economic
lifecycle, followed by bounded lifecycle models, concrete parser refinement,
canonical matching certificates, and dynamic footprint differential tests.

### Morph

Morph was used only for deterministic advisory reformulation retrieval. Five
explicit problem states were built for:

- authority parsing;
- deterministic parallel execution;
- zUSD lifecycle closure;
- canonical allocation;
- release assurance.

Each agenda was generated twice and required identical output. Every candidate
remained `promotable: false`.

The most useful cross-problem reformulation was **assume-guarantee
factorization**: decompose the large claim into interfaces whose composition is
proved separately. For ZenoDEX this means:

```text
Parser contract
Footprint contract
Pure transition contract
Patch/join contract
Atomic commit contract
Receipt/trace contract
Cross-language refinement contract
```

Other useful moves were invariant-coordinate projection, symmetry quotienting
for bounded lifecycle models, and matching-to-flow reduction for capacity-aware
allocation.

Morph also returned structurally similar but semantically dubious suggestions,
such as SAT-to-2-SAT or Horn-SAT reformulations for several unrelated ZenoDEX
problems. That is useful negative evidence: retrieval score cannot authorize a
reformulation. Every `≅`, reduction, relaxation, or restriction tag must receive a
ZenoDEX domain verifier and strict replay before promotion.

### ESSO

ESSO was used as a finite bounded transition-system verifier.

Two models were checked:

```text
Naive shell:
  publish state
  publish effects
  publish receipt
  publish outbox
  as separate actions

Repaired shell:
  commit the complete root-bound candidate in one action
  then deliver only from the committed outbox
```

The naive model failed. Z3 produced a concrete witness for
`inductive_publish_state`:

```text
pre:
  phase = Prepared
  root_match = true
  candidate_valid = true
  worker_failed = false
  all publication flags = false

post:
  phase = Committed
  state_published = true
  effects_published = false
  receipt_published = false
  outbox_published = false
```

The repaired bounded model verified every declared one-step inductive query with
fingerprint:

```text
5820b12530cdd40d1f67c950dfef4c4bb798f2ede514e816424717f7ade1e8d4
```

This establishes only the bounded control relation. Production still needs a
refinement proof to the actual datastore, crash points, compare-and-swap,
transactional outbox, and delivery implementation.

## New formal result: read/write-stable commutation

PR #471 proved that already-computed disjoint immutable patches commute. The
three-tool run exposed the missing semantic premise: state-dependent tasks may
compute different patches after another task changes a value they read.

`Proofs/ReadWriteStableParallel.lean` therefore introduces:

```text
ReadsOnly(reads, task)
  agreeing on `reads` gives the same computed patch

WritesWithin(writes, task)
  every emitted patch cell belongs to `writes`

Noninterfering(left, right)
  left.writes  ∩ right.writes = ∅
  left.reads   ∩ right.writes = ∅
  right.reads  ∩ left.writes  = ∅
```

It proves:

```text
SoundFootprint(leftFP, leftTask)
∧ SoundFootprint(rightFP, rightTask)
∧ Noninterfering(leftFP, rightFP)
→ execute(leftTask) ∘ execute(rightTask)
  = execute(rightTask) ∘ execute(leftTask)
```

The theorem is abstract. Production promotion requires a concrete extractor for
every promoted command profile and evidence that actual runtime reads, writes,
and contextual dependencies are contained in the declared footprint.

## Concrete ZenoDEX consequence

The current `zeno_ledger_conflict_graph_v0` should remain an admission aid. Its
single `touched_cells` set does not establish the read/write/context relation
needed by the theorem above.

A promoted footprint value must bind at least:

```text
command hash
pre-state root
execution-context hash
algorithm version
policy version
read cells
write cells
context cells
possible effect kinds
```

The normative sequential core should be instrumented to establish:

```text
ActualReads    ⊆ DeclaredReads
ActualWrites   ⊆ DeclaredWrites
ActualContexts ⊆ DeclaredContexts
```

An escape from any declared set must force conservative global conflict or
sequential execution.

## Revised engineering order

1. **Source-derived typed authority grammar and concrete round-trip refinement.**
2. **Sound read/write/context footprints with dynamic trace containment.**
3. **One atomic state/effect/receipt/nonce/outbox candidate commit.**
4. **Separate bounded zUSD lifecycle machines and a checked composition rule.**
5. **Canonical finite matching/flow certificates replayed by the sequential core.**

The complete promotion equality remains:

```text
Encode(ParallelStep(S, C, X))
=
Encode(SequentialStep(S, C, X))
```

including acceptance, rejection precedence, successor state, effects, receipt,
roots, nonces, fee allocation, rounding residue, and outbox entries.

## Explicit nonclaims

- Research Kernel’s supported status is a local promotion decision, not an
  external mathematical proof.
- Morph results remain advisory until a ZenoDEX-specific verifier and strict
  replay establish the claimed relation.
- ESSO’s result is bounded; it does not prove the production datastore or crash
  recovery implementation.
- The Lean result does not prove the current runtime footprint extractor sound.
- Remaining zUSD redemption, liquidation, redistribution, recovery, and
  shutdown lifecycles are not closed.
- Arbitrary value-moving parallel execution is not promoted.
