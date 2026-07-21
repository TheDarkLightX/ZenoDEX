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

It also formalizes the `x/y` counterexample showing that disjoint writes alone do
not imply commutation.

The decisive runtime obligation is now explicit:

> For every promoted command profile, prove that the concrete footprint extractor
> satisfies `SoundFootprint` and that every worker computes its patch from the
> same immutable pre-state and execution-context hash.

## Revised deterministic-parallel pipeline

The pipeline should be:

```text
CanonicalCommandBytes
→ TypedCommand
→ AuthenticatedCommand
→ FootprintCertificate
→ immutable snapshot-bound worker evaluation
→ complete immutable patch
→ dynamic trace ⊆ declared footprint check
→ component-level commutation certificate
→ canonical join and rejection order
→ exact sequential differential replay
→ AtomicCandidate {
     expected_pre_root,
     execution_context_hash,
     algorithm_version,
     next_state,
     effects,
     receipt,
     nonce_updates,
     outbox
   }
→ linearizable expected-root commit
```

A task must remain sequential when any of these is true:

- its read, write, or context footprint is unknown;
- its patch depends on completion order;
- it uses a non-fixed arithmetic reduction tree;
- it shares a pool, vault, nonce, claimant, fee accumulator, Oracle lifecycle, or
  other contextual authority with another task;
- exact parallel/sequential encoding equality has not been demonstrated.

## Revised research program

### 1. Footprint refinement before value-moving parallelism

Instrument the normative sequential core to record actual reads, writes, and
context dependencies. For each command profile require:

```text
ActualReadTrace    ⊆ DeclaredReadSet
ActualWriteTrace   ⊆ DeclaredWriteSet
ActualContextTrace ⊆ DeclaredContextSet
```

Any escape is a test failure and a production fail-closed condition. Then run
schedule, worker-count, retry, and partition-profile differential replay:

```text
Encode(ParallelStepₚ(S,C,X))
=
Encode(SequentialStep(S,C,X))
```

for rejection, state, effects, roots, receipt, nonce changes, and outbox.

### 2. Atomic candidate storage refinement

The ESSO model should be refined to the actual persistence implementation. The
proof obligation is stronger than abstract compare-and-swap:

```text
root mismatch
→ no state
→ no nonce
→ no effect
→ no receipt
→ no outbox

root match
→ all five become durable in one linearization point
```

Then exercise crashes before, during, and after commit and duplicate/reordered
outbox delivery.

### 3. zUSD lifecycle decomposition

Follow Morph’s assume-guarantee result. Model separately:

1. canonical redemption traversal and debt-floor handling;
2. partial Stability Pool offset;
3. residual debt redistribution;
4. Recovery Mode bands;
5. shutdown and terminal settlement;
6. fee claimant, cancellation, and no-prior-staker custody.

For each slice:

```text
ESSO bounded model and counterexample search
→ generated reference transition
→ differential runtime oracle
→ Lean conservation/lifecycle theorem
→ composition theorem
```

Do not write one large transition first and attempt to prove it afterward.

### 4. Generated typed authority grammars

Treat parser construction as an equivalence/refinement project:

```text
source grammar
↔ canonical encoder
↔ Python parser
↔ Rust parser
↔ Tau adapter
↔ proof guest
```

Required properties are complete consumption, exact re-encoding, bounded
resources, stable typed errors, and identical acceptance/rejection across every
implementation.

### 5. Canonical allocation certificates

For matching, flow, or Walrasian proposals, require:

- a finite complete candidate domain;
- an exact integer/rational objective;
- a unique total canonical key;
- a compact feasibility and optimality certificate;
- deterministic remainder assignment;
- replay by the sequential economic core.

The deterministic-NC matching result can improve candidate construction, but it
does not replace any of these consensus obligations.

## Tool and licensing boundary

Research Kernel MCP is Apache-2.0 and can be integrated as a research/evidence
service. Morph and ESSO were accessed from the owner’s private repositories and
were used through their own exact-head workflows. Their implementations are not
vendored into ZenoDEX. Only source hashes, result hashes, scoped conclusions, and
formal obligations are retained here.

## Evidence bindings

The machine-readable companion ledger records:

- exact source and study heads;
- PR and workflow-run IDs;
- GitHub artifact digests;
- Research Kernel decision hash;
- Morph stable-study hash;
- ESSO naive and repaired verification fingerprints;
- explicit nonclaims.

## Final operating thesis

ZenoDEX may promote value-moving parallel execution only when every command has a
proved sound footprint over one immutable snapshot, the resulting complete
patches commute and join canonically, exact output bytes equal the normative
sequential core, and the complete candidate is published at one linearizable
expected-root commit point.
