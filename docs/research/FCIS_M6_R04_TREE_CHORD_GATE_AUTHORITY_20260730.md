# FCIS M6-R04 Tree–Chord–Gate Authority Certificate

**Date:** 2026-07-30  
**Status:** `RESEARCH_ONLY_EXECUTABLE_PYTHON_LEAN_JULIA_ESSO_SOURCES_UNMOUNTED`  
**Stack base:** ZenoDEX PR #497, head `1e627cee51c5fe9d8672c5e08f9d75f6f7f709fd`  
**Targets:** M6-R04 lineage composition, M6-R12 proof-obligation closure, and the M6-01/M6-03/M6-09/M6-11 authority chain

## 1. Result

This checkpoint proposes and implements a **Tree–Chord–Gate authority
certificate**, abbreviated `TCG`.

It addresses a specific M6 composition problem:

```text
local theorem A is true
local theorem B is true
local commit check C is true

but A, B, and C may describe crossed source identities,
and an undeclared publisher may bypass all three.
```

The construction combines three obligations that must remain distinct:

1. **Tree:** choose one canonical rooted path to every declared artifact.
2. **Chord:** independently check every alternative edge against the exact
   canonical target artifact and lineage.
3. **Gate:** attach a unit stage filtration so every declared source-to-sink
   path crosses every theorem-bearing authority gate in order.

Two externally anchored roots separate static and dynamic authority:

```text
topology_root
  exact nodes, edges, source, sinks, gate profile, relation/checker identities,
  and canonical parent-edge set

instance_root
  exact artifact identities, lineage bindings, receipt subjects, and receipt
  digests for one execution
```

The certificate cannot authorize either root itself.

The Python checker has 11 adversarial tests.  An independent explicit-state
search preserves a finite model and produces one-step counterexamples for each
removed safety distinction.  Companion Julia, ESSO-IR, and Lean artifacts are
included so CI and the external tools can independently check the construction.

## 2. Novelty discipline

This work follows a stricter rule after the AGQE/SRGD sign-duality correction:

> Novelty is a claim to falsify, not a premise.

Before labeling a mechanism new, search at least:

```text
sign flips
coordinate permutations
affine state conjugacies
renamings and representation isomorphisms
quotient/lift equivalences
existing internal implementations
known literature constructions
```

TCG does **not** claim priority for:

- spanning trees or arborescences;
- chord/path-basis reasoning;
- dominator analysis;
- commutative diagrams;
- complete mediation;
- provenance semirings;
- proof-carrying code;
- filtration arguments.

Its defensible claim is narrower:

> a new project-level FCIS certificate profile that combines a non-invertible
> path basis, theorem-indexed complete-mediation gates, role-indexed source
> lineage, and an externally anchored publisher inventory into one executable
> fail-closed object.

A broader novelty claim requires a dedicated literature review and peer review.

## 3. Pinned experience surface

The immediate input is the current M5-to-M6 chain:

```text
bounded bytes
  -> canonical command
  -> authenticated invocation
  -> current state
  -> current execution context
  -> validated normative decision
  -> authorized candidate
  -> atomic durable publication
  -> reopened authorized head
  -> outbox delivery
```

PR #497 already freezes fee occurrence semantics as a segmented word and derives
separate semantic and lineage roots.  TCG does not replace that work.  It treats
those roots as exact source identities to be transported through the larger M6
chain.

The remaining composition failures are grouped as:

| Class | Representative failure |
|---|---|
| semantic coherence | runtime result refines a different command or state |
| authority coherence | authorization receipt names another candidate |
| durability coherence | committed state and outbox come from different candidates |
| recovery coherence | reopened head does not reconstruct the exact committed candidate |
| complete mediation | an alternate publisher reaches authority without required checks |
| inventory completeness | the model omits a real effect-capable code path |

LineageCube handles a fixed three-axis cube.  The earlier Authority Holonomy
proposal handles path independence in an audited graph, but ordinary cycle
language suggests inverses that decoding, authorization, commit, and delivery do
not have.  TCG reformulates the problem around a rooted path basis and exact
edge receipts, so no inverse is required.

## 4. Surprise packet

The bounded research language preserves these minimal failure shapes.

### 4.1 Crossed lineage

```text
candidate arithmetic derives from witness tuple W1
receipt provenance derives from witness tuple W2
semantic_root(W1) = semantic_root(W2)
lineage_root(W1) != lineage_root(W2)
```

Equal arithmetic does not authorize crossed provenance.

### 4.2 Stage-skipping publisher

```text
raw request -> effect publication
```

A direct edge from stage zero to the final sink can preserve a plausible output
digest while bypassing authentication, current-state provenance, authorization,
commit, and reopen.

### 4.3 Same-stage source injection

A helper path may stay at one declared authority stage but introduce a new
`current_state`, `policy`, or `candidate` binding.  Stage equality alone does
not make that introduction harmless.

### 4.4 Receipt substitution

A valid receipt for

```text
(source A, target B, checker X)
```

must not discharge

```text
(source A, target C, checker X)
(source D, target B, checker X)
(source A, target B, checker Y)
```

The receipt subject therefore binds the complete exact edge instance.

### 4.5 Unanchored inventory

A certificate can be perfectly coherent over an incomplete graph.  A
self-declared topology root proves no-bypass only relative to the graph the
candidate chose to disclose.  The expected topology root must be derived from
an independent deployment/code inventory.

## 5. Morph relation card

### Source problem

```text
M6 runtime authority with multiple implementations, refinement paths,
commit/recovery paths, and effect publishers
```

### Target representation

```text
finite rooted directed acyclic multigraph
  + canonical arborescence
  + unit authority-stage filtration
  + role-indexed lineage environments
  + exact edge receipt subjects
  + static topology root
  + dynamic instance root
```

### Relation tag

`↦` — checked reduction, not yet an equivalence.

### Forward map

- each exact artifact becomes one node;
- each checked transformation becomes one edge;
- every theorem-bearing authority boundary becomes one gate;
- every independent source identity becomes a lineage role;
- one canonical implementation/recovery path supplies the tree;
- alternate implementations and recovery paths become chords;
- effect-capable publishers become final sinks.

### Reverse/lift obligations

The graph result lifts to a production M6 claim only after establishing:

1. every node corresponds to an exact runtime value and producer;
2. every edge receipt is checked by the declared independent checker;
3. the topology inventory contains every authority-bearing publisher;
4. topology and checker identities are deployment-bound;
5. the dynamic instance root is reconstructed from current sources;
6. atomic publication and reopen actually refine the declared edges;
7. no effect path exists outside the inventory.

### Information deliberately lost

TCG does not encode arbitrary source code semantics, scheduler behavior,
datastore physics, cryptographic authenticity, or deployment reachability.  It
is a finite proof object over exact identities supplied by those layers.

## 6. Mathematical object

Define the Tree–Chord–Gate atlas

\[
\mathfrak A_{\mathrm{TCG}}
 =
 (G,T,\lambda,\alpha,\Gamma,\mathcal G,\mathcal R,
   \rho_{\mathrm{top}},\rho_{\mathrm{inst}}).
\]

Its components are:

- \(G=(V,E)\): finite rooted authority DAG;
- \(T\subseteq E\): one parent edge for every non-root node;
- \(\lambda:V\to\{0,\ldots,k\}\): authority stage;
- \(\alpha(v)\): exact artifact identity at node \(v\);
- \(\Gamma(v)\): finite role-to-source identity map;
- \(\mathcal G=(g_0,\ldots,g_{k-1})\): theorem-bearing gate profile;
- \(\mathcal R(e)\): receipt for the exact edge subject;
- \(\rho_{\mathrm{top}}\): static topology/inventory root;
- \(\rho_{\mathrm{inst}}\): dynamic artifact/receipt root.

For an edge \(e:u\to v\), the admitted stage law is

\[
\lambda(v)-\lambda(u)\in\{0,1\}.
\]

If the difference is zero, the edge may introduce no lineage source.  If the
difference is one, it must carry gate \(g_{\lambda(u)}\) and introduce exactly
that gate's role set.

## 7. Role-indexed lineage algebra

A lineage environment is a finite partial map

\[
\Gamma : \mathsf{Role}\rightharpoonup\mathsf{Digest}.
\]

Define the partial agreement join \(\sqcup\):

\[
(\Gamma\sqcup I)(r)=
\begin{cases}
\Gamma(r), & r\in\operatorname{dom}(\Gamma)\setminus\operatorname{dom}(I),\\
I(r), & r\in\operatorname{dom}(I)\setminus\operatorname{dom}(\Gamma),\\
\Gamma(r)=I(r), & r\text{ occurs in both},
\end{cases}
\]

and leave the operation undefined when overlapping digests disagree.

Every edge must satisfy

\[
\Gamma(v)=\Gamma(u)\sqcup I_e.
\]

This is stronger than carrying one aggregate lineage hash.  It identifies the
semantic role whose source was crossed and makes source substitution a local
counterexample.

## 8. Edge receipt subjects

Every edge receipt is bound to

\[
\operatorname{Subj}(e)=H(
  \rho_{\mathrm{top}},
  e,
  \operatorname{relation}(e),
  \operatorname{checker}(e),
  u,\alpha(u),\Gamma(u),
  v,\alpha(v),\Gamma(v),
  I_e,
  \operatorname{gate}(e)).
\]

The receipt digest remains opaque to the generic checker.  A production profile
must independently verify that the named checker accepted this exact subject.
The generic checker only prevents a valid receipt from being replayed against a
different subject.

## 9. Tree–chord path theorem

Let the tree \(T\) define one canonical path \(P_T(v)\) from the root to every
node.  Assume every edge receipt proves

\[
\tau_e(\alpha(u))=\alpha(v).
\]

Then for every declared path \(P:r\leadsto v\),

\[
\tau_P(\alpha(r))=\alpha(v)=\tau_{P_T(v)}(\alpha(r)).
\]

Consequently any two declared paths with the same endpoints agree.

The proof is induction on the path.  No inverse is used.  This is why the
construction applies to many-to-one decoding, authentication, authorization,
commit, reopen, and delivery functions.

The tree does not remove the need for local edge receipts.  It supplies a
canonical endpoint interpretation.  Each non-tree chord is checked once against
that target instead of comparing all complete path pairs.

For one rooted connected graph:

\[
|T|=|V|-1,
\qquad
|E\setminus T|=|E|-|V|+1.
\]

The global certificate therefore needs linear local evidence rather than a
potentially exponential path enumeration.

## 10. Gate filtration theorem

Let a source-to-sink path have stages

\[
s_0=0,s_1,\ldots,s_m=k
\]

with

\[
s_{j+1}-s_j\in\{0,1\}.
\]

For every gate index \(q<k\), there is a path edge whose source stage is \(q\)
and target stage is \(q+1\).  Therefore every final path crosses every gate in
order.

A constructive invariant is

\[
\operatorname{GateComplete}(s,C)
\iff
\forall q<s,\;q\in C.
\]

- stage zero satisfies it with \(C=\varnothing\);
- a same-stage edge preserves it;
- a unit crossing from \(s\) to \(s+1\) preserves it after inserting \(s\).

The Lean file formalizes this prefix invariant and the path-coherence theorem.

## 11. Relative no-bypass theorem

Let \(P\) be every publisher/effect sink in the externally anchored topology.
If:

1. the topology root rederives from the complete node/edge/publisher inventory;
2. every sink is at final stage \(k\);
3. every edge obeys the unit filtration;
4. every edge receipt is sound for its exact subject;
5. every lineage join agrees;
6. every sink contains exactly the source roles plus all gate-introduced roles;

then, relative to that inventory:

```text
all declared paths are artifact coherent
all declared paths carry one compatible lineage
all declared paths cross every gate in order
all declared sinks contain the complete required lineage
```

The qualification **relative to that inventory** is essential.  TCG cannot
prove that source scanning, linker analysis, deployment manifests, RPC routing,
or operational configuration omitted no real publisher.  M6 no-bypass closes
only when an independent inventory procedure anchors `topology_root` and
bypass-insertion mutations demonstrate that the procedure detects a new
publisher.

## 12. Executable checker

The unmounted module is:

```text
src/core/fcis_tree_chord_gate_authority.py
```

It defines immutable exact-type values for:

```text
LineageBindingV1
AuthorityGateV1
AuthorityNodeV1
AuthorityEdgeV1
NodeArtifactExpectationV1
TreeChordGateCertificateV1
TreeChordGateVerdictV1
```

The verifier checks:

- exact Python types, including rejection of `bool` as `int`;
- canonical node, edge, role, sink, and parent-edge order;
- unique identifiers and bounded sizes;
- contiguous gate indices and disjoint gate role sets;
- exact externally supplied topology and instance roots;
- exact source and sink artifact identities;
- DAG shape and root reachability;
- stage monotonicity with increments at most one;
- same-stage non-introduction;
- exact gate label, index, and introduction role set;
- role-indexed lineage agreement;
- complete edge receipt-subject recomputation;
- one parent edge per non-source node;
- complete sink lineage.

The checker is pure.  It authenticates no root, executes no effect, and accepts
no opaque receipt as proof merely because the digest is well formed.

## 13. Adversarial tests

The focused suite contains 11 tests and currently passes locally:

```text
11 passed
```

It includes:

1. a valid ten-node, twelve-edge M6 graph;
2. three independent implementation/recovery chords and eight complete paths;
3. inserted direct-publisher bypass;
4. external topology-root substitution;
5. artifact and instance-root substitution;
6. crossed lineage on an alternative runtime path;
7. same-stage source injection;
8. gate-label and gate-role substitution;
9. receipt-subject and checker substitution;
10. non-spanning parent-edge set;
11. Boolean/integer alias and hostile frozen-object mutation.

All eight complete paths in the positive graph cross the same nine gates in the
same order.

## 14. ESSO and independent finite oracles

The finite abstraction stores:

```text
stage
receipt_mask
lineage_mask
lineage_conflict
artifact_coherent
```

Its safety predicate is:

\[
0\le s\le k,
\qquad
\neg\operatorname{conflict},
\qquad
\operatorname{artifactCoherent},
\]

\[
\{0,\ldots,s-1\}
\subseteq
\operatorname{receiptMask}
\cap
\operatorname{lineageMask},
\]

\[
\operatorname{lineageMask}
\subseteq
\operatorname{receiptMask}.
\]

The Python explicit-state oracle reports:

```text
safe profile:
  10 reachable states
  19 explored transitions
  SAFE_WITHIN_BOUND through depth 10

mutants:
  stage_skip               one-step violation
  fake_gate                one-step violation
  lineage_without_gate     one-step violation
  lineage_conflict         one-step violation
  artifact_chord_mismatch  one-step violation
```

Artifacts:

```text
formal/esso/fcis_tree_chord_gate_authority_v1.yaml
experiments/fcis_tcg_bounded_search.py
experiments/fcis_tcg_bounded_search_result.json
experiments/julia/fcis_tree_chord_gate_oracle.jl
```

The YAML is an ESSO-IR model authored against `esso-ir/v1`.  Until a live ESSO
`validate` and verifier receipt is attached, it is a model source rather than
ESSO evidence.  The Julia program is an independent Base-only oracle intended
for CI comparison with the frozen JSON.  Local Julia was unavailable during
construction, so its result is also pending CI.

## 15. Lean surface

The proof module is:

```text
lean-mathlib/Proofs/FCISTreeChordGateAuthority.lean
```

It contains:

```text
DPath.run_eq_canonical
  local non-invertible edge coherence lifts through any declared path

DPath.two_paths_agree
  two paths with common endpoints reach the same canonical value

DPath.invariant_of_edges
  any edge-local invariant composes along a path

GateComplete
gateComplete_zero
gateComplete_stay
gateComplete_cross
  constructive gate-prefix invariant

unit_stage_edge_crosses_unique_gate
unit_stage_edge_cannot_skip
  local arithmetic filtration facts

equal_lineage_extension
  equal lineage environments remain equal after one deterministic binding
```

The source contains no `sorry`, `admit`, user `axiom`, or `unsafe` declaration.
Local Lean was unavailable, so compilation and the exact axiom audit remain a CI
gate rather than a completed claim.

## 16. ZAG quality-diversity search map

A single elegant diagram is not enough.  The candidate portfolio was separated
along these axes:

| Candidate | Path coherence | Complete mediation | Non-invertible | Source lineage | Inventory dependence |
|---|---:|---:|---:|---:|---:|
| enumerate complete paths | yes | only if paths complete | yes | optional | extreme |
| LineageCube | yes, fixed cube | fixed declared faces | yes | possible | external |
| ordinary cycle holonomy | yes | no | awkward | optional | external |
| dominator-only certificate | no value agreement | partial | yes | no | external |
| filtration-only certificate | no | yes | yes | weak | external |
| provenance-only certificate | ancestry only | no | yes | yes | external |
| **TCG** | yes | yes | yes | yes | explicit/external |

ZAG-style archive descriptors for future campaigns should include:

```text
proof_surface
certificate_size
path_count_eliminated
lineage_conflict_detection
stage_skip_detection
publisher_inventory_dependency
noninvertible_map_support
runtime_trusted_surface
```

A candidate is not promoted merely for novelty or lower certificate size.  It
must retain zero false accepts under all sealed authority mutations.

## 17. Assurance Defect Vector

For search and review, define

\[
\Delta(\mathfrak A)
  = (L,C,G,P),
\]

where:

- \(L\): lineage conflicts or unbound source roles;
- \(C\): failed edge/chord receipt subjects;
- \(G\): gate-order, stage-skip, or gate-role defects;
- \(P\): uncovered or unanchored authority publishers.

The target condition is

\[
\Delta(\mathfrak A)=(0,0,0,0).
\]

This is an audit/search descriptor, not a scalar safety score.  Lexicographic or
weighted minimization must never let an improvement in one coordinate hide a
nonzero safety defect in another.

## 18. Mapping to ZenoFCIS

ZenoFCIS already supplies the architectural direction:

```text
immutable values
closed Accept | Reject outcomes
source-bound authority
nominal commit authorization
atomic SQLite publication
reopen and outbox replay
```

TCG should become a generic ZenoFCIS profile only after the research object
stabilizes.  A generic library surface would likely contain:

```text
AuthorityTopologyProfile
AuthorityGate
AuthorityArtifactNode
AuthorityRelationEdge
AuthorityReceiptSubject
AuthorityLineage
AuthorityCertificate
verify_authority_certificate
```

The library must not discover deployment publishers itself or accept arbitrary
checker import paths.  Applications supply a theorem-indexed profile whose
checker identities are in the authority-owned catalog.  Deployment tooling
supplies the externally anchored topology root.

## 19. M6 impact

TCG can compress or clarify these gates:

| M6 item | Contribution | Remaining obligation |
|---|---|---|
| R04 lineage | role-indexed exact lineage across all declared paths | instantiate actual settlement/state/context/candidate roots |
| R12 proof inventory | finite nodes, edges, gates, receipts, roots | bind each item to source and CI evidence |
| M6-01 bytes-to-command | alternative decoders become checked chords | exact codec and authentication integration |
| M6-03 runtime refinement | reference/runtime paths converge on one target | concrete Python/Rust/guest receipt checkers |
| M6-09 recovery | normal and recovery reopen become chords | datastore crash/reopen refinement |
| M6-11 no bypass | gate filtration plus external topology root | complete publisher discovery and deployment anchoring |

It does **not** close:

- exact settlement witness extraction;
- active-policy authentication or currentness;
- current-state provenance;
- the actual candidate/receipt schema;
- atomic datastore behavior;
- crash consistency;
- outbox delivery semantics;
- complete deployment publisher inventory;
- runtime mounting or M6 promotion.

## 20. Explorer map beyond TCG

The machine-readable companion catalog preserves eight research directions.
The most promising are:

### 20.1 Durable Retraction Algebra

Let authorized candidates be \(A\), durable records \(D\), commit \(c:A\to D\),
and reopen \(r:D\to A\).  Require

\[
r\circ c=\operatorname{id}_A.
\]

Combined with an intervention algebra, recovery must yield exact `PRE` or exact
`POST`, never an authoritative partial projection.  This directly targets M6
publication/recovery.

### 20.2 Dynamic Authority Atlas

A schema or deployment migration changes the theorem-indexed atlas
\(P\to Q\).  Old evidence transports only through an explicit map

\[
M_*:\operatorname{Evidence}(P)\to\operatorname{Evidence}(Q).
\]

Without \(M_*\), receipts are invalidated.  This gives mathematical form to
configuration authority, migration, and anti-ABA requirements.

### 20.3 Authority Descent

Treat subsystem certificates as local sections.  They glue into one global
authority object only when overlap lineage, state, and effect identities agree.
This is a speculative bridge to sheaf/descent methods; TCG is the smaller finite
executable shadow.

### 20.4 Filtered Provenance Semiring

Use addition for alternative derivations, multiplication for joint dependencies,
and an authority-depth filtration for completed gates.  This is aligned with
known provenance-semiring work and should be presented as a new application,
not new algebra.

### 20.5 Equivalence-Before-Novelty Gate

Before LEAP or ZAG labels a candidate `NEW_MECHANISM`, search for a map \(\phi\)
satisfying

\[
\phi(T_{old}(s,e))=T_{new}(\phi(s),e)
\]

and matching outputs.  Exact conjugacies receive labels such as
`ISOMORPHIC_REFORMULATION` or `NEW_CERTIFICATE_PROFILE`.  The SRGD/AGQE sign map
is the permanent regression fixture.

### 20.6 State-indexed intervention quotients

Swap adjacent crash/retry/recovery actions only after checking the exact diamond
at the current prefix state.  Static operation-name independence is forbidden.
This can reduce ESSO search without erasing phase-dependent counterexamples.

## 21. Optimized explorer workflow

The revised workflow is:

1. **Freeze original authority.** State exact inputs, source roots, publishers,
   and nonclaims.
2. **Internal duplicate search.** Search state conjugacies and existing code
   before novelty labels.
3. **Surprise packet.** Preserve minimal counterexamples and failed proof shapes.
4. **LEAP diagnosis.** Search missing distinctions, language extensions, and
   experiment designs.
5. **Morph relation card.** Record the forward map, reverse lift, lost
   information, and authority consequences.
6. **ZAG portfolio.** Maintain diverse candidates across proof surface,
   certificate size, trusted surface, and mutation coverage.
7. **Checker first.** Define a small deterministic verifier before optimizing a
   proposer.
8. **ESSO finite world.** Exhaust bounded state machines and minimize spoilers.
9. **Julia differential oracle.** Recompute finite results independently.
10. **Lean connective theorem.** Prove the general implication from explicit
    premises.
11. **ZenoFCIS refinement.** Bind exact application values, authority catalog,
    commit, reopen, and delivery.
12. **Prospective falsification.** Use sealed mutations and equal verifier
    budgets before promotion.

Tool outputs retain different authority:

| Tool | Proper role | Does not establish |
|---|---|---|
| LEAP | language/abstraction/mechanism proposals | novelty or runtime truth |
| Morph | checked reformulation obligations | a lift that was not verified |
| ZAG | diverse algorithm/certificate candidates | correctness from score |
| ESSO | bounded finite-state evidence | unbounded theorem or adapter refinement |
| Julia | independent witnesses and differential oracles | production authority |
| Lean | reusable implications | authentic bytes, storage physics, or no-bypass |
| ZenoFCIS | exact application authority and publication boundary | correctness of unbound external artifacts |

## 22. ATDD contract

```text
TCG-1 External topology
  Given an authority-owned topology root
  When a node, edge, checker, gate, sink, or parent edge is inserted or removed
  Then the certificate rejects.

TCG-2 External instance
  Given an authority-owned instance root
  When any artifact, lineage binding, receipt subject, or receipt digest changes
  Then the certificate rejects.

TCG-3 Path coherence
  Given sound exact edge receipts
  When two declared paths have common endpoints
  Then both transport the source artifact to the same target artifact.

TCG-4 Gate mediation
  Given source stage zero, final stage k, and unit monotone edges
  When any declared source-to-sink path is replayed
  Then it crosses every gate 0..k-1 in order.

TCG-5 Lineage agreement
  Given role-indexed source bindings
  When two paths introduce the same role with different digests
  Then the partial lineage join rejects.

TCG-6 No same-stage source
  Given an edge whose source and target share a stage
  When it introduces any lineage role
  Then the certificate rejects.

TCG-7 Receipt subject
  Given a receipt for one source, target, relation, and checker
  When any subject field is substituted
  Then the receipt cannot discharge the new edge.

TCG-8 Arborescence
  Given V nodes
  When the parent set does not contain exactly one incoming edge for every
  non-source node
  Then the certificate rejects.

TCG-9 Complete sink lineage
  Given theorem-bearing gate role sets
  When a final sink omits or adds a role
  Then the certificate rejects.

TCG-10 Runtime no-bypass
  Given a complete independently derived publisher inventory
  When an effect-capable path is added outside the declared graph
  Then the deployment topology root or bypass mutation gate must fail.
```

## 23. Evidence ledger

| Claim | Status | Evidence |
|---|---|---|
| Python certificate shape and mutation rejection | `TESTED` | 11 focused tests |
| Safe finite filtration through depth 10 | `TESTED_ONLY` | Python explicit-state oracle |
| Five one-step mutant counterexamples | `TESTED_ONLY` | frozen JSON result |
| Julia independent agreement | `PENDING_CI` | Base-only oracle source |
| ESSO model validity | `MODEL_AUTHORED` | ESSO-IR source, no live receipt yet |
| Generic path-coherence theorem | `LEAN_SOURCE_AUTHORED` | compilation pending CI |
| Generic gate-prefix theorem | `LEAN_SOURCE_AUTHORED` | compilation pending CI |
| Exact ZenoDEX publisher inventory | `GAP` | deployment/source inventory not yet built |
| Exact edge receipt semantics | `GAP` | application checkers not instantiated |
| Atomic commit/reopen refinement | `GAP` | later Durable Retraction checkpoint |
| Production no-bypass | `GAP` | requires complete externally anchored inventory |
| Runtime authority | `UNMOUNTED` | no consumer or publication path added |

## 24. Smallest safe next checkpoint

Do not mount the generic checker yet.

The next checkpoint should instantiate one exact fee-allocation publication
path from PR #497:

```text
settlement replay roots
  -> segmented witness/semantic roots
  -> current SRGD state and active policy
  -> pure allocation decision
  -> authorized candidate and receipt
  -> atomic state/outbox commit
  -> reopened authorized head
  -> outbox delivery
```

For that path:

1. identify every actual producer and effect-capable publisher;
2. freeze a static topology profile and checker catalog;
3. derive the topology root independently from deployment sources;
4. bind each edge receipt to exact node artifacts;
5. create normal/recovery/runtime alternative chords;
6. run bypass-insertion mutations;
7. model commit/reopen as a durable retraction;
8. only then consider a generic ZenoFCIS authority-profile API.

## 25. Nonclaims

This checkpoint does not claim:

- global mathematical priority for its component ideas;
- that the current runtime publisher inventory is complete;
- that a digest proves the receipt behind it is sound;
- that the ESSO model has a live verification receipt;
- that the Julia oracle has run in CI;
- that the Lean file has compiled or completed an axiom audit;
- exact Python/Rust/guest refinement;
- authenticated policy or current state;
- atomic datastore publication or crash safety;
- recovered-head or outbox correctness;
- production no-bypass;
- M6 completion, mounting, or production readiness.

The concrete result is a falsifiable, linear-size composition certificate and a
research map.  Its production value depends on the next application-specific
inventory and refinement checkpoint.
