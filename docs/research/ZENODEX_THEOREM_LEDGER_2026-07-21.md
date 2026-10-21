# ZenoDEX theorem ledger: deterministic parsing, parallel execution, and market mathematics

Date: 2026-07-21  
Status: research candidate; not a production-verification claim  
Companion data: `docs/research/ZENODEX_THEOREM_LEDGER_V1.json`

## Executive conclusion

Typed deterministic parser combinators are highly useful for ZenoDEX, but only in a stricter form than ordinary parser-combinator libraries. The authority parser should be a typed, total, bounded, full-consumption function with statically disjoint choices, canonical re-encoding, no semantic side effects, and stable typed errors. Used this way, parsing becomes the first theorem in one continuous assurance chain:

```text
unique authority bytes
→ unique typed command
→ immutable owned pre-state
→ pure total transition
→ sound read/write footprint
→ independent patch commutation
→ canonical join and error order
→ expected-root atomic commit
→ canonical receipt and trace commitment
→ cross-implementation refinement
```

The most valuable literature in the supplied collection is therefore not one isolated paper. It is the combination of:

1. typed predictive parsing;
2. ownership and transitive reference immutability;
3. typestate and effect systems;
4. Kahn-style deterministic semantics;
5. commutation and permutation invariance for independent pure updates;
6. linearizable atomic commitment;
7. canonical cryptographic framing and trace commitments; and
8. axiomatic and equilibrium results for AMMs and batch auctions.

The main mathematical insight is that ZenoDEX should not attempt to prove that an arbitrary multithreaded implementation is deterministic. It should define a small deterministic batch semantics, compile commands into pure patches against one immutable snapshot, prove the patches independent or commuting, use a fixed join plan, and atomically compare-and-swap one complete candidate.

## 1. Typed deterministic parser combinators

### 1.1 Why they are useful

A conventional decoder often has the type:

```text
bytes → object | error
```

That hides most of the authority obligations. A ZenoDEX parser should instead expose a sequence of typed refinements:

```text
RawBytes
  → CanonicalBytes
  → ParsedCommand
  → AuthenticatedCommand
  → AuthorizedCommand
```

Each arrow should be a total function returning either one typed successor or one stable rejection. No later layer should be able to receive an earlier type.

Krishnaswami and Yallop's *A Typed, Algebraic Approach to Parsing* gives a compositional type criterion for context-free expressions that can be parsed unambiguously by predictive LL(1)-style algorithms. The derived combinators have linear-time behavior, single-token lookahead, and no backtracking. The later **flap** work normalizes context-free expressions to a deterministic Greibach-style normal form and proves the normalization semantics-preserving, while allowing lexer/parser fusion.

Primary sources:

- https://doi.org/10.1145/3314221.3314625
- https://arxiv.org/abs/2304.05276
- https://arxiv.org/abs/2305.07901

### 1.2 The exact theorem ZenoDEX needs

Let a deterministic parser be:

```text
P : Bytes → Option (Value × Bytes)
```

A complete authority parse is:

```text
AcceptsAll(P, b, v) := P(b) = Some(v, ε)
```

Then:

```text
AcceptsAll(P, b, v₁) ∧ AcceptsAll(P, b, v₂) → v₁ = v₂
```

If an encoder satisfies the left-inverse property:

```text
∀v, P(encode(v)) = Some(v, ε)
```

then:

```text
encode(v₁) = encode(v₂) → v₁ = v₂
```

For an authority transport, require the stronger canonical admission rule:

```text
P(b) = Some(v, ε) ∧ encode(v) = b
```

This gives one accepted byte spelling for each accepted typed value.

The PR formalizes these connective results in:

- `lean-mathlib/Proofs/TypedDeterministicParser.lean`

### 1.3 Required implementation restrictions

The parser combinator API should not expose unrestricted backtracking, arbitrary semantic actions, mutable parser state, exceptions as control flow, ambient clock reads, locale-dependent conversion, floating point, or recursive grammars without a checked termination/budget argument.

The production authority parser should require:

- exact bytes, not an already-decoded host object;
- full input consumption;
- one canonical integer and hexadecimal spelling;
- duplicate-key rejection before value loss;
- no NaN, infinity, floating point, exponent aliases, or negative zero;
- bounded bytes, depth, collection length, token count, and recursion;
- declared grammar and algorithm version;
- stable typed rejection codes;
- no I/O or semantic state mutation while parsing;
- reference-parser differential vectors across Python, Rust, proof guests, and any Tau adapter;
- a grammar-normalization or parser-generation certificate if code is generated.

### 1.4 Bibliographic correction

The supplied item “Xie, Yang, Chen, Zhang — typed deterministic parser combinators (2021)” could not be verified as written. The closest and strongest relevant lineage is:

1. Neel Krishnaswami and Jeremy Yallop, *A Typed, Algebraic Approach to Parsing*, PLDI 2019.
2. Jeremy Yallop, Ningning Xie, and Neel Krishnaswami, *flap: A Deterministic Parser with Fused Lexing*, PLDI 2023.
3. Ashish Mishra and Suresh Jagannathan, *Morpheus: Automated Safety Verification of Data-dependent Parser Combinator Programs*, 2023.

## 2. Deterministic parallel programming

### 2.1 The safe architecture

The normative architecture should be:

```text
canonical command bytes
→ typed parse and authentication
→ immutable pre-state S₀ and execution-context digest C
→ deterministic command ordering
→ sound read/write/effect footprints
→ deterministic conflict graph
→ pure worker evaluation against (S₀, C)
→ immutable candidate patches
→ fixed canonical join and reduction tree
→ complete candidate {state, effects, receipt, roots, nonce, outbox}
→ compare-and-swap expected pre-root
```

The shell may run workers in any physical order only after the logical plan is fixed.

### 2.2 Two different semantic models must not be confused

#### Snapshot-batch semantics

All tasks read the same immutable `S₀` and produce patches. If patches write disjoint cells, application order does not matter:

```text
DisjointWrites(Pᵢ, Pⱼ)
→ apply(Pᵢ, apply(Pⱼ, S)) = apply(Pⱼ, apply(Pᵢ, S))
```

For a permutation `π`:

```text
fold(apply, S, [P₁,…,Pₙ])
=
fold(apply, S, π([P₁,…,Pₙ]))
```

This is formalized in:

- `lean-mathlib/Proofs/DeterministicParallelExecution.lean`

The repository already had the concrete single-key version in:

- `lean-mathlib/Proofs/ZenoLedgerDisjointWrites.lean`

The new theorem generalizes the update from a single key assignment to arbitrary finite patches and adds expected-root commit lemmas.

#### Sequential-equivalence semantics

If the normative sequential transition lets task `j` observe task `i`'s newly written state, disjoint writes are not enough. ZenoDEX must establish one of:

```text
Readᵢ ∩ Writeⱼ = ∅
Readⱼ ∩ Writeᵢ = ∅
Writeᵢ ∩ Writeⱼ = ∅
```

or directly prove:

```text
Stepᵢ ∘ Stepⱼ = Stepⱼ ∘ Stepᵢ
```

including state, effects, errors, receipts, roots, fees, and event order.

The production differential gate should therefore be:

```text
ParallelStep(S, C, B) = NormativeStep(S, C, B)
```

for every generated and adversarial batch `B`, comparing:

- acceptance/rejection;
- stable error code and offending command identity;
- successor state bytes and root;
- effect plan bytes and root;
- receipt bytes and root;
- nonce progression;
- fee ownership and residue;
- outbox identity/order;
- proof/public-input commitments.

### 2.3 Why each foundational paper matters

**Ownership types — Clarke, Potter, Noble.** The committed state must own its transitive graph. A frozen outer record retaining mutable children is not immutable. Ownership is the type-level rule that closes constructor aliases and illegal access paths.

**Reference immutability — Birka, Ernst.** Read-only authority must cover transitively reachable abstract state, not only top-level fields. This directly addresses ZenoDEX's `STATE-ALIAS-*` family.

**Persistent data structures — Okasaki.** Persistent structures naturally preserve prior versions and make pure transitions practical. They reduce copying cost, but structural sharing must not expose a mutable node or let pointer identity become semantic.

**Typestate — DeLine/Fähndrich and Garcia et al.** Parsing, authentication, authorization, execution, finalization, settlement, and claim lifecycles should be represented as legal state transitions. Illegal phases should be unconstructable rather than rejected late by convention.

**Effect systems — Lucassen/Gifford and later practical systems.** A scheduler cannot prove independence from source inspection heuristics alone. The effect description must conservatively include actual reads, writes, external calls, time, randomness, and context dependencies.

**Kahn networks and Lustre.** Determinism comes from the denotational model and synchronous data dependencies, not from hoping threads happen to interleave consistently. Lustre's synchronous discipline is particularly relevant to Oracle epochs, clearing phases, and fixed-rate control loops.

**Linearizability — Herlihy/Wing.** The imperative shell needs one observable atomic transition. A correct pure core followed by partial state/effect publication is still incorrect.

**Software fault isolation — Wahbe et al.** Candidate-generating optimizers, provers, GPU kernels, and external solvers should be sandboxed. Isolation constrains damage; it never upgrades their output into authority. The core must recheck typed bounded output.

**CRDTs — Shapiro et al.** CRDT convergence is useful for telemetry, peer discovery, caches, and rebuildable indexes. It is not a substitute for canonical serial economic semantics and should not own authoritative balances, positions, nonces, or fee claims.

**Hash-consing — Goto/Sumii; Filliâtre/Conchon.** Hash-consing can share immutable DAGs and accelerate equality. It is safe only when keys are canonical, collisions are resolved by full equality, and cache/pointer identity never enters consensus semantics.

## 3. Atomic commitment and evidence

The candidate committed by the shell should be one immutable value:

```text
Candidate := {
  expected_pre_root,
  context_hash,
  algorithm_version,
  next_state,
  next_state_root,
  effects,
  effects_root,
  receipt,
  receipt_root,
  nonce_updates,
  outbox_entries
}
```

Commit is:

```text
commit(expected, observed, candidate)
  = Some(candidate)  if expected = observed
  = None             otherwise
```

A root mismatch must not publish any state, effect, receipt, nonce, or outbox row. External delivery occurs from an idempotent transactional outbox after commit.

### 3.1 Domain separation

Every authority hash needs an explicit prefix-free domain containing at least:

```text
protocol | chain | module | object-kind | schema-version | algorithm-version
```

followed by length-delimited fields. State roots, support roots, command hashes, receipts, proofs, signatures, Oracle reports, and settlement certificates must never share an ambiguous preimage language.

Bellare–Canetti–Krawczyk's keyed-hash constructions are not themselves a theorem about ZenoDEX framing, but their security analysis illustrates why structurally different cryptographic roles must be separated. The direct ZenoDEX proof obligation is framing injectivity, already represented by `StateRootFramingInjectivity.lean`.

### 3.2 Tamper-evident logs, Merkle traces, and bisection

Crosby–Wallach-style append-only evidence and Merkle commitments should be used for audit receipts, not as a replacement for transition correctness. Each trace leaf should commit:

```text
index
pre_root
canonical_command_hash
context_hash
accept_or_reject
post_root_or_none
effects_root_or_none
receipt_root_or_none
```

*Light Clients for Lazy Blockchains* proves a succinct, complete, and sound logarithmic bisection protocol under its model. ZenoDEX can adapt the first-divergence pattern to cross-language replay, light clients, and proof disputes, provided the trace encoding and data-availability assumptions are explicit.

Primary source: https://arxiv.org/abs/2203.15968v3

### 3.3 Recursive proofs

Recursive SNARK/STARK composition is valuable after the base transition relation, canonical public inputs, and trace leaves are stable. Recursion should aggregate already-verified step receipts; it should not conceal unproved host-side parsing, Oracle authority, scheduler independence, or effect publication.

## 4. AMM and batch-clearing mathematics

### 4.1 Axiomatic curve profiles

Schlegel, Kwaśnicki, and Mamageishvili characterize a generalized constant-product family by independence and scale invariance, and LMSR by independence and translation invariance, within their axiomatic framework. This suggests a better ZenoDEX curve registry:

```text
CurveProfile := {
  invariance_axioms,
  independence_axioms,
  symmetry,
  liquidity_domain,
  boundary_behavior,
  pricing_oracle_relation,
  fee_semantics,
  integer_rounding_policy,
  implementation_refinement
}
```

A curve is admitted only if its implementation and proof bundle satisfy the declared profile.

Primary source: https://arxiv.org/abs/2210.00048v4

### 4.2 Transaction-splitting-neutral fees

Bichuch and Feinstein develop an axiomatic AMM framework and propose a fee structure intended to make the AMM indifferent to transaction splitting. The direct ZenoDEX requirement should be stronger and fully discrete:

```text
AggregateEffect(split(command)) = AggregateEffect(command)
```

for user debit, pool reserve movement, protocol fee, host claim, staker claim, and explicit bounded residue, whenever the split is semantically admissible.

Primary source: https://arxiv.org/abs/2210.01227v4

### 4.3 Walraswap: useful existence theorem, incomplete implementation theorem

Walraswap's Theorem 2.4 applies Brouwer to show that a strict admissible supply function has a zero. Theorem 6.1 applies the construction to orders and AMMs, proving an AMM swap choice optimal for the auctioneer's price-weighted objective and, under strictness, a price vector with nonnegative surplus in every token. Proposition 7.1 gives a support-separation result that motivates decomposing some token topologies into parallel subproblems.

These are among the most valuable mathematical results in the supplied market list. They still do not provide the full production algorithm ZenoDEX needs. The missing bridge is:

```text
continuous existence theorem
→ bounded rational/integer candidate domain
→ terminating deterministic search or untrusted proposal
→ residual/error certificate
→ exact conservation and limit checks
→ canonical normalization and tie break
→ settlement/effect normal form
```

The safest design is a certificate-producing solver outside the trusted core. The solver proposes prices and allocations. The core checks:

- complete order and pool coverage;
- strictness or a valid boundary-case certificate;
- limit-price satisfaction;
- exact integer conservation;
- no negative balance/reserve;
- fixed rounding policy;
- residual bound relative to the declared rational model;
- canonical price-vector normalization;
- canonical winner among equally valid candidates.

Primary source: https://arxiv.org/abs/2310.12255v2

### 4.4 Double-auction convergence

Pennanen shows that, under the paper's nonstrategic divisible-asset assumptions, zero trading coincides with a Pareto-frontier allocation and repeated double auctions converge to individually rational Pareto allocations. This is a useful simulation oracle and long-run benchmark, not a direct production theorem for strategic blockchain participants.

Primary source: https://arxiv.org/abs/2001.02071v2

### 4.5 am-AMM

The am-AMM paper establishes an equilibrium under its demand, arbitrage, entry, and rent assumptions and concludes equilibrium liquidity is higher than for fixed-fee AMMs in that model. This is promising for an experimental module, but the manager auction enlarges censorship, sandwich, governance, and block-builder concentration surfaces. It should remain outside the normative core until those risks are modeled and bounded.

Primary source: https://arxiv.org/abs/2403.03367v4

### 4.6 Stochastic rounding

Stochastic rounding is deliberately random. Its unbiasedness and variance properties may help off-chain optimization or machine-learning components, but it is inappropriate for consensus arithmetic unless randomness itself is committed, authenticated, and part of the specification. ZenoDEX's value-moving core should remain exact integer arithmetic with one rounding rule.

Primary source: https://arxiv.org/abs/2006.00489v1

## 5. Triage of the supplied literature

| Source or lineage | Tier | ZenoDEX verdict |
|---|---:|---|
| Plotkin/Milner equational and substitution semantics | S | Use as the refinement style: equal inputs and contexts imply observationally equal state/effects/receipt results. |
| Ownership types | S | Adopt for the committed transitive object graph. |
| Reference immutability | S | Adopt for state, commands, effects, receipts, and proof inputs. |
| Okasaki persistent structures | S | Adopt implementation techniques, with no mutable shared nodes or pointer semantics. |
| Herlihy/Wing linearizability | S | Adopt for expected-root atomic publication. |
| DeLine/Fähndrich and Garcia typestate | S | Adopt for every authority and lifecycle phase. |
| Kahn networks | S | Adopt the schedule-independent semantic model. |
| Lustre/synchronous programming | A | Use for epoch/Oracle/control-state machines and fixed logical clocks. |
| Lucassen/Gifford effects | S | Adopt a sound footprint discipline before parallel scheduling. |
| Typed deterministic parsing | S | Adopt at every authority byte boundary. |
| Bellare/Canetti/Krawczyk | S | Adopt explicit cryptographic domains and prove framing injectivity. |
| Crosby/Wallach append-only storage | A | Use for evidence and audit logs, not transition semantics. |
| Merkle proof/light-client lineage | A | Use for trace commitments, data availability, and first-divergence disputes. |
| Recursive zk proof lineage | A | Aggregate verified steps only after the base relation and public inputs stabilize. |
| Wahbe et al. SFI | B | Sandbox untrusted solvers/workers; do not treat isolation as correctness. |
| CRDTs | B | Restrict to non-authoritative replicated views. |
| Hash-consing | B | Use for immutable DAG caches with collision-safe equality. |
| Sedna, arXiv:2512.17045v2 | B | Explore private/coded order dissemination; decode before canonical parsing. |
| MathLedger, arXiv:2601.00816v1 | B | Reuse fail-closed verifier-feedback/evidence-ledger ideas; retain explicit nonclaims. |
| Light Clients for Lazy Blockchains | A | Adapt Merkle bisection for light clients and differential replay disputes. |
| zkSTAR temporal consistency | B | Reuse the pattern for privacy-preserving Oracle/risk-trace consistency. |
| LFT2 | B | Consensus reference; not a functional-core arithmetic theorem. |
| The Functional Era | A | Useful typed-pattern vocabulary; supporting design evidence rather than a core theorem. |
| Free bifibration/parallelization rules | C | Interesting canonical-factorization theory; no immediate runtime mount stronger than effect/commutation proofs. |
| Proto-Quipper dynamic lifting | C | Useful analogy for separating generation-time parameters from execution-time state. |
| Digital image restriction/interpolation | C | Low relevance; possible analogy for multiresolution state summaries only. |
| Xiang et al. strengthened BFT | B | Relevant to validator resilience, not DEX pure-function determinism. |
| Dolev et al. self-stabilizing RSM | B | High-value later work for recovery from corrupted Oracle/registry/validator state. |
| Lambert topos consensus view | C | Conceptual consistency lens; no priority implementation theorem. |
| Range-Arithmetic, arXiv:2505.17623 | B | Useful only for proving approximate ML/range computations; unnecessary for exact AMM arithmetic. |
| Zhang/Zavala, arXiv:2105.11416 | B | Domain correction: electricity-market data-center load shifting; use revenue adequacy/cost recovery as checks. |
| am-AMM | B | Bounded experiment, not trusted-core default. |
| Pennanen double auctions | B | Simulation and welfare benchmark under explicit nonstrategic assumptions. |
| Walraswap | A | Strong abstract batch-clearing specification; needs deterministic certified integer realization. |
| CFMM axioms | A | Use to define curve profiles and prove implementation refinement. |
| AMM axioms/fee neutrality | A | Adopt transaction-splitting and price-impact obligations. |

## 6. Best concrete ideas for ZenoDEX

### Idea 1 — Typed authority pipeline

No function that moves value accepts raw dictionaries. Each phase accepts only the previous phase's successful typed output.

### Idea 2 — Effect capabilities

Each command derives an exact or conservative capability record:

```text
Footprint := {
  read_keys,
  write_keys,
  context_fields,
  effect_kinds,
  algorithm_version
}
```

The scheduler must fail closed when a footprint is unknown or data-dependent beyond a proved bound.

### Idea 3 — Deterministic conflict-graph compiler

Build the conflict graph from canonical command identities and verified footprints. Sort vertices and edges canonically. Partition with a deterministic algorithm. Every worker receives the same state/context commitment. Join with a fixed tree and canonical error order.

### Idea 4 — Patch normal form

Workers do not return arbitrary objects. They return a bounded typed patch normal form containing explicit old-value expectations, new values, effect atoms, and proof-relevant metadata. The core validates the complete patch before any application.

### Idea 5 — Atomic candidate commit

State, effects, receipt, nonce, roots, and outbox are one candidate. Compare-and-swap on the expected root publishes all or none.

### Idea 6 — Merkle trace and first-divergence protocol

Every accepted or rejected step receives a trace leaf. Cross-language disagreement can be localized logarithmically and replayed with exact inputs.

### Idea 7 — Axiomatic curve registry

Curve registration requires an axiom profile, integer refinement proof, boundary semantics, and exhaustive spreadsheet/differential vectors.

### Idea 8 — Fragmentation-invariant fee ledger

Prove that semantically equivalent split/merged commands have the same aggregate liabilities and owners. Explicitly carry bounded rounding residue.

### Idea 9 — Certified uniform-price solver

Keep continuous optimization outside the trusted core. Verify a compact rational/integer certificate and select a unique candidate canonically.

### Idea 10 — Self-stabilizing recovery modes

When consensus or Oracle state is not known valid, enter a typed recovery state in which value movement is impossible. Recovery transitions require a separately verified convergence certificate.

## 7. Formal work in PR #471

The PR introduces:

- `lean-mathlib/Proofs/TypedDeterministicParser.lean`
- `lean-mathlib/Proofs/DeterministicParallelExecution.lean`
- `tools/query_theoremsearch_zenodex.py`
- `docs/research/ZENODEX_THEOREM_LEDGER_V1.json`
- `tools/check_zenodex_theorem_ledger.py`
- `tests/tools/test_check_zenodex_theorem_ledger.py`
- `.github/workflows/theorem-ledger-formalization.yml`

The parser file proves:

- uniqueness of successful parse results;
- uniqueness of full-consumption parses;
- relational semantics of typed `bind`;
- disjoint-FIRST-set exclusion of ambiguous choice;
- uniqueness of canonical acceptance;
- encoder injectivity from exact decoder round trip.

The parallel file proves:

- disjoint patches commute extensionally;
- pairwise commuting task transformers are invariant under task-list permutation;
- an independent patch family has schedule-equivalent execution;
- expected-root mismatch returns no candidate;
- expected-root equality returns exactly the supplied atomic candidate.

The theorem ledger checker rejects:

- missing theorem obligations;
- duplicate theorem IDs or ranks;
- rank gaps;
- S-tier results placed after lower tiers;
- missing assurance-chain links;
- sources without a stable paper or formal locator;
- missing branch-local formal artifacts;
- missing correction/nonclaim records;
- attempts to pass the review gate while the ledger remains a research candidate.

## 8. TheoremSearch method and limitations

`tools/query_theoremsearch_zenodex.py` records exact semantic queries for parser uniqueness, disjoint choices, commuting state updates, schedule permutation, linearizable commit, AMM characterization, batch equilibrium, rounding conservation, and Merkle bisection. It queries both theorem-level search and the formal/informal TheoremGraph embedding endpoint.

TheoremSearch is a discovery instrument, not a checker. Its extracted slogans, heuristic dependency edges, and formal/informal nearest-neighbor matches must be reviewed against primary papers and compiled proof statements. No semantic search result is promoted directly into the trusted proof base.

Service documentation:

- https://www.theoremsearch.com/docs
- https://www.theoremsearch.com/theorem-graph

## 9. Tooling note

This environment exposed Lean, GitHub, GitHub Actions, and TheoremSearch's public REST/graph interfaces. It did not expose Morph or the Research Kernel MCP, so this pass does not claim those tools were used. The formal artifacts are ordinary Lean files compiled against the repository's pinned Lean/Mathlib toolchain, and the theorem-retrieval query bundle is reproducible in CI.

## 10. Promotion conditions

This research can be promoted into the normative core only after:

1. both new Lean files compile with no `sorry`, `admit`, or new axioms;
2. the ledger validator and adversarial tests pass;
3. TheoremSearch results are archived with the exact query and reviewed against primary sources;
4. parser theorems are connected to the concrete Rust/Python/Tau ingress implementations;
5. read/write/context footprint soundness is proved or independently checked;
6. the parallel runtime passes exact sequential differential replay for state, errors, effects, receipts, roots, fees, and nonces;
7. the shell's state/effect/receipt/outbox transaction has crash and linearizability evidence;
8. every market theorem is restated with ZenoDEX's finite integer domain and explicit assumptions;
9. every open proof obligation remains release-blocking rather than being converted into a narrative claim.

The resulting operating thesis is falsifiable:

> ZenoDEX may execute a batch in parallel only when a machine-checked footprint certificate and a canonical plan establish that every permitted physical schedule produces the exact normative state, effect, receipt, and rejection bytes, and one expected-root transaction publishes those bytes atomically.
