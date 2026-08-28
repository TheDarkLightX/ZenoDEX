# ZRPF scaling and assurance frontier

**As of:** 2026-07-14  
**Repository:** [`TheDarkLightX/ZenoDEX`](https://github.com/TheDarkLightX/ZenoDEX)  
**Default branch:** `main` at [`44d7f0d2a36b2141b553af1df734926c9d559bca`](https://github.com/TheDarkLightX/ZenoDEX/commit/44d7f0d2a36b2141b553af1df734926c9d559bca)  
**Active integration:** draft [PR #436](https://github.com/TheDarkLightX/ZenoDEX/pull/436), head `8c223ff0c684d9811ca633b042d0c3edc5220488`, mergeable, authority-false  
**Research basis:** Research Kernel run `run_zrpf_frontier_20260714`, repository inspection, primary literature, and official RISC Zero 3.0 documentation

## Executive answer

ZRPF can scale materially beyond its current evidence, but increasing the recursion tree is not yet the limiting change. The current protocol profile allows fanout 8 and depth 2 (64 leaves), while retained structural evidence covers only four leaves. More importantly, the current source-opened V6/V7 Spot chain admits exactly one ordinary Spot action and its L1 and L2 harnesses each consume one child. A deeper tree would therefore add proof capacity without creating an admissible multi-action settlement.

The highest-leverage sequence is:

1. make assumptions and end-to-end soundness executable and source-digested;
2. specify a bounded, canonical multi-action settlement statement before increasing fanout;
3. exercise real fanout with level-specific image identities, topology-independent semantic commitments, and fresh receipts;
4. schedule the resulting proof DAG deterministically with content-addressed tasks, exact worker capability evidence, and authenticated benchmarks;
5. formalize the semantic merge and release-activation state machines; and
6. only then evaluate a folding/IVC backend as a separately reviewed migration.

The immediate integration branch is not green at its exact head. `zrpf-assurance` run 102 failed on three mypy findings: two argument-unpacking errors in `tests/test_zrpf_spot_v7_firecracker_descriptor_staging.py:209` and one redundant cast in `src/integration/_zrpf_spot_v7_atomic_settlement_engine_v5.py:305`. All other observed workflows on that head completed successfully. No child PR should claim integration readiness until the exact-head gate is green.

## What ZRPF proves today

| Surface | Current evidenced boundary | Consequence |
|---|---|---|
| Common structural profile | Maximum fanout 8, maximum depth 2: 64 leaves and 73 total nodes | This is a policy/evidence ceiling, not a recursion-primitive ceiling. |
| Retained structural evidence | Four Spot V1 receipts through fanout 2 at L1 and fanout 2 at L2 | The maximum profile is not demonstrated. |
| Source-opened V6 harness | L1 consumes one leaf; L2 consumes one L1 receipt | It is proof plumbing, not throughput aggregation. |
| V6 settlement semantics | Exactly one ordinary Spot action, one authorization/grant spend, one state-cell transition, two conserved asset rows; zero mint, burn, reward, carry, or messages | A 64-leaf tree cannot be admitted as a 64-action settlement without a new typed statement. |
| V7 semantics | Exactly one TauSwap V1 `SwapExactIn`, one signed intent, no faucet | Pool creation, liquidity changes, exact-out, multi-intent, and batch settlement are outside the statement. |
| Fresh proof evidence | Final-source V6/V7 identities and receipts are not yet pinned | Old receipts cannot authorize the current source. |
| Settlement/release authority | Every new authority field in PR #436 remains false | The branch adds prerequisites and persistence, not production authority. |
| DA | Exact private full-blob replay plus bounded sampled/longitudinal prerequisites | This is neither continuous nor future public availability. |
| Runtime | Descriptor-bound staging and a root-supervisor contract | No live privileged Jailer/Firecracker execution or governed Linux port is evidenced. |

Relevant implementation surfaces include:

- `zk/zrpf_risc0/README.md`
- `zk/zrpf_risc0/methods/spot_value_leaf_v6/src/main.rs`
- `zk/zrpf_risc0/methods/spot_value_aggregate_l1_v6/src/main.rs`
- `zk/zrpf_risc0/methods/spot_value_aggregate_l2_v6/src/main.rs`
- `zk/zrpf_risc0/methods/source_opened_spot_settlement_v6/src/main.rs`
- `zk/spot_settlement_v7_risc0/methods/guest/src/main.rs`
- `zk/zrpf_protocol/protocol/src/value_node_v4/subtree/merge.rs`
- `src/integration/zrpf_spot_v7_atomic_operational_store_v5.py`
- `src/integration/zrpf_spot_v7_zeno_ledger_finality_adapter.py`

## Scaling analysis

### The recursion primitive is not the 64-leaf bottleneck

RISC Zero documents repeated `join` and `resolve` operations and describes recursive proving as supporting unbounded computation size, constant proof size, aggregation, and composition. Repeated pairwise joins permit logarithmic critical-path depth when independent subtrees are proved in parallel. They do not remove total proving work, coordination, data availability, or application-semantic obligations. See the [RISC Zero recursion reference](https://dev.risczero.com/api/recursion).

For fanout \(k\), leaf count \(n\), and balanced depth \(d=\lceil\log_k n\rceil\), the optimistic critical path is approximately

\[
T_{critical} \approx T_{leaf} + d\,T_{aggregate} + T_{coordination}.
\]

Total work remains at least linear in the number of leaves. At fanout 8 and depth 7, a full tree contains 2,097,152 leaves and 2,396,745 total nodes. RISC Zero describes Succinct receipts as roughly 200 kB, so naively retaining one such artifact for every node would be on the order of 479 GB before indexes, journals, recovery material, and replication. This makes streaming retention and DA policy first-order design constraints, not later optimizations.

### The effective bottleneck is statement capacity

The present V6/V7 settlement statement has capacity one. Increasing aggregate depth before defining multi-action semantics creates a larger proof of a statement that the settlement consumer still cannot admit. The next scaling statement should be bounded and explicit, for example:

- 2 actions first, then 8 only after fresh evidence;
- ordered, contiguous pre/post-state chaining;
- global nullifier and authorization-use uniqueness;
- exact conservation across all asset rows;
- deterministic conflict ordering for shared cells;
- explicit carry and cross-shard messages, or a mandatory empty encoding;
- canonical semantic root independent of proof-tree topology;
- topology-bound proof root kept separate from the semantic root;
- exact resource, input, journal, proof, and cycle ceilings.

The existing `merge_semantic_subtrees_v2` is a strong starting point: it checks ordered partitions, state continuity, shared metadata, global identity uniqueness, bounded rows/flows/uses, and checked sums. Its pure-Rust tests cover associativity and topology-independent semantic roots. Those tests are not a proof of the production codec or guest path, and the repository's existing Lean model abstracts roots as natural numbers and assumes cryptographic soundness. A matching formalization remains open.

### A practical scale path

1. Specify and test a two-action, proof-neutral settlement object.
2. Recompose its exact journal from child-authenticated inputs.
3. Exercise two distinct leaves through an actual two-child L1 and two-child L2 path.
4. Add state-gap, duplicate-nullifier, child-reorder, level-confusion, and image-substitution negatives.
5. Prove fresh receipts only after source freeze.
6. Measure cycles, segments, wall time, RSS, artifact sizes, queue delay, and recovery cost.
7. Increase to fanout 8 only if the semantic and resource gates remain unchanged.

Until step 3 exists, the one-child L1/L2 chain should be described as structural proof plumbing. Removing one-child layers from benchmark claims, or explicitly accounting for their overhead, would prevent misleading throughput conclusions.

## Assurance analysis

### Executable soundness and assumption ledger

The strongest immediate assurance multiplier is a machine-checked ledger that binds every security claim to exact source, version, proof mode, parameters, and verification-event count. RISC Zero's own [security model](https://dev.risczero.com/api/security-model) separates random-oracle, Toy Problem, pairing, knowledge, and ceremony assumptions. A single undifferentiated `security_level_bits` value loses that distinction.

For verification events with failure bounds \(p_i\), a conservative composition is

\[
p_{total} \leq \sum_i p_i.
\]

No independence assumption is needed for this union bound. For \(N\) equal \(b\)-bit events, the resulting bound is at most \(2^{\log_2 N-b}\), or at least \(b-\log_2 N\) effective bits. The ledger must count event classes rather than take the minimum component bit claim.

This ledger must fail closed on unknown mode, missing event class, stale source digest, version mismatch, non-integer/rounded security arithmetic, or an assumption marked unproven, disproven, or version-drifted. The companion decision graph and validator in this directory implement that promotion rule for research candidates.

The version binding matters. Crites and Stewart's 2025 paper [On Reed-Solomon Proximity Gaps Conjectures](https://eprint.iacr.org/2025/2046) disproves several specific up-to-capacity formulations used around FRI-family analyses and proposes modified formulations. This does not show that every FRI configuration is broken. It does show that naming only a family such as "FRI assumptions" is not an auditable dependency.

### Proof-shape enforcement must reach the guest and worker

PR #436 adds `proof_shape_v1` and assumption-registry protocol types, but the inspected V6/V7 guests still call `env::verify` directly with compile-time image IDs. None of the five production guest entry points references `ProofShape`, `AssumptionManifest`, or `resolve_assumptions`. The registry is therefore not yet an enforced production invariant.

A focused PR should bind the registry to:

- every guest `env::verify` call;
- host-side proof planning;
- remote-worker task keys;
- benchmark identity;
- release inventory and exact-head evidence; and
- explicit maximum child, input, journal, proof, cycle, and memory bounds.

### Metamorphic and fault-injection evidence

[Arguzz](https://arxiv.org/abs/2509.10819) combines semantics-preserving metamorphic testing with zkVM fault injection and reports eleven soundness/completeness bugs across three of six tested zkVMs. For ZRPF, the highest-value corpus is not random byte fuzzing alone. It should generate pairs whose semantic equality or inequality is known and then mutate:

- child order and partition boundaries;
- image IDs, levels, profiles, and assumption roots;
- journal field positions, endianness, reserved bits, and canonical encodings;
- state continuity, nullifiers, authorization uses, and conservation rows;
- receipt profile and seal bytes; and
- DA, finality, release, and worker-provenance bindings.

Passing this corpus is sampling evidence, never a cryptographic or formal proof. Mutation-kill rate, seed, corpus digest, backend digest, and exact binary identity should be retained.

### Formal methods targets

The best near-term Lean target is not the cryptographic backend. It is the exact semantic merge contract:

1. associativity under the implemented bounds;
2. preservation of pre/post-state continuity;
3. global uniqueness of nullifiers and authorization uses;
4. conservation and checked-sum invariants;
5. topology independence of the semantic root; and
6. separation from the topology-bound proof root.

The best state-machine/model-checking target is the dormant V5 operational store plus checkpoint cursor: atomic commit, idempotent replay, rollback/revocation interleavings, crash recovery, release-head changes, and the five authority activation blockers. Solver `UNKNOWN` or bounded success must remain a non-promotion result.

## Literature frontier and translation to ZRPF

| Work | Frontier result | ZRPF implication | Adoption posture |
|---|---|---|---|
| [RISC Zero recursive proving](https://dev.risczero.com/api/recursion) | Repeated `join`/`resolve`, constant-size Succinct outputs, recursive compression | The profile can exceed depth 2, but total work and semantics remain | Extend the pinned 3.0.5 path first; do not infer throughput from proof size. |
| [STIR](https://eprint.iacr.org/2024/390), [WHIR](https://eprint.iacr.org/2024/1586) | Newer Reed-Solomon proximity tests target fewer queries, smaller arguments, or faster verification | Plausible proof-size/verifier improvements | Authority-free backend lab only; later proximity-gap results affect some aggressive assumption regimes. |
| [BaseFold](https://eprint.iacr.org/2023/1705), [DeepFold](https://eprint.iacr.org/2024/1595), [Jagged PCS](https://eprint.iacr.org/2025/917) | Foldable/multilinear commitments and heterogeneous-trace designs target better prover/verifier tradeoffs | Jagged traces may fit a zkVM with heterogeneous tables | Measure against the exact ZRPF ABI; none is a drop-in RISC Zero receipt backend. |
| [Binius](https://eprint.iacr.org/2023/1784), [Lasso/Jolt](https://eprint.iacr.org/2023/1216), [Twist and Shout](https://eprint.iacr.org/2025/105), [Circle STARKs](https://eprint.iacr.org/2024/278) | Binary fields, lookup/memory arguments, and M31 designs can change workload cost substantially | Worth testing only after profiling the actual ZRPF trace/opcode mix | Treat published benchmark gains as hypotheses, not transferable ZRPF measurements. |
| [FRIttata](https://eprint.iacr.org/2025/1285), [Shred-to-Shine](https://eprint.iacr.org/2025/1354) | Distributed PCS/proof generation can reduce wall time under explicit fault models | Informs longer-horizon distributed proving | Distribute the existing deterministic proof DAG first; it has much lower integration and assurance risk. |
| [Nova](https://eprint.iacr.org/2021/370), [HyperNova](https://eprint.iacr.org/2023/573), [ProtoStar](https://eprint.iacr.org/2023/620) | Folding/accumulation enables efficient incremental computation | Attractive for append-only, stateful accumulation | Research migration only; common instantiations change commitment and post-quantum assumptions. |
| [Security of Nova-style Folding at Polynomial Depth](https://eprint.iacr.org/2024/232), [Neo/SuperNeo](https://eprint.iacr.org/2026/242) | Recursion security definitions require care at large depth; post-quantum folding is emerging | Prevents an unsafe extrapolation from bounded experiments; supplies a future PQ research path | Frontier-stage evidence only; exact security definition and policy compatibility must be dependencies. |
| [Crites-Stewart 2025/2046](https://eprint.iacr.org/2025/2046) | Refutes several precise Reed-Solomon proximity-gap conjectures | Assumptions need exact names, versions, and source digests | Block promotion on stale or generic conjecture labels. |
| [Arguzz](https://arxiv.org/abs/2509.10819) | Metamorphic testing plus fault injection finds zkVM bugs missed by audits | A ZRPF-specific mutation corpus can cheaply multiply negative evidence | Add as an assurance lane, never as proof of soundness. |
| [RISC Zero Lean proof-of-concept](https://www.nethermind.io/blog/towards-formal-verification-of-the-first-risc-v-zkvm) | Demonstrates that parts of zkVM circuit semantics can be represented in Lean | Supports a digest-pinned formal verifier bridge as a plausible research target | Keep the external implementation as an explicit trusted boundary until refinement is proved. |

Folding is the most interesting long-horizon scaling hypothesis, but it is not the first implementation change. ZRPF already has a pinned RISC Zero verification and receipt ecosystem. A folding backend would need a versioned adapter, exact semantic-equivalence oracle, new assumption ledger entries, new release and verifier authority, cross-backend differential tests, and a full CBC reset. The near-term force multiplier is extracting more scale from the current backend without changing the trusted base.

The literature therefore supports four authority-free labs, not four migrations: a differential backend adapter lab, a distributed-PCS fault-injection lab, a folding/security-definition lab, and a digest-pinned formal verifier bridge. Their output is benchmark, incompatibility, and proof-obligation evidence. None may construct an accepted ZRPF verifier capability.

## Ranked force multipliers

| Rank | Change | Leverage | Principal blocker | Safe first PR |
|---:|---|---|---|---|
| 1 | Source-digested soundness and assumption ledger | Converts prose security claims into executable admission facts; catches literature/version drift | Exact backend event classes and parameters are not yet committed | Authority-false validator, fixtures, union-bound arithmetic, and CBC report only |
| 2 | Bounded multi-action settlement statement | Unlocks real end-to-end throughput instead of larger unused trees | Current V6/V7 semantics accept one action | Two-action proof-neutral types, codec, merge oracle, and negative tests |
| 3 | Level-specific image ladder plus real fanout | Raises evidenced capacity while preventing level/image confusion | Fresh final-source image IDs and receipts are absent | Fanout 2/depth 3 manifest generator and substitution/reordering negatives |
| 4 | Deterministic content-addressed proof DAG | Parallelism, retry, caching, remote execution, and reproducibility share one mechanism | Current remote worker implements eight of twelve planned stages and lacks authenticated freshness | Rebase/fix planner; graph completeness check against source inventory |
| 5 | ZRPF metamorphic/fault corpus | High negative-evidence return across guest, host, codec, and authority boundaries | A trusted semantic-equivalence oracle is not yet defined | Deterministic corpus for merge/journal/image/level mutations |
| 6 | Exact capability and benchmark attestation | Makes hardware/backend optimization measurable and comparable | Self-reported worker records can lie; current settlement proving exceeded 12 hours on a four-logical-CPU host | Raw-sample capture with source/binary/workload/machine identity and timeout retention |
| 7 | Lean semantic merge plus atomic-store model | Shrinks ambiguity at the most authority-sensitive deterministic core | Existing Lean model is too abstract | Model current bounded merge exactly; do not model cryptographic soundness as proved |
| 8 | Streaming retention and sampled DA policy | Prevents receipt storage from dominating large trees | Public/continuous availability and provider/beacon governance are absent | Proof-neutral retention manifest and recovery/DA outage tests |
| 9 | Differential backend adapter lab | Tests STIR/WHIR/BaseFold/DeepFold/Jagged/Binius/Circle hypotheses against one ABI | No statement-equivalence oracle or compatible assumption profile | Offline adapter interface, deterministic fixtures, incompatibility report |
| 10 | Distributed PCS lab | Quantifies whether protocol-level distribution beats DAG-level distribution | New fault model, authentication, and recovery semantics | Fault-injected benchmark only; compare with the current deterministic DAG |
| 11 | Folding and formal-verifier labs | Explores incremental accumulation and reduces implementation/theorem ambiguity | Commitment/PQ policy, depth-security definition, and refinement proof are open | Authority-free prototypes with explicit trusted boundaries |

## PR decomposition and acceptance gates

### PR 0: exact-head integration repair

- Fix only the three mypy findings on PR #436.
- Re-run all required workflows at the new exact head.
- Reconcile stacked PRs #427-#432 as subsumed rather than merging stale heads.
- Rebase #433-#435 only after #436 is green.

### PR 1: assumption-aware frontier graph

- Add the decision graph and standard-library validator supplied with this report.
- Require every selected hypothesis to list typed assumption dependencies.
- Block admission when any dependency is `UNPROVEN`, `DISPROVEN`, or `VERSION_DRIFTED`.
- Distinguish structural validation from promotion admission so a correctly blocked graph remains inspectable.

### PR 2: bounded multi-action statement

- No proof or ledger authority.
- Two actions, canonical ordering, state continuity, uniqueness, conservation, bounds, exact codec.
- Differential oracle against sequential application.
- Reject duplicate/nullifier/state-gap/reorder/overflow/resource-exhaustion cases.

### PR 3: proof-shape and level ladder

- Bind level, child image, assumption root, and proof-shape root into a signed/content-addressed manifest.
- Exercise fanout 2 and depth 3 before fanout 8.
- Require fresh current-source replay and per-layer seal mutations.
- Do not claim unbounded accumulation.

### PR 4: deterministic proof-DAG execution

- Complete identity-build and prover-build adapters before release stages.
- Include source, toolchain, binary, statement, child receipts, policy, resource profile, and backend capability in every cache key.
- Test worker-count invariance, crash/restart, collision corpus, stale task replay, and backpressure.
- Authenticate operator/freshness evidence before any authority use.

### PR 5: assurance corpus and formal targets

- Add deterministic metamorphic fixtures and mutation-kill reporting.
- Formalize `merge_semantic_subtrees_v2` against the actual bounded data model.
- Model V5 store/finality/release activation interleavings.
- Keep fuzzing, theorem, model-checking, and cryptographic evidence as separate claim classes.

### PR 6: benchmark and capability evidence

- Capture raw samples, failures, and timeouts.
- Commit exact source, binary, toolchain, proof shape, backend, accelerator path, workload, machine, and resource identities.
- Compare cold and warm runs and report queue/coordination time separately.
- Never grant production authority from a benchmark.

## Active release blockers

The dormant V5 operational store correctly keeps authority false until all five conditions are independently satisfied:

1. governed release-head selection;
2. release revocation-policy enforcement;
3. monotonic rollback protection;
4. fresh governed release evidence; and
5. fresh governed runtime evidence.

Additional nonclaims remain: no fresh final-source V6/V7 receipts, no unified per-stage mutation evidence, no concrete privileged Linux supervisor, no same-UID hostile-process resistance, no cross-host reproducible final release, no continuous/future public DA, and no privacy proof.

## Knowledge artifacts

- `ZRPF_FRONTIER_DECISION_GRAPH_20260714.json` is a decision layer derived from Research Kernel output `ZRPF_FRONTIER_KNOWLEDGE_GRAPH_20260714.json` (SHA-256 `e4afe4ff8fb7d3287a17e7fb90030900d0e796bbf8917b3a7ba807edf29bc6e8`). The source graph contains 67 atoms, including 20 primary-literature evidence atoms and 12 hypotheses.
- `validate_zrpf_frontier_graph.py` validates structure, typed dependencies, version consistency, and fail-closed promotion decisions using only the Python standard library.
- `test_validate_zrpf_frontier_graph.py` covers missing fields, unknown dependencies, unproven/disproven/version-drifted blockers, incorrect eligibility, duplicate IDs, and admission-mode exit behavior.

Run:

```bash
python -m unittest discover -s tests -p 'test_validate_zrpf_frontier_graph.py'
python tools/validate_zrpf_frontier_graph.py \
  docs/research/ZRPF_FRONTIER_DECISION_GRAPH_20260714.json
```

The second command validates a correctly fail-closed graph. Promotion CI should add `--admission`; the current graph is expected to return exit code 2 because selected hypotheses still depend on unproven, disproven, or version-drifted facts.
