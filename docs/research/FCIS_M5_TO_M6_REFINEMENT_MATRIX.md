# FCIS M5-to-M6 theorem/runtime refinement matrix

**Date:** 2026-07-29
**Status:** `RESEARCH_ONLY_NO_RUNTIME_IMPLEMENTATION_NO_MOUNT`
Matrix fingerprint: `sha256:f5a855b2ab8dd66f88e016599a302a9774d82c6f5e18bea90a50de8c6135cbd8`
Gate count: `71`

## Executive verdict

**M6 is not promotable.** The current evidence contains five narrow machine-proved claims, thirteen narrowly tested implementation/reference/library claims, and fifty-three unresolved end-to-end gates. No gate qualifies as `MOUNTED`, and no production authority switch is authorized by this packet.

The central problem is not merely whether `step` preserves an invariant. It is whether the production runtime supplies the theorem premises from independent authenticated sources, evaluates the exact current state, refines the same pure decision in every implementation, and publishes the complete result at one durable linearization point with recovery, migration, and no bypass.

```text
RuntimeAccept(bytes, store)
  -> canonical bounded bytes
  -> authenticated and authorized command
  -> exact reauthorized store-current state
  -> independently authenticated context
  -> normative pure decision + complete project laws
  -> strict runtime/guest refinement
  -> nominal candidate-bound authorization
  -> one durable atomic publication
  -> strict reopen/recovery + durable outbox
  -> no alternate authority path
```

The matrix treats proof, implementation, testing, mounting, and residual gaps as distinct facts. A proof island cannot inherit runtime authority merely because its assumptions look plausible; a canonical carrier cannot inherit authentication merely because it has a root; and a database transaction cannot inherit protocol atomicity unless it covers the complete candidate and is the sole writer.

## Status summary

| Status | Count | Meaning in this packet |
|---|---:|---|
| PROVED | 5 | The exact narrow claim is discharged by a machine-checked theorem/proof artifact at a pinned source. Runtime assumptions remain separate gates unless the claim explicitly includes them. |
| IMPLEMENTED | 0 | The exact narrow behavior exists in code at a pinned source, but this row does not claim sufficient execution evidence or authoritative runtime use. |
| TESTED | 13 | The exact narrow implementation/reference/library behavior has executable evidence at a pinned source. Tests are not promoted beyond their declared scope. |
| MOUNTED | 0 | The exact nominal path is the authoritative production path, with current-state/commit relation and no-bypass evidence. No row currently qualifies. |
| GAP | 53 | One or more necessary parts of the exact safety claim are missing, refuted, unmounted, or lack executable evidence. |

## Decisive findings

1. **P4B5A remains the first semantic blocker.** The scalar-cursor dynamic-policy claim is refuted by the D=4 adaptive sequence. The surviving mechanical-word allocator is promising only for fixed weights until a policy-lifecycle model is frozen and proved.
2. **B1B-1 is correctly narrow.** It provides bounded canonical untrusted carriers and strong isolation tests, but deliberately provides no pinned verifier, state, transition, receipt, publication, migration authority, or mount.
3. **Nonce arithmetic is not the nonce protocol.** Kani closes the strict-successor classifier, but principal authentication, domain/version parity, current-state lookup, same-candidate binding, atomic persistence, races, bootstrap, and migration remain separate obligations.
4. **ZenoFCIS supplies the strongest reusable M6 substrate.** Its open stacked head contains nominal authority, strict artifact reconstruction, authorized genesis, gap-free SQLite history, candidate-bound authenticated state, validated refinement, project laws, and durable outbox semantics. It is not yet a ZenoDEX mount and explicitly leaves deployment, migration, multi-process, filesystem, and destination qualification open.
5. **The final blocker is composition.** The exact runtime implication fails whenever any relation is sourced independently from a different value, policy, implementation, or commit event. M6 must preserve one lineage from request bytes through durable history.

## Recommended closure architecture

The smallest safe architecture is an assume-guarantee chain in which each boundary consumes a nominal value that only the previous validated boundary can construct:

```text
RawRequestBytes
  -> CanonicalCommand
  -> AuthenticatedInvocation
  + ZenoDexCurrentState
  + AuthenticatedExecutionContext
  -> NormativeDecision
  -> ValidatedRuntimeDecision
  -> CatalogAuthorizedTransition
  -> CatalogAuthorizedAuthenticatedCommit
  -> ProductionCommitPort
  -> ReauthorizedHistoryHead
  -> PendingOutboxEntry -> exact idempotent delivery
```

The shell must not reconstruct omitted semantic facts, choose authority sources, interpret commit evidence, derive new destinations, repair a rejection, or write any authoritative subset separately.

### Highest-leverage closure sequence

1. Freeze P4B5A policy lifecycle and accepted-language semantics; prove the surviving fixed-policy allocator and replacement fee lineage.
2. Define exact ZenoDEX state, command, context, proof, nonce/nullifier, and zUSD law adapters; close the M4/M5 normalized-decision refinement.
3. Instantiate ZenoFCIS catalog authority, project laws, authenticated-state relation, and strict history on exact ZenoDEX types.
4. Map the complete ZenoDEX atomic row set into one transactional commit port and durable outbox; run crash, concurrency, retry, and reopen evidence.
5. Implement and independently review explicit migrations, old-writer fencing, rollback, retention, and deployment topology qualification.
6. Remove legacy/direct/fallback authority paths; run semantic no-bypass mutations over source, build, package, runtime, and operational tools.
7. Rebuild all formal/evidence artifacts at the exact aggregate head, run this checker, obtain independent exact-head review, and issue an explicit promotion receipt only when no GAP remains.

### Tool-specific next work

| Tool | Highest-value exact task | What it may establish | What it must not be credited with |
|---|---|---|---|
| Lean | Prove fixed-policy apportionment conservation, complete-period exactness, split/merge telescoping, corrected `<1,<2,<2` discrepancy bounds, runtime-to-zUSD projections, and the final assume-guarantee composition theorem. | Unbounded algebraic/inductive claims under explicit premises. | Runtime authentication, current-state provenance, datastore atomicity, or no-bypass unless those relations are modeled and refined concretely. |
| Julia | Build an independent exact-integer arithmetic oracle; exhaust small denominators/policy traces; generate U256 boundary and cross-language golden vectors; search counterexamples before formalization. | High-powered falsification and vector generation. | Proof, exhaustive coverage of unbounded domains, or protocol authority. |
| ESSO / SMT | Model configuration activation, nullifier consume-once, candidate publication, crash/retry, migration, and outbox phase machines; retain minimized counterexamples and deterministic fingerprints. | Bounded state-machine invariants and concrete reachable witnesses. | Production datastore/filesystem refinement or unbounded theorem. |
| Research Kernel | Maintain the exact evidence/assumption graph, refute overbroad claims, and block promotion when producer/source/coverage identities are missing. | Evidence discipline and promotion decisions at exact source identities. | Mathematical truth by itself. |
| TheoremSearch | Retrieve adjacent formal/informal results for parsing, apportionment/discrepancy, refinement, linearizability, crash recovery, and authenticated data structures. | Research discovery. | Direct proof relevance or trusted proof-base admission without primary-source and compiled-artifact review. |

## Research and tool-use record

This pass used the GitHub connector against exact commits/PRs, primary-source web research, and Python for generation and validation. It reviewed repository-pinned Lean, Kani, Research Kernel, Morph, ESSO, TheoremSearch, and ZenoFCIS evidence at their original scopes. Live Research Kernel MCP, Lean/lake, and Julia executables were not exposed in this environment; direct TheoremSearch POST execution was also unavailable. Therefore no new theorem/tool-run claim is made, and missing aggregate reruns remain explicit evidence gaps.

## Pinned evidence sources

| Source ID | Kind | Exact locator | Role |
|---|---|---|---|
| `ZDX-B1B1-HEAD` | git | `TheDarkLightX/ZenoDEX@6c22f52c5e65f14b4501a62a049d231fd48aa2d3` | Latest reviewed B1B-1 carrier/codec evidence used as the matrix branch base |
| `ZDX-M5-REFERENCE` | git | `TheDarkLightX/ZenoDEX@a2b570a8e5da043380ec1b3e43aab9932a42692f` | M5 closed decision and reference atomic-publication checkpoint |
| `ZDX-P4B3` | git | `TheDarkLightX/ZenoDEX@6c22f52c5e65f14b4501a62a049d231fd48aa2d3` | Exact unmounted route-binding/replay evidence and final-mount violation inventory |
| `ZDX-P4B5A-RESEARCH` | git | `TheDarkLightX/ZenoDEX@6771bff2d55ba08421b586e2db75441deb87f582` | Apportionment architecture, minimized adaptive-policy counterexamples, and ESSO evidence |
| `ZDX-NONCE-KANI` | git | `TheDarkLightX/ZenoDEX@dab7e983eac92bb9edab13c59246d96b92214540` | Kani proof of the heap-free strict-successor nonce classifier plus parity tests |
| `ZDX-NONCE-DRIFT` | git | `TheDarkLightX/ZenoDEX@73f18fa801cc2878257ecd4281e4b877da14caab` | Minimized Python/Rust nonce-domain divergence evidence |
| `ZDX-LEAN-LEDGER` | git | `TheDarkLightX/ZenoDEX@3c5ee8b7487048a2dd0a370a64eeb1c294cd9c04` | Lean parser uniqueness, patch commutation, and pure CAS theorem ledger |
| `ZDX-RK-SYNTHESIS` | git | `TheDarkLightX/ZenoDEX@8e732fb15635fde35448ddef162b7dfd9a6b6560` | Pinned Research Kernel/Morph/ESSO synthesis and read/write-stable commutation theorem |
| `ZDX-ZUSD-COVER` | git | `TheDarkLightX/ZenoDEX@206c287ccaea4a427c9c37679b99c5249a174d01` | Lean exact global debt-cover and transfer-preservation lemmas |
| `ZDX-ZUSD-FRESHNESS` | git | `TheDarkLightX/ZenoDEX@56a51be326487037919e1fd09e02724c013a5f31` | Lean pending/finalized observation freshness lemmas |
| `ZDX-ZUSD-CAP` | git | `TheDarkLightX/ZenoDEX@6ba8e2606a2a4f6a1734c9019dcf4a2715516a45` | Python and deterministic RISC0-projection total-debt-cap repair and counterexample |
| `ZFCIS-RC-HEAD` | git | `TheDarkLightX/ZenoFCIS@9d0814ec769c0a36261477299df5dd5ecbcbf9f7` | Open stacked ZenoFCIS V1 candidate containing authority, refinement, authenticated-state, SQLite history, and durable-outbox substrates |
| `LIT-REFINEMENT` | literature | Abadi and Lamport, The Existence of Refinement Mappings, Theoretical Computer Science 82(2), 1991 | Refinement-map decomposition and auxiliary-state warning |
| `LIT-LINEARIZABILITY` | literature | Herlihy and Wing, Linearizability: A Correctness Condition for Concurrent Objects, ACM TOPLAS 12(3), 1990, DOI 10.1145/78969.78972 | Single observable operation point for concurrent publication |
| `LIT-DURABLE-LINEARIZABILITY` | literature | Izraelevitz, Mendes, and Scott, Linearizability of Persistent Memory Objects Under a Full-System-Crash Failure Model, DISC 2016, DOI 10.4230/LIPIcs.DISC.2016.19 | Separation of volatile linearizability from crash-durable correctness |
| `LIT-CRASH-HOARE` | literature | Chen et al., Using Crash Hoare Logic for Certifying the FSCQ File System, SOSP 2015 | Recovery relation and crash invariant methodology |
| `SQLITE-ATOMIC-COMMIT` | web | https://www.sqlite.org/atomiccommit.html | Documented SQLite atomic-commit protocol and filesystem assumptions |
| `SQLITE-WAL` | web | https://www.sqlite.org/wal.html | Documented WAL concurrency, checkpoint, and durability behavior |

## Matrix overview

| ID | Gate | Conservative status | Evidence already present | Smallest closing artifact |
|---|---|---|---|---|
| `F-01` | Abstract canonical-parser uniqueness | **PROVED** | PROVED evidence | `lean-mathlib/Proofs/ZenoRuntimeCanonicalIngress.lean` |
| `F-02` | Concrete bytes-to-authenticated-command ingress | **GAP** | IMPLEMENTED evidence, TESTED evidence | `src/integration/fcis_authority_ingress_v2.py` |
| `F-03` | Transitively owned immutable current state | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/state_v2.rs` |
| `F-04` | Pure total closed decision relation | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/program_v2.rs` |
| `F-05` | Complete read/write/context/effect/outbox footprints | **GAP** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_COMPLETE_FOOTPRINT_WITNESSES_V1.json` |
| `F-06` | Whole-result implementation refinement and sequential/parallel parity | **GAP** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_RUNTIME_REFINEMENT_V1.json` |
| `A-01` | Exact untrusted authority carriers and canonical codecs | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M5_P4B5A_B1B1_EXACT_HEAD_REVIEW_20260729.md` |
| `A-02` | Frozen configuration-language semantic validation | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/fee_configuration.rs` |
| `A-03` | Independent expected-root binding for active, proposed, and migration configuration | **GAP** | none | `docs/research/FCIS_M5_P4B5A_B1B2_IMPLEMENTATION_REPORT_20260729.md` |
| `A-04` | Configuration authority state machine and update transition | **GAP** | none | `src/core/fcis_configuration_authority_v2.py` |
| `A-05` | Fixed-policy apportionment conservation and per-period exactness | **GAP** | TESTED evidence | `lean-mathlib/Proofs/FixedPolicyFeeApportionment.lean` |
| `A-06` | Fixed-policy cumulative discrepancy bounds | **GAP** | TESTED evidence | `lean-mathlib/Proofs/FixedPolicyFeeApportionmentDiscrepancy.lean` |
| `A-07` | Adaptive policy activation and bounded fairness | **GAP** | none | `docs/research/FCIS_M5_P4B5A_POLICY_LIFECYCLE_V1.md` |
| `A-08` | Stable apportionment-state key and migration | **GAP** | none | `src/state/fcis_fee_apportionment_state_v2.py` |
| `A-09` | Provisional fee provenance and per-settlement conservation | **GAP** | none | `src/core/fcis_protocol_fee_lineage_v2.py` |
| `A-10` | Checked U256 apportionment arithmetic and cross-language exactness | **GAP** | TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/apportionment_math.rs` |
| `A-11` | Accepted-language versioning for same-batch fee spending | **GAP** | none | `docs/specs/fcis_fee_credit_language_v2.md` |
| `A-12` | Same-candidate apportionment publication | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/p4b5a.rs` |
| `B-01` | Strict-successor nonce classifier | **PROVED** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_NONCE_CLASSIFIER_PROOF_RECEIPT.json` |
| `B-02` | Authenticated principal-to-nonce-key binding | **GAP** | none | `crates/zeno-fcis-adapter-zenodex/src/replay_key.rs` |
| `B-03` | Nonce domain, range, policy version, and cross-language parity | **GAP** | PROVED evidence, TESTED evidence | `tests/fixtures/fcis_nonce_policy_v2_golden.json` |
| `B-04` | Pure per-principal replay-state transition | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/replay_state.rs` |
| `B-05` | Store-current nonce lookup and stale-candidate rejection | **GAP** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/nonce_commit.rs` |
| `B-06` | Same-candidate replay update and receipt binding | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/replay_artifacts.rs` |
| `B-07` | Atomic nonce, state, receipt, history, and outbox publication | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/sqlite_nonce.rs` |
| `B-08` | Concurrent ordering, retry, and rejection stability | **GAP** | none | `docs/research/FCIS_M6_NONCE_CONCURRENCY_V1.md` |
| `B-09` | Nonce bootstrap, migration, and historical-policy continuity | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/nonce_migration.rs` |
| `C-01` | Strict canonical receipt, bundle, authorization, and proof-artifact admission | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/artifacts.rs` |
| `C-02` | Independent evidence provenance and trusted producer binding | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_EVIDENCE_PROVENANCE_V1.json` |
| `C-03` | Persisted command and context reauthentication | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/history_auth.rs` |
| `C-04` | Persisted transition and project-law reexecution | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_REEXECUTION_POLICY_V1.json` |
| `C-05` | Exact persisted candidate row-set equality | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `docs/specs/fcis_m6_sqlite_schema_v1.sql` |
| `C-06` | M4/M5 evaluator-to-normalized-decision refinement | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/refinement.rs` |
| `C-07` | Coverage truth for refinement and evidence recomputation | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_COVERAGE_POLICY_V1.json` |
| `C-08` | Evidence recomputation at every authority-bearing use | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_REVALIDATION_MAP.json` |
| `D-01` | Policy-bound authorized genesis | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_ZENODEX_GENESIS_V1.json` |
| `D-02` | Gap-free reauthorized history reconstructs current state | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/history.rs` |
| `D-03` | Authenticated state projection and exact current root | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/authenticated_state.rs` |
| `D-04` | Project nullifier definition and consume-once state machine | **GAP** | none | `crates/zeno-fcis-adapter-zenodex/src/nullifier.rs` |
| `D-05` | Atomic complete candidate publication | **GAP** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/sqlite_commit.rs` |
| `D-06` | Crash recovery and durable linearizability | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_CRASH_RECOVERY_V1.md` |
| `D-07` | Candidate-derived outbox identity and delivery detectability | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/outbox.rs` |
| `D-08` | Authorized schema and state migration | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_MIGRATION_V1/` |
| `D-09` | History retention, pruning, snapshots, and bounded reopen | **GAP** | none | `docs/research/FCIS_M6_HISTORY_RETENTION_V1.md` |
| `D-10` | Multi-process, replication, backup, and restore qualification | **GAP** | none | `docs/research/FCIS_M6_DEPLOYMENT_TOPOLOGY_V1.md` |
| `E-01` | Strict proof decoding and verification against complete expected context | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/proof_context.rs` |
| `E-02` | Trusted proof-context provenance | **GAP** | none | `docs/research/FCIS_M6_PROOF_CONTEXT_SOURCES.json` |
| `E-03` | Verifier, verification-key, provider, and policy identity pinning | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_VERIFIER_POLICY_V1.json` |
| `E-04` | Projector and public-input completeness relation | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_PROJECTION_RELATION_V1.json` |
| `E-05` | Candidate-bound proof result and public inputs | **GAP** | none | `crates/zeno-fcis-adapter-zenodex/src/proof_authorization.rs` |
| `E-06` | Proof-guest/runtime transition refinement and golden vectors | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_PROOF_GUEST_REFINEMENT_V1.json` |
| `E-07` | Fresh consensus context, epoch/time, and Oracle-source binding | **GAP** | PROVED evidence | `crates/zeno-fcis-adapter-zenodex/src/consensus_oracle_context.rs` |
| `E-08` | Closed verifier dispatch and bypass elimination | **GAP** | IMPLEMENTED evidence, TESTED evidence | `tools/check_fcis_m6_verifier_authority.py` |
| `Z-01` | Exact global debt-cover algebra | **PROVED** | PROVED evidence | `lean-mathlib/Proofs/ZUSDGlobalDebtCoverRuntimeRefinement.lean` |
| `Z-02` | Global debt cap includes free and Stability Pool debt | **TESTED** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/zusd_debt_cap.rs` |
| `Z-03` | Pending/finalized observation freshness algebra | **PROVED** | PROVED evidence | `lean-mathlib/Proofs/ZUSDOracleFreshnessRuntimeRefinement.lean` |
| `Z-04` | Authoritative Oracle lifecycle and consensus time | **GAP** | PROVED evidence | `crates/zeno-fcis-adapter-zenodex/src/oracle_lifecycle.rs` |
| `Z-05` | Complete zUSD lifecycle conservation and state-machine closure | **GAP** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_ZUSD_LIFECYCLE_V1/` |
| `Z-06` | Mechanically complete zUSD economic-law manifest and durable obligations | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/zusd_laws.rs` |
| `Z-07` | Mounted zUSD runtime refinement and no-bypass authority | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_ZUSD_MOUNT_RECEIPT_V1.json` |
| `M6-01` | Canonical runtime acceptance chain | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/runtime.rs` |
| `M6-02` | Pure expected-root compare-and-swap semantics | **PROVED** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_PURE_CAS_PROOF_RECEIPT.json` |
| `M6-03` | Nominal runtime authorization and commit-port admission | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/authority.rs` |
| `M6-04` | Production linearizable atomic publication | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_LINEARIZABILITY_V1.json` |
| `M6-05` | Durable recovery, retry, and externally observable commit result | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_DURABLE_RESPONSE_V1.md` |
| `M6-06` | Transactional outbox completeness and external-operation semantics | **GAP** | IMPLEMENTED evidence, TESTED evidence | `crates/zeno-fcis-adapter-zenodex/src/delivery.rs` |
| `M6-07` | Upgrade, migration, rollback, and mixed-version safety | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_UPGRADE_STATE_MACHINE_V1.md` |
| `M6-08` | Concurrency, process topology, and deterministic scheduling | **GAP** | PROVED evidence, IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_PARALLEL_AUTHORIZATION_V1.json` |
| `M6-09` | Sole authority path and legacy/bypass removal | **GAP** | IMPLEMENTED evidence, TESTED evidence | `tools/check_fcis_m6_authority_closure.py` |
| `M6-10` | Trusted dependency, configuration, key, filesystem, and operational qualification | **GAP** | none | `docs/research/FCIS_M6_TCB_QUALIFICATION_V1.json` |
| `M6-11` | Final composed M5-to-M6 theorem/runtime refinement and promotion | **GAP** | IMPLEMENTED evidence, TESTED evidence | `docs/research/FCIS_M6_PROMOTION_RECEIPT_V1.json` |

## Detailed gate records

## Cross-cutting foundation

### F-01 — Abstract canonical-parser uniqueness

**Status:** `PROVED`
**Evidence layers already present:** PROVED evidence
**Status rationale:** The exact abstract theorem is closed, while its runtime premises remain separate gates.
**Scope:** Formal theorem only; no concrete runtime decoder claim.

**Exact safety claim**

For any deterministic parser P, a full-consumption parse of the same bytes is unique; if P(encode(v)) round-trips exactly, encode is injective.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean theorem | `ZDX-LEAN-LEDGER` | lean-mathlib/Proofs/TypedDeterministicParser.lean — acceptsAll_unique; canonicalAcceptance_unique; encode_injective_of_roundtrip | Unique full-consumption parses and encoder injectivity under round-trip assumptions. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The parser is represented as a mathematical function, so equal input has one returned result. | A closed, deterministic, side-effect-free concrete decoder generated or reviewed from one grammar. | Pinned decoder implementation and algorithm/schema identity. | No whole-runtime producer; B1B-1 supplies only three carrier decoders. | **GAP** |
| `A2` Acceptance requires complete input consumption. | The authority ingress wrapper must reject trailing bytes and alternate host-object paths. | Raw request bytes at the sole authority ingress. | B1B-1 bounded carrier decoder checks full canonical input in its narrow scope. | **TESTED** |
| `A3` The concrete encoder/decoder pair satisfies the stated exact round-trip premise. | Cross-language round-trip tests or a concrete refinement theorem for every admitted command type. | Canonical Python/Rust/proof-guest codec sources. | Only narrow carrier golden vectors exist; whole command surface is open. | **GAP** |

**Authenticated source relation — `NOT_APPLICABLE`:** Not applicable to the abstract uniqueness theorem; authentication is a later refinement. Current evidence: None; this theorem does not authenticate bytes or values.

**Current-state and commit relation — `NOT_APPLICABLE`:** Not applicable to the abstract theorem. Current evidence: None; the theorem does not read or publish state.

**Minimized counterexample `F01-CE-ALIAS`**

Dropping concrete canonical admission permits two byte spellings or a lossy host decode to denote the same apparent command. Minimal witness: JSON object contains duplicate "nonce" keys; a host parser keeps only the last value, so re-encoding cannot prove the original bytes were canonical. Source: `ZDX-LEAN-LEDGER`.

**Executable evidence**

Existing:
- Lean source contains the named theorem statements at the pinned commit.

Missing:
- Compile the exact Lean source under the pinned toolchain in the eventual aggregate branch.
- Connect every production decoder to the abstract parser/round-trip premises.

**Smallest closing artifact:** refinement proof and vector packet at `lean-mathlib/Proofs/ZenoRuntimeCanonicalIngress.lean`. Acceptance condition: Every mounted command decoder has a proof or generated certificate for bounded full consumption, exact re-encoding, rejection precedence, and Python/Rust/proof-guest byte parity.

**Dependencies/coupled gates:** none.

**Explicit nonclaims:** Does not prove concrete decoder correctness, authentication, authorization, state currentness, or publication.

### F-02 — Concrete bytes-to-authenticated-command ingress

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** All production command families and every runtime entry point.

**Exact safety claim**

Runtime acceptance of request bytes implies one bounded canonical decode, one authenticated principal and command, one authorized policy/profile, and no alternate object-based or legacy ingress.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` All authority-bearing input begins as bounded raw bytes. | One closed ingress adapter with byte/depth/node/collection budgets. | Network/IPC request envelope selected by the mounted deployment. | B1B-1 provides bounded carrier decoding only; the complete command registry is absent. | **GAP** |
| `A2` The decoded value is canonical and fully consumed. | The exact registered decoder followed by byte-for-byte re-encoding. | Authority-owned schema registry and canonical codec. | Partial carrier codecs and older command codecs exist on separate branches; no aggregate proof. | **GAP** |
| `A3` Authentication covers the canonical command bytes, domain, deployment, chain, schema, algorithm, principal, and replay identity. | A nominal command authenticator selected by deployment setup. | Pinned key set, signature policy, chain/deployment identity, and canonical bytes. | No M5/M6 aggregate authenticator binds every command family and policy source. | **GAP** |
| `A4` No alternate runtime entry point can construct or pass a later-stage command type. | Static call-graph/structural checker plus runtime negative tests over all entry points. | Repository production roots and packaged binary surface. | P4B3 reports mixed legacy authority and 64 final-mount violations; B1B-1 deliberately forbids authority consumers. | **GAP** |

**Authenticated source relation — `GAP`:** Independent deployment-owned authenticator; never a signature or hash copied from the request object. Current evidence: B1B-1 carriers are explicitly untrusted and cannot construct authenticated authority.

**Current-state and commit relation — `GAP`:** Accepted command must carry its replay identity and expected policy bindings into the exact transition and eventual commit. Current evidence: No mounted end-to-end relation; M5 reference accepts already-formed values.

**Minimized counterexample `F02-CE-HOST-OBJECT`**

A caller bypasses canonical-byte checks by supplying a predecoded mapping or directly constructing a command object. Minimal witness: bytes A and bytes B normalize to the same host mapping; signature/authentication covers B while runtime executes fields retained from A. Source: `ZDX-B1B1-HEAD`.

**Executable evidence**

Existing:
- B1B-1 resource-limit, duplicate-key, carrier-closure, Python/Rust golden-vector, and authority-isolation tests.

Missing:
- Whole command-registry canonical ingress corpus.
- Signature/domain/deployment/replay binding tests for every command.
- Call-graph mutation proving every object-based or legacy bypass is rejected.
- Cross-language exact rejection-code and precedence parity.

**Smallest closing artifact:** mounted ingress adapter and checker at `src/integration/fcis_authority_ingress_v2.py`. Acceptance condition: `RuntimeAccept(bytes)` can be produced only by the nominal adapter; every accepted value retains exact canonical bytes and authenticated bindings, and all bypass mutants fail.

**Dependencies/coupled gates:** `F-01`.

**Explicit nonclaims:** Carrier immutability or a content hash alone is not authentication.

### F-03 — Transitively owned immutable current state

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Every state object read by a promoted transition.

**Exact safety claim**

Every transition evaluates an exact, transitively immutable owned pre-state whose canonical bytes/root equal the store-current authoritative snapshot; no mutable child, borrowed alias, cache, or legacy projection can change semantic reads.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The pre-state owns its complete transitive semantic graph. | Closed exact state constructors and persistent/owned collections; no generic deep-freeze or mutable-base escape. | Store loader plus authority-owned schema. | P4B3 exact route values improve ownership, but final-mount still reports mutable/open/legacy violations. | **GAP** |
| `A2` Canonical state bytes and root cover every consulted value and presence/absence fact. | Complete root projection and presence/absence encoding with dynamic read-trace containment. | State-domain registry and authenticated projector selected by deployment. | M5 receipt lists support-root omissions, recipient/LP coverage, and context coverage as blockers. | **GAP** |
| `A3` The snapshot is the store-current version selected atomically, not merely a self-consistent historical value. | Transactional snapshot/open operation returning version, root, exact bytes, and nominal current-state witness. | Authoritative datastore/history under deployment policy. | ZenoFCIS has a generic strict reopen model; ZenoDEX has no mounted adapter. | **GAP** |

**Authenticated source relation — `GAP`:** Authorized genesis plus a gap-free reauthorized history under one deployment policy. Current evidence: ZenoFCIS supplies a reusable policy-bound genesis/history model; no ZenoDEX authority binds it.

**Current-state and commit relation — `GAP`:** StoreCurrent(store,s) must be witnessed at evaluation and rechecked at the publication linearization point by expected version/root. Current evidence: M5 has an immutable reference CAS; no production datastore relation is mounted.

**Minimized counterexample `F03-CE-ALIAS`**

A frozen outer state retains a mutable child or a sparse projection omits an absent/present cell. Minimal witness: Evaluation reads balance map M; another alias mutates M after root calculation, so step executes a state not named by the stored root. Source: `ZDX-P4B3`.

**Executable evidence**

Existing:
- P4B3 ownership, hostile-corruption, schema/index, and structural mutation tests.
- ZenoFCIS strict history/open tests at its reusable-library head.

Missing:
- Aggregate final-mount structural checker with zero violations.
- State-root/support-root completeness proof or complete static/dynamic footprint witness.
- Mounted store snapshot and stale-root race tests.
- Hostile alias mutation across every nested state family.

**Smallest closing artifact:** exact state-domain adapter at `crates/zeno-fcis-adapter-zenodex/src/state_v2.rs`. Acceptance condition: One nominal `ZenoDexCurrentState` is constructible only from reauthorized store bytes; its complete projection matches all promoted reads, and no legacy state representation reaches the transition.

**Dependencies/coupled gates:** `F-02`.

**Explicit nonclaims:** A frozen top-level record, nonzero root, or internally consistent snapshot is not current-state authority.

### F-04 — Pure total closed decision relation

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** All promoted ZenoDEX commands, including ordinary rejection and committed failure.

**Exact safety claim**

For every admitted exact pre-state, authenticated command, and authenticated context, the reviewed transition terminates deterministically with exactly one closed `Accept | Reject | CommittedFailure` decision; ordinary rejection carries no successor, patch, commit evidence, replay update, or outbox.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` All semantic inputs are explicit bounded values; no ambient time, randomness, I/O, mutable globals, or hidden caches are read. | Generated or reviewed pure transition program and authenticated context adapter. | Exact pre-state, command, and context values. | M5 reference values enforce purity for its substrate, but the complete mounted evaluator remains legacy/mixed. | **GAP** |
| `A2` Every command/profile branch is in the closed registry and has stable rejection precedence. | Closed command/profile dispatch and structural checker. | Authority-owned catalog/profile. | P4B3 route branch is exact unmounted; B1B-2 and later transition families remain open. | **GAP** |
| `A3` All arithmetic is checked in the protocol integer domain and all result artifacts share one candidate lineage. | Checked arithmetic helpers and one controlled candidate/decision/bundle builder. | Protocol schema/algorithm versions. | M5 reference same-candidate binding exists; P4B5A and full zUSD lifecycle remain incomplete. | **GAP** |

**Authenticated source relation — `GAP`:** Authenticated command and context must already be nominal values; raw carriers and proof outputs cannot enter `step`. Current evidence: No whole-system nominal adapter currently supplies all transition inputs.

**Current-state and commit relation — `GAP`:** The pure decision is not publication authority; it must be rebound to store-current state and nominal authorization before commit. Current evidence: M5 explicitly stops before authority switch; ZenoFCIS generic authority exists but is not mounted.

**Minimized counterexample `F04-CE-REJECT-EFFECT`**

A shell repairs an incomplete core result or a rejection retains an effect/outbox field. Minimal witness: Transition returns `Reject`, but an imperative wrapper reconstructs a nonce update or fee transfer from the request and publishes it. Source: `ZDX-M5-REFERENCE`.

**Executable evidence**

Existing:
- M5 closed decision/reference bundle tests, hostile mutation tests, and ordinary-reject purity laws.
- ZenoFCIS project-law framework tests reject ordinary rejection with authority artifacts.

Missing:
- Complete command/profile branch inventory.
- Termination/resource-bound evidence for each transition.
- Exact rejection-precedence vectors across Python, Rust, and proof guests.
- Mutation test killing every shell-side repair/reconstruction path.

**Smallest closing artifact:** closed aggregate transition program at `crates/zeno-fcis-adapter-zenodex/src/program_v2.rs`. Acceptance condition: Every promoted command is handled by one pure program, all decisions strictly normalize to the same candidate algebra, and shell reconstruction mutants fail.

**Dependencies/coupled gates:** `F-02`, `F-03`.

**Explicit nonclaims:** Determinism of a function does not prove input authority or atomic publication.

### F-05 — Complete read/write/context/effect/outbox footprints

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Every component eligible for deterministic parallel execution or partial-state authentication.

**Exact safety claim**

For every admitted input and every `Accept`, `Reject`, or `CommittedFailure` path, observed reads, writes, authenticated-context reads, commit-evidence kinds, and outbox destinations are subsets of an authority-bound static footprint.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean theorem | `ZDX-RK-SYNTHESIS` | lean-mathlib/Proofs/ReadWriteStableParallel.lean — execute_commutes_of_sound_noninterference | Sound read/write footprints plus noninterference imply two task executions commute. |
| Reusable framework | `ZFCIS-RC-HEAD` | docs/COMPLETE_FOOTPRINT_WITNESS.md — CompleteFootprintWitness; authorize_deterministic_parallel | Nominal complete-footprint witnesses can be minted only from authority-selected bindings and a closed proof method. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Each task reads only its declared read set. | Generated control-flow derivation, pinned static analysis, exhaustive finite enumeration, or checked theorem. | Authority-bound transition program/source revision. | No complete ZenoDEX witness exists; touched-cells and observed traces are insufficient. | **GAP** |
| `A2` Each task writes only its declared write set. | Same complete proof method plus patch normalization checks. | Exact patch builder and state schema. | Route-specific traces exist; whole-system write completeness is open. | **GAP** |
| `A3` Context, effect, and outbox dependencies are declared even on rare rejection/committed-failure branches. | Closed catalog of context/effect/outbox sites and decision-class coverage. | Exact profile/catalog and transition build. | M5 lists fee/context support as incomplete; value-moving channels are not all catalogued in ZenoDEX. | **GAP** |
| `A4` The verifier and retained artifact actually establish complete coverage of the exact source/build. | Deployment-selected verifier with exact toolchain/build/artifact identity. | Release authority, not caller-provided evidence. | ZenoFCIS supplies the trait boundary; no ZenoDEX exact artifact is mounted. | **GAP** |

**Authenticated source relation — `GAP`:** Authority selects the expected component/program/schema/catalog/algorithm/toolchain/verifier binding. Current evidence: Generic ZenoFCIS binding model exists; project bindings and artifacts are absent.

**Current-state and commit relation — `GAP`:** Footprints must bind command hash, pre-root, context hash, and algorithm/policy versions used by the committed candidate. Current evidence: No mounted candidate carries a complete proven footprint witness.

**Minimized counterexample `F05-CE-DISJOINT-WRITES`**

Disjoint writes alone do not imply deterministic execution. Minimal witness: Task A reads x and writes y:=x; task B writes x:=1. Writes {y} and {x} are disjoint, but execution order changes y. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- Lean abstract commutation theorem.
- ZenoFCIS negative tests for omitted rare effects, outbox destinations, decision classes, and stale authority bindings.

Missing:
- Complete ZenoDEX footprint claim/artifact per component.
- Verifier adapter and pinned toolchain evidence.
- Dynamic trace-containment corpus as a falsification layer.
- Conservative sequential fallback when any observed path escapes.

**Smallest closing artifact:** complete footprint evidence packet at `docs/research/FCIS_M6_COMPLETE_FOOTPRINT_WITNESSES_V1.json`. Acceptance condition: Exactly one independently verified witness exists for each promoted component and covers all decision classes, context cells, value effects, and outbox destinations.

**Dependencies/coupled gates:** `F-04`.

**Explicit nonclaims:** Observed traces and bounded tests cannot be labeled a complete static proof.

### F-06 — Whole-result implementation refinement and sequential/parallel parity

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Python authority, Rust runtime, proof guests, optimized/parallel evaluators, and any recovery re-execution path.

**Exact safety claim**

For identical canonical pre-state, command, authenticated context, profile, algorithm, budget, and precedence, every accepted implementation returns byte-identical normalized decision artifacts: decision/reason, successor, patch, commit evidence, outbox, receipt, roots, nonce/nullifier updates, fees, residue, and ordering.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean theorem | `ZDX-LEAN-LEDGER` | lean-mathlib/Proofs/DeterministicParallelExecution.lean — applyPatch_commute_of_disjoint; commit_rejects_root_mismatch; commit_accepts_root_match | Already-computed disjoint patches commute and pure expected-root CAS accepts exactly on root equality. |
| Reusable framework | `ZFCIS-RC-HEAD` | docs/VALIDATED_REFINEMENT_AND_EXHAUSTIVE_COVERAGE.md — ValidatedNormalizedDecision | Strict reconstruction prevents equality of fabricated transport objects from becoming promotion evidence. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Every implementation receives the same canonical admitted inputs and complete bindings. | One test/replay harness that derives all implementation inputs from the same canonical fixture. | Pinned source revisions, providers, schema/profile/algorithm/budget. | Partial Python/Rust/OCaml lanes exist, but whole M5 decision parity and proof guests remain open. | **GAP** |
| `A2` Each normalized output is reconstructed from strict canonical receipt/bundle bytes, not caller-selected diagnostic fields. | Strict normalized-decision importer and decoder limits. | Exact bundle/receipt codecs. | ZenoFCIS generic importer is tested; ZenoDEX bundle/decision codec parity is incomplete. | **GAP** |
| `A3` For parallel execution, footprint soundness and the canonical logical join/error order hold. | Complete footprint witnesses plus canonical scheduler/join definition. | Authority-selected composition spec. | No promoted deterministic-parallel ZenoDEX authorization exists. | **GAP** |
| `A4` Coverage is unbounded by theorem or exactly exhaustive over a reviewed finite domain; bounded samples are labeled as such. | Lean proof or canonical exhaustive manifest plus independent verifier. | Release evidence policy. | No whole-domain theorem or exhaustive manifest exists. | **GAP** |

**Authenticated source relation — `GAP`:** All compared implementations and importers are pinned by release authority; a caller cannot choose the reference after seeing outputs. Current evidence: Generic framework supports this relation; no aggregate ZenoDEX authority binds every implementation.

**Current-state and commit relation — `GAP`:** Only a validated result matching the exact current pre-state may be authorized for publication; diagnostic parity grants no commit authority. Current evidence: No mounted adapter connects validated refinement to the commit port.

**Minimized counterexample `F06-CE-NONCE-U32`**

Randomized parity restricted to the shared u32 domain concealed a larger-domain Rust acceptance. Minimal witness: nonce = 2^32: Python rejects because the nonce table is u32-bounded, while the Rust state-root shadow accepted before the drift was documented. Source: `ZDX-NONCE-DRIFT`.

**Executable evidence**

Existing:
- Narrow Python/Rust replay-guard reject-code tests.
- B1B-1 Python/Rust carrier golden vectors.
- ZenoFCIS strict refinement importer and substitution tests.

Missing:
- Whole normalized-decision differential corpus.
- Proof-guest public-input/output parity.
- Rejection phase and precedence parity.
- Finite-domain manifest or mechanized refinement proof for each promoted implementation.
- Integration test proving only validated results reach nominal publication authorization.

**Smallest closing artifact:** cross-implementation refinement packet at `docs/research/FCIS_M6_RUNTIME_REFINEMENT_V1.json`. Acceptance condition: Every promoted implementation is bound to one source/toolchain identity and passes exact normalized decision parity or a checked refinement proof over the declared domain.

**Dependencies/coupled gates:** `F-01`, `F-04`, `F-05`.

**Explicit nonclaims:** Agreement on selected cases does not prove an implementation correct or authorize publication.

## P4B5A — fee apportionment and committed configuration authority

### A-01 — Exact untrusted authority carriers and canonical codecs

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** B1B-1 only: `FCISAuthorityHeaderV2`, bootstrap-anchor claim, migration manifest, and their untrusted source types.

**Exact safety claim**

Arbitrary bounded bytes are either rejected with a closed code or admitted into an exact immutable carrier whose stored fields equal the schema registry and whose canonical bytes/root are injective over admitted values; the result carries no protocol authority.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Implementation report | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B1_IMPLEMENTATION_REPORT_20260729.md — implemented relation and invariant sections | Exact Python/Rust carriers, bounded decoders, canonical bytes/roots, global authority-isolation scan, and exact-head focused evidence. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Input byte, depth, node, and collection budgets are enforced before unbounded host allocation. | B1B bounded lexical scanner and decoder. | Raw untrusted carrier bytes. | Implemented and focused-tested at the exact B1B-1 head. | **TESTED** |
| `A2` Carrier field sets and stored runtime fields exactly equal the closed schema registry. | Closed Python/Rust values plus runtime field-equality and mutation checker. | B1B schema registry. | Implemented and focused-tested. | **TESTED** |
| `A3` Canonical Python and Rust encodings agree on accepted and rejected boundary cases. | Shared golden fixture and Python/Rust codec implementations. | Exact carrier schema/version/domain separators. | Implemented; exact-head Rust/Python jobs reported green. | **TESTED** |
| `A4` No carrier consumer upgrades these values into pinned verifier, state, transition, proof, publication, or mount authority. | Repository-wide authority-isolation scanner over declared runtime roots. | Bounded source inventory at exact head. | 936 runtime files scanned with zero findings; scanner remains a bounded repository gate. | **TESTED** |

**Authenticated source relation — `NOT_APPLICABLE`:** None. These values are deliberately untrusted carriers. Current evidence: The report explicitly denies pinned verifier, migration authority, state authority, proof authority, or publication authority.

**Current-state and commit relation — `NOT_APPLICABLE`:** No state transition or commit relation is permitted in B1B-1. Current evidence: Production runtime and mounted files are unchanged.

**Minimized counterexample `A01-CE-HIDDEN-FIELD`**

An inherited, post-definition, or hidden carrier field changes semantics without entering the canonical registry. Minimal witness: A subclass/property or type-level mutation adds an authority-bearing field while canonical encoding still reads only the declared registry. Source: `ZDX-B1B1-HEAD`.

**Executable evidence**

Existing:
- 111 focused B1B-1 carrier/checker/packet tests; 8 Rust tests; shared golden builder check; structural checker and mutation corpus; exact-head CI report.

Missing:
- Independent exact-head implementation review verdict.
- Aggregate rebase evidence showing no later branch weakens the carrier closure.

**Smallest closing artifact:** independent review receipt at `docs/research/FCIS_M5_P4B5A_B1B1_EXACT_HEAD_REVIEW_20260729.md`. Acceptance condition: Independent review returns the required exact-head unmounted approval without widening the carrier-only claim.

**Dependencies/coupled gates:** `F-01`.

**Explicit nonclaims:** Does not authenticate a deployment, authorize migration, bind current state, or permit B1B-2 implementation.

### A-02 — Frozen configuration-language semantic validation

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** B1A fee-distribution configuration claim only.

**Exact safety claim**

A structurally admitted configuration is usable as semantic evidence only if its algorithm version, accepted-language version, policy root, and embedded configuration root equal the frozen B1A definitions; point-of-use revalidation detects hostile mutation.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Design and implementation evidence | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md — sections 2.2, 3.1, and 3.2 | Separates closed structural admission from B1A semantic validation and defines the exact validation equations. |
| Focused tests | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B1_IMPLEMENTATION_REPORT_20260729.md — ATDD evidence | Reports 14 passing B1A configuration suites at the repaired head. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The admitted claim is exact, owned, and canonical. | B1A closed admission registry. | Canonical configuration claim bytes. | Existing B1A implementation and tests are referenced by Revision 3.4. | **TESTED** |
| `A2` Only the frozen B1A validator constructs the validated type. | Private/controlled validated-claim constructor. | Frozen B1A validator implementation. | Existing implementation; aggregate exact-head source identity must remain pinned. | **IMPLEMENTED** |
| `A3` The validator recomputes policy and configuration roots from the exact body. | Canonical policy/configuration root functions. | Validated body fields, never metadata copied from an untrusted source. | Focused semantic-substitution tests are reported. | **TESTED** |
| `A4` Every authority-bearing use revalidates the exact validated object. | State/command/migration binders repeat `revalidate` before reading authority-bearing fields. | Point-of-use exact object. | Required by design; binders are later checkpoints and absent. | **GAP** |

**Authenticated source relation — `GAP`:** Semantic validity comes from the frozen validator, but authority over which valid configuration applies comes independently from state, command, or migration manifest. Current evidence: Validated claims alone explicitly carry no protocol authority.

**Current-state and commit relation — `GAP`:** A validated configuration can influence a transition only after independent expected-root binding to the exact pre-state/command/manifest and later store-current rederivation. Current evidence: No such committed-state publication path is implemented in B1B-1.

**Minimized counterexample `A02-CE-UNSUPPORTED-ALGORITHM`**

Structural admission plus root equality accepts semantically unsupported configuration content. Minimal witness: Structurally exact body sets `algorithm_version = OTHER_ALGORITHM`; an authenticated command can name its root, but B1A must reject `ALGORITHM_VERSION_MISMATCH`. Source: `ZDX-B1B1-HEAD`.

**Executable evidence**

Existing:
- B1A configuration suites reported passing; Revision 3.4 retains semantic substitution and hostile-mutation requirements.

Missing:
- Point-of-use revalidation tests in every active/proposed/migration binder.
- Python/Rust rejection-code and precedence parity for semantic failures.
- Exact source/build identity for the frozen validator in the aggregate release packet.

**Smallest closing artifact:** validated configuration adapter at `crates/zeno-fcis-adapter-zenodex/src/fee_configuration.rs`. Acceptance condition: One strict cross-language adapter composes B1A admission, validation, canonical root recomputation, and point-of-use revalidation without constructing authority.

**Dependencies/coupled gates:** `A-01`.

**Explicit nonclaims:** Semantic validity is not state, governance, migration, or publication authority.

### A-03 — Independent expected-root binding for active, proposed, and migration configuration

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** B1B-2 and later authority checkpoints.

**Exact safety claim**

For each configuration role, the B1A-valid exact content root equals an expected root supplied by exactly one independent authority source: active root from the exact pre-state, proposed root from a freshly authenticated update command, and initial root from a pinned verified migration manifest.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Approved design | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md — sections 2.3, 3.3, 4, and 5 | Defines independent authority owners and the three root-binding relations. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The configuration content already passed B1A semantic validation and point-of-use revalidation. | Validated configuration adapter from A-02. | Frozen B1A validator and canonical content bytes. | Narrow validator exists; authority binders absent. | **GAP** |
| `A2` The active expected root is read from the exact pre-state authority header. | `bind_fee_configuration_to_state_v2` consuming exact pre-state. | Store-current-derived `FCISCommittedStateV2`. | Design only; committed V2 state is forbidden in B1B-1. | **GAP** |
| `A3` The proposed expected root is covered by fresh command authentication, not copied from content, bundle, or resolver. | Command authenticator producing nominal `AuthenticatedConfigurationUpdateCommandV2`. | Canonical signed command bytes and deployment policy. | Type and authenticator are explicitly deferred. | **GAP** |
| `A4` The initial expected root is covered by a deployment-pinned verified manifest. | Pinned deployment/migration verifier selected by release/deployment setup. | Verified manifest bytes and independently distributed pin. | B1B-1 carries only untrusted manifest data; no verifier exists. | **GAP** |
| `A5` Deployment/domain/version/activation equations are checked against the same exact pre-state/context. | Exact whole-transition derivation over authenticated consensus context. | Store-current pre-state plus independently authenticated context. | Later design only. | **GAP** |

**Authenticated source relation — `GAP`:** State, command authenticator, and pinned manifest verifier are independent; neither content nor bundle can self-supply expected roots. Current evidence: Only the source roles and equations are designed; no nominal authority values are implemented.

**Current-state and commit relation — `GAP`:** Publication must repeat content validation and source binding against store-current state before expected-root CAS. Current evidence: No production publication port or rederivation exists.

**Minimized counterexample `A03-CE-SELF-ROOT`**

A bundle copies a proposed root from the configuration content and checks equality between two attacker-controlled copies. Minimal witness: content.root = bundle.expected_root = R for unsupported or unauthorized content; all internal equalities pass without state, command, or manifest authority. Source: `ZDX-B1B1-HEAD`.

**Executable evidence**

Existing:
- Revision 3.4 design review and bounded phase-DAG obligations.

Missing:
- Nominal active/proposed/migration binders.
- Source-substitution mutants for content, resolver, bundle, shell, and stale command.
- Store-current rebind tests.
- Pinned-verifier distribution/identity evidence.

**Smallest closing artifact:** B1B-2 authority implementation packet at `docs/research/FCIS_M5_P4B5A_B1B2_IMPLEMENTATION_REPORT_20260729.md`. Acceptance condition: Each content role can be bound only to its independent nominal source; mixed-source and self-root substitutions fail before evaluation.

**Dependencies/coupled gates:** `A-01`, `A-02`, `F-03`.

**Explicit nonclaims:** Root equality proves identity, not authority or semantic validity.

### A-04 — Configuration authority state machine and update transition

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Bootstrap, migration, ordinary active use, and authenticated configuration updates.

**Exact safety claim**

The authority header advances only through closed whole-state transitions with exact predecessor sequence/root, one declared cause, checked U256 version increments, domain/deployment continuity, activation rules, and no generic header patch or bare-header update.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Approved design | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md — sections 5, 10, 11, and 12 | Defines receipt-free candidate, receipt-bearing decision, one-decision bundle, and forbids bare-header advancement. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Bootstrap pin and migration manifest are independently verified. | Pinned verifier and authorized genesis/migration ceremony. | Deployment release root and verified manifest. | Absent. | **GAP** |
| `A2` The exact pre-state is current and its active configuration is state-bound. | Store-current exact state binder. | Reauthorized datastore state/history. | Absent in ZenoDEX. | **GAP** |
| `A3` The update command and consensus context are freshly authenticated. | Nominal command/context authentication adapters. | Canonical signed bytes and consensus publication context. | Absent. | **GAP** |
| `A4` The candidate/decision/bundle dependency graph is acyclic and same-lineage. | Controlled candidate, decision, receipt, and bundle builders with cycle checker. | Exact transition artifacts. | M5 V1 substrate exists, but V2 configuration state-machine types are absent. | **GAP** |
| `A5` Only the whole-state transition can change authority-header fields. | Closed dispatch and structural checker rejecting generic writes/patches. | Production source roots and compiled runtime. | B1B-1 checker forbids premature state-machine code; no later implementation. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment pin, state, command, and consensus context each own distinct facts. Current evidence: No implemented nominal composition.

**Current-state and commit relation — `GAP`:** One complete successor state plus receipt/replay/outbox must publish under the same expected pre-root; ordinary rejection publishes nothing. Current evidence: Reference V1 commit model only; no V2 configuration transition or production transaction.

**Minimized counterexample `A04-CE-CYCLE`**

Putting a receipt inside the candidate while deriving the receipt from the complete candidate creates a dependency cycle. Minimal witness: `candidate_id` commits receipt; `receipt` commits candidate_id. No finite canonical construction can satisfy the declared DAG without omitting or self-referencing data. Source: `ZDX-B1B1-HEAD`.

**Executable evidence**

Existing:
- Revision 3.4 dependency-DAG analysis and forbidden-surface checker.

Missing:
- State-machine model covering bootstrap/migration/update/use.
- Lean/ESSO transition invariants and cycle search.
- Python/Rust exact candidate/decision/bundle codecs.
- Stateful stale/competing-update tests and atomic publication evidence.

**Smallest closing artifact:** closed authority state-machine module at `src/core/fcis_configuration_authority_v2.py`. Acceptance condition: All legal authority transitions are constructible only by the closed whole-state relation; all bare-header and cyclic-artifact mutants fail.

**Dependencies/coupled gates:** `A-03`, `F-04`.

**Explicit nonclaims:** A schema-valid header or monotone sequence alone is not a legitimate authority transition.

### A-05 — Fixed-policy apportionment conservation and per-period exactness

**Status:** `GAP`
**Evidence layers already present:** TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Mechanical-word allocator with fixed weights and denominator for one stable fee-distribution domain/asset.

**Exact safety claim**

For fixed nonnegative weights summing to denominator D, every allocated fee amount is exactly conserved; over each complete canonical period D, each role receives exactly its weight; same-policy amount decomposition is independent of chunking.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Research counterexample/review packet | `ZDX-P4B5A-RESEARCH` | docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md — sections 10 and 12 | Retains the hierarchical mechanical-word allocator for fixed weights and reports conservation, per-period exactness, and telescoping as surviving properties. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Weights and denominator remain fixed over the interval being reasoned about. | State-bound validated fee configuration and explicit policy-lifecycle rule. | Exact pre-state authority header and validated content. | Dynamic activation semantics are unresolved. | **GAP** |
| `A2` Weights are protocol-domain integers, nonnegative, and sum exactly to D. | B1A validator plus checked-sum constructor. | Validated configuration body. | Semantic validator exists; exact allocator configuration adapter absent. | **GAP** |
| `A3` Cursor/phase state is stable, authenticated, and advanced once per allocated atom. | Committed per-domain/per-asset apportionment state. | Authenticated store-current state. | Not implemented; current WIP variants disagree. | **GAP** |
| `A4` Allocation uses the exact closed floor/prefix formulas and safe periodic decomposition. | One Python/Rust implementation generated from or proved against the formula. | Pinned algorithm version. | Research scripts only; no production implementation or Lean proof. | **GAP** |

**Authenticated source relation — `GAP`:** Fixed weights come from the active configuration root bound to current state, not a mutable policy service. Current evidence: No active state-bound configuration or allocator state is mounted.

**Current-state and commit relation — `GAP`:** Cursor successor and net fee patch must be in the same candidate and transaction as the fee-producing settlement. Current evidence: No P4B5A-specific candidate/commit integration exists.

**Minimized counterexample `A05-CE-WEIGHT-CHANGE`**

Applying a fixed-weight theorem across a policy change invalidates its premises. Minimal witness: Run one atom under weights w, then change to w' selected from cursor state; the fixed-period exactness theorem no longer describes the combined trace. Source: `ZDX-P4B5A-RESEARCH`.

**Executable evidence**

Existing:
- Deterministic Python research witnesses for selected denominators and amounts.
- ESSO validates the counterexample model shape, not the surviving theorem.

Missing:
- Lean proof of conservation, complete-period exactness, and split/merge telescoping over arbitrary protocol-domain amounts.
- Independent Python/Rust vectors including D=1, D=4, D=10,000, zero weights, U256_MAX, and chunk partitions.
- Runtime integration tests against exact settlement fee credits.

**Smallest closing artifact:** Lean theorem and cross-language allocator corpus at `lean-mathlib/Proofs/FixedPolicyFeeApportionment.lean`. Acceptance condition: Lean discharges conservation, period exactness, and telescoping with no `sorry`; generated Python/Rust implementations pass exact vectors at protocol bounds.

**Dependencies/coupled gates:** `A-03`.

**Explicit nonclaims:** The result does not extend to adaptive or arbitrary time-varying weights.

### A-06 — Fixed-policy cumulative discrepancy bounds

**Status:** `GAP`
**Evidence layers already present:** TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Same fixed-policy allocator and stable cursor.

**Exact safety claim**

For any interval under fixed weights, role-0 allocation differs from ideal quota by less than one atom and role-1/role-2 differ by less than two atoms, with the exact strictness and endpoint conventions frozen in the theorem.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Minimized boundary review | `ZDX-P4B5A-RESEARCH` | docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md — ROLE1-INTERVAL-BOUND-012 | Refutes the former role-1 `<1` claim and identifies the safe `<1,<2,<2` bounds derived from prefix bounds. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Policy weights and denominator are fixed. | State-bound policy-lifecycle rule. | Current validated configuration. | Open. | **GAP** |
| `A2` The prefix-count formulas and interval definition match the implementation exactly. | One formal allocator specification and generated/refined implementations. | Pinned algorithm definition. | Research formulas exist; no Lean theorem or production refinement. | **GAP** |
| `A3` Cursor arithmetic is performed without wraparound or reset. | Checked cursor update with stable semantic key and migration. | Committed apportionment state. | Open. | **GAP** |

**Authenticated source relation — `GAP`:** Current state owns weights and cursor; neither caller nor recipient account can reset them. Current evidence: Not implemented.

**Current-state and commit relation — `GAP`:** The exact successor cursor is committed with the allocation and cannot be dropped on retry or failure. Current evidence: No production relation.

**Minimized counterexample `A06-CE-ROLE1`**

The tighter role-1 `<1` claim is false. Minimal witness: D=10,000, weights=(1,9,998,1), q=1, n=9,998 gives role-1 excess 4,999/2,500 = 1.9996 atoms. Source: `ZDX-P4B5A-RESEARCH`.

**Executable evidence**

Existing:
- Research witness reproduces the false-bound counterexample.

Missing:
- Lean proof of the corrected strict interval bounds.
- Exhaustive finite checks for small D as a theorem-falsification lane.
- Boundary vectors around every floor discontinuity and cursor wrap.

**Smallest closing artifact:** corrected discrepancy theorem at `lean-mathlib/Proofs/FixedPolicyFeeApportionmentDiscrepancy.lean`. Acceptance condition: The exact implementation formulas satisfy the frozen `<1,<2,<2` interval bounds for all valid inputs, and the historical false-bound mutant is killed.

**Dependencies/coupled gates:** `A-05`.

**Explicit nonclaims:** Sampled or exhaustive small-D checks are not the unbounded theorem.

### A-07 — Adaptive policy activation and bounded fairness

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Any configuration update that can change allocation weights or destinations before a fixed-policy cycle closes.

**Exact safety claim**

For every adversarially chosen but authenticated policy sequence allowed by the protocol, cumulative role allocation remains within a declared finite discrepancy bound from the sum of time-varying ideal quotas, or the protocol makes such adaptive activation unrepresentable.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Refutation | `ZDX-P4B5A-RESEARCH` | docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md — ADAPTIVE-POLICY-ROUNDING-008 | Shows preserving one scalar cursor does not bound discrepancy under adaptive policy selection. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The protocol freezes one explicit policy-lifecycle model: cycle-closed activation, dynamic entitlement/error state, or another proved allocator. | Normative configuration-update/state-machine design. | Authenticated current state and update command. | No model selected; current scalar-cursor proposal is refuted. | **GAP** |
| `A2` The adversary may choose any authenticated policy sequence permitted by governance; authentication is not benevolence. | Threat model and bounded/formal quantification over all allowed policy choices. | Protocol governance authority. | Existing witness demonstrates the need; no closing theorem. | **GAP** |
| `A3` Pending activation, destination changes, dormant domains, rollback, and receipts are part of the state machine. | Committed pending/active policy state and atomic migration relation. | Store-current authority state. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Authenticated governance command chooses policy only within the frozen lifecycle; it cannot reset hidden fairness state. Current evidence: Not implemented.

**Current-state and commit relation — `GAP`:** Policy activation and allocator-state transformation must occur atomically with sequence/root advancement. Current evidence: No transition or migration implementation.

**Minimized counterexample `A07-CE-D4`**

Adaptive weights exploit the public cursor and create unbounded excess. Minimal witness: D=4, one atom per epoch; choose (3,0,1),(1,1,2),(2,0,2),(4,0,0). Role 2 receives 3 against ideal 5/4 after four steps and excess grows by 7/4 per cycle; step five reaches excess 5/2. Source: `ZDX-P4B5A-RESEARCH`.

**Executable evidence**

Existing:
- Python witness and ESSO model; Z3 and cvc5 agreed on the reachable step-five counterexample.

Missing:
- Normative lifecycle choice.
- ESSO/Lean model including pending/active states, rollback, destination rotation, and crash points.
- Adversarial policy-sequence generator and invariant checks.
- Migration and receipt vectors.

**Smallest closing artifact:** policy-lifecycle decision and theorem at `docs/research/FCIS_M5_P4B5A_POLICY_LIFECYCLE_V1.md`. Acceptance condition: Independent review approves one model and its proof/model rejects the D=4 adaptive witness by construction or proves the declared dynamic bound.

**Dependencies/coupled gates:** `A-04`, `A-05`, `A-06`.

**Explicit nonclaims:** Governance authentication alone does not close adaptive rounding manipulation.

### A-08 — Stable apportionment-state key and migration

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Cursor/error/entitlement state identity across recipient rotation, configuration versioning, bootstrap, and migration.

**Exact safety claim**

Apportionment state is keyed by a stable semantic fee-distribution domain and asset, cannot be reset by rotating a source/recipient account, cannot fork into parallel fresh domains, and migrates one-to-one with explicit predecessor/successor commitments.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Refutation | `ZDX-P4B5A-RESEARCH` | docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md — CURSOR-KEY-ROTATION-009 | Shows `(source_account_pubkey, asset)` permits reset amplification through account rotation and recommends `(fee_distribution_domain_id, asset)`. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The semantic domain identifier comes from authenticated deployment/configuration authority. | Validated state-bound configuration and deployment pin. | Current authority header/configuration. | No implemented binder/domain registry. | **GAP** |
| `A2` Exactly one live allocator state exists per domain/asset. | Closed state schema with uniqueness constraints and complete root projection. | Authenticated state store. | Absent. | **GAP** |
| `A3` Recipient/account rotation does not change the semantic key. | Configuration update law separating destination identity from allocation-state identity. | Authenticated update command and current state. | Design choice unresolved. | **GAP** |
| `A4` Migration consumes the predecessor state exactly once and preserves or explicitly transforms fairness debt. | Authorized migration candidate plus nullifier/history record. | Pinned manifest and store-current predecessor. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Domain ID is authority-owned; account keys are destinations, not lineage authority. Current evidence: No nominal state type or migration verifier.

**Current-state and commit relation — `GAP`:** State-key creation/update/delete and destination changes publish in one candidate under expected-root CAS. Current evidence: No P4B5A persistence implementation.

**Minimized counterexample `A08-CE-ROTATE`**

Recipient rotation silently resets cursor state. Minimal witness: Cursor is stored at `(recipient_A, asset)`; governance rotates to `recipient_B`, creating missing-key default cursor 0 and repeating favorable early-round allocations. Source: `ZDX-P4B5A-RESEARCH`.

**Executable evidence**

Existing:
- Research counterexample and design recommendation.

Missing:
- Exact state schema and root vectors.
- Duplicate-domain and parallel-state rejection tests.
- Recipient-rotation property tests.
- Migration crash/retry/nullifier tests.

**Smallest closing artifact:** allocator-state schema and migration relation at `src/state/fcis_fee_apportionment_state_v2.py`. Acceptance condition: Stable domain/asset identity survives destination rotation; one-to-one migration is same-candidate, replay-safe, and exact-root bound.

**Dependencies/coupled gates:** `A-03`, `A-07`, `D-04`.

**Explicit nonclaims:** A source or recipient account is not a safe fairness-lineage key.

### A-09 — Provisional fee provenance and per-settlement conservation

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Every protocol-fee credit produced by settlement and later consumed by apportionment.

**Exact safety claim**

Each provisional fee credit is freshly recomputed from one exact settlement occurrence and binds intent, pool, asset, authenticated quote/policy, sender debit, pool reserve credit, and fee amount; `sender_debit = pool_credit + provisional_fee`; the global candidate consumes every credit exactly once and creates none.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Refutation/design requirement | `ZDX-P4B5A-RESEARCH` | docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md — PROVISIONAL-LINEAGE-011 | Shows removing the ordinary balance atom invalidates the old lineage proof and enumerates the replacement witness fields and conservation equation. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Settlement replay is exact and command/route/quote bound. | Exact strong settlement validator and route replay. | Authenticated command, state, route binding, and context. | P4B3 route substrate is exact unmounted; strong validator remains mixed/legacy reachable. | **GAP** |
| `A2` Every fee witness is derived, not accepted from shell or bundle input. | Private provisional-credit constructor inside settlement derivation. | Exact replay result. | Not implemented for the corrected design. | **GAP** |
| `A3` Per-settlement conservation is checked in the protocol integer domain. | Checked arithmetic conservation law in runtime law engine and Lean. | Settlement atoms. | No replacement law implementation/theorem. | **GAP** |
| `A4` The candidate consumes an exact duplicate-free set of fee witnesses once. | Candidate builder with occurrence IDs and duplicate/missing witness checks. | Complete settlement result set. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Quote/policy/context are authenticated independently and rebound to current state; witness self-consistency is insufficient. Current evidence: No nominal authenticated lineage value.

**Current-state and commit relation — `GAP`:** Fee witnesses, net balance patch, allocator state, receipt, and outbox all share one candidate and transaction. Current evidence: Only generic M5 reference binding exists.

**Minimized counterexample `A09-CE-UNBACKED`**

A typed fee credit is accepted without proving which sender debit funded it. Minimal witness: Bundle injects `ProtocolFeeCredit(asset=X, amount=10)` with no matching settlement occurrence; apportionment creates recipient value from nothing. Source: `ZDX-P4B5A-RESEARCH`.

**Executable evidence**

Existing:
- Existing route-binding/replay tests and research witness description.

Missing:
- Replacement provisional-credit value and derivation.
- Duplicate/omission/substitution mutants.
- Per-swap and aggregate conservation property tests.
- Lean law over exact atom algebra.
- Candidate same-lineage integration tests.

**Smallest closing artifact:** provisional fee lineage module at `src/core/fcis_protocol_fee_lineage_v2.py`. Acceptance condition: Only exact settlement replay can mint a provisional credit; every committed credit is uniquely consumed and per-settlement plus aggregate conservation hold.

**Dependencies/coupled gates:** `F-04`, `A-03`, `F-05`.

**Explicit nonclaims:** A root-bound fee record is not proof that corresponding value was debited.

### A-10 — Checked U256 apportionment arithmetic and cross-language exactness

**Status:** `GAP`
**Evidence layers already present:** TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** All cursor, amount decomposition, prefix-count, multiplication/division, and weight-update calculations.

**Exact safety claim**

Python, Rust, Lean/model, and any proof guest implement one overflow-safe integer specification; no intermediate exceeds the declared domain; rejection/checked-failure precedence is identical.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Counterexample | `ZDX-P4B5A-RESEARCH` | docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md — U256-CURSOR-INTERMEDIATE-013 | Shows `q+n` may require 257 bits and gives the exact bounded decomposition `r=n mod D; q'=(q+r) mod D`. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Amount, cursor, denominator, and weights have explicit bounded integer domains. | Closed schema/newtypes and admission checks. | Canonical command/config/state values. | Carrier integer fields exist narrowly; allocator state/schema absent. | **GAP** |
| `A2` Every potentially wide expression is algebraically decomposed or checked before evaluation. | Generated checked arithmetic helpers or direct refinement to formal spec. | Pinned algorithm implementation. | Research correction only. | **GAP** |
| `A3` All implementations use the same Euclidean division/floor and rejection semantics. | Shared positive/negative golden vectors plus proof-guest public-input vectors. | One canonical arithmetic spec. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Domains and algorithm version come from validated configuration/profile, not host integer convenience. Current evidence: No state-bound allocator configuration.

**Current-state and commit relation — `GAP`:** Arithmetic failure is an ordinary rejection with no partial cursor or balance update; success commits exact result once. Current evidence: No integrated transition.

**Minimized counterexample `A10-CE-257BIT`**

A mathematically modulo-safe formula still overflows in checked U256 evaluation. Minimal witness: n=2^256-1 and q>0: computing `q+n` first requires 257 bits; Python/BigUint succeeds while strict U256 traps or rejects. Source: `ZDX-P4B5A-RESEARCH`.

**Executable evidence**

Existing:
- Research script covers selected large amounts and the corrected decomposition.

Missing:
- Lean equivalence proof for decomposed formulas.
- U256_MAX and near-boundary vectors in Python/Rust/proof guest.
- Mutation test reintroducing `q+n`.
- Exact error precedence for invalid weights, overflow, and malformed state.

**Smallest closing artifact:** checked arithmetic spec and generated implementations at `crates/zeno-fcis-adapter-zenodex/src/apportionment_math.rs`. Acceptance condition: All arithmetic derives from one formal equation set, passes boundary vectors, and the 257-bit intermediate mutant is rejected.

**Dependencies/coupled gates:** `A-05`.

**Explicit nonclaims:** Mathematical modular equivalence does not guarantee a finite-width implementation evaluates the same expression safely.

### A-11 — Accepted-language versioning for same-batch fee spending

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Interaction between provisional protocol-fee credits and later intents in the same batch.

**Exact safety claim**

The protocol explicitly chooses and versions whether a provisional fee credit may fund later same-batch commands; settlement replay, apportionment, support roots, receipts, and migration all implement the same rule without double spending or silent accepted-language contraction.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Counterexample | `ZDX-P4B5A-RESEARCH` | docs/research/FCIS_M5_P4B5A_APPORTIONMENT_ARCHITECTURE_CORRECTED_INDEPENDENT_REVIEW_20260728.md — ACCEPTED-LANGUAGE-CONTRACTION-010 | Identifies an existing V1 regression where an earlier protocol-fee credit funds a later intent and shows the corrected provisional design would reject earlier. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` One semantic rule is frozen per accepted-language version. | Versioned profile/configuration registry. | State-bound accepted-language version. | B1A validates a language version, but the new semantic choice is not frozen. | **GAP** |
| `A2` If spending is allowed, provisional value has explicit ownership, availability, consumption, and residual-allocation semantics. | Provisional balance/credit state machine and exact replay. | Settlement lineage and ordered batch semantics. | Absent. | **GAP** |
| `A3` If spending is forbidden, V2 explicitly declares non-equivalence and rejects before any partial effect. | Closed validation/rejection precedence. | Profile selected by current state. | Not implemented. | **GAP** |
| `A4` Migration cannot replay V1 batches under V2 semantics without an explicit relation. | Version-aware migration/replay adapter. | Pinned historical profile and manifest. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Accepted-language version is state/deployment authority, not a local runtime flag. Current evidence: No mounted profile switch.

**Current-state and commit relation — `GAP`:** Batch decisions, fee consumption, residual apportionment, and state update are one deterministic candidate. Current evidence: No implementation.

**Minimized counterexample `A11-CE-V1-SPEND`**

Claiming V1/V2 acceptance equivalence is false if V2 removes spendable fee credit. Minimal witness: Protocol recipient begins at zero; swap 1 credits fee 15; later intent spends 10. V1 strong replay accepts, a non-spendable provisional-credit V2 rejects. Source: `ZDX-P4B5A-RESEARCH`.

**Executable evidence**

Existing:
- Existing V1 regression named in the review; research analysis of the contraction.

Missing:
- Normative language-version decision.
- Positive/negative ordered-batch vectors.
- No-double-spend/residual-conservation properties.
- V1-to-V2 replay/migration relation.

**Smallest closing artifact:** accepted-language amendment at `docs/specs/fcis_fee_credit_language_v2.md`. Acceptance condition: The specification and implementations choose one rule; all batch, migration, and parity tests agree and the historical witness has the declared versioned outcome.

**Dependencies/coupled gates:** `A-09`, `A-04`.

**Explicit nonclaims:** Moving a rejection to an earlier phase is still an accepted-language change.

### A-12 — Same-candidate apportionment publication

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Final P4B5A transition and shell boundary.

**Exact safety claim**

Exact fee witnesses, allocator pre-state, validated policy, allocation result, successor allocator state, net alias-aware balance patch, receipt, replay/nullifier updates, commit evidence, and outbox obligations share one candidate identity and publish atomically against the same store-current pre-root.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable reference substrate | `ZDX-M5-REFERENCE` | docs/research/FCIS_M5_IMPLEMENTOR_NOTES_20260725.md — selected design | M5 V1 binds patch/plan/receipt/replay/outbox to one candidate and models expected-pre-root atomic reference publication. |
| Reusable generic substrate | `ZFCIS-RC-HEAD` | docs/CANDIDATE_COMMIT_BOUNDARY.md — candidate and commit boundary | ZenoFCIS candidate identity and nominal authority separate structural consistency from production publication authority. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The P4B5A pure transition and every prerequisite gate are exact. | Closed P4B5A transition program. | Authenticated state/command/context/configuration. | Not implemented. | **GAP** |
| `A2` Candidate identity commits every semantic and publication artifact, including policy/cursor lineage. | Controlled candidate/decision/bundle builder. | Exact transition outputs. | Generic substrate exists; P4B5A-specific codec/fields absent. | **GAP** |
| `A3` The shell consumes nominal authorization, never raw bundle data. | Catalog/deployment authority adapter. | Pinned program, laws, provider, and policy. | ZenoFCIS generic implementation exists; no ZenoDEX adapter. | **GAP** |
| `A4` The datastore transaction publishes the complete exact row set or none. | Transactional commit port with fault injection and history reauthorization. | Authoritative datastore. | Generic SQLite adapter exists; no ZenoDEX mount. | **GAP** |

**Authenticated source relation — `GAP`:** Nominal authorization composes deployment policy, exact authenticated inputs, law evaluation, and candidate. Current evidence: No P4B5A nominal authorization value is produced.

**Current-state and commit relation — `GAP`:** Expected root/version is rechecked at one datastore linearization point; state and all artifacts are one atomic set. Current evidence: Reference model only in ZenoDEX; generic SQLite substrate unmounted.

**Minimized counterexample `A12-CE-PARTIAL`**

Publishing balances before cursor/history/outbox duplicates or loses fee allocation after crash. Minimal witness: State balance credits commit; cursor update does not. Retry sees old cursor and allocates the same rounding entitlement again. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- M5 reference stale/crash/no-publication tests.
- ZenoFCIS generic SQLite fault points and exact outbox-row tests.

Missing:
- P4B5A exact bundle codec and project laws.
- Mounted ZenoDEX commit adapter.
- Crash after every statement/flush boundary.
- Concurrent competing allocation commits.
- Reopen/replay verification from authorized genesis.

**Smallest closing artifact:** P4B5A authorized transition plus datastore adapter at `crates/zeno-fcis-adapter-zenodex/src/p4b5a.rs`. Acceptance condition: One nominal P4B5A authorization reaches the sole commit port; all state/evidence/outbox rows publish atomically and every injected crash/retry preserves exactly-once semantic allocation.

**Dependencies/coupled gates:** `A-03`, `A-04`, `A-05`, `A-06`, `A-07`, `A-08`, `A-09`, `A-10`, `A-11`, `D-05`.

**Explicit nonclaims:** Reference atomicity is not production datastore linearizability or durability.

## P4B5B — nonce policy and authorization state machine

### B-01 — Strict-successor nonce classifier

**Status:** `PROVED`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow theorem/proof claim is discharged at a pinned source; runtime authority, current-state, refinement, and publication remain separate dependent gates.
**Scope:** Heap-free arithmetic core after sender canonicalization and nonce-range admission.

**Exact safety claim**

For all u64 `last` and `sequence`, the classifier is total and returns `Accept` iff `sequence-last=1`; otherwise it returns exactly duplicate for equality, stale for less-than, or gap for difference greater than one, without overflow at `u64::MAX`.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Kani proof on runtime code | `ZDX-NONCE-KANI` | rust-runtime/crates/zenodex-runtime-core/src/replay_guard.rs — classify_sequence; kani_contracts | Totality, accept-iff-strict-successor, exact reject-code partition, and non-vacuity on the actual heap-free classifier. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Sender canonicalization and nonce-domain validation occur before the classifier. | Closed canonical sender and nonce admission wrapper. | Authenticated canonical command bytes. | Wrapper tests exist; authenticated principal binding is not closed. | **GAP** |
| `A2` The supplied `last` is the authoritative previous accepted nonce for that principal and policy domain. | Store-current nonce table lookup under an authority-bound policy/domain. | Authenticated current state. | No mounted M5/M6 current-state adapter. | **GAP** |
| `A3` On acceptance, the wrapper records `new_last = sequence` and does not alter another principal. | Pure replay-guard state transition and per-sender map update. | Exact immutable replay state. | Python/Rust implementation and tests exist in the legacy/shadow surface. | **TESTED** |

**Authenticated source relation — `GAP`:** Not part of the arithmetic proof; the wrapper must bind the canonical sender to the authenticated principal. Current evidence: Current tests canonicalize sender strings but do not establish full protocol authentication.

**Current-state and commit relation — `GAP`:** The theorem classifies one pair only; state lookup and update must be same-candidate and atomically published. Current evidence: No production relation follows from the Kani harness.

**Minimized counterexample `B01-CE-LAST-PLUS-ONE`**

Computing `last+1` can overflow even though strict-successor classification is total. Minimal witness: last=u64::MAX; an implementation evaluates `last+1` before comparing and traps/wraps. The repaired classifier subtracts only after `sequence>last`. Source: `ZDX-NONCE-KANI`.

**Executable evidence**

Existing:
- Kani 4 harnesses over all u64; Rust proptests; Python/Rust reject-code differential.

Missing:
- Pin and rerun Kani in the aggregate release workflow.
- Connect wrapper preconditions to nominal authenticated command and store-current state witnesses.

**Smallest closing artifact:** aggregate proof receipt at `docs/research/FCIS_M6_NONCE_CLASSIFIER_PROOF_RECEIPT.json`. Acceptance condition: Exact source/toolchain Kani evidence is replayed and the wrapper-to-proof preconditions are separately discharged.

**Dependencies/coupled gates:** `F-01`.

**Explicit nonclaims:** Does not authenticate the sender, prove the nonce table current, or publish the update atomically.

### B-02 — Authenticated principal-to-nonce-key binding

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Every command protected by nonce/replay policy.

**Exact safety claim**

The nonce key is derived canonically from the authenticated principal and policy domain covered by the exact command authentication; request fields, aliases, display strings, or shell-selected identities cannot redirect the lookup or update.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Authentication verifies the exact canonical command bytes and identifies one principal. | Nominal command authenticator. | Pinned key/signature policy and canonical bytes. | No aggregate M5/M6 authenticator. | **GAP** |
| `A2` Principal canonicalization is injective within the policy domain. | Closed principal codec/key derivation with collision/alias vectors. | Authority-owned principal schema. | Legacy canonicalization tests exist; no formal or exhaustive alias evidence. | **GAP** |
| `A3` The nonce-key derivation commits chain/deployment, command family, and policy version where required. | State-bound nonce policy descriptor. | Current authority state/profile. | Absent. | **GAP** |
| `A4` The command cannot carry a separately swappable sender used only by the nonce table. | Command schema and structural checker requiring one source of principal truth. | Closed command registry. | No whole-runtime checker. | **GAP** |

**Authenticated source relation — `GAP`:** Signature/verifier result plus deployment policy; never the untrusted sender field alone. Current evidence: Current replay guard accepts a sender input after format canonicalization; authority remains Python and is not M5-mounted.

**Current-state and commit relation — `GAP`:** Same derived key must identify the store-current lookup, candidate update, receipt, replay record, and persisted row. Current evidence: No end-to-end key-lineage evidence.

**Minimized counterexample `B02-CE-SWAP-SENDER`**

Authentication and nonce accounting use different sender fields. Minimal witness: Signature authenticates principal A, but wrapper passes an alias/caller field B into replay guard, consuming B's nonce while executing A's authority. Source: `ZDX-NONCE-KANI`.

**Executable evidence**

Existing:
- Legacy invalid-sender and sender-before-nonce precedence tests.

Missing:
- Signature-to-principal-to-key integration vectors.
- Alias/canonicalization collision corpus.
- Field-substitution mutation tests across command, receipt, replay update, and persisted row.
- Cross-language key-byte parity.

**Smallest closing artifact:** nominal authenticated replay key at `crates/zeno-fcis-adapter-zenodex/src/replay_key.rs`. Acceptance condition: Only the command authenticator can mint the principal/domain replay key, and that exact key is carried through lookup, decision, receipt, and commit.

**Dependencies/coupled gates:** `F-02`.

**Explicit nonclaims:** Syntactic sender validity is not authentication.

### B-03 — Nonce domain, range, policy version, and cross-language parity

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Python authority, Rust runtime/shadow, proof guests, migrations, and stored nonce state.

**Exact safety claim**

Every implementation admits the same nonce integer domain, missing-key initial value, strict-successor policy, rejection precedence, key canonicalization, and state-root encoding under an explicit version; out-of-domain values fail before state access.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Drift witness | `ZDX-NONCE-DRIFT` | commit evidence for state-root shadow — SR-DRIFT-001 | Documents Python rejection and Rust acceptance for nonce values at or above 2^32 before promotion. |
| Narrow repair/proof | `ZDX-NONCE-KANI` | rust-runtime/crates/zenodex-runtime-core/src/replay_guard.rs — classify_sequence and differential tests | Classifier proof over u64 plus wrapper-level parity tests over the intended u32 domain. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The protocol nonce domain and initial-value rule are explicitly versioned. | State/profile schema and nonce-policy binding. | Current authority state. | No M5/M6 state-bound policy type. | **GAP** |
| `A2` All decoders reject values outside that domain before normalization or root calculation. | Canonical bounded command and state decoders. | Raw command/state bytes. | Partial replay-guard checks; state-root drift proves incomplete closure. | **GAP** |
| `A3` Python, Rust, proof guests, and migration tooling encode the same key/value bytes. | Shared golden vectors and strict codecs. | Exact schema/version/domain separator. | No full proof-guest or migration corpus. | **GAP** |
| `A4` Rejection phase and code precedence are identical. | Whole-wrapper differential and negative vectors. | Same canonical inputs. | Narrow five-code parity exists; whole ingress/state path is open. | **GAP** |

**Authenticated source relation — `GAP`:** Nonce policy version is selected by authenticated current state/deployment, not by request or runtime mode. Current evidence: No nominal policy binding.

**Current-state and commit relation — `GAP`:** Stored nonce bytes/root/history must state their policy version; migrations must not reinterpret old values silently. Current evidence: No authorized migration/history relation.

**Minimized counterexample `B03-CE-U32`**

A shared randomized test domain hides divergent larger-domain behavior. Minimal witness: nonce=2^32: Python rejects due to u32 nonce-table bound; the Rust state-root shadow accepted before the drift was recorded. Source: `ZDX-NONCE-DRIFT`.

**Executable evidence**

Existing:
- Five-code Python/Rust replay-guard parity and Kani core proof.

Missing:
- Exact schema/version decision.
- Golden vectors at 0,1,2^32-1,2^32,2^64-1 and malformed encodings.
- State-root, proof-guest, and migration parity.
- Mutation restoring the documented divergence.

**Smallest closing artifact:** nonce policy v2 schema and vector packet at `tests/fixtures/fcis_nonce_policy_v2_golden.json`. Acceptance condition: Every implementation and stored-history decoder agrees byte-for-byte at domain boundaries and the SR-DRIFT-001 mutant fails.

**Dependencies/coupled gates:** `B-01`, `B-02`, `F-06`.

**Explicit nonclaims:** A proof over a wider arithmetic type does not select the protocol's admitted input domain.

### B-04 — Pure per-principal replay-state transition

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reference Python/Rust replay-guard function, not runtime authority.

**Exact safety claim**

Given an exact immutable replay table, canonical principal key, and admitted nonce, the pure guard either returns a typed rejection with unchanged state or returns a new table differing only at that key with value equal to the strict successor.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Runtime implementation and tests | `ZDX-NONCE-KANI` | rust-runtime/crates/zenodex-runtime-core/src/replay_guard.rs — admit | Actual Rust `admit` calls the proved classifier, sets `new_last=sequence`, and retains proptest/differential evidence. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The replay table is exact, immutable, and contains at most one value per canonical key. | Owned replay-state constructor/decoder. | Exact pre-state replay table. | Legacy Python/Rust tables exist; M5 exact committed-state integration is absent. | **GAP** |
| `A2` The key and nonce passed the authenticated admission gates. | Nominal authenticated replay key and nonce-policy admission. | Authenticated command and state-bound policy. | Open. | **GAP** |
| `A3` Map update preserves all other keys and canonical ordering/root semantics. | Persistent/owned map update and state-root differential. | Replay table schema. | Proptests/differentials provide bounded evidence. | **TESTED** |

**Authenticated source relation — `GAP`:** Outside the narrow pure function; caller-supplied sender remains insufficient. Current evidence: No nominal authority.

**Current-state and commit relation — `GAP`:** The returned table is a candidate value only and must be bound to exact pre-state and atomically committed. Current evidence: Authority unchanged (`python_authority`) at the proof commit.

**Minimized counterexample `B04-CE-CROSS-KEY`**

An in-place/shared map update changes another principal or the pre-state. Minimal witness: Replay table shares mutable storage; accepting A:2 mutates the object retained as pre-state or accidentally overwrites B's entry. Source: `ZDX-NONCE-KANI`.

**Executable evidence**

Existing:
- Rust proptests for replay invariants and Python/Rust differential corpus.

Missing:
- Transitive ownership/alias tests in the final committed-state type.
- Exact state-root update vectors.
- Proof or exhaustive finite check of per-key frame property for generated map update.

**Smallest closing artifact:** owned replay-state adapter at `crates/zeno-fcis-adapter-zenodex/src/replay_state.rs`. Acceptance condition: The pure guard consumes/returns exact owned replay state, passes alias/frame mutants, and refines the canonical state-root representation.

**Dependencies/coupled gates:** `B-01`, `B-02`, `B-03`, `F-03`.

**Explicit nonclaims:** The tested pure guard is not mounted authority and does not establish store currentness.

### B-05 — Store-current nonce lookup and stale-candidate rejection

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Runtime evaluation and publication.

**Exact safety claim**

The `last` nonce used by the transition comes from the same exact store-current pre-state named by the candidate's expected root/version; publication rechecks that root/version, so two candidates cannot both advance the same principal from one predecessor.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Pure CAS theorem | `ZDX-LEAN-LEDGER` | lean-mathlib/Proofs/DeterministicParallelExecution.lean — commit_rejects_root_mismatch; commit_accepts_root_match | Abstract commit rejects root mismatch and accepts exact root equality. |
| Reference implementation | `ZDX-M5-REFERENCE` | src/integration/fcis_atomic_commit_reference.py — reference commit interpreter | Reference expected-pre-root compare-and-swap and replay compare-and-replace validation. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The evaluated pre-state is a nominal store-current snapshot. | Transactional current-state read/open. | Reauthorized authoritative datastore. | No ZenoDEX production adapter. | **GAP** |
| `A2` The candidate binds exact expected pre-root/version and prior nonce value. | Controlled candidate/replay-update builder. | Pure transition outputs and exact pre-state. | M5 reference supports generic compare-and-replace; nonce-specific adapter absent. | **GAP** |
| `A3` The commit port compares current root/version and replay precondition at one linearization point. | Production transaction/CAS. | Datastore current row and candidate. | Reference only; generic ZenoFCIS SQLite substrate unmounted. | **GAP** |

**Authenticated source relation — `GAP`:** Current state derives from authorized genesis and reauthorized history. Current evidence: Generic ZenoFCIS model exists; ZenoDEX unmounted.

**Current-state and commit relation — `GAP`:** Evaluation root and commit comparison must refer to the same state domain/version; failure publishes no state, receipt, replay, or outbox. Current evidence: Not established in production.

**Minimized counterexample `B05-CE-DOUBLE-ACCEPT`**

Two concurrent commands read the same last nonce and both appear valid. Minimal witness: last=7; two workers evaluate nonce=8. Without expected-root/version CAS, both commits can report acceptance or duplicate side effects. Source: `LIT-LINEARIZABILITY`.

**Executable evidence**

Existing:
- M5 reference stale-root and replay compare-and-replace tests.
- ZenoFCIS generic SQLite uniqueness/CAS/fault tests.

Missing:
- Mounted transactional snapshot/CAS.
- Two-process same-principal race tests.
- Linearization trace comparison to the reference model.
- No-partial-row verification on stale failure.

**Smallest closing artifact:** nonce-aware commit-port refinement at `crates/zeno-fcis-adapter-zenodex/src/nonce_commit.rs`. Acceptance condition: Concurrent candidates from one predecessor yield exactly one commit; the loser returns stale/replay failure with no publication.

**Dependencies/coupled gates:** `B-04`, `D-05`.

**Explicit nonclaims:** A pure equality lemma does not prove a database comparison is linearizable.

### B-06 — Same-candidate replay update and receipt binding

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** M5 reference substrate and eventual ZenoDEX transition.

**Exact safety claim**

Every accepted or committed-failure nonce transition carries one exact compare-and-replace replay update bound to the candidate, receipt, authorization, and bundle; ordinary rejection carries none; substituting key, old/new nonce, order, or candidate invalidates the bundle.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reference implementation | `ZDX-M5-REFERENCE` | docs/research/FCIS_M5_COMPLETION_RECEIPT_V1.json — completed_capabilities | Reports replay compare-and-replace validation against pre-state/successor, per-bundle replay batches, and same-candidate substitution rejection. |
| Reusable generic boundary | `ZFCIS-RC-HEAD` | docs/CANDIDATE_COMMIT_BOUNDARY.md — candidate and commit boundary | Replay identity and complete bundle must match for idempotent replay. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The pure transition is the sole producer of replay updates. | Closed nonce transition program. | Exact authenticated invocation and pre-state. | Pure legacy guard exists; M5 adapter absent. | **GAP** |
| `A2` Candidate identity commits exact replay update bytes and ordering. | Controlled candidate builder. | Transition result. | M5 reference implementation tested. | **TESTED** |
| `A3` Receipt/bundle strict decoding reconstructs the same candidate. | Strict receipt/bundle decoder and same-candidate validation. | Canonical artifact bytes. | ZenoFCIS generic implementation tested; ZenoDEX codec absent. | **GAP** |

**Authenticated source relation — `GAP`:** Replay key/identity comes from nominal authenticated invocation, not caller-selected fields. Current evidence: No ZenoDEX nominal authorization.

**Current-state and commit relation — `GAP`:** Replay update persists in the same atomic transaction as state/receipt/outbox. Current evidence: Reference construction only.

**Minimized counterexample `B06-CE-SUBSTITUTE`**

A valid successor state is paired with a replay update from another command. Minimal witness: Candidate state reflects A:8, but bundle replay update records B:8 or old=6; state root may still look valid while anti-replay history diverges. Source: `ZDX-M5-REFERENCE`.

**Executable evidence**

Existing:
- M5 artifact-substitution and repeated-account replay-batch tests.
- ZenoFCIS strict bundle/replay reconstruction tests.

Missing:
- ZenoDEX nonce candidate/receipt/bundle codecs.
- Cross-language substitution vectors.
- Project law requiring exact nonce-state/replay-row equality.

**Smallest closing artifact:** ZenoDEX replay-update adapter at `crates/zeno-fcis-adapter-zenodex/src/replay_artifacts.rs`. Acceptance condition: Exact nonce transition output seals into the generic candidate without field copying; every key/value/order substitution fails strict reconstruction.

**Dependencies/coupled gates:** `B-04`, `F-04`.

**Explicit nonclaims:** Same-candidate structural consistency is not current-state or publication authority.

### B-07 — Atomic nonce, state, receipt, history, and outbox publication

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Production datastore transaction.

**Exact safety claim**

A committing nonce decision publishes the complete successor semantic state, nonce/replay row, authorization, receipt, bundle, history record, and exact outbox set in one durable atomic transaction; stale, invalid, duplicate, gap, or pre-commit crash publishes none.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Generic tested substrate | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Atomic set and failure model | One `BEGIN IMMEDIATE` transaction writes semantic state, authorization, bundle, receipt, replay, and exact outbox rows with injected pre/post-commit crash tests. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The input is a nominal authorized nonce transition, not a raw bundle. | ZenoDEX catalog authority and nonce program/law adapter. | Authenticated invocation, current state, candidate, policy. | Absent. | **GAP** |
| `A2` The database schema constrains candidate/replay/version uniqueness and complete row membership. | Pinned SQLite schema/transaction adapter or another proved port. | Authoritative store. | Generic schema exists; not mapped to ZenoDEX state/nullifier semantics. | **GAP** |
| `A3` Commit/durability settings and filesystem behavior satisfy the qualified deployment assumptions. | Deployment qualification and fault testing. | Pinned SQLite/rusqlite/VFS/filesystem/configuration. | No ZenoDEX deployment evidence. | **GAP** |

**Authenticated source relation — `GAP`:** Only private nominal authorization accepted by the commit port. Current evidence: Generic API has this property; no ZenoDEX producer.

**Current-state and commit relation — `GAP`:** One durable linearization point; replay after post-commit crash returns same complete result and pending outbox. Current evidence: Generic bounded tests only; no mounted ZenoDEX evidence.

**Minimized counterexample `B07-CE-NONCE-ONLY`**

Nonce row commits separately from economic state or receipt. Minimal witness: Nonce advances to 8, then process crashes before balance/state commit. Retry is rejected as duplicate although the requested transition never published completely. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- ZenoFCIS generic seven-point fault-injection tests and exact row-set validation.

Missing:
- ZenoDEX schema mapping and project laws.
- Crash at every SQL statement/commit boundary.
- Power-loss/durability configuration qualification.
- Reopen/reexecute exact-history test including nonce rows.
- Concurrent process race test.

**Smallest closing artifact:** mounted transactional nonce port at `crates/zeno-fcis-adapter-zenodex/src/sqlite_nonce.rs`. Acceptance condition: Fault and concurrency evidence shows every nonce commit is all-or-none with the full semantic candidate, and reopen reconstructs exactly.

**Dependencies/coupled gates:** `B-05`, `B-06`, `D-05`.

**Explicit nonclaims:** Database transaction tests do not prove external delivery exactly once.

### B-08 — Concurrent ordering, retry, and rejection stability

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Multiple principals, same-principal races, batch execution, retries, and recovery.

**Exact safety claim**

The protocol defines a canonical logical order and stable offending-command/rejection precedence; same-principal conflicts serialize or reject deterministically, independent principals may commute only under proved footprints, and retry/recovery cannot change an accepted decision into a different semantic effect.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` One canonical command ordering and error precedence are protocol values. | Batch/profile specification and transition program. | Authenticated ordered batch bytes. | No M6 batch-order publication spec. | **GAP** |
| `A2` Same-principal nonce operations conflict in the declared footprint. | Complete read/write/replay-key footprint. | Authority-bound component witness. | No ZenoDEX complete footprint. | **GAP** |
| `A3` Independent-principal execution is allowed only with complete noninterference evidence. | Deterministic-parallel authorization or sequential fallback. | Pinned scheduler/composition spec. | Absent. | **GAP** |
| `A4` Retry identity is candidate/invocation bound and distinguishes pre-commit from post-commit outcomes. | Transactional history/outbox replay protocol. | Persisted exact authorization/bundle rows. | Generic ZenoFCIS model exists; unmounted. | **GAP** |

**Authenticated source relation — `GAP`:** Command order and retry identity are authenticated/bound, not selected by worker completion order. Current evidence: No complete authority chain.

**Current-state and commit relation — `GAP`:** Commit history determines post-crash answer; no partial acceptance or ambiguous duplicate response. Current evidence: No ZenoDEX durable history.

**Minimized counterexample `B08-CE-WORKER-ORDER`**

Physical worker completion order changes which duplicate/gap error is reported. Minimal witness: Batch contains A:8 and A:9 from last=7; executing 9 first rejects gap, executing 8 first can accept both sequentially. Without a canonical logical order, outcome differs. Source: `ZDX-LEAN-LEDGER`.

**Executable evidence**

Existing:
- Narrow replay-guard deterministic tests.

Missing:
- Canonical batch-order and precedence vectors.
- Same-principal conflict-graph tests.
- Parallel-vs-sequential exact normalized-decision differential.
- Crash/retry response detectability tests.

**Smallest closing artifact:** nonce concurrency semantics packet at `docs/research/FCIS_M6_NONCE_CONCURRENCY_V1.md`. Acceptance condition: Canonical order, conflict rules, and retry outcomes are executable and all schedule permutations normalize to the specified result.

**Dependencies/coupled gates:** `B-03`, `B-05`, `F-05`, `F-06`.

**Explicit nonclaims:** Thread safety alone does not imply deterministic protocol order.

### B-09 — Nonce bootstrap, migration, and historical-policy continuity

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Genesis, account/key migration, policy-version changes, and schema upgrades.

**Exact safety claim**

Initial nonce state is policy-authorized; migration maps every old principal/key/value exactly once into the new domain, preserves consumed-nonce history or explicitly proves a safe reset rule, records migration nullifiers, and never silently interprets old bytes under a new policy.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Generic genesis/history substrate | `ZFCIS-RC-HEAD` | docs/GENESIS_AUTHORIZATION.md — policy-bound genesis | Authorized genesis is policy/root/law bound and reopen accepts no replacement initial state. |
| Generic migration posture | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Schema v5 and migration nonclaims | Older schemas are rejected rather than implicitly reinterpreted. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Genesis nonce policy and empty/default table are covered by the deployment policy and laws. | Catalog-authorized ZenoDEX genesis and nonce laws. | Reviewed genesis source/configuration. | Generic substrate only. | **GAP** |
| `A2` The old and new principal/key/domain codecs are pinned. | Versioned codecs and migration manifest. | Pinned release/deployment authority. | Absent. | **GAP** |
| `A3` Migration input is the exact store-current predecessor and each source entry is consumed once. | Authorized migration transition and nullifier set. | Store-current state and verified manifest. | Absent. | **GAP** |
| `A4` Post-migration history/replay identity is continuous and recoverable after crash. | Transactional migration commit plus reopen validation. | Authoritative datastore/history. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment/migration verifier selects exact source/target policies; caller cannot request a reset. Current evidence: No ZenoDEX nonce migration authority.

**Current-state and commit relation — `GAP`:** Migration is one expected-root transaction and persists exact predecessor/successor/history/nullifier evidence. Current evidence: No implementation.

**Minimized counterexample `B09-CE-RESET`**

Schema upgrade initializes a fresh nonce table while preserving command authority. Minimal witness: Previously consumed nonce 7 is forgotten; attacker replays signed command with nonce 1 after migration and it is accepted as a fresh strict successor. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- Generic ZenoFCIS genesis tamper and unsupported-schema rejection tests.

Missing:
- ZenoDEX nonce-genesis law.
- Versioned old/new key vectors.
- One-to-one migration and duplicate/omission tests.
- Crash/retry/reopen evidence.
- Replay of pre-migration signed commands against post-migration state.

**Smallest closing artifact:** nonce migration state machine at `crates/zeno-fcis-adapter-zenodex/src/nonce_migration.rs`. Acceptance condition: Authorized migration preserves exact anti-replay semantics, is crash-atomic, and all reset/duplicate/omission mutants fail.

**Dependencies/coupled gates:** `B-02`, `B-03`, `D-01`, `D-04`, `M6-07`.

**Explicit nonclaims:** Rejecting old schemas is safe fail-closed behavior but not a completed migration.

## P4B5C — evidence recomputation and implementation refinement

### C-01 — Strict canonical receipt, bundle, authorization, and proof-artifact admission

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reusable ZenoFCIS artifact boundary; downstream ZenoDEX codecs must refine it.

**Exact safety claim**

Persisted or transported authority artifacts are accepted only after bounded complete decoding, private smart-constructor reconstruction, identity/root recomputation, and byte-for-byte canonical re-encoding; raw hashes or decoded mappings cannot directly create nominal authority.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/STRICT_ARTIFACT_AND_SQLITE_HISTORY.md — Inputs and outputs; laws 1-3 | Strict receipt/bundle/authorization decoding, reconstruction, and exact re-encoding. |
| Reusable proof-context implementation | `ZFCIS-RC-HEAD` | docs/AUTHENTICATED_PROOF_CONTEXT.md — Persisted proof bytes | Strict sparse-proof decoder with fixed depth, complete consumption, and canonical reconstruction. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Explicit byte and nested-component limits are supplied before allocation. | Strict artifact decoders. | Untrusted persisted/network bytes. | Implemented and tested in ZenoFCIS. | **TESTED** |
| `A2` Every identity is recomputed from reconstructed canonical content. | Candidate/receipt/bundle/authorization builders and approved commitment provider. | Canonical reconstructed values. | Implemented and substitution-tested. | **TESTED** |
| `A3` Nominal authority types have private constructors and no raw-decoder conversion. | Rust visibility/type boundary and compile-fail tests. | Library public API. | Implemented in ZenoFCIS; ZenoDEX adapters must not bypass it. | **TESTED** |
| `A4` Decoder schema/version/domain separators equal the mounted authority profile. | Deployment-owned exact profile/schema/provider binding. | Mounted catalog/authority. | Generic support exists; ZenoDEX binding absent. | **GAP** |

**Authenticated source relation — `IMPLEMENTED`:** Canonical decoding creates data, not authority; later reauthorization is mandatory. Current evidence: ZenoFCIS enforces this distinction generically.

**Current-state and commit relation — `GAP`:** Decoded artifacts cannot publish; only nominal reauthorization against current state may reach a commit port. Current evidence: Generic API enforces it; no ZenoDEX producer/mount.

**Minimized counterexample `C01-CE-HASH-SHAPED`**

A database row with correctly sized nonzero hashes is treated as valid evidence without reconstructing content. Minimal witness: Attacker changes bundle payload and recomputes row-local hash while leaving an internally plausible candidate/receipt row set. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS truncated/trailing/unknown-tag/noncanonical/over-limit/substitution tests and compile-fail authority tests.

Missing:
- ZenoDEX exact receipt/bundle/proof codecs and decoder limits.
- Cross-language malformed-input and rejection-precedence corpus.
- Structural checker proving no direct deserialization into nominal types.

**Smallest closing artifact:** ZenoDEX strict artifact codec adapter at `crates/zeno-fcis-adapter-zenodex/src/artifacts.rs`. Acceptance condition: Every ZenoDEX persisted artifact strictly reconstructs through the generic smart constructors and no raw/hash-shaped bypass compiles or executes.

**Dependencies/coupled gates:** `F-01`.

**Explicit nonclaims:** Canonical bytes and nonzero hashes are bindings, not truth or authority.

### C-02 — Independent evidence provenance and trusted producer binding

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Formal certificates, golden vectors, state projections, runtime decisions, retained proof artifacts, and migration evidence.

**Exact safety claim**

Every evidence item is bound to the exact claim, source commit/tree, profile, schema, algorithm, toolchain/configuration, importer, verifier identity, coverage declaration, and artifact bytes; the authority independently selects the expected producer/verifier and does not infer provenance from self-declared metadata.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable law/evidence boundary | `ZFCIS-RC-HEAD` | docs/PROJECT_RELATIONAL_LAWS.md — Formal checker integration | Formal checker receives exact source/profile/schema/algorithm/claim/query/assumption/coverage/build bindings; indeterminate or missing tool grants no authority. |
| Pinned research evidence rule | `ZDX-RK-SYNTHESIS` | docs/research/ZENODEX_RK_MORPH_ESSO_SYNTHESIS_2026-07-21.md — Evidence binding rule | Pins exact tool repositories, source commits, runs, artifact digests, stable result hashes, and model fingerprints. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The expected source/build/tool/verifier identities are selected independently by release/deployment authority. | Release manifest and policy-bound authority setup. | Reviewed source/toolchain/verifier distribution. | No aggregate M6 release manifest or binary attestation. | **GAP** |
| `A2` Artifact bytes and manifests are complete, deletion-aware, and content-addressed. | Deterministic Git/artifact packet builder. | Committed Git objects and exact artifact bytes. | B1B packet tooling exists; P4B5A review found untracked evidence omission in an earlier packet. | **GAP** |
| `A3` The verifier checks the exact declared semantics and returns attested only on success. | Pinned evidence verifier adapter. | Exact retained artifact and claim subject. | ZenoFCIS trait exists; concrete ZenoDEX verifiers not selected/qualified. | **GAP** |
| `A4` A successful retained certificate never replaces fresh executable validation for a concrete invocation where required. | Runtime law/refinement/authentication adapter. | Current invocation and state. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Expected producer and verifier identities come from release/deployment policy, never the evidence envelope being checked. Current evidence: Framework exists; project-specific selection and attestation are absent.

**Current-state and commit relation — `GAP`:** Evidence may authorize a law/refinement witness only after exact runtime source/current-state bindings; it never writes state directly. Current evidence: No project composition.

**Minimized counterexample `C02-CE-SELF-ATTEST`**

Evidence declares its own verifier and source identity and is accepted because the hashes are nonzero. Minimal witness: Attacker generates a proof with a permissive verifier, stores that verifier's hash inside the envelope, and passes an equality check against the same envelope field. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- B1B deletion-aware packet/manifest tests.
- ZenoFCIS evidence substitution and indeterminate-verifier negative tests.

Missing:
- Aggregate source/toolchain/artifact manifest.
- Independent verifier selection and binary/build attestation.
- Deletion/rename/untracked-artifact mutation tests across all M5/M6 evidence.
- Fresh invocation-law evaluation after retained-proof verification.

**Smallest closing artifact:** M6 evidence provenance manifest and verifier policy at `docs/research/FCIS_M6_EVIDENCE_PROVENANCE_V1.json`. Acceptance condition: Every promoted proof/test/model artifact has exact independently selected provenance, complete bytes, a qualified verifier, and a declared nonclaim/coverage scope.

**Dependencies/coupled gates:** `C-01`.

**Explicit nonclaims:** A digest identifies bytes; it does not prove the tool, claim, or result is sound.

### C-03 — Persisted command and context reauthentication

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reusable ZenoFCIS SQLite/history boundary and eventual ZenoDEX reopen/replay.

**Exact safety claim**

On reopen or replay, persisted command and context bytes are treated as untrusted, strictly decoded, re-admitted through the authority-owned schema, reauthenticated by the current pinned provider/policy, and required to reproduce the exact canonical authorization bytes before history is usable.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/STRICT_ARTIFACT_AND_SQLITE_HISTORY.md — Inputs and outputs; laws 4-5 | Re-admits persisted command/context, executes the pinned transition/laws, and requires exact authorization-byte equality. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The authority still pins the exact compatible schema/provider/program/policy for the history being opened. | Policy-bound `CatalogCommitAuthority`/history opener. | Deployment identity and authorized genesis. | Implemented generically; no ZenoDEX catalog/program/policy. | **GAP** |
| `A2` Persisted bytes and decoder limits are exact and canonical. | Strict authorization decoder. | Untrusted database bytes. | Implemented/tested in ZenoFCIS. | **TESTED** |
| `A3` Authentication/replay identity is deterministic from retained inputs and policy. | Authority-owned invocation admission/authentication. | Persisted canonical invocation bytes. | Implemented for generic catalog invocations; ZenoDEX adapter absent. | **GAP** |

**Authenticated source relation — `GAP`:** Current mounted authority, not the database row, selects schema/provider/program/policy. Current evidence: Generic implementation has the boundary; project setup absent.

**Current-state and commit relation — `GAP`:** Only a completely reauthorized historical transition may contribute to reconstructed current state or pending delivery. Current evidence: Generic SQLite adapter tested; no ZenoDEX mount.

**Minimized counterexample `C03-CE-TRUST-ROW`**

Reopen trusts a persisted `authenticated=true` flag or authorization ID. Minimal witness: Attacker inserts command/context bytes for an unauthorized invocation and copies a nonzero authorization ID; history opens without recomputing authentication. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS authorization-byte tampering, policy substitution, and strict reopen tests.

Missing:
- ZenoDEX command/context authority adapter.
- Key/provider rotation compatibility policy.
- History vectors across every command family and rejection phase.
- Direct-database mutation tests under the ZenoDEX schema.

**Smallest closing artifact:** ZenoDEX history reauthentication adapter at `crates/zeno-fcis-adapter-zenodex/src/history_auth.rs`. Acceptance condition: Every historical invocation is freshly reauthenticated under the exact history policy and any byte/policy/provider substitution makes reopen fail closed.

**Dependencies/coupled gates:** `F-02`, `C-01`, `D-01`.

**Explicit nonclaims:** Reauthentication under a changed policy requires an explicit compatibility/migration decision; it is not automatic.

### C-04 — Persisted transition and project-law reexecution

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reusable history validation and eventual ZenoDEX evidence recomputation.

**Exact safety claim**

For each persisted committed transition, reopen reexecutes the exact pinned pure program and complete project-law set from the reconstructed predecessor and authenticated invocation; the resulting normalized decision, law observations, candidate, receipt, bundle, and successor must equal persisted artifacts exactly.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/STRICT_ARTIFACT_AND_SQLITE_HISTORY.md — laws 4-7 | Re-executes authority-owned transition and laws during persisted authorization re-entry. |
| Reusable project-law model | `ZFCIS-RC-HEAD` | docs/PROJECT_RELATIONAL_LAWS.md — laws 8-17 | Production authorization binds exact law-set verification and fresh invocation evaluation; missing/extra/indeterminate laws fail. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The exact historical transition program, catalog, laws, provider, schema, algorithm, and policy are available and pinned. | Versioned deployment/history policy and retained program/law artifacts. | Authorized genesis and release manifest. | Generic mechanism exists; ZenoDEX aggregate artifacts not defined. | **GAP** |
| `A2` Predecessor state is the exact result of prior reauthorized history. | Gap-free history fold from authorized genesis. | Strict persisted rows. | Generic SQLite implementation tested. | **TESTED** |
| `A3` Reexecution is deterministic, bounded, and free of ambient inputs. | Pure ZenoDEX transition/law engine. | Canonical pre-state/command/context. | Complete program and laws remain open. | **GAP** |
| `A4` Every project law applicable to the decision appears exactly once and reports satisfied. | Verified project-law manifest and deterministic law engine. | Exact catalog/value-flow classifications. | ZenoFCIS framework exists; ZenoDEX law manifest incomplete. | **GAP** |

**Authenticated source relation — `GAP`:** History policy selects exact executable semantics; stored candidate does not select its own interpreter. Current evidence: No project policy/program binding.

**Current-state and commit relation — `GAP`:** Reexecution result must equal every persisted row and successor before the store is declared current. Current evidence: Generic adapter implements this; no ZenoDEX mapping.

**Minimized counterexample `C04-CE-ROOT-ONLY`**

Reopen checks only that each stored successor root links to the next predecessor root. Minimal witness: Attacker constructs internally linked state roots and bundle hashes that were never produced by the authorized transition or laws. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS strict history reconstruction and law-observation negative tests.

Missing:
- Complete ZenoDEX law manifest derived from all value-moving effects/channels.
- Historical program/version retention strategy.
- End-to-end reexecution corpus across all decisions.
- Mutation of one law, algorithm, or rejection order causing reopen failure.

**Smallest closing artifact:** ZenoDEX replayable program/law package at `docs/research/FCIS_M6_REEXECUTION_POLICY_V1.json`. Acceptance condition: Authorized genesis plus each historical version has a pinned executable program/law package; exact reexecution reconstructs all artifacts or fails closed.

**Dependencies/coupled gates:** `C-03`, `F-04`, `Z-06`.

**Explicit nonclaims:** Exact reexecution proves equality with one implementation, not an unbounded theorem that the implementation satisfies every intended law.

### C-05 — Exact persisted candidate row-set equality

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** State, authorization, receipt, bundle, replay/nullifier, commit evidence, and outbox rows.

**Exact safety claim**

A persisted candidate is usable only if every required row exists exactly once, no extra row exists, all canonical bytes reconstruct one authorized candidate, every outbox entry is an exact member, and the row set agrees with the reexecuted decision.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/STRICT_ARTIFACT_AND_SQLITE_HISTORY.md — laws 5-9 | Requires exact authorization/bundle/receipt/replay/outbox equality, one required row each, no extras, and exact pending membership. |
| Reusable SQLite evidence | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Replay and delivery | Candidate, authorization, version, and ordinal uniqueness plus complete bundle/outbox reconstruction. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The canonical bundle defines the complete required row set. | Strict bundle decoder and candidate authorization. | Canonical bundle bytes. | Implemented generically. | **TESTED** |
| `A2` Database schema/queries cannot silently omit duplicates or extra rows. | Pinned schema, uniqueness constraints, exact enumeration queries, and checked conversions. | Authoritative datastore. | Implemented in generic SQLite schema v5; ZenoDEX schema mapping absent. | **GAP** |
| `A3` Row-local hashes are insufficient; complete candidate reconstruction is performed. | History validator compares entire rows to reexecuted candidate. | Reauthorized history. | Implemented generically. | **TESTED** |

**Authenticated source relation — `IMPLEMENTED`:** Only reauthorized candidate identity determines expected rows. Current evidence: Generic implementation.

**Current-state and commit relation — `GAP`:** Exact row-set validation is required before snapshot, replay success, pending delivery, or acknowledgement. Current evidence: Generic implementation tested; no ZenoDEX port.

**Minimized counterexample `C05-CE-EXTRA-OUTBOX`**

Attacker inserts an extra value-moving outbox row with a valid row-local hash. Minimal witness: State/receipt/bundle remain unchanged; delivery query sees an extra destination/payload unless complete bundle membership is checked. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS missing/extra outbox, changed destination/payload with recomputed hash, redundant bundle change, and candidate substitution tests.

Missing:
- ZenoDEX exact schema and row mapping.
- Project-specific nullifier/history/effect rows included in the complete set.
- Direct SQL mutation/fuzz corpus.
- Query-plan/index changes cannot alter complete enumeration semantics.

**Smallest closing artifact:** ZenoDEX persisted-row schema contract at `docs/specs/fcis_m6_sqlite_schema_v1.sql`. Acceptance condition: Schema and validator enumerate the exact project row set; every missing/extra/substituted row causes reopen and delivery to fail closed.

**Dependencies/coupled gates:** `C-01`, `C-04`, `D-05`.

**Explicit nonclaims:** Foreign keys and row-local hashes alone do not prove complete candidate membership.

### C-06 — M4/M5 evaluator-to-normalized-decision refinement

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Legacy/current Python evaluator, exact M5 decision algebra, Rust runtime, and proof guest.

**Exact safety claim**

For every admitted ZenoDEX invocation, the existing evaluator's observable result strictly normalizes to the exact M5 candidate/decision/bundle defined by the reviewed pure transition, with no shell repair, dropped field, broadened acceptance, altered rejection precedence, or different effect/outbox semantics.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Recorded blocker | `ZDX-M5-REFERENCE` | docs/research/FCIS_M5_COMPLETION_RECEIPT_V1.json — open_mount_blockers | Lists the exact M4-evaluator-to-M5-decision adapter and Python/Rust M5 refinement as open mount blockers. |
| Reusable refinement framework | `ZFCIS-RC-HEAD` | docs/VALIDATED_REFINEMENT_AND_EXHAUSTIVE_COVERAGE.md — validated normalized decision | Strictly reconstructs model/runtime decisions before case comparison or promotion. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` A normative pure transition and exact M5 codecs exist for every promoted command. | Closed aggregate ZenoDEX transition program and codecs. | Pinned profile/schema/algorithm. | Incomplete. | **GAP** |
| `A2` Legacy/runtime outputs are imported only through strict artifact reconstruction. | ZenoDEX normalized-decision importer. | Runtime receipt/bundle bytes. | Generic importer exists; project adapter absent. | **GAP** |
| `A3` The comparison includes every observable artifact and rejection phase/order. | Exact differential harness. | Same canonical state/command/context. | Partial subsystem parity only. | **GAP** |
| `A4` Coverage is theorem-backed or exactly exhaustive for a reviewed finite domain; otherwise status remains sampled. | Mechanized refinement proof or canonical exhaustive manifest/verifier. | Reviewed domain definition. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Release authority pins normative and runtime implementations/importer/verifier; runtime cannot self-select the model. Current evidence: No aggregate binding.

**Current-state and commit relation — `GAP`:** Only a validated refined decision may enter nominal authorization/commit; disagreement fails closed with no state change. Current evidence: No mounted gate.

**Minimized counterexample `C06-CE-DROPPED-OUTBOX`**

Runtime and model agree on successor state but differ on an outbox obligation. Minimal witness: Both produce the same root; runtime omits one value-moving delivery or changes its destination. State-only differential reports success while economic behavior diverges. Source: `ZDX-LEAN-LEDGER`.

**Executable evidence**

Existing:
- Partial Python/Rust/OCaml subsystem differentials and ZenoFCIS generic substitution tests.

Missing:
- Exact M4→M5 adapter.
- Whole-result differential including state, error, patch, receipt, replay/nullifier, fees/residue, commit evidence, outbox, and public inputs.
- Proof-guest parity.
- Promotion policy binding validated results to nominal authorization.

**Smallest closing artifact:** exact evaluator refinement adapter at `crates/zeno-fcis-adapter-zenodex/src/refinement.rs`. Acceptance condition: Every promoted runtime result strictly reconstructs one M5 decision and exact whole-result parity passes; any mismatch blocks authorization.

**Dependencies/coupled gates:** `F-06`, `C-01`, `F-04`.

**Explicit nonclaims:** Matching successor roots or accept/reject bits is insufficient refinement.

### C-07 — Coverage truth for refinement and evidence recomputation

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Claims labeled proof, exhaustive, bounded, sampled, or mutation-tested.

**Exact safety claim**

Every promotion claim states its exact coverage semantics; bounded tests cannot masquerade as unbounded proof, duplicate case IDs cannot pad exhaustive cardinality, and exhaustive promotion requires exact manifest/case-set equality plus an independently verified coverage artifact.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/VALIDATED_REFINEMENT_AND_EXHAUSTIVE_COVERAGE.md — laws 4-9 | Canonical finite-domain manifests, exact case equality, independent coverage verification, and explicit empty-domain handling. |
| Reusable footprint rule | `ZFCIS-RC-HEAD` | docs/COMPLETE_FOOTPRINT_WITNESS.md — supported proof methods | No bounded-test proof method; only generated control flow, pinned static analysis, exhaustive finite enumeration, or independently checked theorem. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The finite domain definition and enumeration algorithm are reviewed protocol artifacts. | Project domain manifest. | Release authority and protocol specification. | No whole ZenoDEX finite-domain manifest; most domains are large/unbounded. | **GAP** |
| `A2` Input commitments are canonical, sorted, unique, and exactly equal to executed cases. | Deterministic enumerator and strict case importer. | Canonical inputs/results. | Generic framework implemented. | **TESTED** |
| `A3` The coverage verifier independently checks the exact artifact and claim. | Pinned coverage verifier. | Retained coverage artifact. | Trait exists; concrete verifier absent. | **GAP** |
| `A4` Unbounded domains require a theorem or remain explicitly bounded/sampled. | Lean/Kani/static proof or conservative status logic. | Exact source/toolchain. | Narrow proofs exist; whole runtime does not. | **GAP** |

**Authenticated source relation — `GAP`:** Release policy selects domain/enumerator/verifier; test generator cannot declare itself exhaustive. Current evidence: Generic model exists; project policy absent.

**Current-state and commit relation — `GAP`:** Coverage status affects promotion only, never directly publishes state. Current evidence: Generic framework enforces this; no ZenoDEX promotion path.

**Minimized counterexample `C07-CE-CARDINALITY`**

A report claims exhaustive coverage because case count equals a declared number. Minimal witness: Same canonical input is repeated under many caller-selected case IDs, satisfying cardinality while most domain members are absent. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS duplicate/missing/extra/noncanonical manifest and arbitrary-cardinality negative tests.

Missing:
- Per-gate coverage classification in CI.
- Exact finite manifests where truly finite.
- Lean/Kani/static artifacts for unbounded claims.
- Independent verifier policy and mutation tests.

**Smallest closing artifact:** coverage policy registry at `docs/research/FCIS_M6_COVERAGE_POLICY_V1.json`. Acceptance condition: Every matrix gate names a verified proof method or an exact bounded scope; CI rejects unsupported `PROVED`/`exhaustive` labels.

**Dependencies/coupled gates:** `C-02`, `C-06`.

**Explicit nonclaims:** Large randomized/property suites remain falsification evidence, not exhaustive proof.

### C-08 — Evidence recomputation at every authority-bearing use

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Evaluation, publication, reopen, pending-delivery read, acknowledgement, proof verification, and migration.

**Exact safety claim**

No authority-bearing operation trusts a previously computed validation flag, cached root, wrapper type, or row-local hash without revalidating/recomputing the exact object and rebinding it to the current authority context; hostile mutation or stale cache fails closed.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| B1B requirement | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md — owned values and alias boundary | Requires point-of-use semantic revalidation and publication repetition from independent sources. |
| Reusable SQLite requirement | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — trusted dependencies and bounds | Revalidates shell identity, cached reconstructed state, candidate row set, and exact bundle before replay/delivery/acknowledgement. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Every boundary has access to exact canonical bytes/object plus authority-owned expected bindings. | Boundary-specific nominal adapter. | Current authority plus untrusted/cached artifact. | Generic and narrow B1B patterns exist; no aggregate ZenoDEX map. | **GAP** |
| `A2` Revalidation traverses the complete nested graph and recomputes all load-bearing roots/identities. | Strict recursive validators and root builders. | Exact owned values. | M5/B1B hostile mutation tests exist; whole graph coverage open. | **GAP** |
| `A3` Caches are diagnostic/performance aids only and cannot bypass recomputation after reopen or mutation. | Store/reopen/delivery APIs that revalidate before use. | Persisted rows and cached state. | Generic ZenoFCIS SQLite implementation tested; no ZenoDEX port. | **GAP** |

**Authenticated source relation — `GAP`:** Expected context comes independently from mounted authority/current state. Current evidence: No aggregate implementation.

**Current-state and commit relation — `GAP`:** Revalidation must precede the linearization point and every post-commit delivery/ack read. Current evidence: Generic substrate only.

**Minimized counterexample `C08-CE-VALIDATED-THEN-MUTATED`**

A frozen wrapper is validated once but contains or references mutable nested content. Minimal witness: Configuration/proof/bundle root is checked; attacker mutates nested policy/destination; later code trusts a `validated=true` wrapper and reads changed fields. Source: `ZDX-M5-REFERENCE`.

**Executable evidence**

Existing:
- M5 hostile `frozen=True` bypass mutation tests; B1B carrier identity mutation tests; ZenoFCIS persisted-row tamper tests.

Missing:
- Boundary inventory proving every authority read calls exact revalidation.
- Mutation tests for every nested value and cached row.
- Static checker rejecting validation flags/casts as authority.
- Performance budget for repeated bounded validation.

**Smallest closing artifact:** authority-use revalidation map at `docs/research/FCIS_M6_REVALIDATION_MAP.json`. Acceptance condition: Every authority-bearing read has one declared recomputation function, expected-source producer, executable test, and no unchecked cache/flag path.

**Dependencies/coupled gates:** `C-01`, `C-02`, `F-03`.

**Explicit nonclaims:** A private constructor or frozen wrapper reduces attack surface but does not replace point-of-use validation.

## P4B5D — authenticated history, nullifiers, atomic persistence, and recovery

### D-01 — Policy-bound authorized genesis

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reusable ZenoFCIS genesis boundary; ZenoDEX project genesis remains to be defined.

**Exact safety claim**

An authoritative store can be created only from a nominal genesis authorization binding the exact initial state/root, reviewed source/configuration/evidence, unique deployment instance, catalog/profile/provider/state domain/execution policy, and complete genesis-applicable project-law evaluation; reopen accepts no replacement initial state.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/GENESIS_AUTHORIZATION.md — boundary and laws | Private `CatalogAuthorizedGenesis`, exact policy/root/law binding, one-time creation, and reopen without caller-supplied state. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The project owner truthfully selects the reviewed genesis source/configuration/evidence and deployment identity. | ZenoDEX release/deployment genesis policy. | Externally reviewed genesis materials. | No ZenoDEX M6 genesis policy artifact. | **GAP** |
| `A2` Every mandatory state invariant law applies at genesis and is evaluated exactly once. | Verified ZenoDEX law manifest and law engine. | Catalog/profile/value semantics. | Framework exists; project laws incomplete. | **GAP** |
| `A3` The initial state is schema-admitted, canonical, and its recomputed root equals the policy root. | Exact ZenoDEX state schema/root adapter. | Canonical initial state bytes. | No V2 committed-state adapter. | **GAP** |
| `A4` Store creation atomically persists exact genesis authorization and version-zero state. | Transactional creation port. | Empty authoritative store. | Generic SQLite implementation tested. | **TESTED** |

**Authenticated source relation — `IMPLEMENTED`:** Deployment policy, not caller input, owns expected root/source/evidence/laws. Current evidence: Generic boundary implements this distinction.

**Current-state and commit relation — `GAP`:** One atomic creation transaction; populated store rejects a second genesis; version zero remains byte-identical until first commit. Current evidence: Generic SQLite substrate tested; unmounted in ZenoDEX.

**Minimized counterexample `D01-CE-RAW-GENESIS`**

A schema-valid initial state is accepted directly as commit authority. Minimal witness: Attacker supplies a self-consistent replacement zero state/root when opening an empty or reset store, bypassing reviewed genesis source and project laws. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS raw-envelope compile failure, changed-root/binding, law violation, second creation, and persisted version-zero tamper tests.

Missing:
- ZenoDEX exact genesis policy and law manifest.
- Initial state/root golden bytes.
- Deployment-instance uniqueness and key-distribution evidence.
- Mounted creation/reopen integration tests.

**Smallest closing artifact:** ZenoDEX authorized genesis package at `docs/research/FCIS_M6_ZENODEX_GENESIS_V1.json`. Acceptance condition: Exact initial state, root, deployment identity, source/configuration evidence, and complete genesis laws mint one nominal authorization consumed by the mounted store.

**Dependencies/coupled gates:** `F-03`, `Z-06`.

**Explicit nonclaims:** A nonzero genesis hash identifies selected bytes but does not prove their economic or governance legitimacy.

### D-02 — Gap-free reauthorized history reconstructs current state

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reusable ZenoFCIS SQLite schema v5 and eventual ZenoDEX authoritative history.

**Exact safety claim**

Opening a populated store succeeds only if state versions are exactly `1..=N`, each persisted transition is strictly reauthorized and reexecuted from authorized genesis, and the reconstructed final canonical state bytes/root/version equal the current-state row exactly.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Replay and delivery; schema v5 | Schema v5 gap-free sequence and strict reexecution from reauthorized genesis. |
| Reusable history contract | `ZFCIS-RC-HEAD` | docs/STRICT_ARTIFACT_AND_SQLITE_HISTORY.md — laws 7-9 | State versions `1..=N`; applying from genesis yields stored current state/root/version. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Genesis authorization is valid under the current history policy. | Authorized genesis opener. | Persisted genesis bytes plus mounted policy. | Implemented generically; project policy absent. | **GAP** |
| `A2` Every historical artifact version has an available compatible schema/program/law package. | Versioned history execution registry. | Release artifacts/toolchains. | No ZenoDEX long-term retention policy. | **GAP** |
| `A3` The complete row set for every version is strictly decoded and reauthorized. | Strict artifact/history validator. | Untrusted database. | Generic implementation tested. | **TESTED** |
| `A4` No direct database mutation can be treated as current until the entire fold succeeds. | Shell API that exposes snapshots only after successful reopen validation. | Validated cache/state. | Generic implementation tested. | **TESTED** |

**Authenticated source relation — `IMPLEMENTED`:** Mounted history policy supplies expected genesis/program/laws; database rows never select their own authority. Current evidence: Generic model exists.

**Current-state and commit relation — `GAP`:** `StoreCurrent(store,s)` means `s` is the exact result of the complete reauthorized fold and equals the live row. Current evidence: Generic model tested; no ZenoDEX mapping/mount.

**Minimized counterexample `D02-CE-GAP`**

A current-state root is accepted despite a missing history transition. Minimal witness: Rows contain versions 1 and 3 with a plausible version-3 state/root; without exact `1..=N` reconstruction, omitted version 2 and its nullifiers/outbox are invisible. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS noncontiguous versions, live state replacement, genesis replacement, authorization/bundle/row-set tamper tests.

Missing:
- ZenoDEX state/history schema adapter.
- Historical program/law artifact retention.
- Large-history and corrupted-tail tests.
- Exact current-state witness passed into runtime evaluation.

**Smallest closing artifact:** ZenoDEX strict history opener at `crates/zeno-fcis-adapter-zenodex/src/history.rs`. Acceptance condition: Mounted runtime obtains current state only from a successful exact genesis-to-head reauthorization fold; any gap, substitution, or unavailable version fails closed.

**Dependencies/coupled gates:** `D-01`, `C-03`, `C-04`, `C-05`.

**Explicit nonclaims:** Exact replay under one implementation is not a proof that the implementation satisfies all intended economics.

### D-03 — Authenticated state projection and exact current root

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Semantic ZenoDEX state and its authenticated sparse-tree or commitment representation.

**Exact safety claim**

An authorized semantic transition can update authenticated state only through a setup-qualified projector whose complete pre-projection equals mounted authenticated leaves, whose post-projection equals a full rebuild of the semantic successor, and whose expected profile/version/root are current; a raw sparse plan or internally consistent proof has no publication authority.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/AUTHENTICATED_AUTHORITY_BOUNDARY.md — laws 1-10 | Candidate-bound authenticated commit authority, setup-pinned projector qualification/relation engine/provider, strict plan reconstruction, and production port boundary. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The projector implementation is pure, deterministic, complete for the project state domain, and independently qualified. | ZenoDEX state projector plus qualification claim/verifier. | Release-selected implementation/source/toolchain/evidence. | No project projector qualification. | **GAP** |
| `A2` The relation engine checks per-transition semantic/authenticated completeness. | ZenoDEX projection relation engine and project law. | Complete semantic pre/post state and plan. | Generic trait exists; project engine absent. | **GAP** |
| `A3` The mounted tree snapshot/profile/version/root are exact and current. | Authenticated store opener/current snapshot. | Pinned tree profile and reauthorized history. | Reference sparse tree only; no production JMT/store. | **GAP** |
| `A4` Semantic and authenticated updates share one candidate and publication boundary, or a proved cross-store atomic protocol. | One integrated commit port. | Nominal semantic+authenticated authorization. | Generic package explicitly does not provide cross-independent-DB atomicity. | **GAP** |

**Authenticated source relation — `GAP`:** Setup authority pins projector, verifier, relation engine, provider, profile, and state domain; request cannot substitute them. Current evidence: Generic nominal boundary implemented; ZenoDEX bindings absent.

**Current-state and commit relation — `GAP`:** Expected semantic root and authenticated root/version are checked at one publication point; both update or neither. Current evidence: No ZenoDEX production implementation.

**Minimized counterexample `D03-CE-OMITTED-LEAF`**

A projector omits a changed semantic value while supplying a self-consistent plan/root. Minimal witness: Balance changes in semantic successor, but projector leaves the balance key untouched; raw plan verifies internally against an incomplete declared projection. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS wrong projector/profile/evidence, omitted changed value, stale tree, plan-substitution, and raw-plan authority tests.

Missing:
- ZenoDEX complete projector and relation engine.
- Static/dynamic footprint proof for every projected field.
- Production authenticated store and crash tests.
- Atomic semantic+authenticated publication or formal protocol between stores.

**Smallest closing artifact:** ZenoDEX authenticated-state adapter at `crates/zeno-fcis-adapter-zenodex/src/authenticated_state.rs`. Acceptance condition: Qualified projector and relation witness bind every semantic change to exact authenticated leaves; stale/incomplete/substituted plans cannot reach the sole commit port.

**Dependencies/coupled gates:** `D-02`, `F-05`, `E-04`.

**Explicit nonclaims:** A projector commitment or internally valid proof does not establish projector completeness.

### D-04 — Project nullifier definition and consume-once state machine

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Proofs, migrations, withdrawals/claims, replay identities, settlement evidence, and every operation whose prior use must be remembered.

**Exact safety claim**

Each nullifier has a canonical domain-separated preimage binding operation kind, chain/deployment, profile/version, authenticated principal or proof subject, source object/commitment, and any required epoch; acceptance requires authenticated nonmembership in current state and the same candidate inserts exactly one nullifier; retries are idempotent only for the same candidate.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The protocol enumerates every operation requiring a nullifier and defines one canonical preimage per family. | Closed nullifier registry/catalog. | Project profile and command/proof schemas. | No M6 nullifier registry found. | **GAP** |
| `A2` Nullifier key derivation is collision-resistant and cross-domain separated. | Canonical codec/approved provider and golden vectors. | Exact domain/version fields. | No project implementation. | **GAP** |
| `A3` Current nonmembership is authenticated and bound to the exact pre-state. | Authenticated current-state proof/context or full store lookup. | Store-current root/version and key. | Generic proof-context boundary exists; no ZenoDEX source. | **GAP** |
| `A4` Insertion is part of the same atomic semantic/authenticated commit and exact history row set. | Candidate builder and transaction port. | Nominal authorized transition. | Generic substrate only. | **GAP** |
| `A5` Migration maps or preserves all prior nullifiers without reset or duplication. | Authorized migration relation. | Pinned predecessor history and manifest. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Operation authority and expected current root/key come independently from authenticated invocation/state; proof cannot self-supply context. Current evidence: No project nullifier authority.

**Current-state and commit relation — `GAP`:** Nonmembership read, semantic decision, nullifier insert, receipt/history/outbox, and authenticated-root update share one linearization point. Current evidence: No implementation.

**Minimized counterexample `D04-CE-CHECK-THEN-INSERT`**

Nullifier nonmembership is checked outside the commit transaction. Minimal witness: Two workers verify absent nullifier N, both perform the value-moving operation, then one or both insert N; uniqueness alone cannot undo duplicate external/economic effects. Source: `LIT-LINEARIZABILITY`.

**Executable evidence**

Existing:
- Generic replay-ID uniqueness and authenticated proof-context negative tests; no project nullifier corpus.

Missing:
- Nullifier family registry and preimage specification.
- Canonical vectors and cross-domain collision/substitution tests.
- Concurrent double-use test.
- Authenticated nonmembership/current-root binding.
- Migration and crash/retry/reopen tests.

**Smallest closing artifact:** nullifier registry and transition adapter at `crates/zeno-fcis-adapter-zenodex/src/nullifier.rs`. Acceptance condition: Every required one-shot operation derives one exact nullifier, proves current absence, inserts it in the same candidate, and concurrent/migration/reset mutants fail.

**Dependencies/coupled gates:** `F-02`, `D-03`, `E-01`.

**Explicit nonclaims:** A database unique index alone does not prove the protected operation occurred at most once.

### D-05 — Atomic complete candidate publication

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Semantic state, authenticated state, authorization, receipt, bundle, history, replay/nullifiers, commit evidence, and exact outbox rows.

**Exact safety claim**

A committing decision is published as one complete root-bound candidate at one linearization point: expected current root/version and every compare-and-replace precondition are checked, then all authoritative rows become visible together; any mismatch, validation failure, or pre-commit crash leaves the prior snapshot and no candidate rows.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean pure theorem | `ZDX-LEAN-LEDGER` | lean-mathlib/Proofs/DeterministicParallelExecution.lean — commit_rejects_root_mismatch; commit_accepts_root_match | Pure commit rejects root mismatch and accepts exact match. |
| ZenoDEX reference model | `ZDX-M5-REFERENCE` | docs/research/FCIS_M5_IMPLEMENTOR_NOTES_20260725.md — selected design | Reference expected-root immutable publication of state, receipt, replay batches, and outbox rows. |
| Generic SQLite implementation | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Atomic set | One immediate transaction writes state/root/version, authorization, bundle, receipt, replay, and complete outbox rows. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The input is a nominally authorized exact candidate. | ZenoDEX catalog/project-law/authenticated authority adapter. | Current state, authenticated invocation, candidate, laws, provider. | Absent. | **GAP** |
| `A2` All project authoritative state and obligations are represented in the declared atomic set. | Project schema and complete row-set contract. | All semantic/authenticated/history/nullifier/outbox domains. | Incomplete. | **GAP** |
| `A3` The datastore transaction/locking mechanism supplies one linearizable comparison and publication point. | Mounted transactional commit port. | Pinned SQLite or other store. | Generic SQLite port exists; no ZenoDEX adapter or no-bypass mount. | **GAP** |
| `A4` The configured durability mechanism preserves the committed set across the declared crash model. | Deployment storage configuration and crash qualification. | SQLite/rusqlite/VFS/filesystem/power-loss assumptions. | No production evidence. | **GAP** |

**Authenticated source relation — `GAP`:** Only a private nominal authorized transition reaches the port; callers cannot submit raw bundle/expected root/replay ID. Current evidence: Generic API implements this; no ZenoDEX nominal producer.

**Current-state and commit relation — `GAP`:** `AtomicCommit(s,result)` is a durable linearizable refinement, not merely a pure function or single-thread test. Current evidence: No mounted ZenoDEX proof/evidence.

**Minimized counterexample `D05-CE-PARTIAL-STATE`**

State becomes visible before receipt/outbox/history. Minimal witness: Crash after semantic row update but before outbox insert leaves value debited with no durable external obligation or audit receipt. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- M5 reference stale/malformed/crash tests.
- ZenoFCIS generic injected crash points and exact row-set tests.

Missing:
- Exact ZenoDEX atomic-set schema.
- Mounted nominal commit adapter.
- Linearization trace/model comparison under concurrent processes.
- Power-loss/fsync/WAL/rollback-journal configuration tests.
- No alternate writers/direct SQL paths.

**Smallest closing artifact:** ZenoDEX production commit-port package at `crates/zeno-fcis-adapter-zenodex/src/sqlite_commit.rs`. Acceptance condition: One reviewed transaction consumes only nominal authorization, publishes the complete project atomic set, passes concurrency/crash/reopen evidence, and is the sole writer.

**Dependencies/coupled gates:** `D-03`, `D-04`, `C-05`, `M6-03`.

**Explicit nonclaims:** A database transaction does not make an external chain/network action atomic with local state.

### D-06 — Crash recovery and durable linearizability

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Process crash, host crash, power loss, commit acknowledgement loss, and restart.

**Exact safety claim**

For every declared crash point, recovery yields either the exact pre-state with no candidate rows or the exact committed state with complete rows and pending outbox; after commit-before-response, retry detects the committed candidate and returns the same semantic result rather than duplicating or contradicting it.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Generic bounded implementation evidence | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Failure model | Seven permanent crash points: six pre-commit roll back; post-commit recovers through exact replay and pending outbox. |
| Methodology | `LIT-DURABLE-LINEARIZABILITY` | literature — durable linearizability | Separates concurrent linearizability from full-system-crash persistence semantics. |
| Methodology | `LIT-CRASH-HOARE` | literature — Crash Hoare Logic | Recovery relation and crash invariants are first-class proof obligations. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The crash model and durability point are explicit, including acknowledgement timing. | Deployment failure-model specification and fault harness. | Production storage/process environment. | No ZenoDEX M6 crash contract. | **GAP** |
| `A2` SQLite journal/WAL/synchronous/VFS/filesystem behavior matches the qualified environment. | Pinned database build/configuration/VFS/filesystem qualification. | Deployment image and host. | No retained qualification. | **GAP** |
| `A3` Recovery strictly validates/reexecutes complete history before serving reads or delivery. | Strict history opener. | Persisted store after crash. | Generic implementation tested; project adapter absent. | **GAP** |
| `A4` Retry identity binds the exact invocation/candidate and complete bundle. | Invocation/replay/candidate identity protocol. | Authenticated command and persisted authorization. | Generic substrate exists; ZenoDEX mapping absent. | **GAP** |

**Authenticated source relation — `GAP`:** Retry and recovery use persisted nominal authorization/history under mounted policy, not caller claims. Current evidence: Generic model only.

**Current-state and commit relation — `GAP`:** Recovery relation distinguishes pre-commit, post-commit-before-response, and post-delivery acknowledgement states. Current evidence: Bounded generic tests; no production/durable trace proof.

**Minimized counterexample `D06-CE-ACK-LOSS`**

Commit succeeds durably but response is lost; retry is treated as a fresh command. Minimal witness: Client resends same operation; runtime recomputes and publishes a second candidate/outbox because it lacks exact persisted replay/candidate detectability. Source: `LIT-DURABLE-LINEARIZABILITY`.

**Executable evidence**

Existing:
- ZenoFCIS generic pre/post-commit fault injection and idempotent replay tests.

Missing:
- ZenoDEX crash-state model (ESSO/TLA+/Crash Hoare style).
- Fault injection at every SQL/VFS boundary and kill -9/restart.
- Durability-mode matrix with explicit supported/unsupported configurations.
- Post-commit response-loss and post-delivery acknowledgement-loss tests.
- Independent filesystem/storage review.

**Smallest closing artifact:** crash-recovery specification and evidence at `docs/research/FCIS_M6_CRASH_RECOVERY_V1.md`. Acceptance condition: Declared crash model maps every persisted state to exact pre or exact committed candidate; mounted adapter passes deterministic fault/restart/retry traces under qualified storage settings.

**Dependencies/coupled gates:** `D-02`, `D-05`, `D-07`.

**Explicit nonclaims:** Unit fault injection is bounded evidence, not proof of SQLite, filesystem, controller, or hardware correctness.

### D-07 — Candidate-derived outbox identity and delivery detectability

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reusable ZenoFCIS outbox boundary and eventual ZenoDEX external operations.

**Exact safety claim**

Every external operation, including value movement, is a durable candidate-bound `OutboxEntry`; `DeliveryId = H(domain, CandidateId, canonical entry bytes)` is implementation-neutral; delivery receives the exact committed entry, and acknowledgement is accepted only for the exact entry hash; retry is idempotent under the mounted destination contract.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/COMMIT_EVIDENCE_AND_OUTBOX_MODEL.md — purpose and authority boundary | All external/value-moving operations are durable outbox obligations; commit evidence is non-executable. |
| Reusable identity repair | `ZFCIS-RC-HEAD` | docs/OUTBOX_DELIVERY_IDENTITY.md — laws | Candidate-derived delivery identity, reference/SQLite parity, exact entry-hash acknowledgement, and legacy schema rejection. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The project catalog truthfully classifies every external/value-moving operation as a durable channel. | ZenoDEX catalog plus mechanically derived project laws. | Profile/effect/channel registry. | Generic mechanism exists; ZenoDEX mapping incomplete. | **GAP** |
| `A2` Candidate sealing and canonical entry encoding are exact. | Controlled candidate/outbox builder and approved provider. | Exact transition outputs. | Implemented generically. | **TESTED** |
| `A3` The destination implements the reviewed idempotency/acknowledgement policy for the delivery ID and entry hash. | Bound delivery interpreter/destination adapter. | Deployment-selected destination instance/profile. | No production ZenoDEX transport qualification. | **GAP** |
| `A4` Pending delivery reads revalidate exact bundle membership and authorization. | Strict SQLite pending/ack APIs. | Reauthorized persisted candidate. | Implemented/tested generically. | **TESTED** |

**Authenticated source relation — `GAP`:** Commit authority binds catalog, destination profile, interpreter instance, deployment, and candidate; caller cannot choose destination at delivery. Current evidence: Generic private-construction boundary exists; no project setup.

**Current-state and commit relation — `GAP`:** Outbox rows commit atomically with state; delivery is separate and detectably idempotent, not part of local atomic transaction. Current evidence: Generic implementation tested; no ZenoDEX mount.

**Minimized counterexample `D07-CE-AUTH-ID`**

Deployment-specific authorization ID is used as delivery identity. Minimal witness: The same semantic candidate moved between reference and concrete shell receives different IDs, or replay under changed deployment collides/re-delivers inconsistently. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS reference/SQLite delivery-ID parity, candidate-vs-authorization substitution, collision, missing/extra row, and acknowledgement-hash tests.

Missing:
- ZenoDEX complete channel catalog and economic laws.
- Production destination idempotency/ack contract.
- Network failure/reorder/duplicate/ack-loss tests.
- No direct effect interpreter/callback path outside outbox.

**Smallest closing artifact:** ZenoDEX outbox channel catalog and transport adapter at `crates/zeno-fcis-adapter-zenodex/src/outbox.rs`. Acceptance condition: Every external/value movement is catalogued, atomically persisted, and delivered only through the bound exact-entry interpreter with duplicate/ack-loss evidence.

**Dependencies/coupled gates:** `D-05`, `C-05`, `Z-06`.

**Explicit nonclaims:** Idempotent delivery is not universal exactly-once execution or proof of external economic correctness.

### D-08 — Authorized schema and state migration

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** SQLite schema, semantic state, authenticated state, authority/configuration, nonce/nullifiers, history, receipt/bundle/outbox identities, and proof formats.

**Exact safety claim**

A migration runs only from an exact supported predecessor version under a pinned verified manifest, strictly reconstructs all predecessor history/artifacts, computes one canonical successor and identity mapping, publishes atomically with a migration receipt/nullifier, and never silently reinterprets legacy bytes or delivery IDs.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Fail-closed baseline | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — schema v5 | Rejects schema v4 and earlier pending explicit migration; no implicit authority assignment. |
| Identity migration warning | `ZFCIS-RC-HEAD` | docs/OUTBOX_DELIVERY_IDENTITY.md — version and migration | Schema v2 authorization-derived delivery IDs are rejected until exact authorized bundles are reconstructed and identities rewritten. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Source/target schemas, codecs, programs, laws, roots, and identity mappings are pinned. | Version registry and retained historical artifacts. | Release policy and exact source commits. | Incomplete. | **GAP** |
| `A2` Manifest authority is independently verified and deployment-specific. | Pinned migration verifier. | Independently distributed manifest/pin. | B1B-1 carries untrusted manifest only. | **GAP** |
| `A3` Every source row/object is consumed exactly once; missing/extra/duplicate data fails. | Strict migration enumerator/reconstructor. | Reauthorized predecessor history. | Absent. | **GAP** |
| `A4` Migration and its history/nullifier/receipt are one crash-atomic transaction. | Migration commit port. | Store-current predecessor and nominal migration authorization. | Absent. | **GAP** |
| `A5` Rollback/abort preserves the exact predecessor and does not expose a hybrid state. | Transactional rollback and recovery harness. | Datastore. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment pin and verified manifest own source/target relation; database/content cannot self-authorize. Current evidence: No verifier/migration authority.

**Current-state and commit relation — `GAP`:** Expected predecessor root/version CAS plus one complete successor; reopen validates migrated genesis/history policy. Current evidence: No implementation.

**Minimized counterexample `D08-CE-SILENT-REINTERPRET`**

New code opens old bytes under a changed identity or omission rule. Minimal witness: Legacy absent field is treated as default present, or old authorization-derived delivery ID is accepted as candidate-derived without reconstructing the original bundle. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- Generic unsupported-schema rejection and legacy delivery-ID negative tests.

Missing:
- Normative source→target migration spec for every state/artifact family.
- Pinned manifest/verifier and golden before/after stores.
- Omission/duplicate/identity-substitution mutants.
- Crash/retry/rollback/reopen tests.
- Independent migration review.

**Smallest closing artifact:** M6 migration package at `docs/research/FCIS_M6_MIGRATION_V1/`. Acceptance condition: One independently approved manifest and executable migrator reconstruct every predecessor artifact, atomically publish the successor, and fail all hybrid/silent-reinterpretation mutants.

**Dependencies/coupled gates:** `A-04`, `B-09`, `D-02`, `D-04`, `D-05`.

**Explicit nonclaims:** Rejecting old schemas prevents unsafe opening but does not complete migration.

### D-09 — History retention, pruning, snapshots, and bounded reopen

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Long-lived production history and authenticated-state node lifecycle.

**Exact safety claim**

Any pruning/snapshot/checkpoint mechanism preserves enough independently authenticated information to reconstruct or verify current state, authorization continuity, nullifiers, pending/acknowledged outbox obligations, and audit receipts; retained-history length and reopen work have explicit bounds without trusting a snapshot seal flag.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The retention policy states which history/evidence may be deleted and what authenticated checkpoint replaces it. | Project retention/pruning policy and laws. | Deployment profile. | No policy; ZenoFCIS explicitly lists retained-history and total-reopen bounds as nonclaims. | **GAP** |
| `A2` Checkpoint construction is an authorized transition bound to exact predecessor history/root. | Checkpoint transition and proof/certificate. | Store-current exact history. | Absent. | **GAP** |
| `A3` Nullifiers and undelivered outbox obligations cannot be pruned prematurely. | Retention-aware nullifier/outbox tables and liveness rules. | Exact history/current obligations. | Absent. | **GAP** |
| `A4` Reopen verifies checkpoint provenance and the suffix under the same policy. | Strict checkpoint+suffix opener. | Pinned checkpoint authority. | Absent. | **GAP** |
| `A5` Resource bounds prevent denial of service from unbounded replay while preserving safety. | Benchmarks/bounds and admission budgets. | Production scale envelope. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Checkpoint authority derives from reviewed policy and predecessor history; a database `sealed=true` flag is not authority. Current evidence: No implementation.

**Current-state and commit relation — `GAP`:** Checkpoint publication is atomic and history deletion occurs only after durable verified replacement under a crash-safe protocol. Current evidence: No implementation.

**Minimized counterexample `D09-CE-PRUNE-NULLIFIER`**

Snapshot retains balances but drops consumed nullifiers or pending outbox rows. Minimal witness: After pruning, an old proof/claim becomes replayable, or a committed external obligation disappears even though current balances look correct. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- No complete ZenoDEX evidence; generic library explicitly records the nonclaim.

Missing:
- Retention law manifest.
- Checkpoint format/root and proof/reconstruction relation.
- Prune-crash/retry tests.
- Nullifier/outbox preservation tests.
- Worst-case reopen-work bound and resource benchmarks.

**Smallest closing artifact:** retention and checkpoint specification at `docs/research/FCIS_M6_HISTORY_RETENTION_V1.md`. Acceptance condition: Authorized checkpoints preserve all safety-critical history obligations, prune crash-safely, and provide reviewed storage/reopen bounds.

**Dependencies/coupled gates:** `D-02`, `D-04`, `D-07`, `E-04`.

**Explicit nonclaims:** A current state root alone cannot replace replay/nullifier/outbox/history provenance.

### D-10 — Multi-process, replication, backup, and restore qualification

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Production deployment modes beyond one process/one local SQLite store.

**Exact safety claim**

The supported deployment topology has a defined consistency/failure model; all writers share the same linearizable authority or are rejected; replicas/backups/restores preserve exact policy identity, genesis/history/current state, nullifiers, receipts, and outbox status; split brain or stale restore cannot become authoritative silently.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Explicit generic nonclaim | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Nonclaims | Lists multi-process qualification, replication, backup/restore, filesystem qualification, and key management as unresolved. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Supported writer/process/replica topology is explicitly declared. | Deployment architecture and configuration gate. | Release/deployment policy. | Absent. | **GAP** |
| `A2` Locking, lease/consensus, fencing, and failover semantics prevent two independent authorities. | Qualified locking/consensus/fencing implementation. | Database/cluster infrastructure. | Absent. | **GAP** |
| `A3` Backup/restore captures a transactionally consistent complete store and deployment identity. | Atomic backup/restore procedure and verifier. | Complete datastore plus keys/policy. | Absent. | **GAP** |
| `A4` Restored/stale copies cannot rejoin without monotonic epoch/fencing and history comparison. | Epoch/instance identity and rejoin protocol. | Independent authoritative service/history. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment authority pins one active store/epoch and rejects stale instance identity. Current evidence: No qualification.

**Current-state and commit relation — `GAP`:** Commit linearization and restore/rejoin relation are deployment-specific and must refine the same reference history. Current evidence: No evidence.

**Minimized counterexample `D10-CE-SPLIT-BRAIN`**

Two restored copies accept writes independently from the same root. Minimal witness: Each process commits a different nonce/value transition under locally valid SQLite transactions; later merge has no canonical history and may duplicate outbox deliveries. Source: `LIT-LINEARIZABILITY`.

**Executable evidence**

Existing:
- None beyond single-process generic tests.

Missing:
- Explicit single-writer-only enforcement or qualified multi-process design.
- Two-process lock/fencing tests.
- Replica/backup/restore consistency vectors.
- Stale restore and split-brain fail-closed tests.
- Operational runbook and monitoring evidence.

**Smallest closing artifact:** deployment topology qualification at `docs/research/FCIS_M6_DEPLOYMENT_TOPOLOGY_V1.md`. Acceptance condition: Unsupported topologies fail closed; the selected topology passes process/restore/failover tests and preserves one exact authoritative history.

**Dependencies/coupled gates:** `D-05`, `D-06`.

**Explicit nonclaims:** SQLite transaction correctness in one process does not qualify distributed or restored deployment behavior.

## P4B5E — trusted proof context and verifier integration

### E-01 — Strict proof decoding and verification against complete expected context

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Reusable sparse-proof boundary; ZenoDEX proof formats must map to an equivalent nominal relation.

**Exact safety claim**

A proof is accepted only after bounded canonical decoding and verification against an independently supplied complete context containing exact profile/projector commitments, tree version, authenticated root, and logical key; changing any proof or expected-context field invalidates the witness; the witness grants read evidence only.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable implementation | `ZFCIS-RC-HEAD` | docs/AUTHENTICATED_PROOF_CONTEXT.md — laws 1-7 | Strict fixed-depth sparse-proof decoding and `verify_against` complete profile/version/root/key context with private witness fields. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Proof bytes are bounded, complete, canonical, and use the exact format/profile version. | Strict proof decoder. | Untrusted proof bytes. | Implemented/tested generically. | **TESTED** |
| `A2` Expected profile/version/root/key are supplied independently of the proof. | Authority-owned proof-context adapter. | Current authenticated state and invocation. | Generic API requires context but cannot prove provenance; ZenoDEX producer absent. | **GAP** |
| `A3` The approved commitment provider and path-combination algorithm match the profile. | Pinned provider/profile. | Deployment authority. | Generic provider/profile binding exists; project setup absent. | **GAP** |
| `A4` Downstream code treats the result as authenticated-read evidence only. | Type/API boundary and compile-fail tests. | Verified witness. | Implemented generically. | **TESTED** |

**Authenticated source relation — `GAP`:** Expected proof context comes from trusted current state/protocol invocation; copying fields from the proof is forbidden. Current evidence: Library leaves provenance to application authority.

**Current-state and commit relation — `GAP`:** Verified proof does not itself produce patch/candidate/publication; it feeds a separately authorized transition. Current evidence: Generic witness has no commit authority; no ZenoDEX composition.

**Minimized counterexample `E01-CE-SELF-CONTEXT`**

Verifier builds expected context by copying root/version/key/profile from the proof. Minimal witness: Attacker constructs its own tree and matching proof/context; internal verification succeeds but says nothing about the production state. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS malformed/trailing/over-limit proof tests; profile/version/root/key/leaf/sibling substitutions; private-witness compile fail.

Missing:
- ZenoDEX proof format adapter and canonical vectors.
- Exact runtime producer for context from store-current authenticated state.
- Mutation replacing expected fields with proof fields.
- Cross-language/proof-guest verification parity.

**Smallest closing artifact:** ZenoDEX proof-context adapter at `crates/zeno-fcis-adapter-zenodex/src/proof_context.rs`. Acceptance condition: Every verifier call receives independently derived store-current context and no proof/self-declared field can become the expected root/profile/version/key.

**Dependencies/coupled gates:** `D-03`, `C-01`.

**Explicit nonclaims:** Cryptographic consistency of a proof does not establish trusted context provenance.

### E-02 — Trusted proof-context provenance

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Oracle/state/proof/settlement verification inputs and public inputs.

**Exact safety claim**

The expected chain/deployment, profile, verifier/VK, algorithm, state root/version, context hash, command/candidate identity, epoch/time, and logical subject used by verification are derived from independent authenticated sources owned by deployment/current state/invocation, not from the proof, bundle, guest output, resolver, or caller.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable warning | `ZFCIS-RC-HEAD` | docs/AUTHENTICATED_PROOF_CONTEXT.md — authority boundary and nonclaims | States that a context-verified witness does not prove the context is trusted and copying proof fields into context establishes no external anchor. |
| B1B authority design | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md — authority owners | Separates deployment verifier, store-current state, authenticated command, migration manifest, consensus context, and publication currentness. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Every expected-context field has one declared independent producer. | Machine-readable source map enforced by code/checker. | Deployment/state/invocation/context authorities. | No complete ZenoDEX proof-context source map. | **GAP** |
| `A2` Producers are nominally authenticated and bound to one deployment/policy. | Nominal deployment/current-state/command/consensus adapters. | Pinned release keys, history, and authenticated messages. | Incomplete. | **GAP** |
| `A3` No fallback copies a missing expected field from proof/bundle/guest output. | Closed verifier API with no optional/caller-selected expected fields. | Production source tree/API. | No mounted verifier integration. | **GAP** |
| `A4` Publication rederives and compares the same complete context against current state. | Candidate-bound proof authorization and commit revalidation. | Store-current state and exact candidate. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Independent deployment/current-state/invocation/context authorities; proof producer has no source-selection power. Current evidence: Design principle exists; implementation absent.

**Current-state and commit relation — `GAP`:** Verification context hash and exact fields are sealed into candidate/receipt/public inputs and rechecked before commit. Current evidence: No implementation.

**Minimized counterexample `E02-CE-BUNDLE-ROOT`**

Bundle supplies both proof and expected state root. Minimal witness: Attacker proves membership in attacker-chosen root R and sets bundle.expected_root=R; verifier succeeds without comparing R to store-current production root. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- Generic context-substitution tests; no project source-provenance tests.

Missing:
- Exact source-of-truth table for every public input/context field.
- Nominal producer adapters.
- API/structural checker rejecting caller/proof/bundle-derived expectations.
- Store-current rebind and stale-context tests.

**Smallest closing artifact:** proof-context source matrix and adapters at `docs/research/FCIS_M6_PROOF_CONTEXT_SOURCES.json`. Acceptance condition: Every expected verifier input has exactly one independent authenticated producer and all self-source/fallback/stale substitutions fail.

**Dependencies/coupled gates:** `F-02`, `D-03`, `E-01`.

**Explicit nonclaims:** A verifier returning true is only as authoritative as the expected context it was given.

### E-03 — Verifier, verification-key, provider, and policy identity pinning

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** RISC0/other proof guests, sparse proofs, signatures, retained theorem artifacts, and migration verifiers.

**Exact safety claim**

Production verification uses one deployment-selected, nonzero, versioned verifier/provider/VK/profile/build identity bound to policy and candidate/public inputs; callers, proofs, bundles, database rows, or environment variables cannot substitute verifier code, keys, or permissive modes.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable authenticated-authority boundary | `ZFCIS-RC-HEAD` | docs/AUTHENTICATED_AUTHORITY_BOUNDARY.md — inputs and authority boundary | Setup owns projector qualification verifier, relation engine, provider, profile, and evidence; request cannot substitute them. |
| Reusable project-law boundary | `ZFCIS-RC-HEAD` | docs/PROJECT_RELATIONAL_LAWS.md — formal checker integration | Release policy selects concrete checker; missing/unknown/crash/disagreement grants no authority. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Deployment policy pins exact verifier/VK/provider/profile/build identities and their distribution/attestation. | Release/deployment verifier manifest and secure distribution. | Independent release root/key management. | B1B-1 has only untrusted carrier fields; no pinned verifier. | **GAP** |
| `A2` Production APIs accept no caller-selected verifier or unqualified generic callback. | Closed nominal verifier adapter/API. | Compiled production runtime. | Generic patterns exist; ZenoDEX integration absent. | **GAP** |
| `A3` Verifier output binds exact claim/public input bytes and nonzero result identity. | Exact verifier implementation and result type. | Canonical proof/public inputs. | Partial deterministic projection checkers exist; full guest/image refinement open. | **GAP** |
| `A4` Rotation/upgrades occur only through authorized versioned migration/update. | Authority state-machine migration/update. | Store-current policy and verified manifest. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Release/deployment authority pins verifier identity; request-time proof producer cannot choose it. Current evidence: No ZenoDEX pinned-verifier value/mount.

**Current-state and commit relation — `GAP`:** Verifier identity/result/public inputs are committed into nominal authorization/candidate; update is state-machine controlled. Current evidence: No implementation.

**Minimized counterexample `E03-CE-ENV-VERIFIER`**

Runtime selects verifier/VK from an environment variable or request field. Minimal witness: Attacker/deployment drift points production at a permissive test verifier that returns true for malformed proofs while artifact hashes remain self-consistent. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- Generic verifier-identity/evidence/profile substitution tests.

Missing:
- Pinned ZenoDEX verifier/VK manifest.
- Binary/image/VK known-answer and attestation evidence.
- API mutation tests for caller/env/database substitution.
- Authorized rotation/migration tests.
- Fail-closed unavailable/unknown/timeout behavior.

**Smallest closing artifact:** pinned verifier package at `docs/research/FCIS_M6_VERIFIER_POLICY_V1.json`. Acceptance condition: Exact verifier/VK/provider binaries and identities are independently pinned, known-answer tested, candidate-bound, and upgradable only through authorized state transition.

**Dependencies/coupled gates:** `A-03`, `C-02`, `E-02`.

**Explicit nonclaims:** A hash binding to verifier bytes does not prove those bytes implement a sound verifier.

### E-04 — Projector and public-input completeness relation

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Semantic state to authenticated tree/public-input projection for every proof-enabled transition.

**Exact safety claim**

Every semantic value and context fact required for verification or committed by the protocol appears exactly once in the authenticated projection/public inputs with the correct key/domain/version; no changed or consulted value is omitted, aliased, defaulted, or duplicated; a project-specific relation witness is mandatory per transition.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable framework | `ZFCIS-RC-HEAD` | docs/AUTHENTICATED_AUTHORITY_BOUNDARY.md — laws 4-7 and project-specific relation note | Per-transition projection relation engine must report `Satisfied` with a nonzero witness; omitted changed values fail authorization. |
| Footprint framework | `ZFCIS-RC-HEAD` | docs/COMPLETE_FOOTPRINT_WITNESS.md — laws | Static context/read/write/outbox footprints can be authority-bound and verified across all decision classes. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The project state/public-input schema is complete and versioned. | ZenoDEX authenticated profile and state-domain registry. | Release/deployment authority. | No complete V2 projection schema. | **GAP** |
| `A2` The projector implementation is pure and qualified against the exact source/build. | Qualified ZenoDEX projector and verifier. | Exact source/toolchain/evidence. | Absent. | **GAP** |
| `A3` Every transition's actual reads/writes/context are covered by complete footprints. | Complete footprint witnesses. | Transition components. | Absent. | **GAP** |
| `A4` The relation engine compares full semantic pre/post states to full projected pre/post values. | Project-specific projection relation engine/laws. | Semantic/authenticated subject. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment setup selects the expected projector/profile/relation engine; projector self-declaration is not authority. Current evidence: Generic setup boundary exists; project implementation absent.

**Current-state and commit relation — `GAP`:** Only a candidate-bound successful relation witness can reach authenticated publication. Current evidence: No ZenoDEX producer/port.

**Minimized counterexample `E04-CE-OMIT-CONTEXT`**

Projection covers state writes but omits a consulted context value. Minimal witness: Oracle freshness/chain epoch affects acceptance but is absent from public inputs; proof for one context can be replayed under another with identical state root. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- ZenoFCIS omitted-changed-value and binding-substitution tests.

Missing:
- Complete ZenoDEX state/context/public-input registry.
- Projector source and qualification artifact.
- Footprint completeness proof.
- Relation-engine tests for omitted/duplicated/defaulted fields.
- Python/Rust/guest projected-byte vectors.

**Smallest closing artifact:** ZenoDEX projection relation package at `docs/research/FCIS_M6_PROJECTION_RELATION_V1.json`. Acceptance condition: Every promoted transition has a verified complete footprint and relation witness connecting exact semantic state/context to exact authenticated/public inputs.

**Dependencies/coupled gates:** `F-05`, `D-03`, `E-03`.

**Explicit nonclaims:** A projection root can be internally consistent while omitting protocol-relevant facts.

### E-05 — Candidate-bound proof result and public inputs

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Proof-producing or proof-consuming transitions and commit bundles.

**Exact safety claim**

Proof verification result, verifier/VK/profile identity, exact canonical public inputs, command/context/pre-state/candidate/post-state roots, and proof bytes/commitment are bound to one evaluation candidate and nominal authorization; proof success for another candidate or stale state cannot be substituted.

**Existing proof or implementation evidence**

No existing proof or implementation artifact closes this exact claim.

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Public inputs are canonically derived from exact authenticated sources and complete projection. | Proof-input builder inside closed transition/authority adapter. | Authenticated state/command/context/profile. | Absent. | **GAP** |
| `A2` Verifier result names exact proof/public-input/verifier identities. | Pinned verifier result type/private constructor. | Exact proof and public-input bytes. | Absent. | **GAP** |
| `A3` Candidate identity commits the proof relation and every semantic/publication artifact. | Controlled candidate/decision/bundle builder. | Transition outputs. | Generic M5/ZenoFCIS substrate exists; proof fields not integrated. | **GAP** |
| `A4` Publication rechecks store-current state and proof authorization before commit. | Nominal commit authorization and port. | Store-current state and candidate. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Only deployment-pinned verifier over independently derived public inputs can mint the result used by the candidate. Current evidence: No implementation.

**Current-state and commit relation — `GAP`:** Proof authorization and semantic state commit occur under same expected pre-root; stale/mismatched proof causes no publication. Current evidence: No implementation.

**Minimized counterexample `E05-CE-PROOF-SWAP`**

A valid proof for candidate A is attached to candidate B with the same coarse state root. Minimal witness: Proof omits command hash, context hash, outbox/receipt roots, or algorithm version; bundle substitutes B's effects while reusing A's verification result. Source: `ZDX-M5-REFERENCE`.

**Executable evidence**

Existing:
- Generic same-candidate artifact-substitution tests; no proof-specific integration corpus.

Missing:
- Canonical public-input schema.
- Private verified-result type and verifier adapter.
- Candidate/receipt/bundle proof fields and roots.
- Proof/candidate/context/state substitution vectors.
- Stale-root commit test.

**Smallest closing artifact:** proof-bound candidate adapter at `crates/zeno-fcis-adapter-zenodex/src/proof_authorization.rs`. Acceptance condition: Verified proof results can be constructed only for exact independently derived public inputs and are inseparable from the candidate authorized for publication.

**Dependencies/coupled gates:** `E-02`, `E-03`, `E-04`, `F-04`.

**Explicit nonclaims:** Proof validity does not imply candidate completeness unless public inputs bind every required fact.

### E-06 — Proof-guest/runtime transition refinement and golden vectors

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** RISC0 or other guests/images, host projection checkers, Python/Rust pure core, and verifier integration.

**Exact safety claim**

For every admitted proof-enabled invocation, the guest proves or verifies exactly the same transition relation, integer domains, rejection/committed-failure semantics, roots, public inputs, and output artifacts as the normative core; guest image/VK identities and shared positive/negative vectors are pinned.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Recorded open blocker | `ZDX-M5-REFERENCE` | docs/research/FCIS_M5_COMPLETION_RECEIPT_V1.json — open_mount_blockers | Lists verifier/proof-guest migration, golden vectors, and Python/Rust refinement as open blockers. |
| Scoped zUSD evidence | `ZDX-ZUSD-CAP` | ZenoDEX PR #466 source/report — scope and nonclaims | Repairs a deterministic non-ZK RISC0 mint projection checker but explicitly denies complete guest/image refinement. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` One normative transition/public-input specification is frozen. | Closed ZenoDEX transition and proof-input schema. | Profile/schema/algorithm authority. | Incomplete. | **GAP** |
| `A2` Guest and host decoders/codecs use exact canonical bytes and bounds. | Generated/shared codecs and golden corpus. | Canonical fixtures. | Partial subsystem vectors only. | **GAP** |
| `A3` Guest arithmetic/state/root semantics exactly match runtime domains. | Guest implementation/refinement proof or exhaustive domain evidence. | Exact source/toolchain. | Absent. | **GAP** |
| `A4` Image/VK/toolchain/source identities are pinned and independently verified. | Release verifier/VK manifest and known-answer tests. | Independent release authority. | Absent. | **GAP** |
| `A5` All rejection and committed-failure paths are represented or proved unreachable. | Whole-decision refinement harness. | Exact normalized artifacts. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Release policy pins guest image/VK and normative source; host cannot accept arbitrary guest IDs. Current evidence: No aggregate pin.

**Current-state and commit relation — `GAP`:** Only validated proof-bound candidate reaches commit; guest disagreement/unavailability fails closed. Current evidence: No mounted integration.

**Minimized counterexample `E06-CE-FREE-DEBT`**

Guest checks a related but weaker arithmetic projection. Minimal witness: Host/core caps total debt including Stability Pool debt, while guest checks only free debt or an indirectly constrained value; a state can satisfy one relation and violate the intended invariant. Source: `ZDX-ZUSD-CAP`.

**Executable evidence**

Existing:
- Focused deterministic projection tests for zUSD total-debt cap; B1B Python/Rust codec vectors.

Missing:
- Complete guest/image implementation.
- Shared exact positive/negative/rejection vectors for every proof-enabled command.
- Public-input byte parity.
- Host/runtime/guest normalized-decision differential.
- Pinned image/VK/toolchain evidence and verifier integration tests.

**Smallest closing artifact:** proof-guest refinement packet at `docs/research/FCIS_M6_PROOF_GUEST_REFINEMENT_V1.json`. Acceptance condition: Exact guest/image source and VK pass shared whole-result vectors or a checked refinement proof, and only those identities are accepted by production verifier policy.

**Dependencies/coupled gates:** `F-06`, `E-03`, `E-05`.

**Explicit nonclaims:** A deterministic host-side projection checker is not a proof guest or image refinement.

### E-07 — Fresh consensus context, epoch/time, and Oracle-source binding

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Proof and transition gates that depend on height, time, epoch, finalized Oracle observations, or publication context.

**Exact safety claim**

Every time/epoch/Oracle/context fact used by proof or transition is independently authenticated, positive/valid where required, monotone/fresh relative to the exact current ledger state, and committed into context/public inputs/candidate; local wall clock or proof-supplied timestamp cannot authorize value movement.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Narrow Lean theorem | `ZDX-ZUSD-FRESHNESS` | lean-mathlib/Proofs/ZUSDPendingObservationFreshness.lean — freshness lemmas | Formal pending/finalized freshness relations under explicit observation/time premises. |
| Explicit theorem nonclaim | `ZDX-ZUSD-FRESHNESS` | lean-mathlib/Proofs/ZUSDPendingObservationFreshness.lean — file comments | Excludes Oracle authentication, positive/valid price, collateralization, state encoding, and atomic publication. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Consensus height/time/epoch comes from an independently authenticated publication context and is monotone from parent state. | Consensus/ledger context authenticator and parent-time relation. | Consensus/ledger authority. | Known repository gap: header time lacks parent monotonicity/future bound in earlier audits; no M6 adapter. | **GAP** |
| `A2` Oracle observation is from an authorized source, for the exact market/domain, positive/valid, and finalized where required. | Oracle authority/finalization adapter. | Authorized Oracle reports/state. | Pending/finalized lifecycle incomplete. | **GAP** |
| `A3` Freshness equations use the same exact units/bounds as runtime. | Checked context/freshness implementation and cross-language vectors. | Canonical context values. | Lean theorem only; runtime producer not proven. | **GAP** |
| `A4` All consulted context fields are present in candidate/public inputs and rechecked at commit. | Complete context footprint/public-input/candidate binding. | Transition/candidate builder. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Consensus and Oracle authorities are independent of proof producer/request; exact source identities are policy-bound. Current evidence: No complete source binding.

**Current-state and commit relation — `GAP`:** Store-current parent context and candidate context are compared at publication; stale proof/candidate publishes nothing. Current evidence: No implementation.

**Minimized counterexample `E07-CE-SELF-TIME`**

Proof supplies the timestamp used to establish its own freshness. Minimal witness: Oracle report is old under consensus time, but proof/public input chooses an earlier `now`, satisfying `now-observed <= max_age`. Source: `ZDX-ZUSD-FRESHNESS`.

**Executable evidence**

Existing:
- Lean freshness theorem; subsystem tests may exist but no aggregate context provenance evidence.

Missing:
- Authenticated consensus-context type and parent monotonic/future-bound checks.
- Oracle source/finalization state machine.
- Runtime-to-Lean unit/domain refinement.
- Stale/future/zero/unseen/substituted context vectors.
- Candidate/public-input binding and commit recheck.

**Smallest closing artifact:** authenticated context and Oracle adapter at `crates/zeno-fcis-adapter-zenodex/src/consensus_oracle_context.rs`. Acceptance condition: Only independently authenticated monotone consensus and finalized Oracle facts can satisfy freshness; every context field is candidate/public-input bound and stale substitutions fail.

**Dependencies/coupled gates:** `E-02`, `E-04`, `Z-03`, `Z-04`.

**Explicit nonclaims:** A freshness inequality does not authenticate the clock, Oracle, market, or state from which its operands came.

### E-08 — Closed verifier dispatch and bypass elimination

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** All production verification paths, feature flags, debug/test modes, legacy validators, host projection checkers, and direct commit callers.

**Exact safety claim**

Every proof-required command reaches exactly one deployment-pinned verifier path before nominal authorization; verifier failure/unknown/unavailable is fail-closed; no legacy, debug, shadow, test, feature, environment, direct-bundle, or alternate commit path can bypass or weaken proof/context checks.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Existing no-mount evidence | `ZDX-P4B3` | docs/research/FCIS_M5_P4B3_IMPLEMENTOR_REPORT_20260727.md — residual risk | Reports mixed mounted strong validator/legacy route module still reachable and final-mount violations, demonstrating why exact path closure is separate from local correctness. |
| B1B authority-isolation pattern | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B1_IMPLEMENTATION_REPORT_20260729.md — authority isolation | Global bounded source scan rejects premature authority consumers for the carrier-only checkpoint. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Production entry points and commit ports form a closed discoverable set. | Repository/package/binary entry-point inventory. | Release source tree and build graph. | No final M6 inventory; P4B3 reports mixed legacy reachability. | **GAP** |
| `A2` Verifier-required command profiles are complete and state-bound. | Closed catalog/profile law. | Current authority state. | No complete proof-required registry. | **GAP** |
| `A3` Only nominal verified authorization types satisfy the commit-port API. | Private nominal verifier/transition authorization and sole production port. | Pinned authority setup. | Generic pattern exists; ZenoDEX absent. | **GAP** |
| `A4` Build/package/feature configuration cannot include permissive test/legacy dispatch. | Locked build/features and release checker. | Exact toolchain/package artifacts. | No proof-specific aggregate gate. | **GAP** |
| `A5` Structural/call-graph checks and runtime mutations cover newly added paths. | Mutation-tested structural checker over all runtime roots. | Repository tree. | B1B narrow scanner exists; final mount not closed. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment policy/catalog decides proof requirement and verifier; caller/runtime mode cannot downgrade it. Current evidence: No mounted policy.

**Current-state and commit relation — `GAP`:** Commit port accepts only nominal proof-complete authorization; direct raw bundle/state writes are impossible or fail. Current evidence: No ZenoDEX port.

**Minimized counterexample `E08-CE-SHADOW-FALLBACK`**

Runtime falls back to Python authority or host projection when verifier is unavailable. Minimal witness: Proof-required command is accepted by a deterministic shadow checker under `verifier_unavailable`, bypassing the pinned guest/VK relation. Source: `ZDX-NONCE-DRIFT`.

**Executable evidence**

Existing:
- B1B narrow global scanner and mutation corpus; P4B3 structural checker exposes remaining violations.

Missing:
- Final production entry-point/call-graph inventory.
- Closed proof-required catalog.
- Compile-fail/private-type tests for direct commit.
- Feature/env/unavailable/fallback mutants.
- Packaged-binary symbol/config scan and runtime adversarial tests.

**Smallest closing artifact:** final verifier-path closure checker at `tools/check_fcis_m6_verifier_authority.py`. Acceptance condition: Checker and mutations prove every proof-required production path uses the pinned verifier and sole nominal commit port; legacy/debug/fallback/direct paths are absent.

**Dependencies/coupled gates:** `E-03`, `E-05`, `M6-09`.

**Explicit nonclaims:** A correct verifier implementation does not help if an alternate path can avoid it.

## ZUSD-P0 — system-wide arithmetic and lifecycle laws

### Z-01 — Exact global debt-cover algebra

**Status:** `PROVED`
**Evidence layers already present:** PROVED evidence
**Status rationale:** The exact narrow theorem/proof claim is discharged at a pinned source; runtime authority, current-state, refinement, and publication remain separate dependent gates.
**Scope:** Lean arithmetic model over aggregate free debt, Stability Pool debt, and backing/supply variables.

**Exact safety claim**

Under the theorem's exact-cover premises, global zUSD liability equals the declared covered debt quantity; the modeled wallet-to-DEX and gas-to-keeper ownership transfers preserve exact global cover.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean theorem | `ZDX-ZUSD-COVER` | lean-mathlib/Proofs/ZUSDGlobalDebtCover.lean — globalDebtCover; walletToDex_preserves; gasToKeeper_preserves | Exact global debt-cover equality and preservation under modeled ownership transfers. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The runtime state variables refine the Lean debt/backing variables exactly and use the same units. | ZenoDEX state-to-Lean projection/refinement map. | Exact committed zUSD state. | No concrete projection proof. | **GAP** |
| `A2` All zUSD debt locations and supply/ownership locations required by the theorem are included. | Complete zUSD state/law registry. | State schema and lifecycle specification. | Known lifecycle gaps remain. | **GAP** |
| `A3` The pre-state satisfies the exact cover premise. | Authorized genesis and inductive transition law evaluation. | Reauthorized current state/history. | No mounted law engine. | **GAP** |
| `A4` The transition is one of the modeled transfer forms or separately proved to preserve the invariant. | Closed zUSD transition family plus theorem/law per branch. | Authenticated command/context. | Only narrow transitions modeled. | **GAP** |

**Authenticated source relation — `GAP`:** Not part of the arithmetic theorem; runtime inputs must come from authenticated current state and commands. Current evidence: No mounted producer.

**Current-state and commit relation — `GAP`:** The invariant must hold at authorized genesis and every committing successor, published atomically. Current evidence: No runtime composition.

**Minimized counterexample `Z01-CE-OMITTED-DEBT`**

A runtime projection omits one debt location while satisfying the Lean equality over the projected variables. Minimal witness: Stability Pool debt is excluded from `totalDebt`; free debt/backing equation holds but actual global liability exceeds the modeled quantity. Source: `ZDX-ZUSD-CAP`.

**Executable evidence**

Existing:
- Pinned Lean theorem source.

Missing:
- Compile theorem at aggregate head.
- Exact runtime state projection and unit/domain proof.
- Law coverage for every zUSD committing decision.
- Inductive history/reopen validation.

**Smallest closing artifact:** runtime-to-Lean zUSD projection proof at `lean-mathlib/Proofs/ZUSDGlobalDebtCoverRuntimeRefinement.lean`. Acceptance condition: Canonical committed zUSD state projects completely into the theorem variables, and every promoted zUSD transition preserves the invariant.

**Dependencies/coupled gates:** `F-03`, `F-04`.

**Explicit nonclaims:** The theorem does not prove runtime state completeness, Oracle authority, publication, or full lifecycle correctness.

### Z-02 — Global debt cap includes free and Stability Pool debt

**Status:** `TESTED`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow implementation/reference/library behavior has executable evidence at a pinned source; the row does not claim production authority or a broader end-to-end relation.
**Scope:** Python zUSD core and deterministic RISC0 mint projection checker at PR #466.

**Exact safety claim**

Mint acceptance requires authoritative post-transition total debt, including both free debt and Stability Pool debt, to be at most the global supply cap; an already over-cap pre-state is rejected; Stability Pool deposits remain debt-location transfers valid at the exact cap.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Implementation and focused evidence | `ZDX-ZUSD-CAP` | ZenoDEX PR #466 changed source and report — PR #466 | Repairs Python single/multi-vault guards and deterministic RISC0 projection to compare total debt; adds invariant and counterexample tests. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Runtime `total_debt` includes every authoritative debt location exactly once. | Complete zUSD committed-state adapter. | Store-current zUSD state. | Python repair includes free+SP; full state projection/mount not proved. | **GAP** |
| `A2` Cap and debt use identical units/domains and checked arithmetic. | Checked integer/domain schema. | State/policy values. | Focused implementation exists. | **TESTED** |
| `A3` Mint delta and successor are derived from the same exact pre-state and command. | Pure mint transition. | Authenticated pre-state/command/context. | Python core and projection checker tested; nominal authority absent. | **GAP** |
| `A4` Every implementation/guest checks the same relation and rejection precedence. | Cross-language/guest refinement. | Pinned implementations and vectors. | Deterministic non-ZK checker only; full guest/image refinement absent. | **GAP** |

**Authenticated source relation — `GAP`:** Cap/policy and debt state must come from current authenticated state; command authorization controls mint. Current evidence: No mounted authority.

**Current-state and commit relation — `GAP`:** Accepted mint successor and invariant evidence publish atomically; reject has no state/effects. Current evidence: Pure implementation tested, production publication absent.

**Minimized counterexample `Z02-CE-FREE-ONLY`**

Checking only free debt admits a cap violation. Minimal witness: Vault A debt 700, vault B debt 700, free debt 100, SP debt 1,300, cap 1,500, mint 200: old guard sees 300<=1,500, actual post total is 1,600. Source: `ZDX-ZUSD-CAP`.

**Executable evidence**

Existing:
- 44 focused Python tests, 24 RISC0 projection witnesses, 213 shared crate tests reported at exact head.

Missing:
- Aggregate exact-head CI and independent review.
- Full guest/image/VK refinement.
- Mounted state/command/context adapter.
- Atomic publication and full lifecycle interaction tests.

**Smallest closing artifact:** mounted total-debt-cap law at `crates/zeno-fcis-adapter-zenodex/src/zusd_debt_cap.rs`. Acceptance condition: Project law reads complete store-current debt, matches all implementations/guest public inputs, and blocks authorization on any cap violation.

**Dependencies/coupled gates:** `Z-01`, `F-06`, `E-06`.

**Explicit nonclaims:** Focused mint repair does not close redemption, liquidation, recovery, shutdown, or production mount.

### Z-03 — Pending/finalized observation freshness algebra

**Status:** `PROVED`
**Evidence layers already present:** PROVED evidence
**Status rationale:** The exact narrow theorem/proof claim is discharged at a pinned source; runtime authority, current-state, refinement, and publication remain separate dependent gates.
**Scope:** Lean model of pending and finalized observation timestamps/epochs.

**Exact safety claim**

Under explicit seen/positive/time-order/max-age premises, pending/finalized observations satisfy the declared freshness relation and permitted transition preserves the modeled timestamp ordering.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean theorem | `ZDX-ZUSD-FRESHNESS` | lean-mathlib/Proofs/ZUSDPendingObservationFreshness.lean — freshness theorem family | Freshness and pending/finalized observation lemmas under declared assumptions. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Observation exists and its value is positive/valid where required. | Oracle admission/validation adapter. | Authorized Oracle report and state. | Not closed. | **GAP** |
| `A2` Current consensus time/epoch and observation time use the same monotone units. | Authenticated consensus context with parent monotonicity/future bound. | Ledger/consensus authority. | Not closed. | **GAP** |
| `A3` Observation source and market/domain are authenticated. | Oracle source/domain/finalization authority. | Pinned Oracle policy and signed/finalized reports. | Not closed. | **GAP** |
| `A4` Runtime transition exactly refines the modeled pending/finalized state machine. | Runtime-to-Lean state-machine refinement. | Exact Oracle state/transition. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Oracle/consensus authorities supply operands independently; proof/report cannot self-declare current time/source. Current evidence: No complete producer.

**Current-state and commit relation — `GAP`:** Freshness is checked in pure transition and rebound to store-current context at atomic publication. Current evidence: No production relation.

**Minimized counterexample `Z03-CE-UNSEEN-ZERO`**

Runtime omits seen/positive checks while satisfying a timestamp inequality. Minimal witness: oracle_seen=false, index_price=0, timestamp numerically fresh; theorem preconditions do not hold, but a weaker runtime guard accepts. Source: `ZDX-ZUSD-FRESHNESS`.

**Executable evidence**

Existing:
- Pinned Lean theorem source; prior repository differential witness documented unseen/zero Oracle acceptance drift.

Missing:
- Concrete runtime refinement theorem/vector corpus.
- Authenticated Oracle/consensus context implementation.
- Unseen/zero/stale/future/domain/source/finalization mutants.
- Candidate/public-input/commit binding.

**Smallest closing artifact:** Oracle freshness runtime refinement at `lean-mathlib/Proofs/ZUSDOracleFreshnessRuntimeRefinement.lean`. Acceptance condition: Runtime guard inputs are proven to satisfy every Lean premise and all boundary/rejection vectors agree across implementations.

**Dependencies/coupled gates:** `E-07`.

**Explicit nonclaims:** Freshness arithmetic does not authenticate source, guarantee collateralization, or publish state.

### Z-04 — Authoritative Oracle lifecycle and consensus time

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Pending, finalized, recovery, stale-data, liquidation, settlement, and shutdown paths.

**Exact safety claim**

Each value-moving zUSD action uses the correct finalized/pending Oracle phase, exact market/domain, authorized source set, quorum/finality policy, monotone consensus time/height, and freshness/positivity bounds; stale or missing data has one closed state-machine outcome and cannot be bypassed through recovery or legacy paths.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Narrow theorem boundary | `ZDX-ZUSD-FRESHNESS` | lean-mathlib/Proofs/ZUSDPendingObservationFreshness.lean — nonclaims | Explicitly leaves Oracle authentication, value validity, state encoding, and atomic publication outside the theorem. |
| Prior audit state | `ZDX-P4B3` | docs/research/FCIS_M5_P4B3_IMPLEMENTOR_REPORT_20260727.md — residual risk | Shows mixed legacy authority can remain reachable even when an exact unmounted component exists. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` One closed Oracle lifecycle/state machine defines pending/finalized/recovery/stale behavior. | Oracle state-machine module and laws. | Current authenticated Oracle state. | Incomplete. | **GAP** |
| `A2` Consensus time/height is authenticated, parent-monotone, and future-bounded. | Ledger/consensus context adapter. | Consensus authority. | Incomplete. | **GAP** |
| `A3` Oracle reports are source/quorum/market/domain/sequence bound and canonical. | Oracle authenticator/finalizer. | Pinned source/quorum policy. | Incomplete. | **GAP** |
| `A4` Each zUSD command profile declares exact allowed Oracle phase and freshness. | State-bound zUSD profile/catalog. | Current authority state. | Incomplete. | **GAP** |
| `A5` No legacy/recovery path omits the same checks. | Final call-graph/no-bypass checker. | Production source/build. | Incomplete. | **GAP** |

**Authenticated source relation — `GAP`:** Independent consensus and Oracle authorities; current zUSD profile selects required phase. Current evidence: No nominal composition.

**Current-state and commit relation — `GAP`:** Oracle state/context and zUSD decision are bound to candidate/public inputs and rechecked on current state at commit. Current evidence: No implementation.

**Minimized counterexample `Z04-CE-RECOVERY-STALE`**

Recovery path accepts an old or pending observation that ordinary liquidation rejects. Minimal witness: Normal path requires fresh finalized price; recovery branch reads cached/pending report or omits staleness check and moves collateral/debt under stale price. Source: `ZDX-ZUSD-FRESHNESS`.

**Executable evidence**

Existing:
- Narrow freshness theorem and historical audit/differential tests; no closed lifecycle evidence.

Missing:
- Oracle lifecycle model (Lean/ESSO).
- Authenticated consensus/Oracle adapters.
- Command-profile phase matrix.
- Recovery/legacy bypass mutations.
- Cross-language and proof-public-input vectors.

**Smallest closing artifact:** closed Oracle/context state machine at `crates/zeno-fcis-adapter-zenodex/src/oracle_lifecycle.rs`. Acceptance condition: Every zUSD value-moving path consumes one authenticated phase-correct Oracle/context witness and all stale/pending/recovery/legacy bypass mutants fail.

**Dependencies/coupled gates:** `Z-03`, `E-07`, `M6-09`.

**Explicit nonclaims:** A valid price signature alone does not establish finality, freshness, market binding, or current-state use.

### Z-05 — Complete zUSD lifecycle conservation and state-machine closure

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Authorized genesis; mint/borrow; repay/burn; Stability Pool deposit/withdraw/offset; liquidation; redistribution; redemption; gas compensation; fees; recovery; shutdown; settlement; bad debt.

**Exact safety claim**

Every legal zUSD lifecycle transition is represented in one closed state machine and preserves declared supply/debt/collateral/ownership/fee/residue laws; every illegal or under-specified state/transition is unrepresentable or rejected before effects; all committing failure branches have explicit allowed state/effect changes.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Pinned synthesis gap | `ZDX-RK-SYNTHESIS` | docs/research/ZENODEX_RK_MORPH_ESSO_SYNTHESIS_2026-07-21.md — Research Kernel result and nonclaims | Ranks incomplete zUSD lifecycle as highest-priority open item and explicitly leaves redemption, liquidation, redistribution, recovery, and shutdown unclosed. |
| Narrow proofs | `ZDX-ZUSD-COVER` | lean-mathlib/Proofs/ZUSDGlobalDebtCover.lean — global debt cover | Provides useful aggregate cover lemmas for a subset of transitions. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The lifecycle state space and transition registry are complete. | Normative zUSD state-machine specification and closed program. | Project profile/schema. | Incomplete. | **GAP** |
| `A2` State invariants and relational laws cover every `Accept` and `CommittedFailure` branch. | Complete law manifest and executable/formal evidence. | Catalog-derived value classifications. | Incomplete. | **GAP** |
| `A3` All arithmetic units, rounding, residue, fee claimant, and gas compensation ownership are explicit. | Checked integer/accounting types and recipient/claimant reachability laws. | State/configuration. | Incomplete. | **GAP** |
| `A4` Oracle/context/authentication preconditions are phase-correct. | Authenticated Oracle/consensus adapters. | Independent authorities. | Incomplete. | **GAP** |
| `A5` Runtime implementations and proof guests refine the same state machine. | Whole-result cross-implementation refinement. | Pinned runtime/guest sources. | Incomplete. | **GAP** |

**Authenticated source relation — `GAP`:** Commands, governance/config, Oracle, consensus, and state each supply independent nominal facts. Current evidence: No whole-system authority.

**Current-state and commit relation — `GAP`:** Every committing transition publishes complete state/nullifiers/receipt/outbox atomically; rejection publishes none. Current evidence: No full lifecycle commit integration.

**Minimized counterexample `Z05-CE-LOCAL-INVARIANT`**

Each local transition passes its own narrow check while the composed lifecycle creates uncovered or unreachable value. Minimal witness: Mint increases debt/supply; Stability Pool moves debt location; liquidation/redistribution/shutdown paths omit one residue or claimant. Local debt split and per-vault invariants pass while global cover/ownership fails. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- Narrow Lean cover/freshness theorems, focused total-debt-cap tests, and subsystem tests.

Missing:
- Complete lifecycle graph and state invariants.
- Per-transition project law definitions/evidence including committed failures.
- Bounded ESSO lifecycle models plus Lean inductive composition.
- Adversarial sequence/property tests across all phase transitions.
- Cross-language/guest and crash/reopen history tests.

**Smallest closing artifact:** zUSD lifecycle closure package at `docs/research/FCIS_M6_ZUSD_LIFECYCLE_V1/`. Acceptance condition: Closed state machine, complete law manifest, proofs/models, whole-result vectors, and history/crash evidence cover every legal transition and all value ownership/residue.

**Dependencies/coupled gates:** `Z-01`, `Z-02`, `Z-03`, `Z-04`, `F-04`.

**Explicit nonclaims:** A collection of local invariants is not automatically an inductive whole-lifecycle proof.

### Z-06 — Mechanically complete zUSD economic-law manifest and durable obligations

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Every catalogued zUSD debit, credit, mint, burn, fee, rounding residue, gas compensation, liquidation/redemption transfer, and external settlement channel.

**Exact safety claim**

Catalog classifications mechanically require conservation, debit/credit, mint/burn, fee/rounding, authority/subject, claimant reachability, and committed-failure laws; every external/value-moving obligation is an exact durable outbox entry; fresh law evaluation covers the complete exact candidate.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable framework | `ZFCIS-RC-HEAD` | docs/PROJECT_RELATIONAL_LAWS.md — laws 15-17 | Value-moving classifications derive minimum economic law families and require both Accept and CommittedFailure coverage. |
| Reusable outbox model | `ZFCIS-RC-HEAD` | docs/COMMIT_EVIDENCE_AND_OUTBOX_MODEL.md — laws and authority boundary | Value-moving commit evidence is rejected; value movement must be a durable outbox channel. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Every zUSD operation/value flow is present in the exact catalog with truthful asset/domain/authority/subject classification. | ZenoDEX zUSD catalog/profile generator and review. | Normative lifecycle specification. | Absent/incomplete. | **GAP** |
| `A2` The law manifest is complete and every required retained artifact/verifier is exact. | Verified project-law set/evidence policy. | Exact source/toolchain/artifacts. | Generic framework exists; project manifest absent. | **GAP** |
| `A3` The runtime law engine implements the declared numeric/ownership semantics. | Reviewed zUSD law engine. | Exact candidate subject. | Absent. | **GAP** |
| `A4` Outbox plan is complete and same-candidate with semantic debits/credits. | Candidate/outbox builder and destination catalog. | Transition outputs and deployment binding. | Generic substrate exists; project mapping absent. | **GAP** |

**Authenticated source relation — `GAP`:** Production authority owns catalog, laws, engine, provider, destination profile, and deployment binding. Current evidence: No ZenoDEX instance.

**Current-state and commit relation — `GAP`:** Law evaluation and complete outbox rows bind into nominal authorization and atomic commit. Current evidence: No mounted adapter.

**Minimized counterexample `Z06-CE-UNREACHABLE-FEE`**

Accounting credits a protocol fee claimant that has no valid durable destination or withdrawal path. Minimal witness: Semantic state debits users and records fee evidence, but outbox/claim state omits or misbinds the authorized recipient, stranding or redirecting value. Source: `ZDX-ZUSD-CAP`.

**Executable evidence**

Existing:
- ZenoFCIS generic law-family and value-moving effect/channel negative tests.

Missing:
- Complete zUSD catalog and generated minimum-law inventory.
- Project law engine and retained proofs.
- Claimant/destination reachability tests.
- Same-candidate state/outbox conservation tests.
- Committed-failure and external-acknowledgement cases.

**Smallest closing artifact:** zUSD catalog and law package at `crates/zeno-fcis-adapter-zenodex/src/zusd_laws.rs`. Acceptance condition: Catalog generation covers every lifecycle value flow, law evaluation is exact for every committing branch, and all external movements appear in the complete durable outbox.

**Dependencies/coupled gates:** `Z-05`, `D-07`.

**Explicit nonclaims:** Catalog hashes bind selected classifications; they do not prove the classifications or law engine are truthful.

### Z-07 — Mounted zUSD runtime refinement and no-bypass authority

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Production command ingress, evaluator, proof/verifier, datastore commit, history/recovery, and all legacy/shadow paths.

**Exact safety claim**

`RuntimeAccept` for any zUSD value-moving command implies canonical authenticated input, exact store-current state/context, the normative zUSD transition/laws, validated implementation/guest refinement, complete candidate authorization, and atomic publication; no legacy/shadow/direct path can accept or write outside this chain.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Current scoped nonclaims | `ZDX-ZUSD-CAP` | ZenoDEX PR #466 report — scope and nonclaims | Explicitly denies complete guest refinement, mounted production authorization, full lifecycle correctness, consensus time, fee transportability, shutdown settlement, and production readiness. |
| Final-mount warning | `ZDX-P4B3` | docs/research/FCIS_M5_P4B3_IMPLEMENTOR_REPORT_20260727.md — residual risk | Exact unmounted components can coexist with reachable legacy authority and final-mount violations. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` All Z-01 through Z-06 and foundation gates are closed. | M6 promotion matrix/checker and independent review. | Exact aggregate source/evidence. | Open. | **GAP** |
| `A2` One nominal zUSD authority adapter is the sole producer of commit-port inputs. | ZenoDEX→ZenoFCIS catalog-authority adapter. | Pinned program/laws/provider/policy. | Absent. | **GAP** |
| `A3` Production build contains no legacy/shadow/direct writer or permissive verifier fallback. | Final call-graph/package/runtime no-bypass checker. | Production source/build. | Absent. | **GAP** |
| `A4` Mounted datastore/history/outbox adapters pass crash/concurrency/migration qualification. | Mounted commit/history/outbox/migration implementation. | Qualified datastore/deployment. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** One release/deployment authority pins the full chain; request/runtime mode cannot downgrade it. Current evidence: No mount.

**Current-state and commit relation — `GAP`:** Only nominal authorized candidate reaches sole production writer; exact recovery/history defines current state. Current evidence: No implementation.

**Minimized counterexample `Z07-CE-PYTHON-FALLBACK`**

A correct Rust/guest path disagrees or is unavailable and runtime falls back to legacy Python authority. Minimal witness: Legacy path accepts a stale Oracle, free-debt cap, or old lifecycle behavior, then writes state through an existing engine not protected by the new laws/commit port. Source: `ZDX-NONCE-DRIFT`.

**Executable evidence**

Existing:
- Subsystem checks and unmounted structural scanners only.

Missing:
- Mounted adapter and authority switch.
- Whole zUSD normalized-decision/guest differential.
- Final no-bypass call-graph/build checker with mutations.
- Production crash/concurrency/migration/reopen evidence.
- Independent exact-head promotion review.

**Smallest closing artifact:** zUSD final mount unit at `docs/research/FCIS_M6_ZUSD_MOUNT_RECEIPT_V1.json`. Acceptance condition: All prerequisite gates are closed, sole nominal authority is mounted, legacy paths are removed, and exact runtime/crash/no-bypass evidence receives independent approval.

**Dependencies/coupled gates:** `Z-01`, `Z-02`, `Z-03`, `Z-04`, `Z-05`, `Z-06`, `M6-09`.

**Explicit nonclaims:** Green subsystem tests or an unmounted proof do not authorize zUSD value movement.

## M6 — publication, recovery, outbox, migration, and final composition

### M6-01 — Canonical runtime acceptance chain

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Every production request type and externally visible acceptance response.

**Exact safety claim**

`RuntimeAccept(bytes,store)` implies existence of exact `s,c,ctx,decision,authorization` such that bytes are bounded/canonical and authenticated as c; s is the exact store-current reauthorized state; ctx is independently authenticated; normalized runtime result equals the normative `step(s,c,ctx)` including every artifact; complete project laws are satisfied; and the accepted result is the one atomically committed candidate.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Target decomposition | `ZDX-RK-SYNTHESIS` | docs/research/ZENODEX_RK_MORPH_ESSO_SYNTHESIS_2026-07-21.md — Morph synthesis | Assume-guarantee factorization into parser, footprint, pure transition, patch/join, atomic commit, receipt/trace, and cross-language refinement contracts. |
| Refinement methodology | `LIT-REFINEMENT` | literature — refinement mappings | Refinement mappings require an explicit relation between implementation states/steps and specification states/steps, often with auxiliary state. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Canonical ingress and nominal authentication/authorization are closed. | F-02 plus project command/policy adapters. | Raw bytes and deployment authority. | Open. | **GAP** |
| `A2` Store-current state/history and authenticated context are exact. | D-02/D-03/E-02/E-07 current-state/context adapters. | Reauthorized store and independent authorities. | Open. | **GAP** |
| `A3` One pure total normative transition and complete laws exist. | F-04 and complete project law manifests. | Exact inputs. | Open. | **GAP** |
| `A4` Every runtime/guest implementation strictly refines the normalized decision. | F-06/C-06/E-06 validated refinement. | Pinned implementations and evidence. | Open. | **GAP** |
| `A5` Only nominal authorized candidates reach the sole atomic commit port. | M6-03/M6-04 nominal authorization and commit port. | Current state, candidate, laws, deployment. | Open. | **GAP** |
| `A6` The acceptance response is emitted only after the commit outcome is known or detectably recoverable. | M6-05 retry/detectability response protocol. | Durable history and replay identity. | Open. | **GAP** |

**Authenticated source relation — `GAP`:** Composed deployment, command, state, context, verifier, and project-law authorities; no single request/bundle field supplies the chain. Current evidence: No aggregate authority type or adapter.

**Current-state and commit relation — `GAP`:** Acceptance is post-linearization or recoverably committed; a pre-commit validation result is not `RuntimeAccept`. Current evidence: No mounted response/commit relation.

**Minimized counterexample `M601-CE-EARLY-200`**

Runtime returns success after pure evaluation but before durable commit. Minimal witness: Client observes accept; process crashes or CAS loses; store remains old and no receipt/outbox exists, so the externally reported operation never occurred. Source: `LIT-DURABLE-LINEARIZABILITY`.

**Executable evidence**

Existing:
- No end-to-end executable evidence; matrix records subsystem proof/reference/library evidence.

Missing:
- One nominal end-to-end invocation/authorization type chain.
- Executable trace harness linking ingress, transition, refinement, commit, response, reopen.
- Mechanized composition theorem or checked assume-guarantee certificate.
- Failure/retry semantics for every point before/after commit.

**Smallest closing artifact:** end-to-end runtime refinement module and trace packet at `crates/zeno-fcis-adapter-zenodex/src/runtime.rs`. Acceptance condition: Every observed accept has an exact canonical/authenticated invocation, store-current pre-state, normative decision, nominal authorization, durable candidate row, and reproducible receipt.

**Dependencies/coupled gates:** `F-02`, `F-03`, `F-04`, `F-06`, `D-02`, `D-05`, `E-02`.

**Explicit nonclaims:** A collection of passing local gates does not prove their assumptions are supplied by the same runtime execution.

### M6-02 — Pure expected-root compare-and-swap semantics

**Status:** `PROVED`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact narrow theorem/proof claim is discharged at a pinned source; runtime authority, current-state, refinement, and publication remain separate dependent gates.
**Scope:** Mathematical/reference commit function only.

**Exact safety claim**

For pure `commit(expected,observed,candidate)`, root mismatch returns no publication and exact equality returns exactly the candidate; no weaker root, candidate-carried observed state, or partial artifact is involved.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean theorem | `ZDX-LEAN-LEDGER` | lean-mathlib/Proofs/DeterministicParallelExecution.lean — commit_rejects_root_mismatch; commit_accepts_root_match | Pure mismatch rejection and exact-match acceptance. |
| Reference implementation | `ZDX-M5-REFERENCE` | src/integration/fcis_atomic_commit_reference.py — reference commit | Immutable expected-pre-root reference interpreter with no-publication stale/crash paths. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Expected and observed roots name the same complete state domain and collision-resistant canonical root function. | Complete canonical state-root implementation/refinement. | Current state/candidate schema. | Incomplete at project level. | **GAP** |
| `A2` Candidate is complete, exact, immutable, and nominally authorized elsewhere. | Candidate/authority chain. | Pure transition and deployment policy. | Generic/reference substrate only. | **GAP** |
| `A3` `None` or failure means no authoritative artifact is published. | Pure reference interpreter. | Immutable values. | Implemented/tested in reference model. | **TESTED** |

**Authenticated source relation — `NOT_APPLICABLE`:** Not established by the pure theorem; authorization is a separate prerequisite. Current evidence: Reference function accepts already-formed candidate values.

**Current-state and commit relation — `NOT_APPLICABLE`:** Pure function models the atomic relation but does not establish a database linearization/durability point. Current evidence: Reference tests only.

**Minimized counterexample `M602-CE-PARTIAL-CAS`**

A shell uses CAS only for the state root, then writes receipt/outbox separately. Minimal witness: Root comparison/update succeeds, but a later row write fails; the pure state CAS theorem held while the required complete publication relation did not. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- Lean theorem source and M5 reference stale/crash/substitution tests.

Missing:
- Aggregate Lean build receipt.
- Concrete state-root refinement.
- Separate production transaction-refinement proof/evidence in M6-04.

**Smallest closing artifact:** pure CAS theorem receipt at `docs/research/FCIS_M6_PURE_CAS_PROOF_RECEIPT.json`. Acceptance condition: Exact Lean source/toolchain compiles and the reference implementation is differentially checked against the theorem's complete candidate model.

**Dependencies/coupled gates:** `F-03`.

**Explicit nonclaims:** Does not prove database linearizability, durability, authorization, or complete atomic row publication.

### M6-03 — Nominal runtime authorization and commit-port admission

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Boundary between validated pure decision/refinement and the production writer.

**Exact safety claim**

Only a private nominal authorization value produced by the deployment-owned catalog/program/law/provider/authenticated-state/proof authority may enter the production commit port; raw candidates, bundles, hashes, replay IDs, proof results, caller-selected expected roots, and diagnostic parity objects cannot be converted or submitted directly.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable boundary | `ZFCIS-RC-HEAD` | docs/CANDIDATE_COMMIT_BOUNDARY.md — candidate and commit boundary | Only `CatalogAuthorizedTransition`, not a raw bundle, may enter production commit. |
| Reusable authenticated boundary | `ZFCIS-RC-HEAD` | docs/AUTHENTICATED_AUTHORITY_BOUNDARY.md — outputs and authority boundary | Only candidate-bound nominal authenticated authorization is accepted by production authenticated port. |
| Reusable refinement warning | `ZFCIS-RC-HEAD` | docs/VALIDATED_REFINEMENT_AND_EXHAUSTIVE_COVERAGE.md — authority boundary | Equality of untrusted normalized artifacts grants no promotion or commit authority. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Deployment setup pins exact catalog/profile/program/laws/provider/policy/interpreter/projector/verifiers. | ZenoDEX `CatalogCommitAuthority` setup adapter. | Release/deployment manifest. | Absent. | **GAP** |
| `A2` Invocation inputs are nominally authenticated and state/context bound. | Ingress/current-state/context/proof adapters. | Independent authorities. | Incomplete. | **GAP** |
| `A3` Transition result strictly normalizes and complete laws/refinement/projection checks succeed. | ZenoDEX program/law/refinement/authenticated-state adapters. | Exact candidate subject. | Incomplete. | **GAP** |
| `A4` Nominal constructors are private and no serialization/deserialization/cast recreates them. | Rust type/module boundary, compile-fail tests, and structural checker. | Production public API/source tree. | Generic implementation exists; ZenoDEX no-bypass adapter absent. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment setup owns every nominal authority dependency; request cannot substitute setup. Current evidence: No ZenoDEX producer.

**Current-state and commit relation — `GAP`:** Commit port API accepts the nominal value and internally derives expected root/replay/candidate rows; caller selects none. Current evidence: Generic SQLite port has this shape; no project mount.

**Minimized counterexample `M603-CE-RAW-BUNDLE`**

A raw internally consistent `CommitBundle` is accepted by production writer. Minimal witness: Attacker constructs candidate/state/effects/receipt/outbox that satisfy same-candidate hashes but were not produced for an authenticated invocation or checked by project laws. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS generic compile-fail/private-constructor and raw-plan/bundle authority negative tests.

Missing:
- ZenoDEX catalog/program/law/policy setup.
- Adapter that produces nominal authorization only after all gates.
- Compile-fail and dynamic type-confusion/canonical-deserialization mutants.
- Public API/call-graph proof that commit port has no raw overload.

**Smallest closing artifact:** ZenoDEX nominal commit authority adapter at `crates/zeno-fcis-adapter-zenodex/src/authority.rs`. Acceptance condition: All production commits consume only one private nominal ZenoDEX authorization; raw/artifact/hash/proof/diagnostic values cannot compile or pass runtime admission.

**Dependencies/coupled gates:** `F-02`, `F-04`, `C-06`, `D-03`, `E-05`, `Z-06`.

**Explicit nonclaims:** Same-candidate hash consistency does not establish authenticated or legal origin.

### M6-04 — Production linearizable atomic publication

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Mounted authoritative datastore writer.

**Exact safety claim**

The production commit operation has one observable linearization point between invocation and response: at that point it checks exact current root/version and all compare-and-replace preconditions and makes the complete candidate atomic set visible; concurrent histories are equivalent to one legal sequential history under the reference relation.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Methodology | `LIT-LINEARIZABILITY` | literature — linearizability | Linearizability requires each operation to take effect at one point between invocation and response while respecting real-time order. |
| Generic implementation | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — Atomic set | Immediate transaction, uniqueness constraints, exact current-root validation, and complete row writes. |
| Official datastore semantics | `SQLITE-ATOMIC-COMMIT` | web — atomic commit | Documents SQLite's atomic commit protocol and dependencies on locking/filesystem assumptions. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` The exact atomic row set and invariants are complete. | Project schema/row-set contract and laws. | ZenoDEX state/history/nullifier/outbox specification. | Incomplete. | **GAP** |
| `A2` The mounted database/locking API serializes competing writers as assumed. | Pinned SQLite/rusqlite build and transaction configuration. | Mounted datastore. | Generic implementation only; project deployment absent. | **GAP** |
| `A3` All authoritative reads/writes use the same transaction/connection discipline. | Closed repository/runtime data-access layer. | Production source/build. | No final no-bypass evidence. | **GAP** |
| `A4` No direct writer, second database, external side effect, trigger, or callback escapes the linearization point. | Effect-only-as-outbox catalog plus direct-write checker. | Catalog and code inventory. | Generic model exists; project mapping absent. | **GAP** |
| `A5` Trace observations map to the pure reference commit relation. | Concurrent trace recorder/model checker. | Runtime operations and reference model. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Commit port receives nominal authorization; database is not an authority source for program/policy beyond reauthorized history. Current evidence: No mounted adapter.

**Current-state and commit relation — `GAP`:** Complete project atomic set at one linearization point; failed/stale operation publishes zero rows. Current evidence: No ZenoDEX production evidence.

**Minimized counterexample `M604-CE-TWO-TRANSACTIONS`**

State and outbox are committed in separate transactions. Minimal witness: State transaction commits and becomes visible; process crashes before outbox transaction. Each transaction is locally atomic, but the protocol operation is not linearizable to the complete reference candidate. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- Generic SQLite transaction/fault tests; no ZenoDEX concurrent trace refinement.

Missing:
- Mounted ZenoDEX schema/commit adapter.
- Concurrency histories checked against reference model.
- Direct writer/trigger/callback inventory and mutations.
- Two-process stale-root and same-nullifier races.
- Exact supported SQLite journaling/locking configuration.

**Smallest closing artifact:** linearizability evidence package at `docs/research/FCIS_M6_LINEARIZABILITY_V1.json`. Acceptance condition: Recorded concurrent histories for every commit outcome refine the pure complete-candidate history, and structural evidence proves the mounted port is the sole authoritative writer.

**Dependencies/coupled gates:** `M6-02`, `M6-03`, `D-05`.

**Explicit nonclaims:** One SQL transaction is necessary but only sufficient if it covers the complete project operation and all writers obey it.

### M6-05 — Durable recovery, retry, and externally observable commit result

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Full-system crash and response-loss behavior around the publication point.

**Exact safety claim**

After any declared crash, reopen/recovery determines an exact durable state: pre-commit with no candidate, or post-commit with complete candidate/outbox; retry with the same authenticated invocation is detectably idempotent and returns the original result; runtime never reports final acceptance for a transition that cannot be recovered as committed.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Generic fault model | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — failure model | Six pre-commit crash points roll back; post-commit-before-delivery recovers exact candidate/pending outbox. |
| Crash-correctness methodology | `LIT-DURABLE-LINEARIZABILITY` | literature — full-system-crash model | Persistent objects need a crash-aware refinement beyond ordinary linearizability. |
| Recovery methodology | `LIT-CRASH-HOARE` | literature — Crash Hoare Logic | Crash invariants and recovery procedure are part of the specification. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Commit durability point and response timing are explicit. | Runtime response/commit protocol. | Commit port and API. | Not specified end-to-end. | **GAP** |
| `A2` Supported journal/WAL/synchronous/VFS/filesystem configuration meets the declared crash model. | Deployment storage qualification. | Pinned build/config/VFS/filesystem. | Absent. | **GAP** |
| `A3` Reopen performs strict genesis/history/candidate row-set reauthorization before serving. | Strict ZenoDEX history opener. | Persisted store. | Generic implementation exists; project adapter absent. | **GAP** |
| `A4` Replay identity binds exact invocation/authorization/candidate/bundle. | Nominal invocation/replay identity. | Authenticated command and policy. | Generic substrate; project mapping absent. | **GAP** |
| `A5` Response code distinguishes committed, definitely not committed, and indeterminate/unrecoverable states where necessary. | Error/result state machine and recovery API. | Runtime/client protocol. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Recovery uses mounted policy/history, not caller reports or cached flags. Current evidence: No project implementation.

**Current-state and commit relation — `GAP`:** Acceptance response is causally after durable commit or recoverably linked to exact committed candidate. Current evidence: No evidence.

**Minimized counterexample `M605-CE-RESPONSE-BEFORE-DURABLE`**

Runtime sends success before durable commit is guaranteed. Minimal witness: Client acts on success; power loss discards transaction/journal; reopen finds pre-state, violating external acceptance semantics. Source: `LIT-DURABLE-LINEARIZABILITY`.

**Executable evidence**

Existing:
- Generic in-process fault injection; no qualified full-system/power-loss evidence.

Missing:
- End-to-end response state machine.
- Kill/crash/power-loss/VFS fault testing under supported modes.
- Strict reopen/retry/detectability corpus.
- Indeterminate-state handling and operator recovery procedure.
- Independent storage qualification review.

**Smallest closing artifact:** durable response/recovery contract at `docs/research/FCIS_M6_DURABLE_RESPONSE_V1.md`. Acceptance condition: Every externally reported accept maps to a recoverable exact committed candidate; every crash/retry trace has one specified result under qualified storage settings.

**Dependencies/coupled gates:** `D-02`, `D-06`, `M6-04`.

**Explicit nonclaims:** Process-level exception tests do not establish full-system or hardware durability.

### M6-06 — Transactional outbox completeness and external-operation semantics

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** All network/chain/filesystem/device/service actions and value movement outside the semantic store.

**Exact safety claim**

The pure transition/catalog/laws produce the complete exact set of external obligations as durable candidate-bound outbox entries; local commit atomically retains all or none; delivery is separate, ordered/canonical as specified, retry-safe and detectably acknowledged; no commit-evidence record, callback, direct client call, or shell reconstruction executes external work.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Reusable model | `ZFCIS-RC-HEAD` | docs/COMMIT_EVIDENCE_AND_OUTBOX_MODEL.md — model and laws | CommitPlan is evidence-only; every external/value-moving operation is an OutboxEntry; exact rows publish atomically. |
| Reusable delivery identity | `ZFCIS-RC-HEAD` | docs/OUTBOX_DELIVERY_IDENTITY.md — normative preimage and laws | Candidate-derived implementation-neutral delivery identity and exact acknowledgement hash. |
| Distributed-systems limitation | `ZFCIS-RC-HEAD` | docs/COMMIT_EVIDENCE_AND_OUTBOX_MODEL.md — explicit nonclaims | Explicitly denies atomic completion of external systems and universal exactly-once semantics. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Project catalog and law engine completely identify all external/value-moving operations. | ZenoDEX effect/channel catalog and derived laws. | Complete transition/lifecycle specification. | Incomplete. | **GAP** |
| `A2` Candidate outbox plan is complete and exact. | Controlled candidate/outbox builder. | Exact transition outputs. | Generic implementation exists; project mapping absent. | **GAP** |
| `A3` Destination interpreter is deployment-bound and receives only committed exact entries. | Bound delivery interpreter and pending-row validator. | Deployment authority and reauthorized history. | Generic API exists; no production ZenoDEX transports. | **GAP** |
| `A4` Destination idempotency/ack policy is reviewed for each channel. | Per-destination idempotency/ack qualification. | External chain/service contract. | Absent. | **GAP** |
| `A5` Operational liveness/retry/backoff/dead-letter policy cannot alter semantic completeness or identity. | Operational delivery worker and monitoring policy. | Pending outbox. | Absent/unquealified. | **GAP** |

**Authenticated source relation — `GAP`:** Deployment authority pins channel catalog and interpreter profile/instance; caller cannot choose destination. Current evidence: No project setup.

**Current-state and commit relation — `GAP`:** Local transaction commits obligations, not external completion; acknowledgement updates only exact committed entry status under its own safe transaction. Current evidence: Generic model tested; no ZenoDEX mount.

**Minimized counterexample `M606-CE-EVIDENCE-EXEC`**

Shell interprets `CommitPlan` or receipt data as executable work. Minimal witness: An attacker/substitution turns audit evidence into a payment/callback, or the same logical operation appears both in commit evidence and outbox and executes twice. Source: `ZFCIS-RC-HEAD`.

**Executable evidence**

Existing:
- ZenoFCIS value-moving commit-evidence rejection, exact outbox membership, ID parity, collision, acknowledgement, and fault tests.

Missing:
- Complete ZenoDEX channel catalog and laws.
- No-direct-external-call structural/call-graph mutations.
- Production destination adapters and duplicate/reorder/ack-loss tests.
- Dead-letter/manual-retry authorization.
- Monitoring for committed-undelivered obligations.

**Smallest closing artifact:** project transactional-outbox package at `crates/zeno-fcis-adapter-zenodex/src/delivery.rs`. Acceptance condition: Every external/value-moving obligation is complete, candidate-bound, atomically durable, and deliverable only by a qualified exact-entry interpreter; all direct/duplicate paths fail.

**Dependencies/coupled gates:** `D-07`, `M6-04`, `Z-06`.

**Explicit nonclaims:** Transactional outbox gives atomic local intent plus idempotent delivery protocol, not a universal distributed atomic transaction.

### M6-07 — Upgrade, migration, rollback, and mixed-version safety

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Program/schema/policy/verifier/projector/codec/database upgrades and emergency rollback.

**Exact safety claim**

An upgrade activates only through an authorized versioned state-machine transition or verified migration from exact predecessor; old/new implementations cannot concurrently interpret the same authoritative store under incompatible semantics; rollback either restores an exact pre-upgrade snapshot with fencing or follows a reviewed reverse migration; hybrid state is never served.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Fail-closed baseline | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — schema v5 | Rejects unsupported legacy schemas and silently incompatible history. |
| B1B migration design | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md — authority owners and migration path | Initial configuration root comes from pinned verified migration manifest and publication uses store-current state. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Source/target program/schema/policy/verifier/projector identities and compatibility relation are explicit. | Release/migration manifest and historical artifact registry. | Release authority. | Incomplete. | **GAP** |
| `A2` Activation/migration authority is independently pinned and current-state bound. | Pinned verifier plus store-current migration candidate. | Deployment/current state. | Absent. | **GAP** |
| `A3` All state/history/nullifier/outbox/proof identities are migrated atomically or versioned compatibly. | Project migrator and exact row/object mapping. | Reauthorized predecessor. | Absent. | **GAP** |
| `A4` Old writers are fenced before target activation. | Deployment epoch/fencing mechanism. | Operational control plane. | Absent. | **GAP** |
| `A5` Rollback/recovery has a precise authority and data relation. | Rollback/reverse-migration specification and tests. | Exact snapshots/manifests. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Release/deployment/migration authority; neither old nor new runtime self-authorizes. Current evidence: No complete implementation.

**Current-state and commit relation — `GAP`:** Migration/activation is one expected-root atomic candidate; unsupported/mixed versions fail before serving or writing. Current evidence: No implementation.

**Minimized counterexample `M607-CE-OLD-WRITER`**

New schema activates while old process remains able to write. Minimal witness: Old writer omits new authority/nullifier/outbox fields and commits from a root it still considers current, creating history the new opener cannot safely interpret. Source: `LIT-LINEARIZABILITY`.

**Executable evidence**

Existing:
- Unsupported-schema rejection and B1B untrusted migration carrier tests only.

Missing:
- Complete M6 migration package.
- Old-writer fencing and mixed-version process tests.
- Forward/reverse golden stores.
- Crash during every migration phase.
- Rollback authority/runbook and independent review.

**Smallest closing artifact:** upgrade/migration state machine at `docs/research/FCIS_M6_UPGRADE_STATE_MACHINE_V1.md`. Acceptance condition: Every source→target/rollback path is authority-bound, crash-atomic, fenced, exact-history preserving, and all mixed-version/hybrid mutants fail closed.

**Dependencies/coupled gates:** `D-08`, `M6-04`, `M6-05`.

**Explicit nonclaims:** Failing closed on old data is safe but does not provide availability or a completed upgrade.

### M6-08 — Concurrency, process topology, and deterministic scheduling

**Status:** `GAP`
**Evidence layers already present:** PROVED evidence, IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Single/multi-thread execution, one or multiple processes, batch workers, retries, and store locking.

**Exact safety claim**

Logical semantics are independent of physical scheduling: commands use a canonical order; parallel tasks run only under complete noninterference and exact sequential parity; commit histories are linearizable; unsupported multi-process/topology modes fail closed rather than relying on accidental locks or scheduling.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Lean theorem | `ZDX-RK-SYNTHESIS` | lean-mathlib/Proofs/ReadWriteStableParallel.lean — execute_commutes_of_sound_noninterference | Sound footprints plus read/write noninterference imply task commutation. |
| Research Kernel counterexample | `ZDX-RK-SYNTHESIS` | docs/research/ZENODEX_RK_MORPH_ESSO_SYNTHESIS_2026-07-21.md — refuted claim | Disjoint writes are insufficient when one task reads another's write. |
| Generic nonclaim | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — nonclaims | Does not qualify multi-process operation or replication. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Complete static footprints and canonical logical join/error order exist. | Complete footprint witnesses and composition spec. | Authority-selected components. | Absent. | **GAP** |
| `A2` Parallel normalized result equals normative sequential result exactly. | Whole-result differential/proof. | Pinned sequential/parallel implementations. | Absent. | **GAP** |
| `A3` Production commit port/locking supports declared process topology. | Deployment topology/locking/fencing qualification. | Store/process infrastructure. | Absent. | **GAP** |
| `A4` Retry/recovery identities are stable across workers/processes. | Nominal invocation/candidate history. | Authenticated request and datastore. | Incomplete. | **GAP** |
| `A5` Any missing footprint/topology evidence forces sequential/single-writer fail-closed mode. | Scheduler/admission policy. | Deployment authority. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Authority pins scheduler/composition/topology policy; worker timing cannot choose semantics. Current evidence: No implementation.

**Current-state and commit relation — `GAP`:** Workers propose pure candidates; only one expected-root nominal commit port changes authoritative state. Current evidence: Reference architecture only.

**Minimized counterexample `M608-CE-RW-CONFLICT`**

Two tasks have disjoint writes but one reads the other's write. Minimal witness: A reads x, writes y:=x; B writes x:=1. Parallel snapshot yields y=old x; sequential B→A yields y=1. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- Lean abstract theorem and generic footprint-witness framework tests.

Missing:
- Complete project footprint witnesses.
- Sequential/parallel whole-result parity.
- Schedule permutation and failure-order tests.
- Process topology/lock/fencing tests.
- Conservative fallback verification.

**Smallest closing artifact:** deterministic scheduling authorization at `docs/research/FCIS_M6_PARALLEL_AUTHORIZATION_V1.json`. Acceptance condition: Every parallel component has a verified complete footprint and exact sequential parity; unsupported conflicts/topologies execute sequentially or fail closed.

**Dependencies/coupled gates:** `F-05`, `F-06`, `M6-04`, `D-10`.

**Explicit nonclaims:** Deterministic code or threads do not guarantee deterministic protocol outcomes without complete dependencies and canonical ordering.

### M6-09 — Sole authority path and legacy/bypass removal

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Source tree, build graph, packaged binary, runtime configuration, data-access layer, proof/verifier dispatch, and operational scripts.

**Exact safety claim**

Every state-changing or acceptance-producing production path passes the exact canonical ingress, current-state/context, normative transition/laws/refinement/verifier, nominal authorization, and sole commit port; all legacy evaluators, mixed validators, raw bundle writers, direct SQL/state mutation, shell-side reconstruction, debug/test fallbacks, and alternate effects are removed or provably unreachable.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Existing gap inventory | `ZDX-P4B3` | docs/research/FCIS_M5_P4B3_IMPLEMENTOR_REPORT_20260727.md — authority impact and residual risk | Mounted files unchanged, mixed legacy authority reachable, final-mount profile has 64 violations, and M6 must remove disconnected legacy representations. |
| Carrier isolation pattern | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_B1B1_IMPLEMENTATION_REPORT_20260729.md — authority isolation | Bounded repository scan and mutation tests prevent premature authority consumers in B1B-1. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Production roots, entry points, writers, effect/delivery paths, build features, and packaged artifacts are completely inventoried. | Machine-generated production boundary inventory. | Exact source tree/build/package. | Incomplete; B1B scan is narrow and P4B3 finds remaining violations. | **GAP** |
| `A2` Nominal types/private APIs make the intended path the only constructible path. | Final adapter/commit API and removal of legacy types. | Production code. | Not mounted. | **GAP** |
| `A3` Structural/call-graph/data-flow checks are semantic and mutation-tested, not name-only. | M6 structural checker with semantic mutations. | Repository AST/build graph. | Not implemented. | **GAP** |
| `A4` Runtime tests exercise feature/env/error/unavailable/fallback configurations. | Adversarial runtime matrix. | Packaged binary/configuration. | Absent. | **GAP** |
| `A5` Operational scripts/migrations/admin tools obey the same authority boundary. | Operational tooling audit/checker. | Deployment scripts/admin interfaces. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** One deployment authority setup; no local mode or admin tool can mint equivalent authority. Current evidence: No final mount.

**Current-state and commit relation — `GAP`:** Only sole nominal port writes state/history/outbox; all other write APIs are absent/private/read-only. Current evidence: No evidence.

**Minimized counterexample `M609-CE-LEGACY-REACHABLE`**

New exact core is correct but production still calls an older validator/writer for one command or fallback. Minimal witness: Legacy route/recovery/proof path accepts broader input or writes only partial state, bypassing every new theorem and law. Source: `ZDX-P4B3`.

**Executable evidence**

Existing:
- P4B3/B1B structural checkers and mutation suites over limited surfaces.

Missing:
- Final production inventory.
- M6 semantic call-graph/writer/verifier/outbox checker.
- Removal of legacy authority representations and direct writers.
- Packaged-binary/config/fallback mutations.
- Independent adversarial no-bypass review.

**Smallest closing artifact:** M6 authority-closure checker at `tools/check_fcis_m6_authority_closure.py`. Acceptance condition: Checker proves zero alternate acceptance/state/effect paths across source/build/package/runtime roots and kills representative legacy, alias, fallback, direct-write, and shell-reconstruction mutants.

**Dependencies/coupled gates:** `M6-03`, `M6-04`, `E-08`, `Z-07`.

**Explicit nonclaims:** Local correctness of the intended path is irrelevant if one alternate authoritative path remains reachable.

### M6-10 — Trusted dependency, configuration, key, filesystem, and operational qualification

**Status:** `GAP`
**Evidence layers already present:** none
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Canonical codec/crypto providers, SQLite/rusqlite, VFS/filesystem/storage, OS/process isolation, keys/pins, clocks/consensus adapters, delivery transports, build/release/supply chain, backups, monitoring, and incident recovery.

**Exact safety claim**

The release explicitly enumerates every trusted component/assumption, pins exact versions/configurations/identities, verifies known-answer and failure behavior, forbids unsupported modes, and retains operational evidence sufficient to know whether the theorem/runtime assumptions hold in the deployed environment.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Generic TCB declaration | `ZFCIS-RC-HEAD` | docs/SQLITE_SHELL_REFINEMENT.md — trusted dependencies and nonclaims | SQLite transaction/locking/WAL/rollback, filesystem, and pinned rusqlite/bundled SQLite are in the TCB; multiple deployment qualifications remain nonclaims. |
| Official SQLite semantics | `SQLITE-ATOMIC-COMMIT` | web — official documentation | Atomic commit depends on locking, journaling, and filesystem/device assumptions. |
| Official WAL semantics | `SQLITE-WAL` | web — official documentation | WAL has explicit concurrency/checkpoint/durability behavior and constraints. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Exact dependency/source/build/configuration closure is pinned and audited. | SBOM/lockfiles/reproducible build/supply-chain policy. | Release artifacts. | Partial lockfiles/workflows; current inherited dependency advisories reported on PR #494. | **GAP** |
| `A2` Cryptographic providers/keys/verifier pins and canonical codecs pass known-answer tests and secure distribution. | Known-answer tests, key/pin ceremony, attestation. | Release/deployment authority. | Incomplete. | **GAP** |
| `A3` Storage/VFS/filesystem/power-loss behavior matches supported crash/durability mode. | Deployment qualification matrix and fault evidence. | Actual host/storage configuration. | Absent. | **GAP** |
| `A4` Consensus time/Oracle/network/delivery adapters have reviewed trust and failure models. | Adapter-specific assurance packages. | External authorities/transports. | Incomplete. | **GAP** |
| `A5` Monitoring, backup, restore, key rotation, incident response, and rollback preserve authority boundaries. | Operational runbooks and tested restore/rotation/incident procedures. | Deployment operations. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Release/deployment/operations jointly own trusted setup; request/database/proof cannot self-select dependencies. Current evidence: No complete qualification.

**Current-state and commit relation — `GAP`:** Operational tools must use nominal history/migration/commit APIs; direct mutation invalidates authority and is detected/fenced. Current evidence: No evidence.

**Minimized counterexample `M610-CE-SYNC-OFF`**

Code assumes durable commit while deployment disables durability. Minimal witness: SQLite `synchronous=OFF` or an unqualified VFS/filesystem reports commit before data survives power loss; runtime returns accepted but reopen loses candidate. Source: `SQLITE-ATOMIC-COMMIT`.

**Executable evidence**

Existing:
- Pinned generic library dependencies and focused workflows; PR #494 reports inherited dependency-audit failures outside its diff.

Missing:
- Exact production SBOM/dependency audit and reproducible build.
- Supported SQLite mode/VFS/filesystem qualification.
- Key/verifier pin ceremonies and rotation tests.
- Delivery/Oracle/consensus adapter threat models.
- Backup/restore/incident/rollback drills and monitoring.

**Smallest closing artifact:** M6 trusted-computing-base qualification at `docs/research/FCIS_M6_TCB_QUALIFICATION_V1.json`. Acceptance condition: Every trusted component/assumption is exact, current, tested in the supported deployment configuration, and unsupported/advisory-failing modes block promotion.

**Dependencies/coupled gates:** `M6-05`, `M6-06`, `M6-07`, `M6-08`.

**Explicit nonclaims:** Formal core proofs cannot compensate for false deployment assumptions or compromised trusted components.

### M6-11 — Final composed M5-to-M6 theorem/runtime refinement and promotion

**Status:** `GAP`
**Evidence layers already present:** IMPLEMENTED evidence, TESTED evidence
**Status rationale:** The exact safety claim is not closed: one or more required runtime producers, authenticated sources, refinement relations, commit/recovery relations, or executable evidence remain missing or refuted.
**Scope:** Aggregate release claim for all value-moving ZenoDEX paths.

**Exact safety claim**

The conjunction of all required gate relations proves or executable-checks the target implication: every observed runtime acceptance has one canonical authenticated command, one exact store-current state/context, one normative decision satisfying all laws and implementation refinements, and one complete durable atomic commit; every rejection/failure has the declared no-publication or committed-failure semantics; no alternate path exists.

**Existing proof or implementation evidence**

| Kind | Source | Artifact / theorem | Establishes |
|---|---|---|---|
| Matrix task | `ZDX-B1B1-HEAD` | docs/research/FCIS_M5_P4B5A_ATDD_EXECUTION_CONTRACT_20260729.md — phase promotion | Demonstrates fail-closed phase promotion and exact-head evidence discipline. |
| Assume-guarantee method | `ZDX-RK-SYNTHESIS` | docs/research/ZENODEX_RK_MORPH_ESSO_SYNTHESIS_2026-07-21.md — Morph synthesis | Recommends proving separately composable parser, footprint, transition, patch/join, atomic commit, receipt/trace, and refinement contracts. |
| Refinement methodology | `LIT-REFINEMENT` | literature — refinement mappings | Final implementation/specification relation must account for all observable states/steps and necessary auxiliary history. |

**Theorem/contract assumptions and runtime producers**

| Assumption | Required runtime producer | Authenticated source | Current evidence | Producer status |
|---|---|---|---|---|
| `A1` Every required matrix gate is closed at its declared scope with exact source/evidence identities. | This matrix/checker plus future gate artifacts. | Exact aggregate source/evidence. | Current matrix will report many GAP rows; no promotion. | **GAP** |
| `A2` All inter-gate assumptions have exactly one authenticated runtime producer. | Machine-checked assumption/producer graph. | Matrix and source adapters. | Matrix checker validates record completeness, not runtime truth. | **GAP** |
| `A3` Composition preserves shared identities: bytes, command, principal, policy, pre-state, context, candidate, receipt, replay/nullifier, outbox, and roots. | Nominal type chain and integration trace/proof. | Mounted runtime. | Absent. | **GAP** |
| `A4` No proof/reference/library result is promoted beyond its explicit nonclaims. | Conservative status/nonclaim checker. | Evidence ledger. | This deliverable enforces static matrix discipline only. | **IMPLEMENTED** |
| `A5` Independent adversarial review approves the exact aggregate head, build, migration, deployment, and rollback plan. | Independent exact-head release review and owner decision. | Complete release packet. | Absent. | **GAP** |

**Authenticated source relation — `GAP`:** Aggregate release/deployment authority selected only after every source authority and trusted dependency is independently pinned. Current evidence: No promotion authority in this research checkpoint.

**Current-state and commit relation — `GAP`:** Final relation covers runtime response, durable state/history/outbox, recovery, and no-bypass path at exact release head. Current evidence: Not established.

**Minimized counterexample `M611-CE-PROOF-ISLANDS`**

Every subsystem has a locally valid theorem/test, but their assumptions are produced by different or unauthenticated runtime values. Minimal witness: Lean proves `Inv(step(s,c))`; runtime decodes c noncanonically, reads stale s, uses a different implementation, and writes state/outbox separately. No local theorem is false, yet the runtime claim fails. Source: `ZDX-RK-SYNTHESIS`.

**Executable evidence**

Existing:
- This matrix/checker can validate required records, conservative statuses, source identities, and dependency graph shape; it cannot execute missing runtime relations.

Missing:
- Close every `GAP` row.
- Generate exact aggregate source/evidence/build/deployment manifests.
- Run checker, theorem builds, whole-result refinement, fault/concurrency/migration/no-bypass gates.
- Independent adversarial review and explicit promotion receipt.
- Post-mount canary/rollback evidence without weakening authority.

**Smallest closing artifact:** final promotion receipt at `docs/research/FCIS_M6_PROMOTION_RECEIPT_V1.json`. Acceptance condition: Checker reports zero gaps; all exact source/tool/build/deployment evidence is green; independent review approves the exact aggregate head and sole authority mount without nonclaim violations.

**Dependencies/coupled gates:** `F-01`, `F-02`, `F-03`, `F-04`, `F-05`, `F-06`, `A-01`, `A-02`, `A-03`, `A-04`, `A-05`, `A-06`, `A-07`, `A-08`, `A-09`, `A-10`, `A-11`, `A-12`, `B-01`, `B-02`, `B-03`, `B-04`, `B-05`, `B-06`, `B-07`, `B-08`, `B-09`, `C-01`, `C-02`, `C-03`, `C-04`, `C-05`, `C-06`, `C-07`, `C-08`, `D-01`, `D-02`, `D-03`, `D-04`, `D-05`, `D-06`, `D-07`, `D-08`, `D-09`, `D-10`, `E-01`, `E-02`, `E-03`, `E-04`, `E-05`, `E-06`, `E-07`, `E-08`, `Z-01`, `Z-02`, `Z-03`, `Z-04`, `Z-05`, `Z-06`, `Z-07`.

**Explicit nonclaims:** This matrix is a research/refinement map, not itself a proof, implementation, mount, or release approval.

## Composition theorem required for promotion

The final proof/evidence package should expose separate relations and one composition theorem rather than one opaque assertion:

```text
IngressSound(bytes, invocation)
StateCurrent(store, pre)
ContextSound(invocation, store, context)
StepSound(pre, invocation, context, decision)
ImplementationRefines(runtime, pre, invocation, context, decision)
AuthorizationSound(decision, state_authority, proof_authority, laws, authorized)
CommitLinearizes(store, authorized, committed)
RecoverySound(store_after_crash, committed)
OutboxSound(committed, deliveries)
NoBypass(runtime_build)

all of the above
  -> RuntimeAccept(bytes, store)
     implies one exact durable normative transition
```

The composition must preserve the same identities at every boundary: canonical request bytes, command/principal/replay identity, profile/policy/algorithm, pre-state version/root, authenticated context, decision/rejection precedence, candidate, receipt, replay/nullifiers, commit evidence, outbox, verifier/public inputs, and post-state roots.

## Checker

Run from the repository root:

```bash
python3 -B tools/check_fcis_m5_to_m6_refinement_matrix.py
python3 -B tools/check_fcis_m5_to_m6_refinement_matrix.py --json
```

The checker validates the exact required gate set, pinned source commits, one-to-one assumption/producer mappings, conservative status evidence, source/dependency references, matrix fingerprint, Markdown completeness, and the no-runtime/no-mount scope. It deliberately does not execute or replace Lean, Kani, Research Kernel, ESSO, Julia, SQLite fault testing, runtime refinement, or independent review.

## Final nonclaim

This deliverable is a research and promotion-control artifact. It changes no runtime behavior, mounts no authority, performs no migration, and does not authorize value movement. Its value is to make every remaining theorem premise, runtime producer, authenticated source, state/commit relation, counterexample, and smallest closing artifact explicit and machine-checkable.
