# ZenoDEX Production Completion Plan V1

Status: `G0_COMPLETE_RESEARCH_ONLY`

Frozen integration base: `b6842cd26aadf32b7ee774f58665570479cacfe6`

Promotion posture: closed. This plan, its task graph, and its structural checker
do not establish M6, ZRPF, or production readiness.

## G0 freeze note

The dirty source checkout was preserved before this plan was added. Its private
payload and manifest were independently hashed and verified. The preservation
receipt is intentionally absent from the public repository because it contains
an inventory of non-ignored local files. The task graph records only the
content hashes and the verification scope.

The assessment received with this plan reported ten deliberately disabled V1
commands. The exact frozen source defines 33 command kinds and eight entries in
`M6_RESEARCH_DISABLED_COMMANDS_V1`. This disagreement remains open for G1. It
does not change the 0/13 M6 posture or authorize either command partition.

Machine-readable companions:

- `docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json`
- `docs/research/PRODUCTION_READINESS_COVERAGE_LEDGER_V1.json`
- `docs/research/PRODUCTION_READINESS_DONOR_INVENTORY_V1.json`
- `tools/check_production_readiness_plan.py`

Replay the structural gate with:

```bash
python3 tools/check_production_readiness_plan.py --json
```

## Summary and strict assessment

ZenoDEX is not production-ready. Under the repository's full promotion
predicate, M6 remains 0/13 complete because no M6 requirement has
`PROVED + IMPLEMENTED + MOUNTED + TESTED` evidence for one exact promotion
subject.

| Area | Current state | Decisive blocker |
| --- | --- | --- |
| Functional core | Partial research core | 33 command kinds exist; the received assessment reported 10 deliberately disabled commands and an independent oracle covering 8/33. The exact G0 base exposes eight disabled commands, so G1 must reconcile the source-observed mismatch. |
| Formal verification | Partial, locally useful | Historical ESSO evidence exists, current source bindings drift, and the global composition/refinement theorem remains open. |
| Imperative shell | Partial research implementation | Commit, filesystem durability, reopen, migration, and outbox prototypes are unmounted and do not implement production ZenoLedger consensus. |
| Testing and hardening | Significant research evidence | Current exact-head evidence is fragmented; a 678-test focused run stalled at 31%; source manifests and several gates are stale. |
| Mounted authority | Open | The received assessment inventoried 18 of 25 value-moving entrypoints as unmounted; this count must be regenerated from the production build. Legacy writers still exist. |
| ZRPF | Partial research implementation | Python/Rust semantics differ, the selected guest does not execute the complete M6 transition, full 73-receipt replay is absent, and observed latency is far above the 60-second target. |
| Production operations | Open | No qualified validator deployment, disaster recovery, key ceremony, external audit, or exact release subject exists. |

Two readiness predicates will be used:

```text
M6DirectReady(P)
  = complete functional core
  + FormalGate(P)
  + RuntimeRefinementGate(P)
  + MountedAuthorityGate(P)
  + ConcreteDurabilityGate(P)
  + complete direct-execution no-bypass evidence

ZRPFReady(P)
  = complete shared execution semantics
  + real recursive proof evidence
  + governed proof admission
  + direct/ZRPF parity
  + target performance

ProductionReady(P)
  = M6DirectReady(P)
  + ZRPFReady(P)
  + OperationalReady(P)
```

M6 correctness is completed before ZRPF activation. ZRPF subsequently scales
the same transition and enters through the same commit capability.

## Frozen architecture

### Authority allocation

- The versioned ZenoDEX functional core defines valid economic transitions.
- ZenoLedger is the sole durable economic ledger and beneficial-ownership
  record.
- Tau may order batches, verify or anchor proofs, provide authenticated external
  ingress/egress evidence, and expose ZenoDEX to Tau users.
- Tau cannot select the ZenoLedger head, change the economic constitution,
  issue assets, bypass a ZenoDEX transition, or reorganize finalized ZenoLedger
  history.
- ZRPF proves batch execution. It carries no finality, issuer, governance, or
  publication authority.
- SQLite remains an unmounted conformance and fault-testing adapter.
- Direct execution remains the safety fallback and uses the same core as ZRPF.

### Production implementation boundary

Create a new production version instead of promoting the drifted research V1
types:

- `M6PromotionSubjectV2`: source, proof, build, ABI, enabled-release, validator
  registry, genesis, Tau profile, proof-image, destination-adapter, and
  writer-epoch roots.
- `GlobalCommandV2`: the closed 33-command language.
- `AuthenticatedExecutionContextV2`: exact parent root, height, sender, nonce,
  epoch, oracle context, deployment, and optional Tau evidence.
- `GlobalEconomicStateV2`: balances, custody, supply, debt, LP state, perps
  liabilities, escrows, reserves, auctions, withdrawals, outbox, history,
  nullifiers, and release state.
- `GlobalOutcomeV2`: exactly `RejectNoCommitV2` or `AcceptCandidateV2`.
- `ValueDeltaCertificateV2`: the complete pre/post economic difference.
- `PublicationBundleV2`: candidate, history, nullifier, finality certificate,
  proof record, effects, and successor.
- `ZRPFRootJournalV2`: exact ordered command, context, pre/post state, delta,
  effect, release, and proof-profile commitments.

The authority-critical production transition will be a deterministic Rust crate
usable by both the native ZenoLedger node and the RISC0 guest. Python remains an
independent reference oracle and research harness.

### Global invariant

Every accepted transition must preserve:

```text
nonnegative, bounded integer quantities
one declared issue and burn authority per managed asset
zUSD issuance and burning exclusively through the collateralized monetary kernel
per-asset balance + custody + reserve + escrow + claim reconciliation
current zUSD debt/supply/protocol-liability reconciliation
LP reserve/share/fee/dust reconciliation
perps margin/PnL/funding/insurance reconciliation
oracle-gated risk increase
nonce and nullifier uniqueness
complete terminal drains
no unnamed rounding remainder
no external effect without a committed outbox ancestor
reject-no-commit leaves state and effects unchanged
```

Unselected economic policies remain `UNSELECTED` and make their command
families unreachable. Implementers may not infer fee ownership, liquidation
parameters, oracle thresholds, or fallback behavior.

## Implementation task graph

### G0: Preserve and freeze the implementation subject

Dependencies: none.

1. Run the repository disk-safety gate before new worktrees or proof builds.
2. Record the current HEAD, branches, worktrees, tracked diff, untracked
   manifest, and SHA-256 identities.
3. Archive and verify the dirty worktree before removing any regenerable caches.
4. Create an isolated integration worktree from the latest verified descendant
   of `b6842cd26aadf32b7ee774f58665570479cacfe6`.
5. Inventory every M6/ZRPF donor commit and import only reviewed,
   obligation-sized patches.
6. Store this plan as:
   - `docs/PRODUCTION_READINESS_PLAN.md`
   - `docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json`
   - `docs/research/PRODUCTION_READINESS_COVERAGE_LEDGER_V1.json`
7. Add a fail-closed plan/task-graph checker and link the plan from the main
   README.

Exit gate: clean isolated subject, verified preservation archive, acyclic task
graph, no lost user work.

### G1: Close product semantics and the global state model

Dependencies: G0.

1. Map every one of the 33 commands through:

```text
UserStory -> NormativeSpec -> CoreTransition -> TerminalPath
          -> FormalObligation -> RuntimeProjection -> MountedEntrypoint
```

2. Freeze profile decisions for:
   - asset classes and issue/burn policy;
   - spot, LP fees, dust, and withdrawal;
   - zUSD fees, collateral, redemption, liquidation, redistribution, and
     Stability Pool;
   - oracle submission, dispute, aggregation, freshness, and recovery;
   - perps funding, liquidation, insurance, bad debt, and terminal close;
   - protocol-token buy-and-burn;
   - proof-reward reserve accounting;
   - both sealed-bid workflows;
   - Tau escrow deposit, withdrawal, outage, and rejoin.
3. Keep emergency zUSD shutdown excluded and unreachable for the first launch
   profile.
4. Define the global state projection and complete value-delta algebra.
5. Rebuild the BDD contract from the closed registry. Every command receives
   happy, rejection, authorization, cancellation where applicable, recovery,
   and terminal scenarios.

Exit gate: no enabled command has `GAP`, `UNKNOWN`, or an unnamed economic
owner.

The helper G1 slice on the exact subject
`e8059cb5e27e80c2f8ba627501d6097f3c5e6b0c` records the source-authoritative
33-command and 8-disabled-command partition in
`docs/research/PRODUCTION_READINESS_G1_SEMANTICS_V1.json`. The received
10-disabled count remains recorded as non-authoritative. The slice also
declares the global economic state projection and value-delta algebra and
leaves all nine profile decisions `OPEN`. The exact-subject BDD companion
`docs/research/PRODUCTION_READINESS_G1_BDD_V1.json` gives every command one
research-only workflow and 267 scenario obligations; all scenarios remain
`UNIMPLEMENTED_RESEARCH_SCENARIO`. The G1 exit gate therefore remains blocked
and these artifacts do not change any production claim.

Replay the slice with:

```bash
python3 tools/check_production_readiness_g1_semantics.py --check --json
python3 tools/check_production_readiness_g1_bdd.py --check --json
```

### G2: Complete the deterministic functional core

Dependencies: G1.

Run economic modules in parallel after their shared ABI is frozen:

1. Asset transfer, spot, LP, fees, and buy-and-burn.
2. Oracle lifecycle.
3. zUSD borrowing, repayment, redemption, liquidation, redistribution, and
   Stability Pool.
4. Perps open, close, funding, liquidation, insurance, and terminal settlement.
5. Seller auction and private swap commit/reveal/cancel/expire/settle.
6. Tau escrow ingress, withdrawal, acknowledgment, fallback, and rejoin.
7. Proof-reward accounting.

For each module:

- implement total typed Rust transitions using checked integer arithmetic;
- preserve immutable state and typed rejection;
- emit a complete delta, terminal obligations, and effect plan;
- add a Python oracle that is independent of the Rust implementation;
- prove rejection is an exact no-op;
- retain named semantic mutants;
- remove the current research-disabled partition only as each command clears
  its complete gate.

Exit gate: all 33 commands have complete semantics; the value oracle reports
33/33 and `production_ready=true`.

### G3: Complete FormalGate

Dependencies: G1; module proofs may proceed alongside G2.

1. Use ESSO for bounded state-machine properties:
   - nonce/retry;
   - command lifecycle;
   - oracle recovery;
   - atomic publication;
   - reopen and reauthorization;
   - outbox redelivery;
   - migration;
   - no-bypass;
   - Tau outage/rejoin;
   - validator finality control.
2. Run pinned private ESSO with both Z3 and CVC5. Retain exact solver versions,
   model hashes, results, and disagreement/unknown rejection.
3. Use Lean for:
   - unbounded conservation and liability arithmetic;
   - SRGD/AGQE and occurrence-stream results;
   - per-command invariant preservation;
   - batch-fold preservation;
   - the global composition theorem.
4. Use Tau Language for pinned policy/profile checks whose supported runtime
   semantics have been independently established. Tau remains a verifier lane.
5. Prove one shared formal trace connects command, context, state, candidate,
   history, proof, publication, and effect models.
6. Keep cryptographic soundness, `f <= 2` validator behavior, filesystem
   durability, oracle authority, destination idempotency, and inventory
   completeness as explicit premises.

Exit gate: every M6-R01 through M6-R13 row has same-subject formal evidence and
the top-level trace theorem compiles without placeholders or hidden user
axioms.

### G4: Implement the production ZenoLedger imperative shell

Dependencies: G1 ABI freeze. It can run in parallel with G2 and G3.

1. Implement an authority-critical Rust ZenoLedger v1 daemon.
2. Store complete publication bundles in append-only, content-addressed block
   files.
3. Advance one canonical HEAD with expected-head compare-and-swap, file and
   directory fsync, and deterministic crash recovery.
4. Require canonical reopen to reconstruct the complete history and reproduce
   the exact durable layout.
5. Require fresh reauthorization after restart or authority-epoch change.
6. Implement a Tendermint-style round/lock finality protocol for seven
   equal-weight validators:
   - five matching precommits finalize;
   - each validator persists and validates the complete block before signing;
   - individual Ed25519 signatures are used initially;
   - BLS aggregation remains disabled until separately qualified.
7. Atomically bind state, history, nullifiers, economic certificate, finality,
   proof record, writer epoch, and outbox.
8. Restrict the outbox to genuine external Tau effects. Internal ledger balance
   changes commit inside the state transition.
9. Treat acknowledgment as a subsequent core transition.
10. Keep the Python filesystem store as a differential crash oracle, without
    production credentials.

Exit gate: independent-process concurrency, kill-point, power-loss simulation,
reopen, quorum, and retry tests produce exactly PRE, POST, or fail-closed
rejection.

### G5: Complete runtime refinement

Dependencies: G2 + G3 + G4.

1. Define total canonical projections for every runtime state, command, context,
   result, proof, finality certificate, publication, and effect.
2. Make the projection checker resolve, import, and execute every named
   projection.
3. Use the same Rust transition crate in direct ZenoLedger execution and RISC0
   guests.
4. Execute BDD scenarios through the real node submission entrypoint.
5. Compare complete outcomes, including post-state, history, nullifier, delta,
   proof, finality, outbox, and epoch.
6. Convert `apply_app_tx` and all legacy adapters into proposal-only clients.
7. Reject any accepted runtime value lacking a formal projection.
8. Run Python/Rust, direct/guest, and node/formal differential campaigns.

Exit gate: `RuntimeRefinementGate(P)=true` for the exact promotion subject.

### G6: Complete mounted direct M6

Dependencies: G5.

1. Generate the writer, entrypoint, credential, and effect inventory from the
   actual production build.
2. Route API, CLI, recovery, migration, administration, Tau adapters, proof
   callbacks, and workers through one ZenoLedger submission/publication
   capability.
3. Remove filesystem credentials and imports that permit legacy direct writes.
4. Require every enabled inventory row to hold:

```text
SPECIFIED
IMPLEMENTED
PROVED
MOUNTED
TESTED
TERMINAL_COMPLETE
MIGRATABLE
NO_BYPASS
RELEASE_BACKED
```

5. Require disabled features to hold `DISABLED_PROVED_NO_WRITER`.
6. Run direct execution in shadow, multi-validator testnet, crash, partition,
   Tau-outage, Tau-rejoin, and migration campaigns.
7. Verify that Tau certificates can assist normal operation and cannot replace
   ZenoLedger finality.

Exit gate: zero open enabled writer rows, zero bypass mutations, complete
direct-execution replay, and `M6DirectReady(P)=true`.

### G7: Complete and integrate ZRPF

Dependencies: G2 + G3; activation depends on G6.

1. Replace the current mismatched M6 RISC0 core with the production Rust
   transition crate.
2. Make each leaf execute up to 16 sequential commands and emit the complete
   `ZRPFRootJournalV2` projection.
3. Implement every enabled economic lane and route, including effects and
   terminal obligations.
4. Build the fixed 8-by-8 recursion:
   - 64 leaf receipts;
   - 8 aggregation receipts;
   - 1 root receipt;
   - 1,024 commands maximum.
5. Verify every child via exact image ID and journal bytes.
6. Pin toolchain, guest images, verifier profiles, release registry, and
   canonical codecs in the promotion subject.
7. Admit verified roots through the same ZenoLedger commit capability as direct
   execution.
8. Require full direct/ZRPF parity for state, deltas, history, nullifiers,
   outbox, and reject behavior.
9. Generate and preserve the full 73-receipt real replay.
10. Optimize until 1,024 commands meet a 60-second p95 on pinned qualification
    hardware.
11. Preserve direct execution automatically when proving is unavailable or
    late.
12. Keep proof-mining as a reward market without fork-choice or settlement
    authority.

Exit gate: the RISC0 semantic-surface and ShapeForge admission gates report
activation eligible, full replay passes, performance passes, and
`ZRPFReady(P)=true`.

### G8: Production security, operations, and release

Dependencies: G6 + G7.

1. Complete key generation, backup, rotation, revocation, validator replacement,
   and incident ceremonies.
2. Test Byzantine equivocation, two-node loss, network partitions, censorship,
   stale Tau profiles, corrupt blocks, proof substitution, and destination
   failures.
3. Require full validators to reject invalid transitions even when presented
   with a quorum certificate.
4. Require light clients to verify the ZRPF proof and finality certificate.
5. Produce reproducible builds, SBOM, dependency provenance, signed release
   artifacts, genesis, and deployment manifests.
6. Run independent code, cryptography, economic, and operations reviews.
7. Run shadow, public testnet, bounded-value canary, and progressive limit
   stages.
8. Permit promotion only when every receipt binds the same
   `M6PromotionSubjectV2`.

Exit gate: `ProductionReady(P)=true`; no unresolved authoritative state,
liability, effect, terminal path, credential, or entrypoint gap.

## Verification policy

Every critical obligation follows RIPR:

```text
Requirement
-> Independent oracle
-> Production observation
-> Refutation evidence
```

Minimum evidence:

- Oracle grade 4 for economic arithmetic and connective theorems.
- Oracle grade 3 or stronger for runtime, durability, migration, and proof
  admission.
- Boundary values at zero, one atom, maximum neighbors, overflow, dust,
  deadlines, epoch changes, price thresholds, and quorum thresholds.
- Stateful histories covering replay, reordering, stale heads, repeated claims,
  crash recovery, cross-epoch evidence, and Tau outage/rejoin.
- At least one named mutant for every formal invariant.
- Current exact-head test runs split into bounded groups with explicit timeouts;
  partial or stalled runs carry no pass claim.

Mandatory final gates include:

```text
M6 value oracle: 33/33, production_ready=true
M6 writer inventory: zero open enabled rows
M6 global ATDD checker: clean exact subject
ESSO Z3/CVC5: agreement, no UNKNOWN
Lean: complete build, no placeholders
Rust: test, Clippy, Miri, Kani, codec parity
RISC0 semantic surface: activation eligible
ZRPF: full 73-receipt replay and performance target
production boundary: M6 mounted and release ready
deployment no-bypass: complete inventory and killed bypass mutants
```

## Agent execution protocol

- Use one integration owner and at most three concurrent implementation agents
  per wave.
- Luna or Terra Max handles ordinary implementation.
- Sol reviews critical core, shell, proof, and promotion work.
- Agents write only in isolated worktrees and receive disjoint task-graph nodes.
- Each node records exact dependencies, writable paths, invariant, authority
  boundary, failing evidence, required commands, artifact hashes, nonclaims,
  and completion receipt.
- Run five adversarial review roles at G1, G5, G7, and G8:
  1. economics and custody;
  2. authority, replay, and no-bypass;
  3. concurrency, crash, and recovery;
  4. proof, codec, and ZRPF substitution;
  5. user workflows, cancellation, recovery, and terminal reachability.
- ShapeForge records one typed delta per change. Cross-axis claims require an
  explicit invariant. Its most important refinement is:

```text
economic evidence
-> release-selected verifier
-> opaque verified witness
-> current-head publication recheck
-> atomic ZenoLedger commit
```

Agent review remains advisory. Deterministic gates own merges and promotion.

## Assumptions retained for this plan

- ZenoLedger remains sovereign economic truth.
- Tau-only external deposits and withdrawals are the initial external-I/O
  profile.
- Internal DeFi operation continues during Tau outage; Tau withdrawals remain
  pending.
- The validator profile is seven validators with five signatures and an
  explicit `f <= 2` safety/liveness premise.
- The launch command registry contains the current 33 commands, including both
  sealed-bid modes.
- Emergency zUSD shutdown remains excluded from the first production profile.
- ZRPF targets 1,024 commands with 60-second p95 qualification.
- These parameters come from earlier planning records and must be reconfirmed
  during G1 because they may be stale. They carry no present implementation or
  production-readiness claim.

The first execution slice is G0 only: preserve the dirty checkout, establish
disk safety, create the isolated subject, and commit the plan, task graph,
coverage ledger, and checker before any functional change.
