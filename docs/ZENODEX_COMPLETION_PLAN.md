# ZenoDEX whole-program value-safety completion plan V3

This is the implementation contract selected by the September 4, 2026 user
directive. It reconciles the recovered August V2.1 scope with the O-008 repair
architecture and parallel semantic, operational-authority and observational work.
The executable dependency graph is
[`ZENODEX_WHOLE_PROGRAM_PLAN_V3.json`](research/ZENODEX_WHOLE_PROGRAM_PLAN_V3.json).
Selection through the active-plan registry is a separate, exact-subject,
research-only admission. This document grants no economic or release authority.

## Objective and starting subject

Complete the formal functional core across twelve economic lanes, connect it to
the actual verifier and publisher, and qualify every reachable value-moving path
against one release subject. The requirements floor is **103 capabilities, four
cross-lane routes and four exclusions**. Discovered obligations expand this
floor. A disabled required feature is incomplete.

The integration base is `c6a9fd028ded9224427a645c1217d0ce576f78af`.
Its retained O-008 packet reports `formal_core_complete=false`,
`whole_value_movement_safe=false` and zero promoted value-movement gates.
The historical D+ findings have retained regressions; that grade is historical.
The base Python projection has no publisher consumer or Rust projection twin.
Real Python cryptographic verification, allocation continuity and complete lane
producers remain open. The SEC candidate
`b802c942a8c7ccf8bf17b1b61021cbd8c960b7ea` requires separate integration review.

Four milestones must be reported separately:

1. Isolated slice qualified: a restricted profile works end to end on test state.
2. Formal core complete: every intended command has complete semantics,
   preservation proofs and implementation-refinement evidence.
3. Production value-safety qualified: the exact deployment also satisfies
   publication, authentication, durability, recovery and complete mediation.
4. Whole product complete: required clients, workflows, operations and performance
   are delivered. M6 completion cannot end at SHADOW.

## Architecture and outcome contract

ZenoLedger owns economic ordering and publication. Tau supplies only qualified,
version-pinned integration capabilities. Governance and agents submit constrained
commands and receive no independent publication capability. Preserve historical
wire decoding; semantic wire changes require a versioned successor and migration.

zUSD issuance and monetary burns belong to its collateralized monetary kernel.
ZDEX buy-and-burn consumes its designated fee allocation through Spot and burns
exactly the ZDEX received in that same occurrence. Treasury or transfer burns
cannot substitute for that route.

The shell acquires and authenticates immutable store snapshots. The functional
core takes those values explicitly. Publication revalidates the current head and
authority at the commit boundary. Neither a core-parameter ban nor a constructed
snapshot proves provenance.

| Outcome | Economic state, replay, history and outbox contract |
| --- | --- |
| Precommit rejection | This attempt adds no economic changes, replay consumption, history or effects. |
| Committed success | One linearization point commits the complete transition and required effect plan. |
| Exact committed retry | Return the original committed identity; add no second transition or effect. |
| Indeterminate client knowledge | Resolve durable status by committed identity; response loss does not imply rejection. |

Rejection purity concerns logical economic state. Database housekeeping or a
concurrent winner may change physical files. Older WF-01/BDD-003 and related
requirements allow nonce and rejection-history consumption. V3 supersedes that
rule for **precommit rejection**. Historical normative artifacts remain intact;
their committed-rejection semantics require explicit outcome classification and
version-transition work before any V3 runtime-refinement claim.

SHADOW consumes committed snapshots through a read-only capability, runs outside
economic commit decisions and writes bounded diagnostics separately. Its absence,
failure or disagreement cannot alter roots, profiles, economic commitments or
external effects. Missing observations remain visible evidence gaps. Local store
consistency does not establish cryptographic or deployment provenance.

Prove journal sufficiency before adding fields: derive allocations from
authenticated state and pinned ownership policy where sufficient; commit only
missing information. Keep immutable release identity, active policy epoch and
individual publication identity separate. A receipt-verifier subprocess provides
cryptographic checking under a trusted host; it does not protect a compromised
publisher process or operating system.

## Work graph and exit conditions

| Task | Dependencies | Exit condition |
| --- | --- | --- |
| W00 Integration subject | None | Reconcile requirements, decisions, retained findings and exact candidate deltas; preserve concurrent work. |
| W01 Scope and authority | W00 | Map launchers, ingress, signing, writers and effect sinks across languages to capabilities and lifecycles; unknown paths block closure. |
| W02 Policy and semantics | W01 | Recover decisions and complete state, commands, outcomes and ownership; interview only about remaining policy gaps. |
| W03 Real receipt verification | W00; fixed verifier contract | Measured Rust/Python bridge verifies a real rebuilt-image receipt and exact journal; malformed, foreign, fake and unavailable outcomes reject. |
| W04 Allocation derivation | W02 | Typed Rust/Python projection, independent reference, formal relation, complete authenticated snapshot and predecessor binding. |
| W05 Isolated SHADOW | W04; committed snapshot contract | Useful agreement/disagreement with provenance and complete observational isolation on an isolated ledger. |
| W06 Isolated publication | W02, W03, W04, W05 | Receipt/context/allocation/current-store checks lead to one atomic state/history/replay/receipt/epoch/outbox commit. |
| W07 Lane lifecycles | W02 | Every required lane has enabling, rejection, authorization, cancellation, recovery, terminal and version-transition paths. |
| W08 Cross-lane composition | Relevant W07 lanes; W06 contract | Purchase-and-burn, zUSD liquidation, perps epoch and strategy Spot routes have exact pairing, ownership, aggregation and atomic outcomes. |
| W09 Formal/runtime refinement | Starts at W02; finishes over W06-W08 | Per-command preservation and trace composition refine actual finite-width arithmetic, decoding and outcomes. Hash equality alone is insufficient. |
| W10 Correctness-critical ZRPF | W03, W08, W09 | Actual module/coordinator/route/epoch proofs bind images, journals, assumptions, order and context. |
| W11 Production shell | W06-W10 | Datastore refinement, restart, concurrency, delivery ancestry, migration, fencing and deployment-complete mediation qualify on isolated infrastructure. |
| W12 Release assessment | W01-W11 | Independent replay on one exact release subject closes blockers and produces a promotion candidate. Live activation requires separate approval. |
| W13 Product and scaling | Corresponding safety milestones | Frontend agents finish workflows; operational polish and ZRPF performance changes preserve contracts and requalify changed builds. |

W01 investigation and minimum semantic work begin immediately. W03 development
does not wait for unrelated documentation. Independent implementation tasks have
disjoint owned files. A task may start a boundary-local subtask before all closure
dependencies finish; that does not close the enclosing task.

W07 covers ASSET_TRANSFER, SPOT_LIQUIDITY, FARM_INCENTIVES, ZDEX_TOKENOMICS,
ZUSD_MONETARY, PERPS_MARKET, ORACLE_MARKET, SEALED_AUCTION, STRATEGY_ESCROW,
PROOF_REWARDS, EXTERNAL_CUSTODY and GOVERNANCE_MIGRATION. Each lane requires
separate accounting and authorization obligations, exact physical-location versus
claimant-liability accounting, rounding ownership, resource bounds, withdrawal,
repayment, cancellation and terminal disposition. Recover historical policy and
design historical verification and migration before freezing new formats.
External finality and shared-asset coexistence gaps remain blockers.

## Acceptance and evidence boundaries

```text
Certified initialization
+ per-command invariant preservation
+ runtime/formal refinement
+ complete publication mediation
+ concrete durability and recovery
+ committed-effect ancestry
=> release-specific value safety under explicit assumptions
```

The projection must distinguish unsafe runtime states sufficiently to establish
the claimed property. Mapping unsafe runtime behavior to a safe abstraction is
insufficient.

Lean owns accounting, authorization, ownership and trace theorems. ESSO with pinned
solvers supplies scoped state-machine evidence. Kani checks declared Rust bounds.
Julia/Python provide independent reference computations. RISC0 binds execution to
exact guests and journals. Tau claims require replay on the selected
implementation. Research Kernel, LEAP, TheoremSearch, Kurate and reviewers are
advisory and grant no authority.

Keep initial ZRPF limits of 1-8 receipts per route and 1-64 commands per epoch.
Every workflow needs positive controls, independent guard failures, boundary
cases, stateful histories and meaningful semantic mutants. Required cases are
wrong-context or stale-head proofs; conserved but unauthorized movement; missing,
duplicate or misattributed allocation/terminal rows; state growth and overflow;
competing writers, exact retries and response loss; complete PRE/POST or
fail-closed crash recovery; restart without restored writer authority; delivery
ancestry and destination idempotency; profile revocation and old-writer exclusion;
unknown value writers; and SHADOW failures with unchanged economic behavior.

## Execution and reporting

Reuse existing specifications before requesting policy decisions. Qualify an
isolated ledger first. This integration authorizes no live balance migration,
profile activation or production promotion. Unknown policy values remain disabled
or symbolically constrained until approved. Tests cannot select business policy.

Astra owns integration and critical mathematical review. Implementation agents
receive bounded tasks. Independent Opus review is advisory when reachable; the
prior timed-out requests produced no verdict. The prior two read-only Codex
reviews and unavailable Research Kernel strategy run are historical limitations,
not current replay evidence. The recovered September analysis and A+ design are hash-bound in the graph.
Their G1-G14 dispositions and inherited or superseded decisions are recorded in
[`ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md`](research/ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md).
A finding remains open until its own acceptance evidence is established.

Full proof generation and large solver builds run remotely. Material remote
expenditure needs scoped authorization. The September 4 continuation additionally
authorizes careful deletion of verified stale workspaces and regeneratable build
artifacts after inventory and ownership checks; source changes, receipts,
sessions and recovery evidence must remain recoverable.

Report implemented changes, proved obligations, isolated qualification and
production promotion separately. No review grade, test count or packet count is
a whole-program completion percentage. Replay the graph with
`python3 tools/check_whole_program_plan_v3.py`; its success establishes only the
declared scope, source pins and dependency structure.
