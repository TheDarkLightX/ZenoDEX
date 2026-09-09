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

## Consolidated completion checklist

Assessment date: September 8, 2026. Exact integration subjects are recorded in
the progress ledger and linked evidence below. This is a closure checklist,
not a fresh deployment audit. Linked older evidence retains
its exact original subject and bounds. A checked item below denotes the stated
scoped deliverable; it does not close the enclosing workstream. The
[September 8 assessment](research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.md)
establishes a reproducible advisory baseline: Fable estimates 23.4% for V3 and
21.0% for the formal core; Opus estimates 28.9% and 23.4% using different weights.
These estimates retain their judgment ranges and evidence limitations. They do
not change the closure counts below or measure remaining code or time. The older
35–45% handoff estimate had no equivalent scored baseline.

### Delivery audit at the September 8 checkpoint

The committed checklist at `c159bd59bc05bd857a96f695aba8ea6b849d8bba`
contains **15 checked rows out of 44**.
This inventory must not be converted into a completion percentage: a row
retaining historical evidence and a row completing an entire lane have unequal
scope, and the retained evidence does not all qualify the current release.

The earlier checkpoint `2f769e7ba2d578b3518f91c882a56430072f7f70`
had 13 checked rows out of 42. Between those subjects, **29 rows remained open
and no previously open row was completed**. Two completed rows were added:
historical claim correction and finite effect-plan construction/encoding.
The first W09 open row was narrowed as construction work advanced; universal
runtime refinement and the combined lane gate remained open. Thus the higher
checklist count must not be reported as a gain in whole-plan completion.

| Acceptance unit | Recorded complete at this checkpoint |
| --- | --- |
| V3 workstream exit conditions | 0/14 (0% fully closed) |
| Complete lane lifecycles | 0/12 (0% fully closed) |
| Complete required cross-lane routes | 0/4 (0% fully closed) |
| Release value-movement gates | 0/12 (0% qualified) |

These closure figures coexist with implemented and proved partial work. The
[transfer outcome evidence](research/ZENODEX_TRANSFER_FINITE_OUTCOMES_20260908.md)
records the exact effect-plan ownership and encoding results, their replay,
the repaired test failure and remaining constructor/runtime obligations.

Subsequent status reports must compare against this fixed checkpoint: identify
existing open obligations completed, remaining obligations narrowed, regressions
and newly discovered obligations separately. Adding a completed support row
does not count as closing an existing obligation. A claimed closure needs its
acceptance evidence and exact subject; a percentage alone supplies neither.

The plan checker still records `formal_core_complete=false`,
`whole_value_movement_safe=false` and zero closed value-movement gates out of
twelve. That last ratio is release-gate closure, not implementation completion.
The 103-capability floor, four routes and four exclusions remain the denominator
for scope; each capability needs its own complete evidence chain before counting
it complete. Counting the unequal checklist items below cannot estimate time or
effort remaining.

### Executable progress tracking

The [progress ledger](research/ZENODEX_V3_PROGRESS.json) records scoped support
work against the unchanged capability, route, exclusion and task inventories.
The [checker](../tools/check_v3_progress.py) derives changed files and structural
observations from exact Git subjects. Each entry names its obligation,
acceptance condition, simpler alternative, rationale and stopping point.
Documentation or a saved test result cannot close a baseline capability.

```bash
python3 tools/check_v3_progress.py --json
python3 tools/check_v3_progress.py --replay --gate receipt_copy_boundaries_v1 --json
```

The default command reports historical records and source drift. The second
command freshly runs the one registered receipt-copy gate. Its result applies
only to that gate's declared source and acceptance scope. The checker keeps
review acceptance separate from execution and retains the local-tool trust
assumption. There are no registered whole-capability or whole-core closure
gates in this initial tracker.

Before changing records, retain the last reviewed commit containing the ledger
and pass it with `--baseline-commit` to check that existing entries were
preserved. Corrections append a superseding record. Omitting that option does
not establish historical preservation. The initial entries cover four recent
committed changes; earlier work still requires explicit reconciliation.

Structural observations and repeated-work findings guide review. Fewer lines,
functions or branches do not prove equivalence, minimality or optimality.
Complete the named acceptance check and review before opening adjacent work;
extend this tracker only when a concrete missing check prevents that decision.

### W00-W06: subject, semantics, verification and publication

- [x] W00: preserve the original scope and isolated integration subject in this
  plan and its executable graph; retain the
  [SEC candidate review](research/ZENODEX_WHOLE_PROGRAM_V3_SEC_CANDIDATE_REVIEW.md).
- [ ] W00: reconcile all outstanding candidate dispositions against the final
  selected release, including any required selective SEC integration.
- [x] W00: correct thirteen unsupported historical registry records to disputed;
  retain the original assertions and missing evidence requirements in the
  [reconciliation](research/ZENODEX_DERIVATIVE_CLAIM_RECONCILIATION_20260908.md).
- [x] W01: retain the cross-language
  [authority and effect map](research/ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md).
- [ ] W01: qualify every deployed launcher, writer, administrative path and
  effect worker together; resolve unknown reachability and alternative writers.
- [x] W02: define the pure-core/snapshot boundary, distinct publication outcomes
  and separate release, policy-epoch and publication identities.
- [ ] W02: recover approved policy choices and close complete semantics,
  ownership and terminal dispositions for every required command family.
- [x] W03: retain the measured verifier bridge and
  [five genuine receipts](research/ZENODEX_WHOLE_PROGRAM_V3_FINAL_RECEIPT_QUALIFICATION.md)
  for the qualified historical one-command, zero-custody subject.
- [x] W03: retain real sealed BLS execution and its malformed/subgroup checks in
  the [completion follow-up](research/ZENODEX_V3_COMPLETION_FOLLOWUP_20260905.md).
- [ ] W03: qualify genuine receipts and measured backends for the final changed
  guests, authentication profile and release subject.
- [x] W04: implement restricted Python/Rust allocation projection and
  [module/coordinator binding](research/ZENODEX_WHOLE_PROGRAM_V3_ALLOCATION_BINDING_REVIEW.md).
- [ ] W04: close allocation derivation for all lanes, complete snapshots,
  shared-asset ownership and authenticated predecessor binding on that subject.
- [x] W05: retain an isolated read-only SHADOW consumer with bounded diagnostics
  and [observational isolation tests](research/ZENODEX_WHOLE_PROGRAM_V3_SHADOW_EVIDENCE.md).
- [ ] W05: qualify the complete intended observation sources and witness
  provenance; retain missing or unverified observations as gaps.
- [x] W06: mount the isolated raw-evidence pipeline into the SQLite publisher,
  including store-derived allocation, BLS verification, CAS and exact retries;
  retain the [mounted evidence](research/ZENODEX_WHOLE_PROGRAM_V3_MOUNTED_PIPELINE_EVIDENCE.md).
- [x] W06: implement and test distinct precommit, committed-retry and
  indeterminate-response outcomes in the
  [publication follow-up](research/ZENODEX_V3_COMPLETION_FOLLOWUP_20260905.md).
- [ ] W06: qualify the complete current publication path with genuine matching
  receipts. The historical real-receipt batch and later synthetic-RISC0 mounted
  tests are different evidence subjects.

### W07: twelve complete lane lifecycles

Every row requires the applicable enabling, authorized success, rejection,
cancellation, recovery, terminal and version-transition behavior. These are
unclosed completion requirements, not assertions that every listed component
is absent. Existing policy decisions must be recovered before asking for new
ones. The [lane map](research/ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md)
routes requirements to the earlier implementation; newer scoped proof and
repair checkpoints are linked below this checklist.

- [ ] ASSET_TRANSFER: complete registration, managed issuance/burn, fee policy,
  transfer authorization and shared-state lifecycle/refinement.
- [ ] SPOT_LIQUIDITY: complete pool and LP lifecycle, rounding/dust ownership,
  cancellation, closure and authenticated routes.
- [ ] FARM_INCENTIVES: complete funding, activation, accrual, claims,
  cancellation and terminal drain without inventing emission policy.
- [ ] ZDEX_TOKENOMICS: complete designated fee funding, exact purchase/burn
  pairing, retained supply and applicable host/staking claims.
- [ ] ZUSD_MONETARY: complete collateralized issuance/burn, repayment,
  liquidation, recovery and shared-asset version coexistence.
- [ ] PERPS_MARKET: complete funding, margin, insurance, ADL/bankruptcy and
  terminal closeout ownership.
- [ ] ORACLE_MARKET: complete occurrence/finality authentication, query/bond,
  reward/dispute/clawback and terminal policy.
- [ ] SEALED_AUCTION: complete bond/inventory custody, reveal, expiry,
  cancellation, refund/slash and authorized winner settlement.
- [ ] STRATEGY_ESCROW: complete authorized trigger, replacement, expiry,
  recovery and Spot route consumption.
- [ ] PROOF_REWARDS: complete funding ancestry, eligibility, replay/nullifier
  scope, payout and task termination.
- [ ] EXTERNAL_CUSTODY: complete registered origins/destinations, qualified
  finality, committed delivery ancestry, recovery and destination idempotency.
- [ ] GOVERNANCE_MIGRATION: complete command-only governance, policy epochs,
  migration continuity and old-writer exclusion.

### W08-W13: composition, refinement and release completion

- [ ] W08: qualify designated-fee Spot purchase and exact same-occurrence ZDEX burn.
- [ ] W08: qualify atomic zUSD liquidation across collateral, debt and supply.
- [ ] W08: qualify ordered perps epoch settlement and terminal ownership.
- [ ] W08: qualify strategy-triggered Spot execution and escrow recovery.
- [x] W09: retain scoped proofs of registered supply support, shared accounting,
  finite recomposition and derived row/byte capacity.
- [x] W09: prove finite managed/transfer acceptance and rejection outcomes,
  accounting and admission-preserving traces under explicit premises.
- [x] W09: prove the checked forward transfer algorithm relation and retain
  runtime comparisons, arithmetic-order and capacity/no-op counterexamples.
- [x] W09: construct finite managed/transfer effect plans and prove per-owner
  transfer attribution; derive their explicit model encoding's 8,192-byte bound
  and retain [bounded complete-byte comparisons](research/ZENODEX_TRANSFER_FINITE_OUTCOMES_20260908.md#exact-effect-plan-encoding-and-derived-byte-bound).
- [ ] W09: finish concrete constructor/journal correspondence, universal codec/parser and
  Python/Rust execution refinement; close the combined lane gates.
- [ ] W09: close per-command and composed-trace obligations across all twelve
  lanes and all four routes, including authorization separately from accounting.
- [ ] W10: qualify actual module/coordinator/route/epoch proofs for the final
  subject, including required multi-command, custody and context cases within
  the admitted 1-8 receipt and 1-64 command limits.
- [x] W11: retain tested logical publication outcomes and the
  [live writer identity repair](research/ZENODEX_WRITER_AUTHORITY_IDENTITY_20260905.md).
- [ ] W11: qualify concrete datastore refinement, crash/restart authorization,
  migration, writer fencing, committed delivery and deployment-wide mediation.
- [ ] W12: replay all applicable gates against one exact release subject;
  resolve blocking findings and prepare the independently assessed candidate.
- [ ] W13: finish required client workflows, operational usability and scaling;
  requalify changed builds without weakening the established contracts.

## Execution and reporting

Each work item must name its enclosing V3 obligation, the runtime caller or
consumer it connects, the decisive acceptance check and a stopping condition.
Finish and integrate reviewed work before opening adjacent proof or research
branches. A blocked check calls for a repair or an explicit dependency decision;
it does not justify expanding the task indefinitely.

Compare the direct implementation with existing helpers before adding another
abstraction. Simplify duplicated decisions or state when retained evidence shows
the smaller version preserves the contract. Keep independent oracles, negative
controls and authority checks. Rerun completed checks or reopen a review only
for changed subjects, failures or unresolved concerns. Report which obligation
closed and which enclosing milestone remains open; activity counts do not
measure progress toward completion.

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

The September 7 user directive adds a post-correctness simplification pass
within W07, W09 and W13. The
[`execution addendum`](research/ZENODEX_POST_CORRECTNESS_SIMPLIFICATION_20260907.md)
records reviewed candidates, counterexamples and the qualification needed before
applying a patch. It leaves the admitted graph and safety milestones intact.

The September 8 [registered supply update checkpoint](research/ZENODEX_REGISTERED_SUPPLY_UPDATE_20260908.md)
proves complete-row/sparse-row update correspondence and records finite Python
observations. The subsequent
[registered lifecycle accounting checkpoint](research/ZENODEX_REGISTERED_LIFECYCLE_ACCOUNTING_20260908.md)
closes reconstruction for arbitrary covered canonical supply views and derives
managed lifecycle account totals from finite balance rows. Their composed
accounting update preserves all-asset physical holdings, including custody and
reserves, under explicit input assumptions. Authenticated snapshot
sourcing, complete shared-state refinement and production qualification remain
open in W04/W07/W09.

The [shared asset lifecycle checkpoint](research/ZENODEX_SHARED_ASSET_LIFECYCLE_20260908.md)
adds finite transfer materialization and proves that managed and transfer views
read and update one shared account source. The subsequent checkpoints below
cover finite recomposition and tested resource outcomes; complete runtime
refinement remains open.

The [asset-lane resource outcome repair](research/ZENODEX_ASSET_LANE_RESOURCE_OUTCOMES_20260908.md)
adds typed no-op rejection for POST-state row or byte excess in Python and Rust,
and enforces route-owned rejection decoding. Isolated runtime and shared wire
tests pass. Formal resource-aware traces and the wider qualification gates remain
open; this repair grants no publication authority.

The [finite recomposition checkpoint](research/ZENODEX_ASSET_LANE_FINITE_RECOMPOSITION_20260908.md)
subsequently proves exact managed balance and complete supply-table recomposition,
including dormant asset identities and the runtime tuple-key shape. Its fresh
Lean replay closes that arithmetic/table obligation. Derived resource admission,
complete mixed outcomes and universal runtime refinement remain open.

The [derived row-growth checkpoint](research/ZENODEX_ASSET_LANE_ROW_GROWTH_20260908.md)
then derives exact aggregate account-row counts and capacity conditions from
finite updates. It distinguishes new owners, existing owners, full burns and
reissue. Complete byte admission, mixed outcomes and implementation refinement
remain open; a row-count theorem does not close the formal core.

The [derived byte-accounting checkpoint](research/ZENODEX_ASSET_LANE_BYTE_ACCOUNTING_20260908.md)
adds exact escaping, decimal-width, comma and complete-supply byte relations,
and combines these with row growth into source-derived capacity criteria.
Independent Lean review and the retained fresh-build tests pass. Owned metadata
serializer correspondence, complete resource-aware outcomes and full runtime
refinement remain open; this checkpoint grants no publication authority.

The [finite managed-outcome checkpoint](research/ZENODEX_MANAGED_FINITE_OUTCOMES_20260908.md)
then derives accepted and rejected outcomes from owned finite tables, with
resource checks on the computed candidate. Admission, accounting, supply identity
and trace-prefix preservation are proved under explicit input assumptions.
Independent retained replay checks the theorem surface and 37 runtime cases.
Complete transfer and cross-lane outcomes, actual effect/journal constructor
correspondence and universal runtime refinement remain open.

The [finite transfer outcome](research/ZENODEX_TRANSFER_FINITE_OUTCOMES_20260908.md)
and [checked forward loop](research/ZENODEX_TRANSFER_FORWARD_LOOP_20260908.md)
checkpoints connect finite tables, ordered arithmetic failures and final resource
checks to the operational update order, with retained runtime comparisons.
The managed parity gates now include the finite resource rejection while keeping
the original economic-prefix controls. These close scoped W07/W09 dependencies;
they do not close a whole lane or a V3 milestone. Concrete effect/journal
construction, combined lane gates and universal runtime refinement remain open.
