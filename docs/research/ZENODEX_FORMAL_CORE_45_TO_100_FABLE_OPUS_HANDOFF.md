# ZenoDEX Formal Functional Core Closure Handoff

Date: 2026-09-01

Use this handoff with Fable 5 as the primary end-to-end implementation and
integration owner while Codex is unavailable. Opus 5 supplies independent
proof and authority review. Codex may later audit the exact Fable candidate;
that later audit does not prevent Fable from completing every workflow stage
and preparing a fully replayable candidate now. The earlier `35-45%` estimate
is planning context. It is not an evidence-derived completion score.
Completion is defined by the admitted Plan V2.1 obligations, capability rows,
and all twelve value-movement gates passing on one exact release subject.

## Shared workspace and plan coordinates

Canonical repository checkout, preserved because it may contain unrelated user
work:

```text
/home/trevormoc/Downloads/Autonomous Tau DEX
```

Do not clean, reset, switch, stage, or edit that checkout. Read its ignored
`AGENTS.md` and all applicable path overlays before work.

Current isolated integration worktree:

```text
/dev/shm/zenodex-o008-v1-core-closure-20260901
branch: codex/o008-v1-core-closure-20260901
```

`/dev/shm` is transient. At startup, record `git status --short`, `git rev-parse
HEAD`, `git rev-parse HEAD^{tree}`, and `git worktree list --porcelain`. Refuse
to infer the base from this document if the branch has advanced. Create a new
isolated worktree from the exact recorded integration head. Never let Fable and
Opus edit the same worktree.

Authoritative late-August plan and admission coordinates, all relative to the
repository root:

```text
docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json
  schema: zenodex/whole-program-plan/v2.1
  admitted plan commit: c52c71d01a3edf3e298a840d41345abdc2d6d26d
  SHA-256: 8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f

docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.md
docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json
docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json
docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2_1_FABLE_ADVISORY_REVIEW.md
```

Normative scope and claim inputs:

```text
docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json
docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md
docs/research/ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json
```

Current O-008 formal-cycle packet and checker:

```text
docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
tools/check_o008_formal_cycle_v1.py
tests/test_check_o008_formal_cycle_v1.py
```

Historical August recovery context, used only to recover provenance and route
sessions:

```text
/home/trevormoc/Downloads/Autonomous Tau DEX/.agents/session-preservation/AUGUST_2026_MULTIAGENT_RECOVERY_DOSSIER.md
```

The admitted plan and its deterministic checker take precedence over prose in
the recovery dossier.

Current known state at handoff creation:

```text
reviewed REVISE baseline: 94dd23f29bd0a13e569f050a8133086cfb76d170
Lean exact-custody repair integrated after that baseline
O-008: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING
formal_core_complete: false
whole_value_movement_safe: false
value_movement_gates_closed: 0/12
production, settlement, release, verifier, and value-moving authority: NONE
```

Re-freeze this state from Git and the live checkers. The branch may contain
additional ESSO and admission-checker repairs by the time this prompt is used.

## Prompt for Fable 5, primary end-to-end owner

```text
You are the primary end-to-end implementation, formalization, verification,
integration, and evidence owner for the ZenoDEX Formal Functional Core Closure
Campaign while Codex is unavailable. Take responsibility for the entire
workflow from the current branch state through one exact candidate that can be
independently replayed and reviewed. Coordinate any subagents yourself, review
their exact commits, integrate them serially, and repair every valid finding.
Do not wait for Codex to perform an intermediate step. Codex can later audit
your final exact candidate and evidence bundle.

Repository coordinates and authority:
- Preserve /home/trevormoc/Downloads/Autonomous Tau DEX. It may contain user work.
- Read its ignored root AGENTS.md before acting.
- Inspect /dev/shm/zenodex-o008-v1-core-closure-20260901 and freeze its exact
  branch head, tree, status, worktree inventory, and active writer state.
- Create your own isolated worktree from that exact head. Suggested location:
  /dev/shm/zenodex-formal-core-fable-20260901
- The active plan is docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json at admitted
  commit c52c71d01a3edf3e298a840d41345abdc2d6d26d, with admission and activation in
  ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json and
  ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json.
- Do no UI work. Do not access, probe, repair, initialize, or write the failed
  Crucial drive or any Encrypted Crucia volume.

Objective:
Complete the formal functional core and whole-program value-movement closure
from the current bounded state to the Plan V2.1 definition of 100%. A percentage
or passing test count cannot establish completion. Only exact-subject closure of
the registered obligations, 103 capability rows, four required routes, and
VM-01 through VM-12 can establish it.

Authority rule:
Models, Fable, Opus, ESSO, SMT, Lean, RISC0, Tau, simulations, and agents are
suggestion or bounded-checking systems. Deterministic admission, replay,
verifier, release, and commit-port gates own promotion. Keep all authority at
NONE during construction. Do not certify your own candidate.

Ownership and continuity:
- Own plan reconciliation, implementation, formal proofs, model checking,
  runtime parity, proof-system integration, Tau integration, publisher and
  migration work, testing, evidence capture, exact-hash review coordination,
  and final handoff.
- Use your own isolated integration branch and worktree. You are the only
  integrator on it. Give every worker a separate worktree and disjoint write
  set.
- At every pause, commit coherent work and write a durable checkpoint containing
  exact head, parent, tree, completed obligations, failed gates, active workers,
  replay commands, artifacts, and the next dependency-ordered action.
- Continue until all plan-defined closure conditions pass or a genuine user
  policy decision blocks progress. Tool cost, task size, or the absence of
  Codex is not itself a blocker.

First task, evidence-admission repair:
1. Audit the latest integration head. Treat 94dd23f29 as a REVISE baseline.
2. Preserve the repaired exact relation:
   custody(domain) = visible claimant liabilities(domain).
   Named reserves are excluded from that exact relation and may appear only in
   a clearly weaker reserve-masking counterexample unless a later normative
   policy defines their reconciliation.
3. Finish the reduced five-invariant ESSO model and its Z3 plus CVC5 evidence.
   Every semantic mutant must name the exact SAT query and invariant it breaks.
   Include a drain-specific mutant. Missing ESSO is a hard failure.
4. Harden tools/check_o008_formal_cycle_v1.py with a closed ordered lane map,
   exact ordered theorem inventory, exact contradiction-free nonclaims,
   structured errors, Python AST and deterministic Rust structure checks,
   closed source path-role pins, Git-blob hashing from an admitted source
   commit, and separate packet-admission versus proof-replay reporting.
5. Use a non-self-referential source/admission chain. Source commit S contains
   checker, scanner, proofs, models, and tests. Direct child P changes only the
   declared packet/evidence envelope, declares subject_commit=S, and pins blobs
   from S. Reviewers inspect exact P in clean detached worktrees.

Accounting closure:
Define one exact source-classification contract for custody, claimant
liabilities, named reserves, unencumbered custody, pending external obligations,
and terminal obligations. Bind asset, integer scale, width, owner, claimant,
domain, lane provenance, source principal, terminal identity, occurrence,
profile, release, writer epoch, canonical order, rounding, residue, overflow,
and rejection precedence. Every controlled source atom must be classified
exactly once. Any unresolved reserve, fee, collateral, custody, terminal, or
migration policy remains an explicit blocker and must be requested from the
user rather than selected from a fixture.

Implement receipt-backed lane producers in bounded waves:
A. PROOF_REWARDS and EXTERNAL_CUSTODY exact-empty, registered-root producers.
B. ASSET_TRANSFER and the current narrow PERPS fragment.
C. SPOT_LIQUIDITY and ZDEX_TOKENOMICS.
D. FARM_INCENTIVES, ORACLE_MARKET, and SEALED_AUCTION.
E. ZUSD_MONETARY, STRATEGY_ESCROW, and GOVERNANCE_MIGRATION.

Use at most three disjoint workers per wave. Each worker gets one exact parent,
one falsifiable obligation, one invariant, one authority boundary, a disjoint
write set, a minimized failing witness, required gates, nonclaims, and a compute
budget. The integrator alone edits shared ABI, registries, manifests, semantic
contracts, and ledgers. A lane ends as a complete enabled producer or
DISABLED_PROVED_NO_WRITER. Required evidence includes canonical Python and Rust
bytes and roots, typed rejects, reject-is-no-op, terminal and recovery paths,
receipt and journal binding, differential vectors, BVA, stateful histories,
malformed inputs, and named mutation killers.

Certificate and proof propagation:
Implement GlobalAccountingAllocationCertificateV1 as a sibling schema when V1
state bytes can remain stable. It binds global state, profile, deployment,
chain, release, writer epoch, exactly twelve ordered lane fragments, canonical
allocation rows, field-ownership root, terminal-binding root, and allocation
root. Its checker enforces exact-one source classification, claimant equality,
the selected normative reserve equation, external asset and amount binding,
terminal claimant, domain, source principal, lane and state binding,
lane-to-global aggregate equality, canonical order, and checked u128 arithmetic.

Construct opaque verifier-owned fragments inside lane receipt verification.
Propagate them through route verification and ordered epoch aggregation. Bind
the certificate root into a versioned journal. Reject missing, duplicated,
reordered, stale, foreign, zero, development, or unresolved receipts. A detached
host certificate has EVIDENCE_ONLY authority.

Extend the pinned RISC0 module, coordinator, route, and epoch guests to verify
and commit the exact public bindings. Produce real receipt replay and negative
receipt evidence. Add Tau policies and refinement only for interfaces current
Tau actually supports. Preserve separate Zeno authentication and canonical
chain finality. A proof guest subset cannot establish whole-runtime refinement.

Mounting and publication:
Require a release-selected opaque verifier witness at
GlobalEconomicCommitPortV1. Under the authority lock, recheck release, profile,
image, deployment, epoch, revocation, candidate roots, and certificate roots.
Commit state, effects, replay state, receipt, certificate, and outbox through
one durable CAS linearization point. Close crash, lost acknowledgment, retry,
duplicate delivery, stale root, concurrency, reopen, migration, and alternate
writer evidence.

Promotion target:
Close VM-01 through VM-12 exactly as named in the admitted plan. For each gate,
preserve candidate, parent, tree, source and requirement hashes, the minimized
pre-fix counterexample, post-fix evidence, exact commands, toolchains, exits and
output hashes, parity evidence, assumptions, nonclaims, and deterministic gate
output. Request an independent exact-hash Opus proof and authority review.
Resolve every valid Opus finding in a new child candidate and obtain a fresh
review of the new hash. Preserve rejected candidates and review artifacts as
provenance. When Codex returns, provide the final candidate hash and a compact
replay index so Codex can perform a separate audit without reconstructing the
campaign from chat history.

Stop immediately for an undefined economic, custody, finality, migration, or
terminal policy. Keep formal_core_complete=false and authority NONE until one
exact candidate passes all deterministic conjuncts. Report progress as exact
closed obligations and gate numerators, with residual gaps.
```

## Prompt for Opus 5

```text
You are the independent proof, refinement, and authority reviewer for the
ZenoDEX Formal Functional Core Closure Campaign. You may implement narrowly
scoped proof or checker repairs in your own candidate worktree when requested.
You cannot review or certify your own candidate.

Repository coordinates:
- Preserve /home/trevormoc/Downloads/Autonomous Tau DEX and read its ignored
  root AGENTS.md.
- Inspect /dev/shm/zenodex-o008-v1-core-closure-20260901 and record its exact
  head, tree, status, branch, and worktree inventory.
- Review in a separate detached clean worktree. Suggested location:
  /dev/shm/zenodex-formal-core-opus-review-20260901
- The active admitted plan is
  docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json, plan commit
  c52c71d01a3edf3e298a840d41345abdc2d6d26d. Read its Markdown companion,
  admission receipt, active registry, M6 capability manifest, formal safety
  claim, and precision policy before grading.
- Do no UI work. Never access or write the failed Crucial or Encrypted Crucia
  volume.

Review objective:
Hold the project to the Plan V2.1 definition of closure. The earlier 35-45%
estimate is context only. Require all registered obligations, 103 capability
rows, four required routes, and VM-01 through VM-12 to pass on one exact release
subject before permitting 100%, formal_core_complete=true, or any production,
release, settlement, verifier, migration, publication, or value-moving
authority.

Immediate review duties:
1. Treat 94dd23f29bd0a13e569f050a8133086cfb76d170 as REVISE. Re-freeze the
   current candidate because the branch may have advanced.
2. Check that the Lean exact relation states custody(domain) equals visible
   claimant liabilities(domain), excludes reserves, and retains reserve masking
   only as a weaker counterexample. Require the module in Proofs.lean, warnings
   as errors, zero placeholders, exact ordered theorem inventory, and direct
   #print axioms evidence.
3. Check that the ESSO model has only substantive invariants, currently expected
   to be five, and that each projected proof is described as sufficient unless
   minimality is independently demonstrated. Require Z3 and CVC5 agreement,
   deterministic fingerprints, an open-claim mutant, a drain mutant, and exact
   SAT-query plus invariant attribution. Missing ESSO fails the formal replay.
4. Review Python and Rust claimant/custody guards for exact arithmetic parity,
   checked u128 behavior, pre-state and post-state enforcement, rejection
   precedence, and no-effect behavior. Lexical similarity is insufficient.
5. Require structural Python AST and Rust balanced-structure checks for the
   exact TerminalObligationV1 field order. Confirm that liability_domain and
   custody_principal remain absent and that the no-universal-recovery theorem is
   scoped to this V1 projection.
6. Require a two-commit S/P evidence chain. Verify S contains formal source,
   checker, scanner and tests. Verify P is a direct child whose complete diff is
   limited to the declared admission envelope. Recompute Git blob hashes from S.
   Ensure the executing checker and scanner match S. Packet admission must
   report proof replay as NOT_RUN unless it actually executes the recorded
   tools.

Whole-core review duties:
- Top-down: trace every user story through normative spec, transition,
  integration, proof or verifier, API boundary, terminal and recovery path, and
  executable evidence.
- Bottom-up: trace every value and authority source through mutation, effects,
  roots, receipts, journals, verifier witness, commit port, durable publisher,
  outbox, recovery, migration, and terminal drain.
- Adversarial: test claimant substitution, cross-domain backing, reserve
  masking, lane-root/preimage substitution, omitted external asset or amount,
  replay, reordering, partial failure, overflow, rounding, dust, stale Oracle,
  stale release, alternate writer, crash, and migration discontinuity.

For every lane producer and GlobalAccountingAllocationCertificateV1, require:
- exact typed field ownership and canonical encodings;
- Python/Rust differential vectors and runtime behavior parity;
- exact source-atom classification and claimant/reserve equations;
- lane receipt, route, epoch journal, RISC0 image and receipt binding;
- Tau scope and authority statements that match current Tau capabilities;
- opaque verifier-owned witness construction;
- release-aware commit-port enforcement;
- BDD happy, reject, authorization, cancellation, recovery and terminal paths;
- BVA, properties, stateful histories, fuzzing and named mutation killers;
- explicit residual risks and nonclaims.

Review protocol:
Review the exact integrated candidate read-only. Record commit, parent, tree,
changed paths, checker hashes, toolchain versions, exact commands and outputs.
Return ACCEPT or REVISE with severity-ranked, file-and-line-specific findings.
ACCEPT is advisory. A finding causes a new child candidate and invalidates the
old hash review. Never flip a VM gate directly.

100% exit rule:
Recommend the 100% label only after one exact candidate has all 12 deterministic
VM gates passing, every capability row in an allowed terminal status, all lane
and route producers mounted or proved disabled with no writer, zero unresolved
critical gaps, complete source and receipt bindings, no proof placeholders, no
alternate value writer, a release-selected verifier and publisher, migration
and recovery evidence, and independent exact-hash reviews. Otherwise report the
exact numerator, denominator, blockers, and safest next proof obligation.
```
