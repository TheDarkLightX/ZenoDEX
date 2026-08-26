# ZenoDEX Whole-Program Implementation Plan V2.1

Status: research-only candidate pending admission
Implementation base: `92bec186d36846bb5e43b2be90a58b8a46ee56c6`
Production authority: `NONE`
Settlement authority: `NONE`

## Result

This candidate proposes one current plan for completing the Modular
Whole-Economy Zeno Recursive Proof Fabric. It becomes active only through a
user-selected, research-only admission receipt and active-plan registry entry.
The user-selection premise is external and is not machine verified. LLM reviews
are hash-bound advisory artifacts. Deterministic checkers replay the evidence.
The plan reconciles the
original six-phase architecture, the current 103-capability M6 registry, the
value-movement claim target, the G0 production-readiness work, the historical
65-task decomposition, current Tau upstream behavior, and exact-subject
independent review.

GlobalSettlementABI V1 remains the working research decision. This is an
architectural judgment rather than a formal result. A V2 is
permitted only for a new foundational effect category or invariant, together
with an approved typed delta, migration obligations, and compatibility policy.

At the recorded implementation base, the candidate is a substantial research
implementation. It is not a production or whole-program closure candidate.
The architecture inventory contains 12 lanes, 103 capabilities, four required
routes, and three exclusions. Strict release closure is 0 of a
manifest-derived minimum of 966 evidence cells:

```text
103 capabilities * 9 required statuses
  + 4 routes * 9 required statuses
  + 3 exclusion certificates
  = 966 minimum cells
```

The denominator expands when requirements, terminal behavior, migration, or
evidence rows create more obligations. The checked value-movement ledger is
stale and requires exact-subject reconciliation. At the baseline, zero of the
12 value-movement gates has `PASS` evidence. Component percentages remain
planning estimates outside this normative plan and cannot promote a claim.

The machine-readable plan is
`docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json`.

## Scope and semantic anchors

The provisional closed-name registry and requirements floor is the 12 lanes,
103 capabilities, four mixed-lane routes, and explicit exclusions in
`ZENODEX_M6_CAPABILITY_MANIFEST_V1.json`. Requirements closure remains
incomplete. The 18 workflows, 81 scenarios, 11 required expansions, eight
confirmed completeness findings, and 20 unresolved policy decisions must map
into versioned rows before scope or VM-01 may be called complete. Five of the
eight findings remain `OPEN_BLOCKER`; two have bounded-model repairs, and one
requires a product and theorem decision. An advisory finding never closes its
own requirement row.

The following decisions are fixed for this program:

- Asset amounts use eight decimal places represented as unsigned integer atoms.
  Authoritative paths do not use floating point.
- Autonomous governance and LLM agents may submit authenticated typed commands.
  They have no independent publication capability.
- Buy and burn spends the governed quote-asset fee allocation through the
  release-selected Spot route, purchases ZDEX, and burns the exact ZDEX atoms
  received. A treasury-balance shortcut or transfer-burn substitution does not
  satisfy this contract.
- Hosting compensation is a separate governed fee allocation with an explicit
  claimant, eligibility rule, expiry, cancellation, and terminal disposition.
- ZDEX hyperdeflation uses a profile-bound retained-supply rule. No fixed
  percentage of initial supply is required as a floor.
- GlobalSettlementABI V1 does not rescale denominations.
- Key control determines practical custody. Same-ledger protocol state uses
  accounting location, accounting control domain, claimant entitlement, and
  key-authority language.
- The registered external lane starts empty. Unregistered destinations reject
  without mutation.
- Current Tau testnet may authenticate and tentatively order Tau transactions.
  Tau Language may evaluate governed predicates through a versioned adapter.
  Separate Zeno-domain authentication is required before
  an observation can become an `EconomicCommandOccurrenceV1`. ZenoLedger
  ordering and publication remain authoritative.

## Current blockers

Five issues take precedence over broader implementation:

1. Replayable current-Tau differentials must establish the incompatibility
   boundary before route quarantine receives evidence status. The plan pins
   both `tau-testnet` and `tau-lang`; O-003A must replay source bytes, reserved
   streams, signature preimages, JSON envelopes, and the `TAU_FORCE_TEST`
   disqualifier.
2. Bridge-backed stream-8 perps and stream-11 zUSD monetary operations are
   described as mounted despite incompatibility with current Tau. Stream 11
   also lacks the required verifier-owned execution clock. Both value-moving
   routes must remain unmounted until their replacement paths have positive
   liveness and adversarial evidence.
3. `tools/dex-ui/README.md` still presents stream-9 zUSD wallet, stream-11 zUSD
   monetary, and stream-8 perps paths as current mounted behavior while later
   sections describe quarantine. The operator surface is internally
   contradictory.
4. Current Tau removed the historical application bridge and state-proof RPCs,
   reserved streams 5 through 11, changed its signed transaction preimage to
   include `tx_type`, and changed RPC responses to JSON envelopes. The local
   profile also sets `TAU_FORCE_TEST`, so it does not demonstrate real Tau
   evaluation. The patched bridge also folds the ZenoDEX application hash into
   Tau state, allowing Tau to select the durable economic head. Every dependent
   route requires explicit quarantine and redesign.
5. The checked value-movement ledger is historical. It does not certify the
   current candidate.

Current Tau alpha also states that it has no economic finality or slashing and
may reorganize. The production external lane therefore remains disabled. The
historical Python bridge can remain a research and differential oracle. It
cannot be a publication authority.

The replacement boundary is:

```text
Tau-originated signed event or policy verdict
  -> current-Tau versioned ingress adapter
  -> domain-bound EconomicCommandOccurrenceV1
  -> module, lane, and route verification
  -> opaque VerifiedEconomicEpochV1
  -> atomic ZenoLedger CAS commit
  -> external-only outbox
  -> current-Tau submission and reorg-aware observation
```

The adapter must parse current JSON envelopes, sign `tx_type=user_tx`, use a
release-registered nonreserved stream, bind an inner Zeno signature to both
network domains and the command occurrence, and observe canonical transaction
status. A pre-finality observation removed by reorganization becomes
`ORPHANED` and causes no irreversible settlement. Irreversible external value
movement stays disabled until an approved finality policy exists.

Economic parameters that the user has not selected remain explicitly
unselected. This includes fee percentages, host-service evidence, farm
emissions, complete zUSD and perps profiles, Oracle economics, auction and
strategy rules, proof-reward funding, governance quorum and timelock, Tau-origin
asset finality, Spot and LP policy details, transfer fees, retained-supply
parameters, future ZDEX issuance, fixed-point scales beyond asset amounts,
local-settlement helper reachability, and faucet exclusions. The JSON plan
retains these as `UP-01` through `UP-20`. Fixtures cannot select them.

## Six phases

### P1: Freeze and reconcile the trustworthy candidate

Exit when one pushed candidate, one active plan, exact semantic-source hashes,
a current Tau compatibility classification, a current closure ledger, and
consistent mounted-route claims all agree.

### P2: Close requirements and mediate every value writer

Exit when every reachable value command and sink maps to a capability row,
typed transition, canonical effect, governed route, terminal path, adapter, and
evidence row. Unknown and disabled paths must reject without mutation.

### P3: Complete the functional core and sole publisher

Exit when global state and effect ownership, canonical codecs, rejected no-op
behavior, conservation invariants, and a crash-tested verifier-gated atomic
publisher close without caller-selected or sidecar economic authority.

### P4: Complete enabled lane and route lifecycles

Exit when all 103 capability rows and four mixed-lane routes are release-backed
or carry a proved disabled-no-writer certificate. This includes recovery,
terminal drain, and migration behavior.

### P5: Complete the recursive proof fabric

Exit when module, coordinator, route, and bounded epoch proofs use pinned
images, exact assumption resolution, owned canonical journals, complete public
bindings, real receipts, negative receipt evidence, and direct-versus-proof
parity.

The initial qualification shape remains 1 to 8 module receipts per route and 1
to 64 composed commands per epoch, with no more than 64 leaf occurrences.
Qualification must reject route counts 0 and 9 and epoch counts 0 and 65.
Larger proof shapes require a new measured root release.

### P6: Mount, migrate, cut over, and release

Exit when one release-selected verifier and atomic publisher are mounted,
migration is proved, legacy writers are retired, and exact-profile evidence
plus independent reviews close all 12 value-movement gates.

## Dependency-ordered obligations

The list below is a stable topological order. Independent obligations may run
in parallel only with exact-parent packets and disjoint write sets.

1. O-001 admits the exact plan through a user-selected research receipt, hashed
   advisory review artifact, deterministic checker, and active-plan registry.
2. O-003A creates replayable current-Tau incompatibility witnesses.
3. O-002 quarantines bridge-backed stream-8 perps and stream-11 zUSD value
   movement with startup, deployment, manifest, no-effect, and alias-mutant
   evidence.
4. O-003B classifies every retired-bridge dependency as `QUARANTINED`,
   `RESEARCH_ORACLE`, or `REMOVED`.
5. O-004 replaces selected phrase checks with a closed operator-surface
   registry.
6. O-005 maps 18 workflows, 81 scenarios, 11 expansions, eight confirmed
   findings, and 20 unresolved policies into nonvacuous rows.
7. O-005B regenerates the value-movement ledger on the exact admitted subject
   without promoting any VM gate.
8. O-006 binds every registered user command to exactly one lane or governed
   route.
9. O-007A closes deployed-launcher sink reachability after selecting between
   the two competing donor implementations.
10. O-007B extends sink discovery across Python, Rust, Tau, shell, and generated
    code.
11. O-007C closes recovery, migration, callback, worker, dynamic-loading, and
    administrative reachability.
12. O-008A qualifies a reproducible Rust and RISC0 build host.
13. O-008 freezes ABI V1 ownership and reconciles global state and effects.
14. O-009 fences one verifier-gated atomic publisher in `SHADOW`.
15. O-010A advances ASSET_TRANSFER capability rows.
16. O-010B advances Spot, liquidity, and tokenomics, including governed
    fee-funded ZDEX purchase and exact burn. It remains blocked on UP-01,
    UP-12, and UP-14.

Each obligation has explicit closure evidence in the machine-readable plan.
Individual obligations may contribute to a value-movement gate. Only aggregate
deterministic checkers may close a VM gate after every formal-claim conjunct
passes on one exact subject.

## Multi-agent execution protocol

Each wave uses one exact candidate and at most three implementation workers.
Each worker receives one falsifiable obligation, one invariant, one authority
boundary, a disjoint write set, a minimized failing witness or discovery
contract, an expected closure delta, required tests, nonclaims, and a disk and
compute budget. Each candidate is one direct child of the declared integration
head and contains only its declared write set. Evidence and review materialize
the exact commit in a clean isolated checkout. Preserved unrelated working-tree
changes receive no candidate or evidence status. The integrator alone edits
shared ABI files, registries, manifests, semantic contracts, and ledgers.

Promotion order is fixed:

```text
worker candidate
  -> donor review
  -> serial integration and conflict resolution
  -> advisory independent review of the exact integrated candidate
  -> deterministic receipt
  -> ledger promotion
  -> push
```

A workstream stops or is reformulated after two review cycles with no newly
closed obligation. Commit count, test count, changed lines, and compute usage
remain telemetry. Each wave records their cost per newly closed obligation.
The minimized BEFORE witness must fail on the parent. AFTER evidence must pass
on both the worker child and the post-integration head.

Fable and Opus may implement or perform broad hostile reading. Max and Sol may
review exact committed subjects. Their outputs remain advisory and are stored
as hash-bound artifacts. Deterministic gates own acceptance. A `NO_RESULT`
review is recorded as `NO_RESULT` and never becomes a pass.

## Release gate

Every enabled capability row must be `SPECIFIED`, `IMPLEMENTED`, `PROVED`,
`MOUNTED`, `TESTED`, `TERMINAL_COMPLETE`, `MIGRATABLE`, `NO_BYPASS`, and
`RELEASE_BACKED`. Every excluded row must be
`DISABLED_PROVED_NO_WRITER`.

The whole-value-movement safety claim remains forbidden until all 12 gates pass
on one exact release subject. A plan check, local test, historical receipt, LLM
review, or source inventory cannot grant settlement or production authority.

## Evidence and nonclaims

Normative source hashes are recorded in the JSON plan. Historical plans,
competing sink-inventory commits, and ledgers are labeled as donors or stale
diagnostics. The commit adding this plan must be bound by a later immutable
receipt because a committed file cannot truthfully contain its own final commit
hash. The receipt records the external user-selection premise as unverified by
the machine and labels every LLM review advisory.

This document is not a proof, verifier receipt, production release, migration
certificate, or settlement authorization. Current Tau alpha observations do
not establish economic finality. Historical proof receipts do not establish
current-subject implementation parity. The current-Tau integration defect does
not invalidate standalone Spot, zUSD, perps, or other scoped cores and proofs.
They remain donors until rebound to GlobalSettlementABI journals.
