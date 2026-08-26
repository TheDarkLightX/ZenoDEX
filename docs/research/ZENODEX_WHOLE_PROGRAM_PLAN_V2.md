# ZenoDEX Whole-Program Implementation Plan V2

Status: research-only active implementation plan
Implementation base: `92bec186d36846bb5e43b2be90a58b8a46ee56c6`
Production authority: `NONE`
Settlement authority: `NONE`

## Result

This is the single current plan for completing the Modular Whole-Economy Zeno
Recursive Proof Fabric. It reconciles the original six-phase architecture, the
current 103-capability M6 registry, the value-movement claim target, the G0
production-readiness work, the historical 65-task decomposition, current Tau
upstream behavior, and exact-subject independent review.

The architecture remains sound. GlobalSettlementABI V1 stays selected. A V2 is
permitted only for a new foundational effect category or invariant, together
with an approved typed delta, migration obligations, and compatibility policy.

At the recorded implementation base, the candidate is a substantial research
implementation. It is not a production or whole-program closure candidate.
Architectural implementation
maturity is approximately 33 percent under a conservative component rubric.
Formal-artifact maturity is approximately 15 to 25 percent as a coarse estimate.
Strict release closure is 0 of at least 350 registered required evidence cells
because no complete command or M6 row is closed on one exact subject. The
350-cell denominator is a lower bound and must expand when the 103-capability
registry creates additional obligations. Exact-ledger closure is approximately
1 to 3 percent and must be reconciled on the current head. These figures answer
different questions. They are an immutable baseline diagnosis, not a live
progress counter. Exact-subject obligation and value-movement ledgers govern
live progress and promotion. At the baseline, zero of the 12 value-movement
gates has `PASS` evidence.

The machine-readable plan is
`docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json`.

## Scope and semantic anchors

The closed scope is the 12 lanes, 103 capabilities, four mixed-lane routes, and
explicit exclusions in `ZENODEX_M6_CAPABILITY_MANIFEST_V1.json`.

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
- Tau may authenticate or order typed command occurrences and may evaluate
  governed predicates. ZenoLedger retains the sole durable publication path.

## Current blockers

Four issues take precedence over broader implementation:

1. Bridge-backed stream-8 perps and stream-11 zUSD monetary operations are
   described as mounted despite incompatibility with current Tau. Stream 11
   also lacks the required verifier-owned execution clock. Both value-moving
   routes must remain unmounted until their replacement paths have positive
   liveness and adversarial evidence.
2. `tools/dex-ui/README.md` still contains a contradictory mounted-posture claim
   for quarantined stream-9 zUSD and AutoTrader behavior.
3. Current Tau removed the historical application bridge and state-proof RPCs,
   reserved streams 5 through 11, changed its signed transaction preimage to
   include `tx_type`, and changed RPC responses to JSON envelopes. The local
   profile also sets `TAU_FORCE_TEST`, so it does not demonstrate real Tau
   evaluation. The patched bridge also folds the ZenoDEX application hash into
   Tau state, allowing Tau to select the durable economic head. Every dependent
   route requires explicit quarantine and redesign.
4. The checked value-movement ledger is historical. It does not certify the
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
network domains and the command occurrence, observe canonical transaction
status, and represent reorganization as a pending or reversed external
obligation. Irreversible external value movement stays disabled until an
approved finality policy exists.

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

## Next ten obligations

The next work executes in this order:

1. Admit this plan with an immutable exact-commit review receipt.
2. Quarantine bridge-backed stream-8 perps and stream-11 zUSD value movement.
3. Add an exact-upstream Tau compatibility gate and classify every dependency
   on the retired bridge protocol.
4. Replace selected phrase checks with a closed operator-surface consistency
   registry.
5. Reconcile the 12 value-movement gates and 103 capability rows against the
   post-quarantine candidate.
6. Bind every registered user command to exactly one lane module or governed
   route.
7. Complete operation-derived, cross-language writer and sink mediation.
8. Freeze ABI V1 field ownership and complete global state and effect
   reconciliation.
9. Make one verifier-gated atomic publisher the only durable value writer.
10. Close lane capability rows starting with ASSET_TRANSFER, SPOT_LIQUIDITY,
    and ZDEX_TOKENOMICS, including governed fee-funded ZDEX purchase and exact
    burn.

Each obligation has explicit closure evidence in the machine-readable plan.

## Multi-agent execution protocol

Each wave uses one exact candidate and at most three implementation workers.
Each worker receives one falsifiable obligation, one invariant, one authority
boundary, a disjoint write set, a minimized failing witness or discovery
contract, an expected closure delta, required tests, nonclaims, and a disk and
compute budget. Each candidate is one direct child of the declared integration
head, and a dirty subject invalidates its packet. The integrator alone edits
shared ABI files, registries, manifests, semantic contracts, and ledgers.

Promotion order is fixed:

```text
worker candidate
  -> donor review
  -> serial integration and conflict resolution
  -> independent review of the exact integrated candidate
  -> deterministic receipt
  -> ledger promotion
  -> push
```

A workstream stops or is reformulated after two review cycles with no newly
closed obligation. Commit count, test count, changed lines, and compute usage
remain telemetry. Each wave records their cost per newly closed obligation.
The minimized BEFORE witness must fail on the parent. AFTER evidence must pass
on both the worker child and the post-integration head.

## Release gate

Every enabled capability row must be `SPECIFIED`, `IMPLEMENTED`, `PROVED`,
`MOUNTED`, `TESTED`, `TERMINAL_COMPLETE`, `MIGRATABLE`, `NO_BYPASS`, and
`RELEASE_BACKED`. Every excluded row must be
`DISABLED_PROVED_NO_WRITER`.

The whole-value-movement safety claim remains forbidden until all 12 gates pass
on one exact release subject. A plan check, local test, historical receipt, LLM
review, or source inventory cannot grant settlement or production authority.

## Evidence and nonclaims

Normative source hashes are recorded in the JSON plan. Historical plans and
ledgers are labeled as donors or stale diagnostics. The commit adding this plan
must be bound by an external immutable receipt because a committed file cannot
truthfully contain its own final commit hash.

This document is not a proof, verifier receipt, production release, migration
certificate, or settlement authorization. Current Tau alpha observations do
not establish economic finality. Historical proof receipts do not establish
current-subject implementation parity. The current-Tau integration defect does
not invalidate standalone Spot, zUSD, perps, or other scoped cores and proofs.
They remain donors until rebound to GlobalSettlementABI journals.
