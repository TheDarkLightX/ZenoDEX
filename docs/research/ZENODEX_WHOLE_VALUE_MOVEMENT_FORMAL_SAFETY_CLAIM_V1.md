# ZenoDEX Whole-Value-Movement Formal Safety Claim V1

Date: 2026-08-22

Status: `DRAFT_REVISED_VERIFIER_RELEASE_BOUND`

Claim authority: `NONE`

Production authority: `NONE`

This document is a proposed release claim and an implementation contract. It
does not assert that the claim is currently true. Promotion requires a clean,
pinned release candidate and checker-derived evidence for every gate below.

## Review subject

The target is a release-specific statement about every value movement admitted
by one closed ZenoDEX economic profile. The claim concerns protocol accounting,
authorization, proof admission, and durable publication. It does not promise a
profit, a stable market price, Oracle truth, key security, consensus soundness,
or availability.

The word `custody` is not used here as a legal characterization of same-ledger
balances. Whoever controls the applicable keys has practical custody. The
formal model tracks accounting locations, control domains, claimant
entitlements, locked value, reserves, and registered external obligations.

## Proposed claim

For an exact deployed release bundle `R`, complete capability profile `P`,
genesis or proved migration state `S0`, verifier set `V`, and writer epoch `W`,
ZenoDEX provides a machine-checked safety guarantee for every durable
value-affecting event reachable through any deployed interface, subject to the
explicit assumptions in this document. `P` commits the exact intended M6
command and lifecycle manifest. Every absent capability has a release-bound
`DISABLED_PROVED_NO_WRITER` certificate.

Let raw command admission and certified initialization be:

```text
Decode(raw_bytes, decode_profile)
  = DecodeReject(typed_code)
  | CanonicalCommand(C)

InitialStateAccept(R, P, S0, certificate0)
  = ValidGenesisCertificate(R, P, S0, certificate0)
  | ValidMigrationCertificate(predecessor, R, P, S0, certificate0)
```

`S0` is never an arbitrary supplied snapshot. Every positive accounting atom,
supply atom, liability, reserve, locked position, replay item, pending external
obligation, and terminal obligation in `S0` must be covered exactly once by a
genesis allocation row or a predecessor migration classification. The initial
certificate is part of the verified history.

Let:

```text
Commands(P)     = the closed command grammar enabled by P
Step(R, P, S, C)
  = Reject(code)
  | Accept(S_post, effects, replay, terminal_obligations)
```

Complete mediation is quantified over deployed interfaces and durable sinks,
including interfaces or writers that violate the intended transition graph. A
bypass cannot disappear from the theorem universe by definition:

```text
every deployed value-affecting event
  -> exactly one retained EconomicEffectOccurrenceV1 accepted by V
     and atomically published under active R, P and W
  | no durable value effect
```

For every certified state reached through this sole publication history, every
raw input has one typed decode result. Every canonical authenticated `C` in
`Commands(P)` has one typed transition result. Decoder rejection and
transition rejection preserve the exact durable pre-state and emit no economic
effect. Independent writer discovery must establish that no other durable
state can arise through a deployed interface.

### Semantic continuity anchors

These decisions prevent context-reset drift. A future change requires an
explicit versioned semantic amendment and new evidence.

- Balances are described by accounting location, control domain, and claimant
  entitlement. Key control determines practical custody; the protocol does
  not characterize same-ledger balances as a separate form of custody. The ABI
  V1 field name `custody_domain` means accounting control domain only and does
  not assert possession of user keys. Rename it before freezing the ABI if that
  normative definition remains legally or operationally ambiguous.
- Initial token amounts use integer base units with eight decimal places.
  Consensus and proof paths use no floating point. Denomination rescaling is
  outside GlobalSettlementABI V1; it requires an ABI V2 rule and a proved total
  migration that distinguishes denomination conversion from economic issue or
  burn.
- Protocol buy-and-burn atomically spends its governed quote-asset fee
  allocation to purchase ZDEX through the selected authenticated Spot route,
  then burns the exact ZDEX atoms received by that purchase. A treasury-balance
  shortcut or legacy transfer-burn substitute is not conforming behavior.
- Hosting compensation is a separately named governed fee allocation with an
  explicit claimant and terminal claim path. PulseX behavior is an economic
  comparison point; its percentages do not define ZenoDEX policy.
- Hyperdeflation is the intended long-run ZDEX policy. No arbitrary fixed
  percentage of initial supply is assumed as a floor. Every active release must
  bind and prove a retained-supply rule such as `R(S) = ceil(p*S/q)`, with
  `0 < p < q` and `burn <= S - R(S)`, so every accepted occurrence preserves a
  positive represented supply without underflow. Literal infinite execution is
  outside a finite-machine theorem.
- Autonomous governance and LLM agents have command-submission authority only.
  Their proposals pass through the same authentication, route, proof, release,
  and commit gates as other commands.

The current detailed tokenomics design is
`docs/research/ZDEX_HYPERDEFLATION_V1_20260821.md`. Any conflict between that
document and these anchors is a release-blocking semantic gap.

Known legacy and experimental surfaces remain incompatible with these anchors.
The local-testnet tokenomics path in
`src/integration/zeno_ledger_tokenomics.py`, its node and Tau-witness adapters,
and the current token-statistics UI still implement or describe a fixed
`supply_floor`. They cannot be mounted under the selected M6 profile unless
they are replaced or passed through a separately proved migration. The
experimental ZDEX precision-rescale transition also cannot be routed under
GlobalSettlementABI V1; changing denomination requires an ABI V2 migration.
Their presence in the repository is research or legacy evidence, not semantic
authority.

### 1. Total deterministic decision

```text
same canonical S, C, R, P and authenticated evidence
  -> byte-identical decision, state, effects, replay and obligations
```

The transition is total over the bounded input domain. Unknown variants,
unknown fields, malformed values, stale context, excess resources, and
unregistered dependencies reject with a typed result.

### 2. Accepted-transition safety

When `Step` accepts:

```text
partitioned_same_ledger_atoms_post(asset)
  = partitioned_same_ledger_atoms_pre(asset)
  + authorized_issue(asset)
  - authorized_burn(asset)

supply_post(asset)
  = supply_pre(asset)
  + authorized_issue(asset)
  - authorized_burn(asset)

fee_charged(asset)
  = current_fee_allocations(asset)
  + explicitly_carried_residue(asset)
```

`partitioned_same_ledger_atoms` includes every profile-declared account, pool, margin
account, vault, Stability Pool position, escrow, reserve, reward allocation,
pending registered external obligation, and other committed accounting
location. The partitions are disjoint. Key-controlled self-custody balances
are not counted again as claimant liabilities. For every applicable accounting
control domain:

```text
controlled_atoms
  = claimant_entitlements
  + named_unencumbered_reserves
  + pending_registered_external_obligations
```

Every issue and burn has exactly one profile-authorized source occurrence,
grant, policy, and release. Every claim, liability, reserve, fee allocation,
residue, hosting claim, reward, slash, terminal obligation, and registered
external-delivery occurrence is represented and reconciled by its owning
module and by global composition.

Acceptance also preserves:

- exact authorization and grant scope;
- nonce and nullifier uniqueness;
- consensus-height, epoch, and Oracle-occurrence policy;
- integer widths, units, rounding, residue, and dust rules;
- canonical effect order and unique state-field ownership;
- route, release, profile, image, journal, and occurrence binding;
- lane-specific solvency and lifecycle invariants;
- terminal-path reachability for every created claim or obligation.

### 3. Rejection safety

```text
Step(R, P, S, C) = Reject(code)
  -> post_state = S
  -> effects = empty
  -> replay_update = empty
  -> terminal_obligations = empty
  -> outbox = empty
```

Any intentionally charged or nonce-consuming failure must be represented as a
separate typed committed-failure transition with its own proved effects. It
cannot be classified as a rejection.

### 4. Proof-to-transition binding

Every accepted proof journal binds the exact chain, deployment, writer epoch,
profile, release set, command occurrence, authenticated subject, pre-state,
post-state, canonical effects, replay update, terminal obligations,
data-availability commitment, and expected verifier image.

```text
ProofAccept(receipt)
  -> journal(receipt) = canonical_journal(S, C, Step(R, P, S, C))
```

Conditional, unresolved, fake, development-mode, foreign-image,
foreign-profile, stale, noncanonical, duplicated, reordered, or mutated
receipts cannot construct publication authority.

### 5. Complete commit provenance and atomicity

Each canonical route effect row receives an injective identity before epoch
aggregation:

```text
effect_occurrence_id
  = H(command_occurrence_id,
      route_release_id,
      canonical_effect_index,
      canonical_effect_row)
```

A user-visible operation may project to several signed accounting effects.
The route transition defines that projection. Epoch aggregation may combine
equal accounting rows, while the verified epoch retains every route-level
effect occurrence and its identity.

Every durable post-initialization economic effect has exactly one authorized
origin:

```text
DurableEconomicEffect(e)
  -> exists exactly one verified epoch E such that
       e is an exact retained route-effect occurrence of E
       and E was accepted under the active R, P and W
       and E committed against its exact expected pre-root
```

Genesis and predecessor migration atoms have corresponding unique rows in the
certified initial-state event. They cannot be justified by ordinary epoch
conservation alone.

The sole publisher atomically commits the complete accepted tuple:

```text
global state
+ canonical effects
+ header and history
+ replay data and nullifiers
+ receipts and release observations
+ terminal obligations
+ external outbox rows
```

A stale compare-and-swap, inactive release, revoked verifier, wrong profile,
wrong body commitment, or crossed candidate rejects without partial
publication. Crash recovery yields either the complete pre-commit state or the
complete committed tuple.

### 6. External-effect discipline

Same-ledger value movement is committed directly and never enters the external
outbox. Registered external actions are derived only from a committed outbox
row. Retry, ambiguous acknowledgment, and redelivery use a canonical commit
identity and destination idempotency policy. Unregistered destinations reject.

### 7. Upgrade and migration continuity

Release activation and migration preserve every balance, supply value,
claimant entitlement, locked position, liability, reserve, residue, nonce,
nullifier, history link, pending external obligation, and terminal obligation.
Every source object is classified exactly once as migrated, retained for
drain, closed, or tombstoned. Historical receipts remain verifiable under
their historical profile. An inactive or revoked profile cannot authorize a
new commit.

### 8. Closed authority surface

Every reachable writer in APIs, CLI commands, node paths, Tau adapters,
recovery, migration, proof callbacks, workers, governance, administrative
operations, and external-delivery callbacks is either:

```text
bound to the sole verified publication path
```

or:

```text
DISABLED_PROVED_NO_WRITER
```

Autonomous governance and LLM agents may submit ordinary authenticated typed
commands. They receive no independent publication capability.

## Explicit assumptions

The claim is conditional on the following assumptions. Review must minimize
this set and state any additional trusted component discovered during
implementation.

1. The selected cryptographic hash, signature, proof, and commitment schemes
   satisfy their stated security properties.
2. The selected consensus and finality mechanism supplies the authenticated
   chain order, height, writer epoch, and finality facts consumed by the model.
3. Private keys and signing devices used by authorized principals are not
   compromised. The protocol still enforces grant, nonce, and policy scope.
4. Oracle reports are authentic, finalized, fresh, and policy-admissible.
   Formal verification does not establish that an observed price is true.
5. Registered external systems satisfy their declared finality and
   idempotency assumptions. A first release may keep the external registry
   empty to remove this premise.
6. Release artifact measurement identifies the implementation and backend that
   actually execute. The current process-local Python verifier handles do not
   establish this condition against hostile same-process code. A promoted
   release requires a measured process, hardware, or equivalent isolation
   boundary, plus compiler, runtime, and verifier-deployment assumptions stated
   in its trusted-computing-base manifest.
7. Governance-selected economic parameters lie inside their proved envelopes.
   Economic loss permitted by the specification, including slippage, funding,
   liquidation, or market-price movement, is outside this safety claim.

## Required implementation and evidence gates

All gates are release-blocking. `PASS` must be derived by deterministic
checkers from pinned evidence. A producer-supplied Boolean cannot promote a
gate.

| ID | Required implementation | Definition of done |
| --- | --- | --- |
| VM-01 | Closed requirements and value-writer registry | Every user story, raw decoder, command, writer, asset, control domain, effect, rejection, committed failure, recovery path, and terminal path has one versioned row. Discovery begins from actual durable storage and effect sinks and traverses their callers across every implementation language, generated code, dynamic loading, CLI, workers, callbacks, migration, deployment configuration, and deployed entrypoints. Novel names cannot evade coverage. The release-mode checker reports zero open or unknown rows. |
| VM-02 | Complete typed global state and canonical codec | Python reference, Rust core, proof guest, verifier journal, and durable schema represent the same fields, widths, units, order, and roots. Canonical decoding rejects unknown, duplicate, malleable, or excess input. |
| VM-03 | Global economic delta algebra | Canonical account, issue, burn, liability, reserve, fee, residue, hosting claim, reward, slash, claimant obligation, terminal obligation, lane-write, occurrence, and registered external-delivery effects cover every enabled transition. Each row binds its source occurrence, authorization grant, policy, release, accounting control domain, and canonical index. Each route effect has an injective occurrence identity retained across epoch aggregation. Machine-checked conservation, provenance, disjoint-partition, claimant, and reconciliation theorems hold. |
| VM-04 | Complete lane transition cores | Each enabled lane has a deterministic total transition with typed rejection, exact effects, lifecycle state, recovery, and terminal drain. Every excluded lane is `DISABLED_PROVED_NO_WRITER`. |
| VM-05 | Lane and route composition | Governed routes derive every required module occurrence. Coordinators prove exact port pairing, release coexistence, field ownership, effect aggregation, and lane invariants. Callers cannot choose proof requirements. |
| VM-06 | Ordered epoch proof fabric | Real pinned-image module, coordinator, route, and epoch receipts bind exact canonical journals. Bounded recursion rejects zero, excess, unresolved, fake, development-mode, stale, foreign, reordered, and duplicated receipts. |
| VM-07 | Formal model and implementation refinement | The normative transition is machine checked. Python, Rust, RISC0 guest, Tau policy where applicable, verifier, and mounted adapters match decision, rejection precedence, state, effects, replay, roots, and outbox on generated and adversarial vectors. |
| VM-08 | Release-aware verifier authority | Only an opaque verifier-owned witness for the active release, complete capability profile, deployment, writer epoch, measured executing backend, and exact journal can reach the commit port. The authoritative path does not accept a caller-selected verifier implementation. The selected verifier is derived from committed profile state and rechecked under the commit lock. Commit-time freshness, revocation, and old-proof-after-activation tests pass across the actual isolation boundary. |
| VM-09 | Sole atomic publisher | One durable compare-and-swap linearization point commits the complete tuple under the authority/write lock. Every former writer is removed, fenced, or proved unreachable. Architecture checks fail on any bypass or newly introduced writer. |
| VM-10 | Crash, concurrency, replay, and delivery refinement | Fault injection covers every persistence boundary. Concurrent roots, stale reads, exact retries, duplicate nonces, lost acknowledgments, outbox redelivery, and reopen histories refine one sequential commit model. |
| VM-11 | Certified initialization, migration, and version coexistence | Genesis or predecessor migration certifies `S0`; a proved migration classifies every object and preserves accounting, identity, replay, obligations, and historical verification. Shared-asset coexistence, especially zUSD, is proved or new issuance remains disabled. |
| VM-12 | Release evidence and independent review | Reproducible artifacts, exact toolchain locks, checker-source hashes, complete checked-file lists, exact commands and exit codes, source manifests, real receipt replay, mutation evidence, security review, formal review, economic-lifecycle review, and authority-boundary review all bind one candidate root. |

For each enabled release row, VM-01 through VM-12 must imply:

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

## Required evidence portfolio

Each semantic obligation requires evidence selected for its failure family:

- BDD for happy, rejection, authorization, cancellation, recovery, and
  terminal paths for every affected user class;
- boundary-value analysis at zero, one atom, minimum and maximum neighbors,
  integer limits, fee and collateral thresholds, rounding, dust, epochs, and
  Oracle freshness boundaries;
- property and metamorphic checks for conservation, canonicalization,
  determinism, split/merge behavior, monotonicity where specified, and
  reject-is-no-op;
- differential vectors across the formal reference, Python, Rust, proof guest,
  verifier, Tau policy where applicable, and mounted runtime;
- stateful histories for replay, reordering, repeated claims, activation,
  cancellation, terminal drain, migration, and recovery;
- requirement-linked mutants for omitted effects, incorrect rounding,
  authority bypass, stale roots, wrong profiles, wrong images, crossed
  candidates, partial commits, and duplicate delivery;
- model checking, SMT, ESSO, Lean, Kani, or equivalent machine evidence for the
  property family each tool can soundly establish;
- real proof replay and reproducible build evidence for the pinned images and
  verifier set.

Passing examples or aggregate coverage percentages cannot substitute for these
obligations.

## Current evidence snapshot

This historical snapshot describes the dirty checkout observed on 2026-08-22 at branch
`codex/zrpf-m6-cybersecurity-audit-20260811`, committed head
`b6842cd26aadf32b7ee774f58665570479cacfe6`. It is diagnostic context only and
does not describe the later isolated implementation branch. It is not release
evidence.

- `tools/check_m6_writer_inventory.py --json` reported 25 open coverage rows,
  18 unmounted entrypoints, `release_ready=false`, and
  `production_authority=false`. No discovered writer lacked an inventory row,
  while every row still lacked release-complete bindings.
- `tools/check_m6_research_boundary.py --json` found no static M6 production
  mount in 729 checked source files and reported `production_authority=false`.
- `docs/research/M6_RISC0_SEMANTIC_SURFACE_V1.json` reports
  `BLOCKED_SEMANTIC_SURFACE`, `activation_eligible=false`, missing Python/Rust
  state and command parity, missing canonical codec parity, absent independent
  execution parity, and no selected guest call to the shared full-M6
  transition.
- `docs/research/GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md` documents a
  substantial `RESEARCH_ONLY_UNMOUNTED` ABI and bounded asset-lane proof slice.
- Separate reviewed verifier-binding work exists as local commit
  `3ff2cb08762748a9809e558b7505c0aff87ffc67`. It closes a bounded release and
  artifact binding defect. It is not whole-economy proof or production
  authority.

Current claim verdict:

```text
WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY = UNPROVED
RELEASE_READY = false
PRODUCTION_AUTHORITY = NONE
```

Maximum-reasoning hostile review returned `REVISE`. Its first decisive
counterexample was an arbitrary or insufficiently certified `S0`: all later
steps can conserve perfectly while retaining an unauthorized genesis or
migration allocation. It also found undefined movement identity, incomplete
raw-decode semantics, process-local Python verifier authority, stale evidence
binding, name-pattern writer scans, and absent durable atomicity evidence. The
revised definitions and gates above incorporate those findings. They do not
close the corresponding implementation obligations.

An independent maximum-reasoning review of exact committed subject
`568637e894a52649aacc15723e808b9e9a713dfa` also returned `REVISE`. It found
that a transition-defined `Reach` set can hide bypass-writer states, and that a
profile enabling only a small subset of intended M6 capabilities can satisfy a
vacuous claim. Its smallest code counterexample is the public
`verify_economic_epoch_v1(candidate, receipt_verifier)` boundary: a caller can
supply a verifier implementation that returns success and thereby obtain the
otherwise opaque epoch witness. The authoritative path must select a measured
verifier from committed profile state instead of accepting this argument.

The implementation branch distinguishes that research witness from a
publisher-bound witness. `GlobalEconomicCommitPortV1` retains its selected
receipt backend, re-verifies the candidate through that backend, and rejects a
caller-selected or different-publisher witness before mutation. Commit
`369fe53f29184cd85a039459703d1b1f31d9b42f` further requires the durable
publisher to receive an opaque verifier capability selected from the exact
registry root and image committed by its active profile. The capability binds
a content-derived release, evidence-manifest root, measured artifact bytes,
deployment, backend-protocol root, purpose, and receipt/journal byte ceilings.
Generic protocol-shaped verifier objects reject before backend use.

This closes the reviewed caller-selected-verifier path for the unmounted
durable publisher. VM-08 remains `PARTIAL`: evidence statuses are committed
producer-supplied labels rather than checker-derived receipts, supplied
artifact bytes are not proven to be the code executed by the injected backend,
and Python same-process state is not an isolation boundary. Real RISC0 replay,
executable attestation, revocation under a mounted write lock, and OS-separated
writer authority remain absent.

The reference publisher also now requires an
`EconomicInitialStateAdmissionV1`; it no longer accepts a plain caller-supplied
profile and state pair. The admission binds an active profile, exact state root,
chain, deployment, writer epoch, height, source lineage, coverage and
continuity roots, source/toolchain manifests, selected root image, canonical
journal, receipt digest, and a succinct-receipt check before the publisher is
constructed. Python and Rust share canonical certificate golden vectors, and
the publisher owns snapshots before invoking the verification callback. This
closes the plain-snapshot constructor counterexample in the in-memory reference
model. VM-11 remains open: the coverage roots are not yet established by a real
initialization guest, migration releases are not yet selected from the
committed migration registry, the existing object-classification certificate
is not yet composed into admission, the bounded durable activation journal is
not mounted behind verifier-owned authority, and coexisting shared-asset
releases lack their required theorems.

The bounded initialization admission now derives a canonical occurrence for
every explicit balance, supply, named accounting-location, liability, reserve,
and terminal-obligation row in `GlobalEconomicStateV1`. Each occurrence binds
its row kind, canonical table index, and canonical row root. A closed source
manifest classifies every target occurrence exactly once as a genesis
allocation, migrated target, or retained drain target and binds a nonzero
source-authorization root. The manifest root is committed both by the active
profile policy registry and by the initialization certificate. Python and Rust
derive the same roots for all six kinds and every terminal status. Relative to
one exact authority-selected profile-bound manifest, omitted, duplicated,
reordered, stale, source-substituted, or illegal-for-kind classification rows
reject before receipt verification. A coherently substituted profile or a
different allowed migration label requires separate authority and predecessor
evidence; this structural checker does not decide either question. The checked
row-count boundary accepts 4,095 and 4,096 and rejects 4,097 before row copying,
validation, or hashing. The future guest wire boundary rejects inputs larger
than 8 MiB before deserialization.

This closes fixed-profile exact target-row coverage for valid, deeply owned
states in the six explicit tables. The standalone Python and Rust checkers
reject hostile state values outside the shared `u128` domain. Commit
`8eea5cb80ececccada8253cd2c758544de906c2c` also requires every migration proof
input to disclose one full predecessor `GlobalEconomicStateV1`. The same Rust
core imported by the guest recomputes that predecessor state root and binds its
chain, deployment, profile root, writer epoch, and height to the public journal.
Genesis requires the predecessor witness to be absent. The predecessor's
explicit-row graph receives the same 4,096-row preflight ceiling as the target.

This predecessor binding proves knowledge of the exact committed global-state
preimage. It does not prove that the disclosed state was the finalized ledger
head or that the target is a valid migration of it. Oracle, history, terminal
validity and payable paths, external-effect authorization and delivery, and
private lane contents remain separate obligations beyond state-root content
commitment.

Commits `93798a67a878b6e821e42fb6c8f40bd1f4fc18fd` and
`877ba86cf9b57df39667f3cbc5ca3a291bc1bb86` close one adjacent
publisher-authority counterexample in the in-memory reference model. A commit
port can now be constructed only from a genesis admission. Migration is an
operation on an existing port: under the port lock it snapshots the exact
current profile, state, retained receipt verifier, and publisher-binding token;
the core requires byte-equivalent canonical equality between that owned state
and the admission predecessor; after receipt verification the port rechecks
the same head, profile, verifier, and token before atomically replacing its
in-memory profile, state, initialization-certificate root, and epoch-witness
token. Tests reject a self-consistent foreign predecessor, stale expected head
or profile, and an activation whose source head advances during the receipt
callback. Direct migration construction rejects before receipt verification.
An independent GPT-5.6 Sol xhigh review found that the profile and
initialization-certificate getters could read between tuple assignments. The
follow-up commit synchronizes both getters with activation and preserves a
deterministic regression that pauses activation inside the tuple update. The
regression failed before the repair and passes afterward.

This establishes publisher-current source-head authority only inside the
in-memory conformance shell. The separately reviewed SQLite activation journal
provides a bounded durable candidate checkpoint. Verifier admission and durable
publication remain separate operations. Objective consensus finality,
committed migration-release selection, cross-process isolation, deployed
writer fencing, and production activation remain open.

Commit `0d29ea7286bd302cf3e2135a7fc7511d78ef5816` strengthens the bounded
replay relation. Genesis requires an empty replay table. An isolated migration
requires exact equality between the predecessor and target global replay
tables, and the public continuity root commits both complete tables. Addition,
deletion, replay-ID rewriting, occurrence-ID rewriting, noncanonical order and
public-root substitution reject before receipt verification. A shared generated
Python/Rust vector fixes the expected canonical root; only the Python renderer
has executed locally. This excludes migration-time pre-consumption of a global
replay identifier. It does not prove private-lane nullifier continuity,
complete nonce continuity, or source-head finality. One bounded GPT-5.6 Sol max
read-only review attempt returned no report, so independent review of this
strengthening remains pending.

Commit `1ea1303dd8509b34bf8278c54720fa9f458060fc` adds one bounded external-outbox
relation. Genesis requires an empty outbox. Migration requires byte-equivalent
canonical preservation of every outbox row, including effect ID, destination,
payload hash, originating commit ID, status, row count and order. Source and
target tables each reject above 4,096 rows before state validation, copying or
hashing in the raw admission and guest entry paths. The public continuity root
commits both complete tables and both state roots. A generated Python/Rust
vector fixes the expected root; only the Python renderer has executed locally.
Migration-time enqueue, deletion, acknowledgment, rewrite or compaction
therefore rejects in this bounded source model. This does not prove that a
source row came from an authorized committed effect, or that delivery,
external finality, retry, acknowledgment authenticity, destination idempotency
or durable reconciliation is correct.

Commit `348076a1dacc3348fb819f217d4bb40913edb27f` adds one conservative
terminal-obligation continuity relation. Genesis requires no predecessor and
commits the complete target terminal table whose rows the separate atom
manifest classifies. Migration requires exact equality between complete
predecessor and target tables, including obligation ID, lane ID, claimant,
asset, amount atoms, status, row count, and canonical order. The public root
also commits the initialization kind and exact source and target state roots.
Terminal rows share the 4,096-row combined explicit-value ceiling with
balances, supplies, named accounting-location rows, liabilities, and reserves.

Executed Python admission tests kill public-root substitution, addition,
deletion, reordering, every terminal field mutation, and both illegal
kind/predecessor shapes before receipt verification. The checked-in golden
fixture commits the complete Python/Rust projection. Rust ABI, vector, and
RISC0 shared-core test sources exist and remain uncompiled. This relation
rejects migration-time erasure or rewrite of the disclosed terminal table in
the bounded admission model. It does not establish obligation validity,
funding, claimant key control, a payable terminal route, correct drain or
tombstone semantics, source-head finality, or complete migration
classification. Four built-in max-review workers spanning Sol, Terra, and Luna
stalled without returning a report, so independent review of this slice
remains pending.

A pinned RISC0 3.0.6 guest and host source use the same Rust statement checker
over canonical bounded input and contain guards for development mode,
placeholder methods, non-succinct receipts, wrong journals, and wrong measured
images. The source keeps the prepared statement opaque, recomputes its journal
before certificate construction, and requires the journal's image field to
equal the measured guest image. Commit
`d3b0e38c872106940a0a8e7478d78481281a7c8a` added a real-proof harness that
records non-authoritative host cycle diagnostics, canonically serializes and
replays a Succinct receipt, kills removal of the cryptographic verification
call, and retains explicit unmounted and no-production-authority wording. The
predecessor-bearing Rust candidate has passed formatting parse and locked Cargo
metadata resolution only. Its Rust targets have not been type-checked or run:
the local workstation heat constraint excludes the several-gigabyte rebuild,
and the previously authorized proof-machine endpoints are unavailable. No real
ELF, image ID, cycle measurement, proof, or receipt replay has therefore been
produced for this guest.

The current manifest does not individually source-classify Oracle occurrences,
replay rows, history, outbox rows, or objects hidden behind private lane roots.
The replay-preservation relation now requires exact equality of predecessor and
target global replay tables, excluding migration-time additions, deletions and
rewrites. Private lane replay and nullifier state remains outside this result.
It also does not establish total predecessor-source classification for a
migration, the semantic truth of a migration label, the objective authority
represented by a source-authorization root, selection from the governed
migration-release registry, verifier-owned durable activation mounting,
objective source-head finality, writer rotation, or shared-asset coexistence.
Those remain VM-11 blockers.

The 18-workflow/81-scenario ATDD catalogue and its historical 11 Luna-required
expansions are insufficient as a complete M6 capability manifest. The catalogue
does not yet provide closed lifecycle contracts for every required farm,
buy-and-burn, Oracle-economics, strategy-escrow, proof-task, external-finality,
and autonomous-governance capability. A profile containing only the workflows
already represented there must not satisfy VM-01 or VM-04 by omission.

`ZENODEX_M6_CAPABILITY_MANIFEST_V1.json` now fixes an independent research
universe of 103 capability requirements over all 12 lanes, four required
cross-lane routes, and the day-one exclusions. Its content-derived root is
bound through the profile's governed policy registry, and certified initial
state admission rejects a missing, foreign, or altered capability binding.
This closes the self-declared subset-universe counterexample for the in-memory
reference path. The manifest deliberately remains `manifest_complete=false`
and `release_eligible=false`: individual command semantics, disabled-writer
certificates, implementation/evidence mappings, and economic policy decisions
are still unresolved, so this binding grants no production authority.

The operation-derived Python sink inventory now scans direct `os.replace`
calls and literal SQL mutation calls throughout `src`, plus direct
`self._state` publication assignments in `src/integration`. It classifies 20
sink identities containing 29 current occurrences. Its negative evidence uses
an arbitrarily named `persist_balance_patch()` function, demonstrating that a
new literal SQL value mutation cannot evade this V1 scan by avoiding known
writer names. Nineteen authority-relevant sink groups remain without
release-backed bindings. VM-01 therefore remains `PARTIAL`. Dynamic SQL, ORM
mutation, indirect assignment, Rust, Tau, shell, generated code, native
extensions, runtime loading, deployment wiring, and actual deployed
reachability still require independent sink-first inventories and a composed
complete-mediation gate.

Commit `7b5b142e32c505261fbcea68ebb915464b187acb` adds a bounded durable
activation journal for complete genesis or migration candidate bundles. The
journal redecodes caller bundles into newly validated owned snapshots, checks
exact lineage and projected retention bounds under `BEGIN IMMEDIATE`, and
commits the immutable candidate plus singleton head through one SQLite CAS.
Exception and child-process crash tests establish exact `PRE` or `POST`
recovery at the tested transaction boundaries; concurrent-reader, stale-CAS,
lost-acknowledgment, historical-retry, schema-mutation, capacity BVA, hostile
frozen-object mutation, and canonical-decoding regressions pass. The focused
journal suite has 36 passing tests, and the shared ABI plus journal run has 104
passing tests. GPT-5.6 Sol max returned `GO` only for `UNMOUNTED`,
`TESTED_DISCOVERY` infrastructure after two earlier `NO-GO` reviews produced
and then verified concrete repairs.

Commit `edd03093d3a4485c26bc73df231cb507094d2cf6` adds an unmounted
ordinary-epoch durability contract. One canonical bundle retains the complete
post-state, epoch certificate, global effect plan, published record, release
observation, and raw receipt bytes. It equates canonically sorted effect
occurrence consumption with the certificate occurrence set, requires the exact
canonical journal-byte declaration, enforces the ABI resource ceilings, and
rejects foreign inner ABI schemas. Its SQLite transaction inserts the bundle
and advances the head under CAS, unique durable commit identity, contiguous
lineage, and row/byte capacity bounds. Exact-limit and one-byte-over capacity
tests, exact and historical
retry, cross-instance serialization, exception faults, and abrupt-process
crashes exercise recovery. The focused ordinary-epoch suite has 37 passing
tests; the combined ABI, activation-journal, and ordinary-journal run has 141.
Two max reviews returned `NO-GO` and identified byte-capacity, occurrence
ordering, exact journal-length, proof-resource, and evidence defects. Commit
`edd03093d3a4485c26bc73df231cb507094d2cf6` repairs those findings. The final
max re-review returned `GO` only for `UNMOUNTED`, `TESTED_DISCOVERY`
infrastructure and preserved every authority and production nonclaim.

These durable slices narrow VM-10 and VM-11. They do not verify retained
receipt bytes, select a migration release, establish objective source-head
finality, reconcile external acknowledgments, mount a sole writer, or retire
legacy paths.

Commit `eb6bf17b1c0b210fc6d7bee8bb25c0f0aa2a7dae` joins the ordinary-epoch
verification and durable-publication path behind one unmounted,
factory-constructed Python API. The publisher fixes one genesis activation,
profile, receipt-verifier instance, private binding token, and SQLite journal.
It resolves the caller's expected source against validated durable history,
captures the journal CAS token before receipt verification, rechecks the exact
state, effect, body, profile, verifier, and source bindings, constructs the
published record and complete durable bundle internally, and delegates the
only durable linearization point to the journal's SQLite transaction. Exact
historical retry re-verifies the receipt and covers a lost commit
acknowledgment. Competing publications and a head change during verification
cannot overwrite the winning head.

The focused publisher suite has 11 passing AAA tests. The combined ABI,
ordinary-journal, publisher, writer-inventory, and value-sink run has 136
passing tests. An independent maximum-reasoning review returned `GO` only for
`UNMOUNTED`, `TESTED_DISCOVERY` use. The review confirmed exact source/profile
checks and in-transaction CAS revalidation.

Commit `369fe53f29184cd85a039459703d1b1f31d9b42f` removes the public ordinary
epoch journal commit method from that API and gives the intended publisher path
a separate journal-instance-bound write capability in addition to the CAS
token. The same commit explicitly preserves and tests the
underscore-prefixed `_commit_epoch_v1` same-interpreter bypass as negative
evidence. The writer and sink ledgers retain this private structural writer as
a release blocker, so the slice cannot acquire `NO_BYPASS` status by hiding it.

Commit `a34f11ff50cb6615bc68ffaa240c7e215ad4a379` preserves four minimized
composition counterexamples and their repairs:

- replacing a verifier backend method after binding cannot change the exact
  callable retained by the capability;
- a privately constructed authority shape must still name the registry-selected
  release and its exact implementation, evidence, backend, image, and resource
  coordinates;
- opening a WAL/schema-mutant store rejects before persistent journal-mode
  configuration in the tested case;
- verified-publisher create retry recovers only a byte-identical committed
  activation after acknowledgement loss.

Commit `0b0d93cdd5df08a8a0a8a6d591c13659ec8f6d64` closes three composed
follow-up histories. Create retry now rejects matching activations with a
nonzero stored history. Open rejects crash-left WAL/SHM and a WAL-mode database
header before SQLite can checkpoint or unlink those artifacts, with a regression
covering the complete tested file family. Journal paths accept exact strings or
the exact platform `Path` type, preventing method-overriding path subclasses
from redirecting a publisher capability.

The callable guarantee is process-local. Mutable callable behavior, globals,
closure state, and the executing binary remain unattested. Commits
`44fd5ca175f812c72906b0bac7ac41af2046a04e`,
`84d702fbad7d8f8c81a44bb4aed0d3b300f5474c`, and
`a70a8f099c570b39dfd5c4a1ceb76aa686942ded` establish and review the bounded
directory-local current-authority head. Commit
`d606affe4aa53a82c849c385b656bf6cf90e7479` repairs the review findings by
building a private `0600` same-directory SQLite candidate, validating and
fsyncing it, installing it at an absent final name with atomic no-replace
semantics, and returning a typed busy exception for cooperating contention.
Reopen requires current-process ownership, exact `0600` mode, a regular file,
and one link. The canonical head binds activation, profile, writer epoch,
verifier coordinates, root image, deployment, one named epoch store, adjacent
generation, and active or revoked status. The epoch CAS token snapshots that
authority, and publication rechecks the complete active head inside one
`BEGIN IMMEDIATE` transaction with the authority database attached. A
differently named second publisher rejects, in-flight explicit revocation
returns `AUTHORITY_STALE`, active rotations reserve revocation capacity, and
historical authority retry returns `STALE_HEAD`. An exact epoch already in
validated history returns `ALREADY_COMMITTED` after revocation without mutating
the epoch file; unpublished work remains fenced.

Commit `3812518d60cc7fa8532850b43c0b6d18952afb26` closes the bounded
post-link process-crash wedge. Exact retry opens final and candidate names
without following symlinks, proves that both descriptors name one private
two-link inode, validates the complete expected sequence-zero authority or
epoch store through the held final descriptor, removes only the reserved
candidate name, fsyncs the directory, and requires the final descriptor to
have one link. Fault injection covers the first directory fsync, candidate
unlink, and second directory fsync boundaries for both stores, plus the
verified-publisher create route. Byte-identical separate inodes, wrong expected
heads, and wrong activation bundles remain unchanged. Exact single-link
current-UID `0644` stores receive typed migration-required rejection without
automatic permission or content mutation. The release remains
fresh-install-only until a descriptor-validated legacy migration exists.

Commit `0535b90fc404e5785bb316ad30aa96a8631c4642` closes the paired
special-file availability counterexample. Recovery first opens identity-only
descriptors with Linux `O_PATH|O_NOFOLLOW`, rejects non-regular entries before
any readable open, and reopens the held final inode through `/proc/self/fd`.
Paired FIFOs therefore reject promptly while the directory lock is held. A
missing `O_PATH` or unusable procfs produces a typed non-mutating
unsupported-platform rejection. The accepted recovery relation intentionally
includes an exact current-UID `0600` two-name hardlink pair regardless of
install provenance; the shared-UID research model supplies no authenticated
install-intent marker. Production requires exclusive directory ownership or
an authenticated equivalent.

Commit `8725fa0ad9e9a177c19c4dd10434aec8a566237d` completes the typed
platform boundary. Raw proc-descriptor `os.open` failures and the initial
SQLite connection failure through procfs now map to the store-specific
unsupported-platform class before candidate unlink or any persistent
mutation. Adversarial tests simulate both denial points and preserve both
names plus the two-link recovery state.

The same evidence preserves four executable release blockers. Restoring old
authority-file bytes resurrects a revoked publisher. Restoring only the epoch
database to sequence zero under unchanged active authority permits the same
epoch publication to commit again. Replacing the authority pathname with a
revoked database leaves an already-open publisher attached to the detached
active inode and able to commit. Committing the separate migration journal
leaves the old publisher able to commit. Authority successor admission remains
an unauthenticated private same-process hook. A production closure therefore
requires one anti-rollback authority and epoch anchor, descriptor/inode
binding, plus one atomic migration transaction that installs the new
activation, matching authority successor, profile, writer epoch, and old-writer
retirement.

The `GlobalEconomicMonotonicAnchorV1` shadow slice now defines the complete
authority/publication checkpoint and an optional publisher profile. It rejects
restored authority bytes and an epoch tip behind the externally observed tip.
If SQLite is exactly one ordinary epoch ahead, only byte-identical verified
retry of that committed epoch may advance the external checkpoint. This closes
the two saved-byte traces only under an independently authenticated, current,
monotonic, linearizable backend assumption. The repository supplies a measured
shadow port and in-memory test backend, with no concrete external service,
production release selection, genesis initialization, authority-successor
anchor protocol, atomic migration retirement, or sole-writer mount. The formal
whole-value-movement claim therefore remains `UNPROVED`.

Atomic no-replace install prevents the creator from opening a pre-existing
final pathname writable. Advisory locking coordinates participating installers.
A noncooperating same-UID process can still race the namespace, and an open
descriptor can diverge from a replaced pathname. `open` validates structural
history and does not replay every retained receipt under a newly supplied
verifier. Production recovery therefore requires exclusive authenticated store
ownership, descriptor binding, and an exact receipt-replay or equivalent
authenticated-provenance design.

The closure-status checker now treats the Git object database as the exact
subject oracle for mapped evidence. It requires each recorded artifact hash to
equal both the scoped live file and the blob at the declared 40-hex subject.
The durable publisher map includes `global_economic_proof_v1.py`, and the older
publisher-bound verification row is now independently checked. This prevents a
later worktree edit plus refreshed hash from representing an earlier commit.
The checker itself still requires release packaging, independent replay, and
authenticated distribution before it can contribute production authority.

The local unattested execution receipt records 245 passing tests in two
post-commit runs against implementation subject `8725fa0ad`: 236 adjacent
settlement ABI, verifier release, activation, authority, epoch, publisher, and
migration tests plus nine exhaustive value-sink tests. The ephemeral JUnit
outputs are hash-recorded and are not committed or independently replayed. The
portfolio includes
zero/one/max/max+1 receipt and journal boundaries, active-profile selection,
wrong registry/image/deployment/manifest/artifact rejection, generic-verifier
rejection, forged and foreign capabilities, retained-callable mutation killing,
exact activation create recovery, rejected-open nonmutation, restart/retry,
competing heads, typed first-create contention, pre-existing-namespace
rejection, no-replace install, post-link descriptor recovery, typed legacy-mode
rejection, prefetch resource bounds, exact post-revocation retry, and tested
SQLite crash points. Ruff, mypy, diff checks, and the repository security
red-flag scanner pass. Independent max review returned a conditional
fresh-install research-only `GO` for `d606affe4`, confirmed its four precursor
repairs, and identified the post-link crash wedge plus legacy-mode compatibility
as medium operational gaps. Review of `3812518d6` confirmed those repairs and
found paired-special-file blocking plus unconditional non-adoption wording.
Commit `0535b90fc` uses nonblocking identity descriptors and narrows the
accepted recovery relation. Review then found incomplete procfs error typing;
`8725fa0ad` repairs it. Final max re-review found no High or Medium defect and
returned `GO` only for the declared bounded Linux/procfs, same-UID, unmounted
research ceiling. Rollback, non-atomic migration, legacy permission migration,
shared-UID install provenance, private same-process writers, SQLite
availability bounds, and sole-writer enforcement remain open.

This narrows the directory-local fixed-profile ordinary-epoch authority and
revocation race. It
does not establish executable attestation, process isolation, sole-writer
enforcement, migration, outbox delivery and acknowledgment reconciliation,
objective finality, hardware power-loss behavior, or Rust/RISC0 parity. Other
legacy writers remain callable research paths. Python private construction is
an engineering interlock and not a security boundary. VM-10 remains `PARTIAL`;
the whole-value-movement claim remains `UNPROVED` and production authority
remains `NONE`.

The eight-decimal anchor is now represented by the content-derived policy root
`0xacfbd1be88e823fcdd1b094b8d2f0c8ee1bf19c826004e89752f27fd22aa49dd`.
The Python reference initial-state admission requires this exact binding in the
profile's governed policy registry before receipt verification. Rust
independently derives the same policy root and exposes the corresponding
profile-binding validator. This closes policy substitution at that bounded
admission surface. It does not yet prove that every decoder, command, rounding
rule, proof guest, Tau policy, API formatter, UI formatter, or mounted runtime
uses the same eight-decimal conversion contract. Denomination rescaling
remains excluded from GlobalSettlementABI V1.

## Recommended implementation order

1. Freeze the exact complete M6 capability manifest and ZDEX semantic anchors,
   including buy-and-burn, hosting compensation, eight-decimal units,
   retained-supply hyperdeflation, recovery, and terminal behavior.
2. Add separate invariant-owner certificates for Oracle, history, terminal
   validity and payable-path completeness, and private lane-object continuity;
   complete private nullifier continuity, prove outbox source authorization and
   delivery/acknowledgment
   refinement, and complete predecessor-source migration classification.
   Select the genesis or migration release from committed profile state. Build
   and measure the predecessor-bound RISC0 guest, then generate and replay its
   real succinct receipt on the proof machine. Mount the reviewed durable
   activation primitive only behind that verifier-owned admission boundary.
3. Extend the operation-derived sink inventory across dynamic Python, Rust,
   Tau, shell, generated code, native extensions, runtime loading, deployment
   wiring, and deployed entrypoints. Bind every discovered sink to an
   authoritative release row and close VM-01 with zero open or unknown rows.
4. Complete the typed Rust global state, canonical bytes, effect algebra,
   injective effect provenance, and Python/Rust parity required by VM-02 and
   VM-03.
5. Seal initial-state and epoch authority behind release-selected verifier
   implementations, measured images, and exact receipt replay. Remove
   caller-selected verifier objects from every authoritative constructor path.
6. Implement each enabled lane behind the stable ABI. Keep unresolved lanes
   absent from active routes and prove they have no writer.
7. Complete coordinators, governed routes, terminal obligations, and the global
   composition theorem.
8. Make the selected RISC0 guests execute the same Rust transitions, rebuild
   every image, and establish exact direct-versus-proof parity.
9. Integrate release-bound verifier authority and expose one opaque verified
   epoch type to the sole atomic publisher.
10. Prove crash, replay, outbox, migration, coexistence, and forward-recovery
   behavior against the mounted runtime.
11. Generate the claim certificate from the pinned release evidence and obtain
   independent formal, security, economic-lifecycle, and authority reviews.

The shortest critical path begins with VM-01, VM-02, VM-03, and VM-07. Proof
compression cannot close an omitted semantic field or an unregistered writer.

## Review instructions for a maximum-reasoning agent

Treat the proposed claim as hostile input. Review the exact pinned candidate
and answer:

1. Does `DurableEconomicEffect -> exactly one verified accepted epoch` cover
   every way value can be created, destroyed, reassigned, locked, claimed,
   released, liquidated, migrated, or externally delivered?
2. Which reachable writer, state bucket, asset class, effect, lifecycle phase,
   or recovery path is omitted?
3. Can local lane invariants all hold while global accounting, claimant
   entitlement, terminal drain, or atomicity fails?
4. Are any assumptions circular, unverifiable, broader than necessary, or
   falsely presented as proved properties?
5. Does the proof journal bind every field required to exclude crossed-state,
   crossed-command, crossed-release, crossed-profile, and crossed-effect
   attacks?
6. Can any shell, migration, governance, callback, retry, or external-delivery
   path publish value without consuming the exact verifier-owned witness?
7. What is the smallest counterexample that falsifies the claim under its
   stated assumptions?
8. Which gate can pass while the claim remains false, and what checker or
   theorem would close that defect?

Return:

```text
Verdict: REJECT | REVISE | CONDITIONALLY_SOUND
First decisive counterexample:
Omitted authority or value path:
Weakest assumption:
Unsound or incomplete gate:
Required claim-language correction:
Required implementation changes, ordered by dependency:
Residual nonclaims:
```

`CONDITIONALLY_SOUND` means that the statement is a coherent target under its
explicit assumptions. It does not promote the current implementation.

## Promotion rule

The public claim may be emitted only by a checker that binds a clean candidate,
an exact profile, all enabled release rows, all VM gates, the verifier set, the
migration predecessor, the writer epoch, and the independent review receipts.

```text
ClaimMayBeTrusted
  = complete_capability_profile
  and closed_semantics
  and complete_mediation
  and proved_model
  and runtime_refinement
  and proof_binding
  and sole_atomic_publication
  and migration_continuity
  and release_backed_evidence
```

Any false or missing conjunct keeps the claim disabled.

## Nonclaims

- No current production readiness, production authority, deployment, mount,
  writer rotation, settlement authority, or value-moving authority.
- No assertion that the current M6 model is semantically complete.
- No assertion that existing local proofs compose into a whole-economy proof.
- No assertion of Oracle truth, key safety, consensus soundness, availability,
  privacy, market profit, price stability, or protection from specified
  liquidation and trading losses.
- No assertion that a passing test suite alone establishes formal safety.
- No assertion that a proof system repairs an incorrect or incomplete guest.
- No assertion that exact global replay-table preservation proves complete nonce
  and private-nullifier continuity behind lane roots.
- No assertion that outbox-table preservation proves authorized origin,
  external delivery, finality, acknowledgment authenticity or idempotency.
- No assertion that terminal-table preservation proves obligation validity,
  funding, claimant key control, payable-path completeness, or correct drain
  and tombstone semantics.
