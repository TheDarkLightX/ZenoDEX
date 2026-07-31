# FCIS M6 Implementation Taskbook for GPT-5.6 Luna

**Version:** 1  
**Date:** 2026-07-31  
**Intended model:** GPT-5.6 Luna or another smaller implementation model  
**Status:** `AUTHORITATIVE_TASK_DECOMPOSITION_NO_PRODUCTION_AUTHORITY`  
**Primary repository:** `TheDarkLightX/ZenoDEX`  
**Required supporting repositories:** `ZenoFCIS`, `ESSO`, `LEAP-MCP`, `Morph`, `ZAG`, `Research-Kernel-MCP`  
**Starting research stack:** ZenoDEX PRs #496, #497, #498, #499 and the Durable Retraction follow-up PR

---

## 0. Mission

Complete M6 without weakening the theorem, bypassing the functional-core / imperative-shell boundary, or confusing a passing test with production authority.

The complete theorem is:

```text
RuntimeAccept
  -> authenticated command
  -> authenticated datastore-current state and execution context
  -> deterministic kernel evaluation
  -> authorized candidate
  -> exact receipt and bundle lineage
  -> atomic publication
  -> recoverable committed state
  -> committed outbox effects only
  -> no alternate acceptance path
```

M6 is not complete when a carrier, root, proof, test, or reference model exists. It is complete only when the exact production path refines this chain and every value-moving alternative path rejects.

This taskbook intentionally gives Luna small, ordered tasks. Do not combine tasks merely to reduce the number of pull requests. A task may be split further when its diff becomes difficult to review.

---

## 1. Non-negotiable operating rules

Luna must obey every rule in this section.

### 1.1 Exact-head discipline

Before changing code:

1. fetch the named base branch;
2. record the exact base commit SHA;
3. confirm the working tree is clean;
4. create one new branch for the task;
5. never silently rebase onto a moving branch;
6. report the final commit SHA and exact commands run.

If the base head differs from the SHA named by the task packet, stop that task and report `BASE_HEAD_MOVED`. Do not guess whether the new head is compatible.

### 1.2 One task, one claim

Each task must have one principal claim. Examples:

```text
Python and Rust compute the same SRGD transition.
A recovered durable layout is an exact fixed point of canonical reopen.
Every production publisher is dominated by the verified commit port.
```

Do not mix unrelated cleanup, formatting, dependency upgrades, UI changes, or refactors into an assurance task.

### 1.3 No caller-owned authority

Public production functions must not accept caller-provided values that can replace an earlier source in the lineage, including:

```text
precomputed state roots
post-state roots
SLNF boundary or lineage roots
candidate roots
receipt roots
bundle roots
proof-context roots
migration authority roots
outbox acknowledgment roots
promotion status
```

A caller may supply raw authenticated bytes or a typed source value at an explicit boundary. Every downstream root must be recomputed by the verifier-owned implementation.

### 1.4 Exact types and closed variants

At public boundaries:

- reject subclasses;
- reject Boolean-as-integer aliases;
- reject floats;
- reject unknown fields and enum variants;
- reject duplicate map keys;
- reject noncanonical order;
- reject oversized collections before expensive work;
- reject unsupported versions before interpreting payload fields.

Use immutable values. A frozen dataclass alone is not sufficient if it retains aliases to mutable data.

### 1.5 Fail closed

Treat all of these as non-supporting:

```text
timeout
UNKNOWN
solver disagreement
missing file
missing row
extra row
unrecognized variant
integer overflow
codec disagreement
stale state
stale configuration
unavailable verifier
incomplete publisher inventory
unreviewed migration
unresolved crash outcome
```

Never turn an exception into acceptance. Unexpected internal exceptions should remain visible as engineering failures, not be relabeled as semantic rejection unless the boundary contract explicitly requires that mapping.

### 1.6 No self-modifying assurance workflow in final diffs

A temporary workflow may be used only on a disposable branch to obtain formatting or tool output. The final task branch must contain a read-only workflow:

```yaml
permissions:
  contents: read
```

and checkout must use:

```yaml
persist-credentials: false
```

The final workflow must never commit or push changes.

### 1.7 Proof boundaries

Keep these claims separate:

```text
abstract theorem
executable reference model
Python implementation refinement
Rust implementation refinement
canonical byte/root parity
authentication
current-state binding
transactional persistence
recovery
external delivery
no-bypass mounting
```

Do not describe one layer as proving another.

### 1.8 Permanent negative tests

Every fixed defect must leave a mutant that would fail if the defect returns. The mutant must target the semantic failure, not merely a syntax error.

### 1.9 Required response from Luna

For every completed task return exactly:

```text
TASK_ID:
BASE_SHA:
HEAD_SHA:
BRANCH:
FILES_CHANGED:
CLAIM_IMPLEMENTED:
COMMANDS_RUN:
RESULTS:
MUTANTS_ADDED:
FORMAL_EVIDENCE:
REMAINING_NONCLAIMS:
REVIEW_RISKS:
```

Do not report “done” without the exact evidence.

---

## 2. Frozen vocabulary and architecture

### 2.1 Segmented Lineage Normal Form — SLNF

Within one accepted transition, same-key fee witnesses may group. Across accepted transitions, segments remain ordered. Every segment carries both:

```text
semantic_stream_root
lineage_stream_root
```

The semantic root commits to allocator-visible arithmetic. The lineage root commits to exact ordered provenance. Neither replaces the other.

### 2.2 Certificate Closure Cube — C3

Semantic, authority, and durability projections enter one conflict-detecting claim language. Same-key / different-digest joins reject. Derived keys have canonical writers.

### 2.3 Tree–Chord–Gate — TCG

TCG checks declared authority paths against:

```text
complete topology inventory
rooted spanning tree
local edge receipts
chord coherence
gate filtration
lineage bindings
```

TCG does not prove that the supplied publisher inventory is complete. The inventory must be independently derived and anchored.

### 2.4 Canonical Durable Retraction — CDR

```text
encode : AuthorizedHistory -> DurableLayout
reopen : DurableLayout -> AuthorizedHistory | Reject
reopen(encode(h)) = h
N = encode o reopen
Authoritative(d) iff N(d) = d
```

The fixed-point gate rejects missing, extra, duplicate, reordered, crossed, or foreign durable evidence.

### 2.5 Detectable Commit Fiber — DCF

Durable state and client knowledge are different types.

Durable resolution:

```text
NEWLY_COMMITTED
ALREADY_COMMITTED
ABSENT_RETRYABLE
STALE_STATE
DEFINITE_REJECTION
```

Client observation:

```text
CONFIRMED_NEW
CONFIRMED_ALREADY
CONFIRMED_STALE
CONFIRMED_REJECTION
INDETERMINATE
```

`INDETERMINATE` is never persisted as a durable state.

### 2.6 Retraction-Quotiented Authority Graph — RQAG

Runtime loops may be collapsed only when a checked receipt proves they are observational identities on the exact canonical state:

```text
retry same committed request
reopen and re-encode canonical snapshot
redeliver same effect to an idempotent destination
repeat pure verification
```

A new commit, acknowledgment publication, migration step, or state change is not a stutter and must remain a theorem-bearing edge.

### 2.7 M6 Authority Normal Form — ANF

The integration target for one committed transition is:

```text
source-bound SLNF extraction
+ C3 closed artifact certificate
+ TCG topology and instance certificate
+ authenticated proof-context root when applicable
+ DRA publication atom
+ canonical durable fixed-point receipt
```

The candidate, receipt, bundle, history atom, and outbox must all bind the same ANF identity.

---

## 3. Branch and pull-request stack

Do not merge research branches arbitrarily. Preserve the dependency order.

```text
PR #496  AGQE/SRGD sign-dual theorem
  -> PR #497  SLNF occurrence semantics
       -> PR #498  source-bound concrete C3
       -> PR #499  TCG authority certificates
            -> Durable Retraction follow-up
```

Before an integration branch is created, produce a compatibility report that compares:

```text
#498 head against #499 head
#498 changed files against #499 changed files
public schema/version names
Lean lake roots
workflow names
shared imported symbols
```

The first integration branch should be based on the later common ancestor or an explicitly reviewed synthetic merge, never on an assumed stack.

---

## 4. Task dependency graph

Execute in this order unless a task explicitly says it may run in parallel.

```text
A00-A04: exact-head preparation and stack integration

B01-B09: R02 complete adaptive apportionment theorem and dual-language refinement
C01-C07: R03 entitlement identity, representation factorization, migration

D01-D10: R04 ANF integration of SLNF, C3, TCG, and DRA

E01-E08: R05 authenticated nonce, CAS, retry, concurrency
F01-F09: R06/R07 exact evidence, history, nullifiers, reopen authorization
G01-G07: R08 proof-context binding

H01-H08: R09 concrete atomic publication and crash recovery
I01-I08: R10 outbox delivery and acknowledgment
J01-J09: R11 migration and authority switch

K01-K08: R12 no-bypass mount audit
L01-L09: R13 zUSD whole-system invariant

M01-M08: final composition, independent review, mounting, promotion
```

Tasks inside B, C, E, F, and G may proceed in parallel only after A04 freezes the shared identifiers and schema ownership.

The companion 105-task JSON graph targets the M6 obligation lanes R02 through
R13. R01 is an external prerequisite and is not represented as a graph target.
The A00-A04 and M01-M08 tasks are program-composition tasks; they do not add a
claim that R01 is covered by this graph. The graph remains a plan, not evidence
that any planned task is complete.

---

# Wave A — Exact-head preparation

## A00 — Record all exact research heads

**Purpose:** eliminate hidden branch drift.

**Actions:**

1. fetch PR metadata for #496, #497, #498, #499, and the Durable Retraction PR;
2. record base branch, base SHA, head branch, head SHA, mergeability, draft state;
3. fetch every changed filename list;
4. write `docs/research/FCIS_M6_EXACT_HEAD_LEDGER_<date>.json`;
5. include SHA-256 of the ledger itself in the report.

**Required fields per PR:**

```json
{
  "number": 498,
  "base_branch": "...",
  "base_sha": "...",
  "head_branch": "...",
  "head_sha": "...",
  "changed_files": ["..."],
  "workflow_runs": [{"name": "...", "id": 0, "conclusion": "success"}]
}
```

**Acceptance:** repeated generation against unchanged GitHub state is byte-identical.

**Stop condition:** any required PR is not fetchable or its head changes during packet construction.

---

## A01 — Produce a semantic conflict map

**Purpose:** identify collisions before merging code.

Compare the exact heads for:

```text
same path / different content
same exported symbol / different meaning
same schema ID / different fields
same root domain / different preimage
same workflow name / different gates
same Lean declaration root / different import graph
```

Write:

```text
docs/research/FCIS_M6_STACK_CONFLICT_MAP_<date>.md
```

For every collision classify:

```text
IDENTICAL
COMPATIBLE_ADDITIVE
RENAME_REQUIRED
SCHEMA_MIGRATION_REQUIRED
SEMANTIC_CONFLICT
UNKNOWN_REQUIRES_REVIEW
```

Do not resolve `SEMANTIC_CONFLICT` automatically.

---

## A02 — Freeze cross-branch identifiers

Create one reviewed registry for identifiers that later tasks must share:

```text
semantic allocator profile
SRGD representation profile
AGQE representation profile
fixed role order
fee distribution domain
SLNF versions
C3 claim keys
TCG topology version
DRA durable-layout version
proof-context version
ANF version
```

Recommended new file:

```text
src/core/fcis_m6_profile_ids.py
```

It must contain constants only, no mutable registry or plugin discovery.

**Mutants:** duplicate semantic ID, representation ID used as semantic ID, role-order substitution, domain separator collision.

---

## A03 — Create the M6 task evidence directory

Create:

```text
docs/research/m6_tasks/
```

Every implementation task writes:

```text
TASK_<id>_REPORT.md
TASK_<id>_EVIDENCE.json
TASK_<id>_SOURCE_MANIFEST.sha256
```

The JSON must include exact commands, results, tool versions, source hashes, mutants, and nonclaims.

---

## A04 — Build the first reviewed integration base

**Prerequisites:** A00-A03.

Create a synthetic integration branch containing only conflict-free commits from #498, #499, and DRA. Do not mount anything.

Required checks:

```text
git merge-tree or equivalent conflict report
Python compile
Ruff
strict mypy on all research modules
all focused tests from #497-#499 and DRA
all Lean roots
Julia oracle parity
no duplicate workflow names
no duplicate domain separators
```

**Acceptance:** one exact green integration head and a reviewer-readable source inventory.

**Nonclaim:** an integration branch is not a production mount.

---

# Wave B — M6-R02 complete adaptive apportionment theorem

## B01 — Implement the overflow-safe Euclidean quota primitive

**Files:**

```text
src/core/fcis_fee_apportionment_transition.py or existing transition module
tests/core/test_fcis_fee_apportionment_transition.py
```

**Algorithm:** for amount `A`, denominator `D`, and weight `w`:

```text
q, r = divmod(A, D)
base = q*w + (r*w)//D
remainder = (r*w)%D
```

Never compute `A*w` in U256.

**Validation:**

```text
0 <= amount <= U256_MAX
0 <= weight <= D
D == 10_000 for the production profile
q*w <= amount
r*w < D^2
0 <= remainder < D
base <= amount
```

**Tests:** exact values at `0,1,D-1,D,D+1,U256_MAX-1,U256_MAX`; all weights `0,D`, and representative middle values.

**Mutants:** direct U256 `A*w`, float division, truncated machine integer, unchecked addition, Boolean amount.

---

## B02 — Freeze the exact three-role selector

Use scores:

```text
score_i = deficit_i + remainder_i
```

Select exactly:

```text
h = sum(remainders) / D
```

eligible roles with `remainder_i > 0`, largest score first, fixed role order as tie break.

**Implementation requirements:**

- exactly three roles;
- no generic unordered dictionary iteration;
- `h` must be an integer in `{0,1,2}`;
- bonus is a three-bit tuple;
- selected role must have positive remainder;
- stable rejection codes.

**Mutants:** omit current remainder from score, reverse tie order, choose zero-remainder role, select wrong number of roles.

---

## B03 — Prove one-occurrence conservation and quota laws in Lean

Create:

```text
lean-mathlib/Proofs/FCISFeeApportionmentSRGDTrace.lean
```

Import the reviewed SRGD and AGQE/SRGD modules.

Prove named theorems:

```text
safe_euclidean_floor
residual_sum_divisible
residual_count_zero_one_two
one_step_conservation
zero_weight_zero_allocation
one_step_local_quota
```

Do not introduce `axiom`, `sorry`, `admit`, or `unsafe`.

**Axiom gate:** record `#print axioms` for every public theorem.

---

## B04 — Prove finite adaptive trace preservation

Define a typed occurrence relation and an ordered trace fold. Prove:

```text
valid initial deficit
+ every occurrence has a valid authenticated policy
+ every step satisfies the reviewed SRGD relation
-> every prefix deficit is zero-sum and strictly inside (-D,D)
```

The theorem must not assume a fixed policy.

The trace carrier must be the R01 ordered SLNF word. Do not flatten across segment boundaries.

---

## B05 — Prove the cumulative discrepancy theorem

Preserve the history identity:

```text
d_t,i = sum_{j<t} A_j*w_j,i - D*sum_{j<t} allocation_j,i
```

Then derive:

```text
abs(cumulative_actual_i - cumulative_ideal_i) < 1 atom
```

Keep integer identity and rational interpretation as separate lemmas.

**Mutants:** history initialized to zero during representation migration, occurrence reordering, segment aggregation, policy substituted after allocation.

---

## B06 — Implement exact Python postcondition revalidation

Before constructing success, recheck:

```text
sum allocations == amount
zero-weight -> zero allocation
local quota bounds
sum post deficits == 0
all abs(post deficit) < D
bonus support
exact fixed role order
```

A postcondition failure is an internal relation failure and grants no candidate.

---

## B07 — Implement the Rust transition

**Crate:** the existing FCIS runtime-core crate.

Use:

```text
U256 for amount/base/allocation
u32 or u64 for denominator, weights, remainders
signed i64 or wider checked type for deficits and scores
```

Use checked arithmetic. Do not cast U256 to `u128`, `usize`, or floating point.

Provide a pure function returning a closed `Accept | Reject` enum.

---

## B08 — Add Kani/SMT arithmetic refinement

Prove or exhaustively check the bounded machine claims:

```text
q*w never overflows admitted U256 inputs
r*w < D^2
base <= amount
allocation <= amount
score stays inside admitted signed range
```

If Kani cannot model the exact U256 library, create a smaller arithmetic lemma crate with an explicit refinement map to the production type.

Timeout or unsupported features are non-supporting.

---

## B09 — Build Python/Rust/independent-oracle parity

Freeze canonical vectors and compare:

```text
allocations
post deficits
bonus bits
remainders
canonical bytes
transition root
rejection code and path
```

Exhaust all valid states for `D <= 12`. Add at least 1,000 adaptive-policy steps at production D and U256 edge vectors.

**R02 completion gate:** B01-B09 green at one exact head.

---

# Wave C — M6-R03 entitlement identity and migration

## C01 — Separate semantic profile from representation codec

Create identifiers:

```text
semantic_profile = adaptive-global-quota-entitlement/three-role/v1
representation = srgd-deficit/v1 | agqe-surplus/v1
```

The state key includes semantic profile, not the representation label.

**Reason:** SRGD and AGQE are sign-dual representations of one transition. Treating them as unrelated semantic algorithms creates a reset hazard.

---

## C02 — Freeze the entitlement key

Exact key fields:

```text
fee_distribution_domain_id
asset
semantic_profile_id
fixed_role_order_id
```

Explicitly exclude:

```text
buyback destination
treasury destination
rewards destination
custody account
ordinary policy weights
representation codec
```

Deployment replay protection belongs in the surrounding authority/context root, not in a rotatable entitlement key field.

**Mutants:** destination rotation creates a new key; custody rotation creates a new key; role permutation aliases; domain omitted.

---

## C03 — Add canonical state and migration codecs

Create versioned values for:

```text
EntitlementStateV1
RepresentationMigrationManifestV1
```

Manifest fields:

```text
old semantic key
new semantic key
old representation ID
new representation ID
old state root
new state root
migration map ID
authority epoch root
activation sequence
```

No caller-provided `new_state_root`; recompute it from transported entries.

---

## C04 — Implement exact SRGD-to-AGQE transport

For every entry:

```text
sigma_i = -deficit_i
```

Require:

```text
same semantic key
same role order
strict old-state validity
strict new-state validity
complete entry set equality
no missing or surplus entry
```

The map is involutive. A zero-initialized target is a hard rejection.

---

## C05 — Prove trace conjugacy

Extend the existing one-step sign-dual theorem to the complete SLNF word:

```text
phi(fold SRGD d events) = fold AGQE (phi d) events
```

Prove `phi(phi(d))=d` and key preservation.

---

## C06 — Add rotation and reset mutants

Permanent tests:

```text
policy rotation preserves state key and residuals
destination rotation preserves state key and residuals
custody rotation preserves state key and residuals
representation migration preserves exact entitlement history
zero-reset migration rejects
partial-entry migration rejects
cross-deployment state substitution rejects at authority layer
```

---

## C07 — Produce an exact migration review packet

Include old/new bytes, roots, every entry mapping, activation sequence, authority roots, Lean theorem hashes, and Python/Rust parity vectors.

**R03 completion gate:** no path can rename or rotate configuration to erase residual history.

---

# Wave D — M6-R04 Authority Normal Form integration

## D01 — Define `FCISAuthorityNormalFormV1`

Create one immutable value containing exact roots for:

```text
source-bound command/context/pre-state
SLNF boundary/policy/witness/semantic/lineage
candidate patch and next state
C3 closed claim set
acceptance decision and receipt
base bundle and outbox
TCG topology and instance
proof context, when required
DRA pre-history and post-history
migration authority epoch
```

Do not include cached roots that are not freshly recomputable.

---

## D02 — Embed source-derived SLNF roots in evaluation evidence

Modify the actual evaluation evidence schema so the evaluator consumes or binds the exact source-derived segment before producing the candidate.

Required equality:

```text
extractor material == evaluator material
extractor segment is the segment used by fee-state transition
```

Do not bolt roots onto a receipt after the candidate has already been computed.

---

## D03 — Bind ANF into the acceptance receipt

The receipt must include or commit to:

```text
ANF version
command/context/pre/next roots
SLNF dual roots
policy and witness roots
budget root
patch/plan roots
TCG instance root
proof-context root
```

The receipt root is recomputed from exact typed fields.

---

## D04 — Bind ANF into the commit bundle and outbox

The bundle must retain the exact decision object or a canonical byte-identical reconstruction. Recompute:

```text
receipt root
bundle root
outbox plan
outbox root
ANF root
```

Crossing an outbox from another accepted candidate must reject before publication.

---

## D05 — Derive the TCG publisher inventory independently

Generate the topology inventory from reviewed deployment/build sources, not from the certificate being checked.

Inventory at least:

```text
API
CLI
administrator
migration worker
recovery worker
proof verifier
legacy runtime
background outbox worker
direct datastore adapter
```

Anchor the topology root in configuration controlled outside the runtime certificate.

---

## D06 — Validate the C3 rule manifest

Replace the implicit fixed tuple with a typed validated manifest or provide an exact theorem that the fixed tuple has:

```text
one writer per derived key
complete derived-key coverage
acyclic dependencies
canonical dependency order
fixed-point termination
rule-order independence
```

Keep the public source-bound constructor as the only exported constructor. Arbitrary-segment builders remain private test seams.

---

## D07 — Implement RQAG stutter receipts

Create a closed `StutterReceiptV1` with:

```text
operation ID
pre canonical root
post canonical root
observable root
checker ID
proof/verification root
```

Accept a collapsed loop only when:

```text
pre == post
observable pre == observable post
checker is the pinned checker for that operation
```

Operations initially eligible:

```text
same-commit retry
canonical reopen/re-encode
same-effect destination dedup
repeat pure verification
```

Do not classify migration, ack publication, or a new commit as stutter.

---

## D08 — Build the combined ANF checker

Input instance fields are supplied externally. The checker must:

1. recompute source extraction;
2. recompute evaluation;
3. recompute C3 closure;
4. verify TCG topology and instance against anchored expectations;
5. verify proof context;
6. verify publication atom and DRA history transition;
7. reject any conflict or missing gate;
8. return one canonical ANF root.

No stage may accept a root produced by a later stage as a replacement for its source.

---

## D09 — Add crossed-axis and temporal mutants

Required mutants:

```text
semantic from transition 1 + receipt from transition 2
receipt from transition 1 + bundle from transition 2
bundle from transition 1 + outbox from transition 2
TCG receipt from foreign topology
DRA atom with foreign authority epoch
same semantic root + different lineage root
stutter receipt hiding a new commit
stutter receipt hiding a migration step
```

---

## D10 — Prove the abstract ANF composition theorem

Lean theorem structure:

```text
horizontal artifact coherence
+ global path/gate coherence
+ vertical durable retraction
+ external effect ancestry
-> one source lineage for every accepted durable effect
```

The theorem may take authentication and inventory completeness as premises, but those premises must remain visible in its statement.

---

# Wave E — M6-R05 nonce, retry, and concurrency

## E01 — Define authenticated request identity

Freeze a stable request/idempotency identity bound to signed command bytes and deployment context. Decide whether it is externally supplied by the authenticated command or deterministically derived; document the replay semantics.

Do not derive it from a post-state or server-generated random value.

---

## E02 — Define the nonce/nullifier relation

For each authenticated sender:

```text
current nonce = n
command nonce = n+1
nullifier = H(deployment, sender, nonce, command family)
```

The exact nullifier preimage and domain separator are protocol data.

---

## E03 — Add datastore uniqueness constraints

At minimum:

```text
UNIQUE(commit_id)
UNIQUE(nullifier_root)
UNIQUE(effect_id)
```

Store the commit fingerprint beside `commit_id`. A duplicate ID with a different fingerprint is a hard collision, never idempotent success.

---

## E04 — Implement the total stored-state classifier

Exact order:

1. same commit ID and same fingerprint -> `ALREADY_COMMITTED`;
2. same commit ID and different fingerprint -> `DEFINITE_REJECTION`;
3. nullifier consumed by another commit -> `DEFINITE_REJECTION`;
4. expected pre-root differs -> `STALE_STATE`;
5. writer/head authorization differs -> `DEFINITE_REJECTION`;
6. otherwise -> `ABSENT_RETRYABLE`.

Client transport uncertainty is returned separately as `INDETERMINATE`.

---

## E05 — Implement expected-root atomic CAS

The transaction must compare the datastore-current root and authority epoch inside the same transaction that inserts the publication atom and uniqueness rows.

No preflight read followed by an unguarded write.

---

## E06 — Add real concurrency tests

Use independent database connections and barriers. Required cases:

```text
two different commands, same sender/nonce
same exact command retried concurrently
two commands with same commit ID, different fingerprint
commit racing migration quiescence
commit racing authority switch
```

Assert one linearized result and no partial rows.

---

## E07 — Add transport-loss tests

Inject loss:

```text
before request reaches server
after validation before transaction
after transaction commit before response
after response generation during transport
```

Fresh lookup must resolve the exact durable class.

---

## E08 — Prove the abstract classifier in Lean/ESSO

Lean proves classifier partition/disjointness. ESSO/TLA explores concurrent commit and migration words. The database test is still required; the abstract model does not prove the SQL adapter.

---

# Wave F — M6-R06/R07 evidence, history, nullifiers, and reopen

## F01 — Define the authoritative history atom schema

The production atom must bind every durable fact required by M6, including ANF and proof-context roots. Do not rely on a loose collection of optional rows.

---

## F02 — Implement one canonical history encoder

`encode_history` is the only function that materializes authoritative table rows from history. It must emit:

```text
state header
history rows
evidence rows
nullifier rows
receipt/decision/bundle rows
replay rows
outbox rows
authority epoch rows
ack rows
```

Use canonical order and exact counts.

---

## F03 — Implement total fail-closed reopen

Reopen order:

1. exact row decoding and resource bounds;
2. canonical order and uniqueness;
3. root/cache verification;
4. reconstruct full history;
5. strict state-chain replay;
6. exact evidence projections;
7. nullifier bijection;
8. outbox ancestry;
9. authority-epoch replay;
10. canonical re-encoding;
11. exact whole-layout equality.

Return a stable rejection code/path, never a partial history.

---

## F04 — Enforce the canonical fixed-point gate

Final acceptance:

```text
encode_history(reopen(layout)) == layout
```

Do not accept selected-root equality as a substitute.

Mutate every table with missing, extra, duplicate, reordered, and crossed rows while recomputing any selected cache/root the attacker can recompute.

---

## F05 — Bind authenticated genesis

Genesis must commit to:

```text
chain/deployment
initial state root
initial configuration root
initial authority profile
history schema/version
proof-context policy
migration policy
```

A caller-selected empty history is not genesis authority.

---

## F06 — Require fresh reopened-head authorization

After process restart or datastore reopen, value movement is locked. Construct a fresh token only after canonical reopen and external authority checks bind:

```text
snapshot root
current state root
authority state root
deployment/configuration root
external authorization root
```

Commit, ack publication, and migration require the exact token. A successful state change invalidates it because the snapshot root changes.

---

## F07 — Define checkpoint and truncation semantics

If history compaction is required, a checkpoint is a new authenticated genesis-like object with:

```text
prior history root
checkpoint state root
complete nullifier accumulator root
complete authority epoch summary
proof of replay or approved snapshot certificate
```

Never delete history rows while retaining untransported nullifiers or outbox identity.

---

## F08 — Add reopen and corruption fault tests

Test process death and physical corruption around every table. Reopened state must be:

```text
exact PRE
exact POST
or reject/lock
```

It must never accept a command from a partial layout.

---

## F09 — Prove CDR and concrete refinement

Lean supplies abstract retraction/fixed-point theorems. The concrete adapter must show every committed database state decodes to the reference layout and every recovered authoritative layout is a fixed point.

---

# Wave G — M6-R08 proof-context binding

## G01 — Define `FCISProofContextV1`

Required exact fields:

```text
chain ID
deployment ID
state root
configuration root
protocol version
language/runtime version
verifier implementation ID
verification-key digest
statement/public-input schema ID
algorithm profile ID
history/genesis authority root
authority epoch
not-before / expiry or epoch rules
```

Use fixed-length digests and bounded text/enums.

---

## G02 — Define canonical proof-context bytes and root

One versioned domain separator, length framing, and shared Python/Rust vectors. Reject unknown fields and versions.

---

## G03 — Create a pinned verifier registry

Registry entries are deployment configuration, not proof-supplied data. Each entry binds:

```text
verifier ID
verification-key digest
statement schema
allowed algorithm profile
activation epoch
retirement epoch
```

A proof cannot select a new verifier implementation.

---

## G04 — Bind public inputs to ANF

The proof statement must include the exact roots required by the transition. Recompute public inputs from ANF values; do not trust a caller-provided public-input blob/root.

---

## G05 — Add substitution and freshness mutants

```text
proof from deployment A under B
old configuration under new state
retired verification key
foreign statement schema
foreign algorithm profile
expired proof
proof bound to state root of another transition
valid proof with caller-supplied public-input root
```

---

## G06 — Harden RISC0 and other verifier adapters

The adapter must receive typed context plus proof bytes, recompute journal/public inputs, verify against the pinned key, and return a controlled receipt. No free debt, free state, or caller journal roots.

---

## G07 — Add Lean/Tau schema theorem and exact-head review

Prove that equality of accepted proof contexts implies equality of every authority-bearing dimension. This is a schema theorem, not cryptographic soundness.

---

# Wave H — M6-R09 atomic publication and crash recovery

## H01 — Map the DRA publication atom to concrete tables

Create a field-to-column matrix. Every atom field must have exactly one canonical physical representation or one deterministic projection with a checked relation.

---

## H02 — Implement one database transaction

The transaction publishes together:

```text
successor state
authority header
history atom
nullifier
receipt
decision
bundle
replay data
outbox rows
ANF root
```

Use expected-root and authority-epoch CAS inside the transaction.

---

## H03 — Add deterministic crash points

Instrument at least:

```text
before BEGIN
after BEGIN
before CAS
after CAS check
between every logical insert/update
before COMMIT
after COMMIT before response
```

For storage-engine tests also exercise WAL/fsync boundaries where controllable.

---

## H04 — Reopen after every injected crash

For every crash point:

1. terminate the process/connection;
2. reopen with a fresh connection/process;
3. run canonical reopen;
4. compare to exact PRE and exact POST;
5. reject any third layout;
6. verify no external effect occurred without a committed outbox row.

---

## H05 — Test concurrent linearization

Combine commit, ack publication, migration, and checkpoint operations. Verify serializable outcomes against the reference state machine.

---

## H06 — Add WAL and durability configuration assertions

Record required SQLite/PostgreSQL settings. Tests must fail if production configuration weakens the assumed durability/transaction contract.

---

## H07 — Produce a concrete refinement report

For every abstract DRA action, name the SQL transaction, isolation assumptions, uniqueness constraint, recovery behavior, and test evidence.

---

## H08 — Independent exact-head review

Reviewer must attempt split-publication, stale-CAS, phantom/surplus row, and crash-mixture attacks. No mount before review approval.

---

# Wave I — M6-R10 outbox delivery and acknowledgment

## I01 — Freeze stable effect identity

Use the reviewed preimage:

```text
commit_id
ordinal
destination
payload_root
writer/authority profile root
```

Include deployment identity through the commit/authority roots. Ordinals are contiguous in canonical outbox order.

---

## I02 — Implement committed outbox rows

Rows are inserted in the same transaction as the publication atom. Required fields:

```text
effect_id
commit_id
ordinal
destination
payload bytes or canonical payload reference
payload_root
status
lease owner/expiry
attempt count
last error
ack receipt root
```

Operational fields must not alter semantic effect identity.

---

## I03 — Implement safe leasing

Workers claim rows atomically. Expired leases return to pending. Multiple workers may attempt the same effect, but all use the same `effect_id` and payload.

No worker may synthesize a new semantic ID after a timeout.

---

## I04 — Implement destination dedup adapters

Each adapter must support one of:

```text
native idempotency key with verified semantics
query-by-effect-ID before/after attempt
application-owned destination receipt table
```

If a destination cannot provide an acceptable dedup contract, the effect type is not mountable.

---

## I05 — Verify acknowledgment provenance

Ack subject must bind:

```text
effect_id
destination
payload_root
destination receipt bytes/root
adapter/verifier identity
```

Recompute the receipt subject root. Reject a merely well-shaped digest.

---

## I06 — Handle lost acknowledgments

Crash after destination acceptance and before local ack must lead to:

```text
same effect ID redelivery
-> destination ALREADY_ACCEPTED
-> same receipt or verified equivalent
-> one local durable ack
```

---

## I07 — Add outbox disaster matrix

```text
delivery before local commit
orphan outbox row
payload collision under same effect ID
foreign receipt ack
ack before delivery
lost lease
worker crash before send
worker crash after send
worker crash after ack write
migration during delivery
```

---

## I08 — State the honest contract

Documentation and API names must say:

```text
atomic enqueue
at-least-once attempts
stable idempotent semantic identity
provenance-bound acknowledgment
```

Do not claim network-level exactly-once unless the destination contract genuinely proves it.

---

# Wave J — M6-R11 migration and authority switch

## J01 — Implement the exact lifecycle enum

Only:

```text
LEGACY
SHADOW_REPLAY
DUAL_CHECK
QUIESCED
AUTHORITY_SWITCH
POST_SWITCH_VALIDATION
LEGACY_DISABLED
```

No skip, reverse, or ad hoc emergency state without a new reviewed protocol version.

---

## J02 — Enforce the writer matrix

```text
LEGACY / SHADOW_REPLAY / DUAL_CHECK -> legacy writer only
QUIESCED                            -> no value-moving writer
AUTHORITY_SWITCH and later          -> target writer only
```

Read/shadow computation is distinct from publication authority.

---

## J03 — Define evidence transport maps

For each artifact type state whether it is:

```text
preserved unchanged
recomputed under target profile
transported by a proved map
invalidated and regenerated
forbidden across the boundary
```

At minimum cover state, configuration, residual fee history, proof contexts, receipts, nullifiers, history, and outbox effects.

---

## J04 — Bind migration manifests to roots and sequence

Manifest fields:

```text
source profile/deployment/config roots
target profile/deployment/config roots
source state/history roots
target state/history roots
transport checker IDs and roots
activation sequence
rollback window and rules
quiescence evidence
complete replay evidence root
```

---

## J05 — Implement shadow replay and dual check

Shadow outputs have no authority. Dual check requires exact candidate/result equality or an explicitly reviewed refinement relation. Any mismatch blocks progression.

---

## J06 — Implement quiescence

Prove no writer can commit while final replay/current-head comparison occurs. Include API, CLI, background workers, admin, and direct adapters.

---

## J07 — Implement switch and stale-writer rejection

The authority epoch and writer profile are checked in the same commit transaction. A legacy writer holding an old token must fail after switch.

---

## J08 — Define rollback without history erasure

Rollback must restore a complete authorized history, configuration, residual state, nullifiers, and outbox identity. It may not restore balances alone.

---

## J09 — Migration ESSO/TLA/crash suite

Explore every phase with crashes, retries, stale tokens, old/new writers, pending outbox rows, and restart. Permanent mutants include skipped phase, dual writers, missing residual transport, and mixed V1/V2 evidence.

---

# Wave K — M6-R12 mounted no-bypass theorem

## K01 — Inventory every value-moving entrypoint

Produce a machine-readable inventory with:

```text
symbol/path
caller
input type
state/effect touched
required ANF/commit-port call
legacy status
runtime reachability evidence
```

Search API, CLI, admin, migration, recovery, verifier callbacks, workers, legacy code, and datastore adapters.

---

## K02 — Define the unique publication capability

Only one narrow commit-port capability may publish value-moving state. Core modules return values; they do not import database, network, filesystem, process, time, random, or logging side-effect adapters.

---

## K03 — Add static dependency/reachability checks

Fail CI if a value-moving module:

```text
imports a forbidden adapter
writes a protected table outside the commit port
calls a legacy publisher
constructs an authoritative receipt/bundle directly
bypasses ANF verification
```

Use AST and Rust syntax-aware tooling, not regex alone for final authority.

---

## K04 — Anchor the TCG publisher topology root

Derive topology from the inventory/build manifest and compare it to the externally pinned root. Added or removed publishers require a reviewed topology update.

---

## K05 — Add dynamic bypass mutants

For every entrypoint, mutate the verified commit call to:

```text
return success without commit
write state directly
write outbox directly
skip proof context
skip current-root CAS
use legacy writer
```

The integration suite must kill every mutant by semantic invariant or missing durable evidence.

---

## K06 — Seal legacy paths

After authority switch, legacy publisher symbols must be unreachable and preferably removed from production builds. Feature flags must be authenticated and covered by topology/inventory roots.

---

## K07 — Run a production-boundary audit

Audit actual deployment commands, containers, migrations, worker entrypoints, and database credentials. Source-level no-bypass is insufficient if a direct operational path can write protected tables.

---

## K08 — Prove the bounded mounted theorem

The final claim is:

```text
for every inventoried runtime entrypoint,
ValueMove(entry,input)
-> exists one verified ANF bundle consumed by the unique atomic commit port
```

State explicitly that completeness depends on the anchored inventory and deployment audit.

---

# Wave L — M6-R13 zUSD whole-system invariant

## L01 — Freeze authoritative economic quantities

Define exact stored quantities for:

```text
total zUSD debt
active debt
redistributed/defaulted debt
stability-pool debt offset
gas compensation debt
protocol fee liabilities
collateral backing by asset
oracle-valued backing
pending/unsettled liabilities
```

Do not derive the invariant from UI totals or optional indexes.

---

## L02 — State the whole-system invariant

Write one exact integer theorem with explicit scale and rounding. At minimum distinguish:

```text
nominal debt conservation
collateral quantity conservation
oracle-valued safety/solvency condition
freshness and authority of oracle observations
```

Do not combine quantity conservation and price-dependent solvency into one ambiguous number.

---

## L03 — Build the command effect matrix

Inventory every command that can change debt or backing:

```text
mint
burn
open/adjust/close position
liquidation
stability-pool offset
redistribution
settlement
funding
fee transfer
gas compensation
migration
recovery
administrative transition
```

For each command list exact preconditions, deltas, rounding, oracle reads, and outbox effects.

---

## L04 — Prove pure transition preservation

Each command theorem:

```text
ValidState(s)
+ AuthenticatedFreshContext(c)
+ Precondition(command,s,c)
+ step(s,command,c)=s'
-> ValidState(s')
```

Use integer arithmetic and explicit widths. Rejection leaves state unchanged.

---

## L05 — Enforce Oracle freshness and finalized authority

Every price-dependent path must require seen, positive, finalized, fresh observations bound to the execution context and current state. Recovery cannot silently use stale or pending Oracle data.

---

## L06 — Add cross-command composition and trace theorem

Prove the invariant over any finite accepted command trace. Include migration/recovery edges or explicitly show why they preserve/transport the invariant.

---

## L07 — Add Python/Rust differential vectors

Cover normal, boundary, rounding, partial stability-pool, gas compensation, liquidation, zero/maximum values, and stale Oracle cases.

---

## L08 — Connect to DRA and no-bypass

The economic theorem is meaningful only if every debt/backing change is inside the verified candidate and unique commit port. Add the economic root/delta certificate to ANF and the publication atom.

---

## L09 — Whole-system falsification audit

Attempt to find one debt-changing path absent from the matrix, one stale-oracle path, one overflow/rounding mismatch, one migration/recovery mismatch, and one direct-table bypass.

**R13 completion gate:** all command families proved/refined/mounted with no uncovered publisher.

---

# Wave M — Final integration and promotion

## M01 — Create one exact integration branch

Integrate all approved task heads. Produce a conflict and schema migration report. No squashing that destroys reviewed commit identities unless separately approved.

---

## M02 — Run complete assurance

Required minimum:

```text
all Python tests
Ruff and strict mypy
all Rust tests, fmt, Clippy -D warnings
Kani/SMT gates
all Lean roots and axiom audits
Julia independent oracles
ESSO/TLA bounded models
canonical vector parity
crash and concurrency suites
mutation suites
publisher inventory/no-bypass checker
```

Record exact versions and hashes.

---

## M03 — Perform independent exact-head reviews

At least separate reviewers for:

```text
allocator mathematics
lineage/authority composition
datastore/recovery
outbox/delivery
migration
no-bypass
zUSD economics
```

A reviewer must receive exact source manifests and falsification prompts, not only the PR description.

---

## M04 — Mount behind shadow mode

Shadow execution compares the mounted candidate with the legacy authority but cannot publish. Retain every divergence and complete input lineage.

---

## M05 — Enter dual check

Both implementations evaluate; only the authorized writer publishes. Exact or reviewed-refinement equality is required. No divergence suppression.

---

## M06 — Quiesce and switch authority

Follow J01-J09. Pin exact deployment/configuration/topology roots. Reject old tokens and writers.

---

## M07 — Post-switch validation

Reopen the actual datastore, replay history, validate nullifiers, redeliver pending effects idempotently, verify ANF roots, and run the production entrypoint audit.

---

## M08 — M6 promotion decision

M6 may be promoted only when every row below has explicit evidence:

```text
R01 canonical occurrence semantics       PROVED IMPLEMENTED MOUNTED TESTED
R02 adaptive allocator theorem           PROVED IMPLEMENTED MOUNTED TESTED
R03 entitlement identity/migration       PROVED IMPLEMENTED MOUNTED TESTED
R04 concrete authority composition       PROVED IMPLEMENTED MOUNTED TESTED
R05 nonce/retry concurrency              PROVED IMPLEMENTED MOUNTED TESTED
R06 complete evidence recomputation      PROVED IMPLEMENTED MOUNTED TESTED
R07 history/nullifiers/reopen            PROVED IMPLEMENTED MOUNTED TESTED
R08 proof-context binding                PROVED IMPLEMENTED MOUNTED TESTED
R09 atomic publication/recovery          PROVED IMPLEMENTED MOUNTED TESTED
R10 outbox delivery/ack                  PROVED IMPLEMENTED MOUNTED TESTED
R11 migration authority switch           PROVED IMPLEMENTED MOUNTED TESTED
R12 no-bypass                            PROVED IMPLEMENTED MOUNTED TESTED
R13 zUSD whole-system invariant          PROVED IMPLEMENTED MOUNTED TESTED
```

Use `NOT_APPLICABLE` only with an explicit theorem showing why the obligation does not apply. Never use `PASS` as a substitute for one of these four dimensions.

---

## 5. Tool routing for Luna

### LEAP

Use only when a counterexample shows the current representation is inadequate. Required output: SurprisePacket, proposed distinction, certificate language, smallest falsifier, and nonclaim.

### Morph

Use for exact reductions such as:

```text
SRGD deficit <-> AGQE surplus
physical durable rows <-> authorized history
runtime cyclic trace -> TCG quotient path
```

Every Morph card needs a reverse map or residual fiber and a list of lost information.

### ZAG

Use only when a mechanism candidate fails or multiple algorithms remain. Do not restart allocator search while SRGD satisfies the current theorem. Use ZAG for implementation schedules, recovery policies, or alternative data structures only against a frozen verifier.

### ESSO

Use for bounded stateful sequences:

```text
adaptive policies
concurrent nonces
crashes and retries
outbox loss/ack
migration phases
bypass mutants
```

Export exact bounds, explored-state count, transition count, and minimized witnesses.

### Lean

Use after the statement is frozen. Compile exact theorem roots, print axioms, and scan placeholders. Never hide runtime premises.

### Julia

Use as an independent discovery/oracle implementation. CI compares parsed results with the frozen Python result. Julia output does not grant authority.

### Research Kernel

For every task store:

```text
claim atom
dependency edges
counterexample/refutation attempts
evidence records with source paths/hashes
promotion status
next frontier
```

A claim remains `TESTABLE` or `PARTIALLY_SUPPORTED` until every required evidence class exists.

---

## 6. Luna preflight checklist copied into every prompt

```text
[ ] I fetched the exact named base SHA.
[ ] I verified a clean worktree.
[ ] I read the task's prerequisite reports and source manifests.
[ ] I identified the one principal claim.
[ ] I listed caller-controlled fields and removed authority-bearing ones.
[ ] I wrote the negative mutants before or with the implementation.
[ ] I used exact immutable types and bounded collections.
[ ] I kept abstract theorem, runtime refinement, and mounting claims separate.
[ ] I ran exact focused gates.
[ ] I left the final workflow read-only.
[ ] I recorded exact commands, versions, SHAs, evidence, and nonclaims.
```

---

## 7. Luna stopping rules

Stop the current task and report rather than improvising when:

```text
base head moved
schema meaning is ambiguous
two reviewed branches conflict semantically
proof statement is false
Lean requires an unreviewed new axiom
solver returns UNKNOWN or disagrees
a valid U256 input reaches unexplained overflow
publisher inventory cannot be derived completely
database crash yields a third authoritative layout
destination lacks a usable idempotency contract
migration requires erasing residual/history/nullifier state
zUSD command effect is not defined
```

Stopping one task does not mean stopping the program. Produce the smallest counterexample and route it back to the correct research lane.

---

## 8. Final output expected from Luna after the complete program

```text
1. exact final integration SHA;
2. PR and commit ledger;
3. 13-row M6 status matrix;
4. theorem receipt index;
5. Python/Rust/Julia parity report;
6. ESSO/TLA bounded-model report;
7. datastore crash/concurrency report;
8. outbox destination-contract report;
9. migration execution report;
10. publisher/no-bypass inventory and anchored topology root;
11. zUSD command coverage and invariant report;
12. all surviving nonclaims;
13. explicit PROMOTE_M6 or DO_NOT_PROMOTE_M6 decision.
```

The default decision is `DO_NOT_PROMOTE_M6`. Promotion must be earned by the complete evidence set.
