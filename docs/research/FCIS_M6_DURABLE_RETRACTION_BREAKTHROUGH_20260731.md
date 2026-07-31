# FCIS M6 Durable Retraction, Detectable Retry, and Retraction-Quotiented Authority

**Date:** 2026-07-31  
**Status:** `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`  
**Stacking base:** ZenoDEX PR #499, Tree–Chord–Gate authority certificates  
**Primary targets:** M6-R05, R06, R07, R09, R10, R11  
**Secondary targets:** M6-R04, R08, R12

## 1. Result

The previous M6 work supplied two strong static constructions:

1. Segmented Lineage Normal Form preserves transition boundaries and separates
   allocator-visible arithmetic from exact witness provenance.
2. Tree–Chord–Gate certificates make declared authority paths coherent and force
   every declared path through a fixed gate filtration.

The remaining production sequence is stateful. Commit, crash, retry, reopen,
outbox delivery, acknowledgment, and migration introduce loops and persistent
state. A finite authority DAG alone cannot state what those loops are allowed to
do.

This checkpoint introduces three connected abstractions:

```text
Canonical Durable Retraction (CDR)
  exact authorized history <-> canonical durable layout

Detectable Commit Fiber (DCF)
  durable outcome is separated from client transport knowledge

Retraction-Quotiented Authority Graph (RQAG)
  verified retry/reopen/dedup loops collapse to identity before TCG checking
```

The combined profile is called the **Durable Retraction Algebra (DRA)**.

Its strongest new reduction is:

```text
encode : AuthorizedHistory -> DurableLayout
reopen : DurableLayout -> Except Reject AuthorizedHistory

reopen(encode(h)) = h

N = encode o reopen

Authoritative(d)  iff  N(d) = d
```

A datastore is not accepted because selected roots match. It is accepted only if
fresh reopen reconstructs the complete authorized history and canonical
re-encoding reproduces the entire durable layout exactly.

This turns the following attacks into one fixed-point failure:

```text
missing row
surplus row
duplicate row
wrong canonical order
foreign receipt
crossed decision/bundle
orphan nullifier
orphan transition
orphan outbox row
ack without a committed effect
state root copied from another transition
```

## 2. Mathematical construction

### 2.1 Authorized histories and durable layouts

Let:

```text
A = type of exact authorized histories
D = type of durable layouts
```

A history in `A` contains all authority-bearing facts needed to reconstruct the
current state:

```text
genesis authority
ordered publication atoms
authority epochs
command identities
pre/post state roots
nonce/nullifier consumption
decisions
receipts
bundles
replay sources
outbox effects
delivery acknowledgments
```

A durable layout in `D` is the concrete relational representation:

```text
current-state header
publication rows
evidence rows
nullifier rows
outbox rows
acknowledgment rows
authority-epoch rows
```

The canonical encoder materializes every required table from one history. The
reopen function parses and validates every table, reconstructs one history, and
rejects any ambiguity or mismatch.

### 2.2 Retraction law

The essential theorem is:

```text
reopen(encode(a)) = a
```

Therefore `encode` is injective. Two different authorized histories cannot share
one canonical durable layout.

Define:

```text
N(d) = encode(reopen(d))
```

Then:

```text
N(N(d)) = N(d)
```

and:

```text
N(d) = d
  iff
exists a, encode(a) = d
```

The authoritative durable states are exactly the fixed points of `N`.

This is stronger and simpler than accumulating many local positive checks. Local
checks remain useful for precise rejection codes, but the final authority gate is
exact fixed-point equality.

### 2.3 Why this solves complete evidence recomputation

Suppose a verifier checks only a selected digest or selected subset of rows. An
attacker may add a valid-looking surplus row, omit an unselected row, or attach a
correct digest to the wrong transition.

Under CDR, `reopen` must reconstruct the complete history and `encode` must emit
exactly the authoritative rows. Any extra or missing row changes the layout and
violates:

```text
encode(reopen(d)) = d
```

M6-R06 therefore reduces to:

```text
1. one closed authorized-history schema;
2. one canonical encoder;
3. one totalized fail-closed reopen API returning a partial relation;
4. exact fixed-point equality;
5. implementation refinement for the concrete datastore.
```

The first four now have an executable research model. The fifth remains a
production adapter obligation.

## 3. Publication atoms

One accepted value-moving transition is represented by a publication atom:

```text
PublicationAtom =
  sequence
  commit_id
  command_root
  expected_pre_root
  post_state_root
  authority_epoch
  writer_profile_root
  nullifier_root
  response_root
  receipt_root
  decision_root
  bundle_root
  replay_root
  deployment_config_root
  verifier_profile_root
  ordered outbox tuple
```

The atom is indivisible at the authoritative layer.

The physical database may temporarily contain journal, WAL, lock, shadow-page,
or uncommitted transaction state. Those representations are not authoritative.
After database recovery, the exposed canonical snapshot must be exactly:

```text
PRE
or
POST = encode(append(reopen(PRE), atom))
```

No third authoritative mixture is legal.

## 4. Detectable Commit Fiber

### 4.1 Separate durable outcome from client knowledge

“Indeterminate” is not a durable commit result. It is a statement about what a
client learned after a transport failure.

Durable outcomes are:

```text
NEWLY_COMMITTED
ALREADY_COMMITTED
STALE_STATE
DEFINITE_REJECTION
```

The transport observation may instead be:

```text
known durable outcome
or
INDETERMINATE
```

A fresh canonical reopen resolves an indeterminate observation.

### 4.2 Stable identities

Every commit carries:

```text
commit_id
commit_fingerprint
nullifier_root
expected_pre_root
response_root
```

The fingerprint binds the entire publication atom, including outbox identity and
authority epoch.

Given canonical history `h` and request `q`, retry classification is:

```text
commit_id exists with same fingerprint
  -> ALREADY_COMMITTED(original response)

commit_id exists with different fingerprint
  -> DEFINITE_REJECTION(identity collision)

nullifier exists under a different commit
  -> DEFINITE_REJECTION(replay/collision)

commit absent and expected_pre_root != current_root
  -> STALE_STATE

commit absent, current root matches, writer is authorized
  -> ABSENT_RETRYABLE

The client may still observe `INDETERMINATE` after a crash or lost response.
That epistemic observation is kept in a separate type and never persisted as the
durable resolution.
```

An absent retryable request can execute the same atomic commit attempt. If an
earlier indeterminate attempt committed, the durable index returns
`ALREADY_COMMITTED`; if it did not, the new attempt may return
`NEWLY_COMMITTED`.

### 4.3 Nonce concurrency theorem

For a sender/nonce nullifier `nu`, canonical history requires at most one mapping:

```text
nu -> (commit_id, fingerprint)
```

Two concurrent different commands with the same `nu` cannot both extend one
canonical history:

```text
first commit wins the CAS and installs nu
second commit observes either:
  commit identity equality -> ALREADY_COMMITTED
  nullifier collision       -> DEFINITE_REJECTION
  changed current root      -> STALE_STATE
```

This is the abstract M6-R05 solution. The concrete datastore must refine the
single atomic index/state update.

## 5. Reopen authorization latch

Canonical recovery is evidence, not permission to resume value movement. A
restarted shell enters a locked state until an external authority binds a fresh
head token to:

```text
snapshot_root
current_state_root
authority_state_root
  deployment_config_root
  verifier_profile_root
  external_statement_root
  activation/expiration bounds
  verifier evidence root
```

The token is accepted only after full canonical reopen. Commit, acknowledgment
publication, and migration require an exact token for the current snapshot. A
successful state-changing operation changes the snapshot root and therefore
invalidates the old token automatically.

This closes the abstract form of the R07 falsifier:

```text
reopened state accepts a value-moving command before reauthorization
```

The implementation separates raw external evidence from the authority boundary:

```text
ExternalHeadAuthorizationEvidenceV1
  -> shell-owned verifier adapter
  -> VerifiedExternalHeadAuthorizationV1
  -> ReopenAuthorizationV1
```

Every authority-bearing operation freshly invokes the shell-selected verifier
against the exact current subject. The core independently checks subject,
epoch, deployment, verifier profile, statement, and freshness bindings. No
accepting verifier or importable authority-minting token ships in the production
source. A sound production signature, quorum, deployment trust root, and proof
context remain explicit shell premises and nonclaims.

## 6. Authorized history and reopen

A canonical history is a strict chain:

```text
genesis_root = atom[0].expected_pre_root
atom[i].post_state_root = atom[i+1].expected_pre_root
```

It additionally requires:

```text
unique commit identities
unique nullifiers
unique effect identities
contiguous transition sequence
nondecreasing authority epochs
one exact evidence row of every required kind per atom
one outbox row per exact effect
acknowledgment references one committed exact effect
current_state_root = last post root, or genesis for empty history
```

Reopen performs complete reconstruction, not header trust:

```text
raw durable rows
  -> exact type and bound admission
  -> canonical row order
  -> complete table equality against publication atoms
  -> strict state-chain replay
  -> nullifier and effect uniqueness
  -> authority-epoch replay
  -> acknowledgment ancestry
  -> canonical re-encoding
  -> exact whole-layout equality
```

This supplies an abstract solution to M6-R07. Production promotion still requires
an authenticated genesis, a concrete database schema, history truncation rules,
and reauthorization before post-reopen value movement.

## 7. Outbox and acknowledgment

### 7.1 Effect identity

Each effect identity is derived from:

```text
effect_id = H(
  commit_id,
  ordinal,
  destination,
  payload_root,
  writer_profile_root
)
```

`adapter_profile_root` is deliberately absent from this derivation. Adapter
provenance remains in the outbox and acknowledgment rows, so profile rotation
does not create a second semantic effect identity.

The complete ordered outbox tuple is inside the publication atom. Therefore:

```text
external effect
  -> committed canonical outbox ancestor
```

### 7.2 Realistic delivery contract

Without one transaction spanning the local datastore and the external
destination, the shell should claim:

```text
atomic local enqueue
+ at-least-once transport attempts
+ destination idempotence by effect_id
+ payload collision rejection
+ provenance-bound acknowledgment
```

It should not claim network-level exactly-once delivery.

### 7.3 Lost acknowledgment

If the destination accepts an effect and the acknowledgment is lost:

```text
retry uses the same effect_id
same payload -> ALREADY_ACCEPTED
foreign payload under same id -> PAYLOAD_COLLISION
```

A durable acknowledgment consumes a controlled destination-verifier receipt that
binds:

```text
effect_id
destination
payload_root
  destination_receipt_root
  adapter_profile_root
  idempotency_root
  response_root
```

An unrelated receipt, a locally recomputed structural digest, or a raw response
cannot acknowledge the effect.

This supplies the abstract M6-R10 solution. Concrete destination deduplication
and acknowledgment durability remain adapter-specific refinement obligations.

## 8. Migration authority atlas

The exact lifecycle is retained:

```text
LEGACY
-> SHADOW_REPLAY
-> DUAL_CHECK
-> QUIESCED
-> AUTHORITY_SWITCH
-> POST_SWITCH_VALIDATION
-> LEGACY_DISABLED
```

The research model represents every phase as an authority epoch with:

```text
epoch_index
legacy_profile_root
target_profile_root
  active_profile_root
  allowed_writer_roots
  transport_root
  predecessor-bound transition_root
```

The legacy and target writer roots must be distinct. Every non-genesis
`transition_root` hashes the predecessor authority root, the next lifecycle
phase, the active/allowed writer set, and the exact transport root. Migration
therefore cannot substitute an unbound transport or silently reset authority.

Rules:

```text
LEGACY / SHADOW_REPLAY / DUAL_CHECK
  active writer = legacy only

QUIESCED
  active writers = none

AUTHORITY_SWITCH / POST_SWITCH_VALIDATION / LEGACY_DISABLED
  active writer = target only
```

Publication atoms retain their contemporaneous epoch identity. Migration appends
a new epoch without rewriting historical atoms, nullifiers, receipts, or outbox
identity.

An old writer after switch is rejected even if it possesses previously valid
receipts.

The `transport_root` is an equality target for the exact evidence-transport
certificate. This checkpoint does not yet define the complete profile-specific
transport payload; Luna must implement that in the concrete migration packet.

## 9. Retraction-Quotiented Authority Graph

Tree–Chord–Gate currently operates on a finite authority DAG. Runtime execution
adds cycles:

```text
retry same commit
reopen canonical snapshot
redeliver same effect identity
repeat defensive verification
```

The correct extension is not to turn every loop into a new authority path. A loop
may be collapsed only when it is an observational identity on canonical values:

```text
StutterIdentity(f) := forall a in Canonical, f(a) = a
```

Examples:

```text
reopen/encode normalization on a canonical snapshot
same-commit retry returning the retained response
same-effect redelivery to an idempotent destination
repeated verification of the same fixed evidence
```

After deleting verified stutter loops, the remaining path must map to the TCG
authority DAG. TCG path coherence then applies to the quotient path.

This is the **Retraction-Quotiented Authority Graph**:

```text
runtime cyclic graph
  / verified canonical stutters
  -> finite TCG authority DAG
```

Non-idempotent actions such as a new commit, acknowledgment publication, or
migration phase change are not collapsed. They remain theorem-bearing edges.

This construction connects static R04 composition to stateful R05–R11 behavior.

## 10. Executable evidence

### 10.1 Python reference

`src/core/fcis_durable_retraction.py` implements:

```text
exact immutable authority epochs
publication atoms
canonical history
redundant durable row layout
encode/reopen/fixed-point normalization
retry classifier
PRE/POST crash reference
nonce/nullifier collision handling
stable outbox identities
destination deduplication
provenance-bound acknowledgments
fresh reopen-head authorization
migration writer switching
```

### 10.2 Focused tests

The focused suite checks:

```text
encode/reopen left inverse
normalization idempotence
missing evidence
surplus evidence
duplicate evidence
reordered evidence
crossed evidence
corrupt snapshot root
same-commit retry
commit-id collision
same-nullifier concurrency
PRE/POST crash refinement
no effect without outbox
lost-ack idempotence
crossed destination receipt
forged destination receipt root
reopen-without-reauthorization rejection
phase-skip rejection
history-preserving migration
old writer rejection after switch
quiesced no-writer phase
Boolean/integer alias rejection
```

### 10.3 Independent finite search

The bounded search explores all safe states through depth fourteen and freezes:

```text
49 reachable safe states
254 safe transitions
7 minimized mutant witnesses

The Python semantic suite contains 44 focused tests, including permanent
verifier-at-use, destination-adapter, context-binding, migration-transition,
type-width, resource-bound, Lean-shape, and bounded-model-premise witnesses.
```

Mutants killed:

```text
split publication
orphan delivery
orphan acknowledgment
same-nonce double commit
old writer after switch
publication without fresh reopened-head authorization
selected-root reopen with missing receipt
```

### 10.4 Julia oracle

A Base-only Julia model independently performs the same state exploration and
mutant minimization. CI compares parsed Julia output with the frozen Python JSON.

### 10.5 Lean theorems

`FCISDurableRetraction.lean` proves:

```text
encode injectivity
normalize(encode(a)) = encode(a)
normalization idempotence
fixed points equal the encoder range
fixed-point extensionality
stored retry classification laws
transport/durable-state separation
stale head-authorization invalidation
PRE-or-POST crash view
composition and iteration of stutter identities
idempotent duplicate effect acceptance
```

These are connective theorems under explicit premises. They do not prove a
particular database or destination satisfies those premises.

### 10.6 Public model replay and optional ESSO evidence

The ESSO-IR model represents:

```text
atomic publication bits
retry and crash stutters
committed-only delivery
acknowledgment ancestry
exact migration lifecycle
  legacy / none / target writer modes
```

The authorization transition requires a singleton
`VERIFIED_EXTERNAL_GRANT` environment premise and the acknowledgment transition
requires a singleton `VERIFIED_DESTINATION_RECEIPT` premise. These are explicit
verifier premises in the model, not runtime authority. The checked-in public
model checker exhaustively replays 56 reachable states and 268 enabled
transitions, validates 10 invariants across 14 actions, and kills four semantic
self-test mutants. Historical local execution at private ESSO commit
`ef5b06cb7dbed9e8a78d27e9918550ee591e42eb` passed validation and 15/15
inductive queries with Z3 and CVC5 agreement. Private ESSO is optional evidence
and is not required by public CI. Neither bounded result establishes external
signer or destination trust.

## 11. Relation to established work

This construction intentionally builds on known ideas rather than claiming that
retractions, durable linearizability, detectability, idempotence, redo recovery,
or state-machine migration are new.

Relevant foundations include:

- Izraelevitz, Mendes, and Scott, *Linearizability of Persistent Memory Objects
  Under a Full-System-Crash Failure Model*, DISC 2016.
- Attiya, Ben-Baruch, Fatourou, Hendler, and Kosmas, *Detectable Recovery of
  Lock-Free Data Structures*, PPoPP 2022.
- Cho, Jeon, and Kang, *Practical Detectability for Persistent Lock-Free Data
  Structures*, 2022.
- Ramalingam and Vaswani, *Fault Tolerance via Idempotence*, POPL 2013.
- Mukherjee et al., *Reliable State Machines: A Framework for Programming
  Reliable Cloud Services*, ECOOP 2019.
- Lomet and Tuttle, *A Theory of Redo Recovery*, SIGMOD 2003.
- Lorch et al., *The SMART Way to Migrate Replicated Stateful Services*,
  EuroSys 2006.
- Malkhi, *Virtually Synchronous Methodology for Dynamic Service Replication*,
  2010.

The narrower candidate contribution is the FCIS combination:

```text
canonical durable fixed points
+ detectability separated from transport knowledge
+ lineage-complete publication atoms
+ TCG authority paths quotiented by verified stutter retractions
```

Novelty remains a claim to falsify.

## 12. M6 status after this checkpoint

### Abstractly resolved or materially reduced

```text
R05 nonce/replay concurrency
  reduced to atomic commit-id/nullifier index plus total retry classifier

R06 complete evidence recomputation
  reduced to canonical durable fixed-point equality

R07 history/nullifiers/reopen
  reduced to strict canonical history replay, retraction law, and a fresh
  reopened-head authorization latch

R09 atomic publication/crash
  reduced to concrete datastore refinement of PRE-or-POST publication atom

R10 outbox delivery
  reduced to atomic enqueue, stable effect identity, destination dedup, bound ack

R11 migration switch
  reduced to exact authority epochs, no-writer quiescence, one active writer
```

### Still open before mounting

```text
concrete SQLite/PostgreSQL schema and transaction refinement
real WAL/crash fault injection
production current-head CAS
full authenticated genesis and configuration authority
profile-specific migration evidence transport
route per-leg protocol-fee provenance
source-derived SLNF roots inside production candidate/receipt/bundle schemas
Rust/Python root parity
real destination idempotency adapters
outbox leasing and acknowledgment recovery
complete publisher inventory and no-bypass audit
whole-system zUSD debt/backing closure
```

## 13. Promotion rule

This checkpoint may be labeled, with `PROVED_CONNECTIVE_MATH` scoped only to the
exact Lean theorem layer:

```text
RESEARCH_HYPOTHESIS
PROVED_CONNECTIVE_MATH
PYTHON_REFERENCE_MODEL_TESTED
ESSO_INDUCTIVE_MODEL_VERIFIED_BOUNDED_HISTORICAL
PUBLIC_FINITE_MODEL_REPLAYED_BOUNDED
PYTHON_JULIA_BOUNDED_PARITY
UNMOUNTED
```

It must not be labeled:

```text
production atomicity proved
production exactly-once proved
migration mounted
no-bypass proved
M6 complete
```

The next safe engineering target is a concrete datastore adapter whose recovered
layouts are checked against this fixed-point model at every injected crash point.
