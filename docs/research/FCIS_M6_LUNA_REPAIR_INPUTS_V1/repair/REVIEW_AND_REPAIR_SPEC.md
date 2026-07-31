# FCIS M6 Durable Retraction Research Packet V1
## Independent Review and Luna Repair Specification

**Status:** revision required  
**Review verdict:** `REVISE_M6_DURABLE_RETRACTION_RESEARCH_PACKET_V1`  
**Review date:** 2026-07-31  
**Visibility:** repository-local  
**Runtime posture:** research-only, unmounted  
**Implementation authority:** repair this research packet only; do not mount it

## 1. Result

The durable-retraction idea is worth retaining. The reviewed packet supplies a
useful canonical-reopen model, retry classifier, PRE/POST publication model,
outbox identity model, migration phase machine, bounded Python exploration,
Julia parity, and an ESSO model.

The packet is not ready to carry its current authority or proof claims. Four
blocking defects must be repaired:

1. Reopen authorization is caller-mintable.
2. Destination acknowledgments can be forged without delivery.
3. Several untrusted boundary values escape closed typed rejection or are
   accepted under the wrong type.
4. The Lean file does not compile and models total reopen while the runtime
   relation is partial.

Exact-head delivery also remains incomplete. The intended remote branch still
points to the pre-packet base, the two supplied archives differ, and the
declared CI would fail on Lean, Ruff, and mypy.

## 2. Exact reviewed evidence

| Item | Reviewed result |
| --- | --- |
| Intended implementation base | `babffa56dcbddc5886487fbb6e62740b15370000` |
| Intended branch | `agent/fcis-m6-r05-r11-durable-retraction-20260731` |
| Branch state at review | Still equal to the intended base; no packet commit |
| TAR SHA-256 | `3d1ac7ed5d9404cc4b293a9707502e4e4d8d714498448501b4b878d7b8afcd70` |
| ZIP SHA-256 | `8e1c5cea2588682f84da2a9fe71f7e1b2bacd79143f1df12695d4542e81d9890` |
| ZIP integrity | Passed |
| ZIP internal manifest | 16/16 passed |
| Common ZIP/TAR files | Byte-identical |
| Python focused tests | 17 passed |
| Python bounded model | 49 states, 254 transitions, 7/7 original mutants killed |
| Julia/Python bounded parity | Exact parsed JSON equality |
| ESSO validation | Passed |
| ESSO multi-solver check | 15/15 inductive queries; Z3 and CVC5 agreed |
| Lean 4.27 | Failed to compile |
| Ruff | Failed |
| mypy | Failed with 40 errors |

Archive mismatch:

```text
ZIP only:
  README_BUNDLE.md
  SHA256SUMS.txt

TAR only:
  lean-mathlib/lakefile.lean
```

The replacement delivery must have one canonical, manifest-bound file set.

## 3. Claim level after review

Only these labels are justified:

```text
RESEARCH_HYPOTHESIS
PYTHON_REFERENCE_MODEL_TESTED
ESSO_INDUCTIVE_MODEL_VERIFIED_BOUNDED
PYTHON_JULIA_BOUNDED_PARITY
UNMOUNTED
```

The packet does not currently justify:

```text
PROVED_CONNECTIVE_MATH
AUTHENTICATED_REOPEN_AUTHORITY
PROVENANCE_VERIFIED_DESTINATION_ACK
PRODUCTION_DATASTORE_REFINEMENT
MOUNTED
M6_COMPLETE
```

## 4. Functional-core preflight

### Authority ownership

The deterministic core may decide:

```text
canonical durable reconstruction
fixed-point equality
retry classification
commit identity and fingerprint
effect identity
migration transition legality
typed accept or reject
```

The imperative shell must acquire and verify:

```text
external reopen authorization
store-current durable bytes
compare-and-swap currentness
destination delivery receipt
atomic datastore commit
actual external effect delivery
```

The core may consume an already verified, subject-bound witness. A
caller-supplied digest is not verified authority.

### State and ownership

Every persisted, hashed, compared, or receipt-bound value must be transitively
immutable and canonically encoded. Exact integer types are required where
Python Boolean values could masquerade as integers.

### Failure semantics

Expected malformed, stale, oversized, unauthenticated, or inconsistent inputs
must return a closed typed rejection. They must not:

```text
raise OverflowError or RecursionError
silently coerce a string into an enum
construct successor state
persist an acknowledgment
emit an outbox effect
grant reopen authority
```

### Commit and effect boundary

The research model remains:

```text
authenticated inputs
  -> deterministic candidate
  -> one atomic publication tuple
  -> durable PRE or complete POST
  -> idempotent delivery from committed outbox
  -> verified destination acknowledgment
```

The repair does not implement a production datastore or effect adapter.

## 5. Blocking repair obligations

### DR-AUTH-01: External reopen authority must be verifier-produced

Current defect:

```text
caller chooses external_authorization_root
  -> local code hashes it with the reopened head
  -> ReopenAuthorizationV1
```

This proves internal freshness binding. It does not prove the root came from an
authorized signer, quorum, deployment verifier, governance authority, or
authenticated service.

Required construction:

```text
ExternalHeadAuthorizationEvidenceV1
  -> authoritative verifier
  -> VerifiedExternalHeadAuthorizationV1

VerifiedExternalHeadAuthorizationV1
  + exact canonical reopened snapshot
  -> ReopenAuthorizationV1
```

The verified witness must bind at least:

```text
canonical durable snapshot root
current committed-state root
current authority-state root
authority epoch
deployment/configuration identity
verifier or signer-set identity
external authorization statement root
expiration or activation bounds when applicable
```

Mechanical guarantee:

```text
reopen token construction requires verifier-produced evidence
```

Explicit non-guarantee:

```text
the research packet does not prove the external verifier or signer set is
deployed, honest, current, or production-mounted
```

Permanent falsifier:

```text
Mallory supplies an arbitrary self-selected digest and asks the ordinary public
API to authorize the reopened head. Construction must fail before a controlled
token exists.
```

The ESSO action may assume a verified grant as an explicit environment input.
It must not model an unauthenticated `authorize_reopened_head` action as though
the state machine itself established external authority.

### DR-ACK-01: Destination acknowledgment must require verified delivery

Current defect:

```text
effect_id + destination + payload_root
  -> public deterministic destination_receipt_root
  -> caller-constructible DestinationReceiptV1
  -> durable acknowledgment
```

The root can be recomputed without contacting or verifying the destination.

Required construction:

```text
raw destination response
  -> destination-specific verifier adapter
  -> VerifiedDestinationReceiptV1
  -> acknowledge committed outbox row
```

The verified receipt must bind:

```text
effect identity
destination identity
payload root
raw or canonical destination receipt root
adapter/verifier profile identity
destination-specific idempotency identity
```

The core may recompute structural binding from the verified value. It must not
turn a well-shaped caller-supplied digest into proof of delivery.

Permanent falsifier:

```text
construct the expected hash locally without invoking delivery or a destination
verifier, then attempt acknowledgment. The operation must reject and leave the
durable snapshot byte-identical.
```

### DR-BOUND-01: Close range, type, and resource boundaries

Required bounds:

```text
OutboxRowV1.ordinal:
  exact int, not bool
  0 <= ordinal <= 2^32 - 1

all encoded fixed-width values:
  validate before serialization
  encode only after checked conversion

crash point:
  exact CrashPointV1 enum
  no string or integer aliases

Boolean protocol values:
  exact bool when a Boolean is required

durable tables:
  explicit maximum row counts and canonical byte budget
  bounds checked before full reconstruction, sorting, or hashing
```

Defense in depth:

```text
canonicalization and reopen catch host overflow exceptions and convert them to
a stable typed reject, while constructor checks remain the primary boundary
```

Permanent falsifiers:

```text
ordinal = 2^32
ordinal = 2^40
ordinal = True
crash_point = "BEFORE_LINEARIZATION"
oversized redundant receipt, bundle, history, nullifier, or outbox table
```

The string crash-point witness must not silently execute a normal commit.

### DR-LEAN-01: Formalize partial reopen faithfully

Current Lean model:

```text
reopen : D -> A
```

Runtime relation:

```text
reopen : D -> A | Reject
```

Required formal shape:

```text
reopen : D -> Except Reject A
```

An equivalent accepted-layout subtype is permitted if it preserves the same
partiality and rejection boundary.

Minimum theorem set:

1. `reopen (encode a) = Except.ok a`.
2. `encode` is injective under the left-inverse premise.
3. Successful normalization is idempotent.
4. A layout is authoritative only when reopen succeeds and canonical rewrite
   equals the exact durable layout.
5. Same-commit retry is an observational stutter under the declared identity
   relation.
6. Changed-head authorization invalidates the old subject-bound token.
7. Crash observation is exactly PRE or complete POST in the abstract model.
8. Effect replay with one stable effect identity is idempotent in the declared
   observation.

Acceptance:

```text
Lean 4.27 and pinned mathlib compile the exact file
no sorry
no admit
no user axiom
no unsafe
no sorryAx dependency
```

The theorem and runtime structure must share a written field-to-symbol mapping.

### DR-EVID-01: Make the packet exact and self-reproducing

Required:

```text
one exact implementation target commit
one exact packet commit with a declared parent
one canonical archive format or two byte-equivalent declared projections
status-aware change inventory including deletions
source manifest covering every load-bearing file
exact-head CI checkout
Ruff, mypy, Python, Julia, ESSO, and Lean gates
machine-readable result and explicit nonclaims
```

The workflow must add ESSO validation and strict multi-solver verification.

The implementation report must say `max_depth = 14`. A depth-seven statement
must be removed or scoped to the actual subset reached by depth seven.

The 105-task taskbook must state accurately that its graph targets R02-R13 and
program composition. If R01 is a prerequisite, represent it as an external
dependency or add explicit R01 tasks. Do not claim graph coverage that the JSON
does not encode.

## 6. Dependency-ordered Luna work

```text
L00 exact-source preflight
  -> L01 retain failing witnesses
  -> L02 repair reopen authority
  -> L03 repair destination acknowledgment
  -> L04 close types, widths, and resource bounds
  -> L05 repair and compile Lean
  -> L06 synchronize ESSO, Python, Julia, docs, ledger, and task graph
  -> L07 pass focused quality gates
  -> L08 create exact remote review packet
```

L02, L03, and L04 may be implemented independently after L01. L05 can proceed
in parallel with those code repairs. L06 waits for their final semantics.

## 7. Acceptance relation

The repaired research packet is acceptable only if all of these hold:

```text
SelfSelectedReopenRoot
  -> no verified reopen witness

UnverifiedDestinationDigest
  -> no durable acknowledgment

MalformedOrOversizedBoundaryInput
  -> closed typed rejection
  and durable state unchanged
  and effects empty

LeanBuild
  -> exact theorem file compiles without trust-expanding placeholders

PythonBoundedResult
  = JuliaBoundedResult

ESSOValidate
  and ESSOVerifyMulti(z3, cvc5)
  and no solver UNKNOWN or disagreement

ExactHeadCI
  -> all declared gates pass on the packet's exact source head
```

Positive boundary case:

```text
an externally verified, exact-subject reopen grant authorizes only its bound
canonical head and becomes stale after the head changes
```

Adversarial near-miss:

```text
a digest has the exact expected length and recomputes locally, but lacks an
authoritative verifier receipt; it remains untrusted
```

## 8. Forbidden outcomes

The repair must not:

```text
mount a datastore adapter
switch runtime authority
add a production command or API route
enable value movement
claim production recovery
claim destination idempotency without destination evidence
replace typed authority with a Boolean flag
weaken or delete existing negative evidence
edit frozen search output without running its generator and parity gates
change the SRGD/AGQE algorithm
begin R08, R12, or R13 implementation
merge the draft PR
```

No new dependency may be added without a determinism, security, license,
pinning, transitive-size, and removal analysis.

## 9. Required review packet

Luna's completion handoff must include:

```text
base commit and tree
implementation target commit and tree
packet commit and tree
remote branch and draft PR URL
status-aware change inventory
source manifest and its SHA-256
canonical archive and its SHA-256
toolchain versions
exact commands and results
minimized counterexamples retained
formal theorem dependency audit
explicit unrun commands and residual nonclaims
```

The packet must remain marked:

```text
UNMOUNTED
NO_PRODUCTION_AUTHORITY
REQUIRES_INDEPENDENT_EXACT_HEAD_REVIEW
```

## 10. Terminal condition

The Luna repair is complete when:

1. all four blocking defect families have retained failing witnesses that pass
   only after the repair;
2. the Python, Julia, ESSO, Lean, Ruff, and mypy gates pass;
3. public claims match the verified evidence;
4. one canonical manifest-bound archive is reproducible;
5. the exact implementation target and documentation-only packet child are
   pushed to a reviewable draft PR;
6. no runtime mount, production datastore, authority switch, or value-moving
   path exists in the diff.

