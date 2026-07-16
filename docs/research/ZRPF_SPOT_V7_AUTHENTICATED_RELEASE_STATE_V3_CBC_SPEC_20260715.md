# ZRPF Spot V7 Authenticated Release State V3 CBC Specification

Status: proposed implementation contract, authority neutral

Date: 2026-07-15

## Scope

This specification defines one bounded SQLite state machine that durably records
authenticated Spot V7 release selections and authenticated release revocations.
It replaces neither release governance nor an externally finalized monotonic
release registry.

The accepted trust progression is:

```text
canonical candidate, selector, or revocation bytes
  -> exact quorum-signed envelope
  -> private authenticated SELECT or REVOKE capability
  -> complete cryptographic evidence replay
  -> exact durable event projection
  -> BEGIN IMMEDIATE transition and compare-and-swap
  -> authority-neutral durable release-state cursor
```

No mapping, report dictionary, path, Boolean, or caller-constructed facts object
may enter the durable commit boundary in place of the private authenticated
capability.

The commit status returned by the store is opaque, immutable, noncopyable, and
nonserializable. Normal construction requires a module-private store-result
seal. It exposes the typed disposition, stable code, event identity, and cursor;
it exposes no positive `authenticated=true` or
`durable_authenticated_release_state_recorded=true` Boolean. The status carries
the same false authority properties as the store and cursor. Boolean conversion
raises a typed error so committed, idempotent, and rejected results all require
explicit disposition handling. Attribute deletion, copying, deep copying, and
serialization reject.

## Positive claim

A successful V3 result may establish only this claim:

> Under one exact locally configured store identity, a quorum-authenticated
> release selection or revocation event was cryptographically replayed, matched
> the current durable cursor, and was appended exactly once to the local SQLite
> history, or the exact previously committed event was recognized
> idempotently.

## Explicit nonclaims

Every V3 identity, cursor, result, event, and error object must keep these facts
false:

```text
release_governed_trust_roots_authenticated
external_monotonic_state_anchor_verified
hostile_same_interpreter_resistance_established
same_uid_path_substitution_resistance_established
revocation_authority
release_authority
runtime_authority
settlement_authority
production_authority
```

An older internally valid database snapshot can be restored without detection.
The promotion blocker is:

```text
EXTERNAL_MONOTONIC_RELEASE_STATE_ANCHOR_REQUIRED
```

The intended future anchor is a chain-finalized or independently governed
release-registry state root. A second unanchored local sidecar is insufficient.

## Store identity

The immutable genesis identity must bind:

```text
application_id
chain_id
domain_id
release_profile

selection signer registry:
  registry_id
  registry_hash
  registry_revision
  activation_epoch
  revocation_epoch
  quorum_threshold
  derived_static_trust_pin_identity

revocation signer registry:
  registry_id
  registry_hash
  registry_revision
  activation_epoch
  revocation_epoch
  quorum_threshold
  derived_static_trust_pin_identity

rollback_policy_root
revocation_policy_root
revocation_registry_root
```

The selection and revocation payload kinds are distinct. Their signer-registry
hashes must therefore also be distinct.

The current authentication envelopes do not carry an externally issued
trust-pin provenance identity. V3 therefore derives each static identity from
one domain-separated canonical object containing only the immutable scope,
policy roots, signer-registry identity and lifecycle, payload kind, and quorum
threshold. Event cursor, candidate, evaluation-epoch, signature, and quorum
report fields are excluded. Changing any included field changes the derived
identity; changing only event fields does not.

This derivation detects disagreement with the locally configured static pins.
It does not authenticate who governed those pins. The property
`release_governed_trust_roots_authenticated` remains false until a later shared
authentication-envelope version carries independently governed provenance.

## Cursor

The cursor contains:

```text
database_revision
state_root
last_evaluation_epoch
current_candidate_id
current_candidate_sha256
current_release_revision
current_select_input_id
current_revoked
current_revocation_record_id
```

Genesis has revision zero, no current candidate, and no revocation. Every
non-genesis cursor has one complete current candidate. The revocation fields
must satisfy exactly one of:

```text
current_revoked = false and current_revocation_record_id = null
current_revoked = true  and current_revocation_record_id = 32-byte ID
```

## SELECT transition

A SELECT transition succeeds only when all of these hold:

1. The value is the exact sealed authenticated-selection capability.
2. Its durable projection is freshly revalidated from complete retained
   evidence, including the BLS quorum.
3. Its scope, policies, selection signer-registry tuple, and derived static
   trust-pin identity equal the store identity.
4. The selector CAS values equal the current database revision, candidate ID,
   and selection-input ID.
5. Evaluation epoch does not move backward.
6. The candidate is active and unexpired at evaluation.
7. Genesis selects release revision one with no parent.
8. A successor has revision `current + 1` and names the current candidate as
   parent.
9. The current head is not revoked.
10. The event limit and all integer bounds hold.

## REVOKE transition

A REVOKE transition succeeds only when all of these hold:

1. The value is the exact sealed authenticated-revocation capability.
2. Its durable projection is freshly revalidated from complete retained
   evidence, including the dedicated revocation BLS quorum.
3. Its scope, policies, revocation signer-registry tuple, and derived static
   trust-pin identity equal the store identity.
4. A current selected candidate exists and is not already revoked.
5. Selector and signed-envelope CAS values equal the current database revision,
   candidate ID, candidate SHA-256, release revision, and selection-input ID.
6. The exact candidate bytes revalidate to the current candidate identity.
7. The revocation record binds the same candidate, revocation policy, registry
   root, effective epoch, reason, issuer set, and record revision.
8. Evaluation epoch does not move backward.
9. Revocation effective epoch is no later than evaluation epoch.
10. The event limit and all integer bounds hold.

V3 revocation is terminal. A later SELECT requires a separately specified and
governed recovery profile. The V3 store does not invent implicit unrevocation.

## Exact replay and collision behavior

`selector_input_id` is globally unique across both event kinds.

When the exact selector already exists, every stored derived field and every
authentication-evidence byte must equal the submitted event. The result is an
idempotent exact replay. A same-ID mismatch is an integrity failure, never a
normal duplicate.

At minimum the schema also enforces:

```text
unique authentication_evidence_sha256
unique result_state_root
unique SELECT candidate_id
unique SELECT release_revision
unique REVOKE candidate_id
unique REVOKE release_revision
unique non-null revocation_record_id
```

## State-root construction

The genesis root binds schema version and the complete store-identity digest.
Each event root must domain-separate and commit:

```text
previous_state_root
event_revision
event_kind
selector_input_id
candidate_id
candidate_sha256
release_revision
evaluation_epoch
optional revocation_record_id
authentication_evidence_sha256
```

The state root authenticates local ordering and event identity. It does not
provide anti-rollback authority without an external monotonic anchor.

## Transaction and crash contract

Commit uses one SQLite `BEGIN IMMEDIATE` transaction:

```text
validate exact schema
cryptographically replay complete existing history
resolve exact replay if present
derive the next cursor
insert one event
compare-and-swap metadata on prior revision and state root
commit once
fsync the private parent directory
```

The database uses a private owner-only directory and file, DELETE journaling,
`synchronous=EXTRA`, strict tables, trusted schema disabled, and exactly one
hard link for the database file.

If an error occurs after commit begins, the store reopens the database and
cryptographically resolves the exact event. If neither success nor absence can
be established, it raises a typed durability-uncertain result. It must not
guess.

## Complete-history replay

Opening, reading, and committing revalidate every retained event from its
canonical authentication evidence. Replay must:

1. Reconstruct the exact external pins and raw artifacts.
2. Re-run the applicable SELECT or REVOKE quorum authentication.
3. Recompose and byte-compare the retained authenticated evidence.
4. Recheck the immutable store identity.
5. Reapply every transition from genesis.
6. Compare every previous and resulting root.
7. Compare the replayed cursor with metadata.
8. Require all authority columns to remain zero.

The Store-owned checkpoint projection returns the complete replayed cursor
sequence from genesis through the current head under one read transaction. A
checkpoint adapter must derive every parent from that sequence and must not
accept a caller-provided parent checkpoint.

V3 must reject a V2 database rather than reinterpret or silently migrate it.

## Required negative evidence

The focused suite must include:

```text
caller-constructed facts rejected
wrong private capability type rejected
selection and revocation cross-kind substitution rejected
wrong scope, policy, registry tuple, or derived static trust-pin identity rejected
event-only changes preserve the derived static trust-pin identity
scope, policy, registry lifecycle, payload kind, or threshold changes alter it
stale database revision rejected
stale evaluation epoch rejected
release revision gap, fork, and rollback rejected
revocation without a current head rejected
noncurrent candidate revocation rejected
second conflicting revocation rejected
selection after terminal revocation rejected
exact SELECT replay idempotent
exact REVOKE replay idempotent
two concurrent identical commits produce one event
two concurrent conflicting commits produce one winner
stored evidence mutation rejects on reopen
stored metadata or state-root mutation rejects on reopen
schema extension or authority-bit mutation rejects
symlink, non-private path, wrong owner/mode, and hard-link database reject
V2 database opening as V3 rejects
valid old-snapshot restoration leaves monotonic_state_anchor_verified false
post-commit fsync failure resolves exact outcome or raises typed uncertainty
committed, idempotent, and rejected results reject Boolean conversion
result attribute deletion, copying, and serialization reject
same-identity divergent Store history cannot substitute checkpoint ancestry
cold restart reconstructs the exact non-genesis checkpoint head
```

## Promotion boundary

Implementing and testing this store closes durable local authenticated
SELECT/REVOKE recording. Promotion to release authority additionally requires:

1. independently governed signer-registry and trust-pin sources;
2. a finalized monotonic release-state anchor;
3. current nonrevoked selection bound to the exact execution-authority
   manifest and opened component bytes;
4. finality, DA, runtime, proof, and economic-state checks;
5. one atomic authority-bearing application commit;
6. fresh final-source proof and runtime evidence;
7. operational qualification and independent security review.
