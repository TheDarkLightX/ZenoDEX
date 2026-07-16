# Spot V7 Highest-Observed Release-Event Watermark V1 CBC Specification

Status: authority-neutral protocol and deterministic checker implemented;
external monotonic backend and authority promotion are not implemented.

Date: 2026-07-15

## 1. Purpose

The local authenticated release-state store can replay its complete signed
history, but a same-UID process can restore an older internally valid database.
Comparing that restored head only with the latest finalized release checkpoint
does not preserve knowledge of a newer locally authenticated event whose release
finality is pending.

V1 defines one canonical highest-observed watermark projection and a
deterministic authority-neutral currentness assessment. The checker records the
safe response to this schedule:

```text
F1: release selection at database revision 1 is externally finalized
R2: terminal revocation at database revision 2 is authenticated locally
W2: an external monotonic registry durably observes exact R2
L1: the local Store V3 database is restored to valid pre-revocation state F1

assessment:
  relation    = LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_REVOCATION
  disposition = PAUSED
  blocker     = PENDING_REVOCATION_WATERMARK_UNAUTHENTICATED
```

The older finalized candidate is never selected as a fallback while W2 remains
the externally authenticated highest-observed event.

## 2. Authority progression

The implemented progression ends at an authority-neutral assessment:

```text
exact local checkpoint bytes
+ exact latest-finalized checkpoint bytes
+ exact highest-observed checkpoint bytes
+ exact raw watermark projection bytes
  -> bounded canonical decoding
  -> exact scope and Store identity equality
  -> finalized-to-observed adjacency
  -> exact watermark/checkpoint field binding
  -> deterministic local relation
  -> opaque authority-neutral PAUSED assessment
```

The raw watermark is untrusted. Its backend identity, position, block or record
commitment, parent commitment, and checkpoint fields are proposals until a
protocol-specific backend authenticates them.

No local SQLite row, path, copied file, report dictionary, nominal Python value,
or caller Boolean can establish external monotonicity.

## 3. Exact watermark bytes

`SpotV7HighestObservedReleaseEventWatermarkV1` contains exactly:

```text
schema
application_id
chain_id
domain_id
release_profile
store_identity_hash

external_backend_id
external_position
external_backend_commitment
external_parent_commitment

latest_finalized_checkpoint_hash
latest_finalized_database_revision

highest_observed_checkpoint_hash
highest_observed_database_revision
highest_observed_release_state_root
highest_observed_event_kind
highest_observed_select_input_id
highest_observed_revocation_record_id

watermark_hash
```

The accepted encoding is ASCII canonical JSON with sorted keys, no insignificant
whitespace, and exactly one trailing newline. Maximum encoded size is 16 KiB.
Maximum JSON nesting depth is two. Unknown fields, missing fields, duplicate or
escaped-duplicate keys, floats, nonfinite values, Booleans substituted for
integers, uppercase digests, and noncanonical bytes reject.

All digests are exactly 64 lowercase hexadecimal characters. All identifiers
are bounded ASCII tokens. All counters are non-Boolean unsigned 64-bit integers.

The watermark hash is:

```text
SHA256(
  domain_sep(
    "zrpf_spot_v7_highest_observed_release_event_watermark",
    version=1
  )
  || encode_bytes(canonical_json(watermark_without_watermark_hash))
)
```

The self-hash establishes byte identity only. It does not authenticate the
external backend or establish monotonic persistence.

## 4. Watermark shape

The watermark obeys these local relations:

```text
latest_finalized_database_revision
  <= highest_observed_database_revision

equal revisions
  -> equal finalized and highest-observed checkpoint hashes

external_position == 0
  <-> external_parent_commitment is zero
```

The highest-observed event shape is exact:

```text
GENESIS:
  highest_observed_database_revision == 0
  highest_observed_select_input_id is absent
  highest_observed_revocation_record_id is absent

SELECT:
  highest_observed_database_revision > 0
  highest_observed_select_input_id is present
  highest_observed_revocation_record_id is absent

REVOKE:
  highest_observed_database_revision > 0
  highest_observed_select_input_id is present
  highest_observed_revocation_record_id is present
```

These checks establish internal consistency. They do not establish that the
backend position exists, is final, is monotonic, or contains the claimed event.

## 5. Exact checker inputs

The checker accepts four keyword-only exact-byte inputs:

```text
exact_local_checkpoint_bytes
exact_finalized_checkpoint_bytes
exact_highest_observed_checkpoint_bytes
exact_watermark_bytes
```

It does not accept parsed checkpoint objects, mappings, backend objects,
`verified`, `authenticated`, or authority Booleans.

The names `finalized` and `highest_observed` identify protocol roles. This
checker does not authenticate either role. A finality adapter and monotonic
watermark adapter must independently verify the exact bytes before promotion.

All three checkpoints must have identical:

```text
application_id
chain_id
domain_id
release_profile
store_identity_hash
```

The watermark must bind the same scope and Store identity.

V1 deliberately supports only these finalized-to-observed shapes:

```text
highest observed == exact latest finalized checkpoint

or

highest observed == exact immediate successor of latest finalized checkpoint
```

The second case is checked with the canonical release-checkpoint successor
validator. A gap larger than one returns
`OBSERVED_FINALIZED_DISTANCE_UNSUPPORTED`. A later version may carry a complete
bounded intermediate checkpoint chain.

The watermark must equal the exact finalized and observed checkpoints for:

```text
latest finalized checkpoint hash and revision
highest observed checkpoint hash and revision
highest observed release-state root
highest observed event kind
highest observed SELECT input ID
highest observed revocation-record ID
```

## 6. Deterministic relation table

Every implemented result has disposition `PAUSED`.

| Condition | Relation | Blocker |
| --- | --- | --- |
| local revision is below finalized | `LOCAL_BEHIND_FINALIZED` | `LOCAL_RELEASE_STATE_ROLLBACK_OR_INCOMPLETE` |
| local equals finalized revision with different exact checkpoint | `LOCAL_FORK_AT_FINALIZED` | `LOCAL_RELEASE_STATE_FORK` |
| local equals finalized while a successor SELECT is observed | `LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_SELECTION` | `PENDING_SELECTION_WATERMARK_UNAUTHENTICATED` |
| local equals finalized while successor REVOKE is observed | `LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_REVOCATION` | `PENDING_REVOCATION_WATERMARK_UNAUTHENTICATED` |
| local equals observed revision with different exact checkpoint | `LOCAL_FORK_AT_HIGHEST_OBSERVED` | `LOCAL_RELEASE_STATE_FORK` |
| local revision exceeds highest observed | `LOCAL_AHEAD_OF_HIGHEST_OBSERVED` | `HIGHEST_OBSERVED_WATERMARK_STALE` |
| local equals genesis | `LOCAL_MATCHES_GENESIS` | `GENESIS_NOT_OPERATIONAL` |
| local equals an unrevoked finalized selection | `LOCAL_MATCHES_FINALIZED_SELECTION` | `EXTERNAL_WATERMARK_AND_FINALITY_AUTHENTICATION_REQUIRED` |
| local equals an unfinalized observed selection | `LOCAL_MATCHES_PENDING_SELECTION` | `PENDING_SELECTION_WATERMARK_UNAUTHENTICATED` |
| local equals an observed revocation | `LOCAL_MATCHES_REVOKED_HIGHEST_OBSERVED` | `REVOKED_RELEASE_WATERMARK_UNAUTHENTICATED` |

Even the matching finalized-selection case remains paused because this module
does not authenticate the raw watermark backend.

## 7. Exact assessment bytes

The private retained assessment commits exactly:

```text
schema
assessment_hash
disposition
relation
blocker_code

local_checkpoint_sha256
local_checkpoint_hash
local_database_revision
local_release_state_root

finalized_checkpoint_sha256
finalized_checkpoint_hash
finalized_database_revision

highest_observed_checkpoint_sha256
highest_observed_checkpoint_hash
highest_observed_database_revision
highest_observed_release_state_root
highest_observed_event_kind

watermark_sha256
watermark_hash
external_backend_id
external_position
external_backend_commitment

external_monotonicity_authenticated = false
external_finality_authenticated = false
store_derived_checkpoint_provenance_verified = false
rollback_safe_currentness_established = false
release_authority = false
runtime_authority = false
settlement_authority = false
production_authority = false
```

Its encoding is canonical JSON plus one trailing newline. `assessment_hash` is:

```text
SHA256(
  domain_sep(
    "zrpf_spot_v7_authority_neutral_release_currentness_assessment",
    version=1
  )
  || encode_bytes(canonical_json(assessment_without_assessment_hash))
)
```

The returned object has no public constructor, is final, immutable,
non-copyable, and non-serializable. Every data projection reparses retained
input bytes and rederives the assessment. Same-interpreter code remains outside
the authority threat model, and every authority property is fixed false even if
module-private objects are reached. Boolean conversion rejects so callers must
inspect the exact `PAUSED` disposition and typed blocker explicitly.

## 8. External monotonic backend obligation

Production rollback protection requires a concrete backend adapter that verifies
all of the following before minting a separate authenticated capability:

```text
the exact raw watermark bytes
the exact backend protocol and network
the external position and parent relation
the external block, record, or registry commitment
payload inclusion or exact state projection
backend signer or validator set and lifecycle
quorum signatures or consensus finality
fork-choice and rollback policy
strictly monotonic highest-observed revision
conflict rejection at one revision or position
durable retrieval of the observation
```

The external registry records observation of an authenticated release event.
This observation is distinct from finalizing that release for execution. It may
therefore durably remember pending R2 while F1 remains the latest release
checkpoint authorized by finality.

### Ordering requirement

Publishing W2 only after committing local R2 leaves a crash or rollback window.
The production protocol must use one of these equivalent constructions:

```text
external-first:
  authenticate and deterministically derive event/checkpoint R2
  -> durably reserve or append exact R2 in external monotonic registry
  -> commit local Store V3 R2
  -> reconcile exact local and external identities

or

atomic cross-domain protocol:
  prove equivalent linearization and crash semantics
```

If the external observation is present but local commit is absent, operation
remains paused as local rollback or incomplete recovery. If local state is newer
than the authenticated watermark, operation remains paused as stale external
observation. Uncertainty never falls back to F1.

A second local SQLite database, copied checkpoint file, local signature, or
same-host sidecar does not satisfy this obligation.

## 9. Required negative evidence

The focused V1 suite covers:

1. canonical round trip and a fixed hash vector;
2. the exact `F1 -> pending R2 -> restore L1 -> PAUSED` schedule;
3. local R2 before rollback remains paused;
4. matching F1 remains paused without backend authentication;
5. matching pending SELECT remains paused;
6. local rollback, fork, and stale-watermark relations;
7. unknown, missing, duplicate, escaped-duplicate, float, noncanonical, deep,
   oversized, and hash-substituted watermark bytes;
8. every checkpoint-binding field substitution;
9. unsupported finalized-to-observed distance;
10. absence of authority-Boolean ingress;
11. output immutability, copy and serialization rejection;
12. Boolean conversion rejection for the always-paused assessment;
13. same-interpreter field mutation invalidates every data projection while
    authority fields remain false.

Boundary mutation testing is bug-finding evidence. It is not proof that the
external backend is monotonic or correctly governed.

## 10. Explicit nonclaims

This V1 slice does not establish:

- authentication of any external backend;
- monotonicity or finality of `external_position`;
- correct external payload inclusion;
- observation-before-local-commit ordering;
- same-UID rollback or path-substitution resistance;
- release trust-root governance;
- current release authority;
- proof or runtime authority;
- settlement authority;
- production authority.

These facts remain false even when every V1 test passes.

## 11. Promotion boundary

A later authority-bearing currentness capability may be minted only after:

1. a reviewed protocol-specific backend authenticates the exact watermark
   bytes and its external monotonic position;
2. the observation-before-local-accept ordering obligation is implemented and
   crash-tested;
3. Store-derived checkpoint provenance and complete chain linkage are verified;
4. the final consumer rechecks the exact local head, authenticated watermark,
   nonrevoked candidate, and economic-state cursor in one authority-bearing
   transaction;
5. backend unavailability, ambiguity, fork, timeout, stale state, or replay
   produces a typed pause;
6. release, runtime, proof, DA, finality, and economic-state evidence are fresh
   under the final source and release closure;
7. independent security review approves the complete composition.
