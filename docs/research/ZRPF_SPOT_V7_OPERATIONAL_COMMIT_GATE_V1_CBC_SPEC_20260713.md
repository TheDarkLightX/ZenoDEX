# ZRPF Spot V7 Operational Commit Gate V1/V2 CBC Specification

Date: 2026-07-14

Status: authority-false V2 commit capability, combined atomic sink, exact
manifest-pinned `full_blob_da_v1` Rust checker adapter, and bounded
policy-pinned ZenoLedger BLS checkpoint adapter implemented; an exact canonical
BLS-quorum operational-policy verifier and private-handoff-gated mint adapter
are implemented, while the independently governed mint for that release-pin
handoff, canonical ZenoLedger finality authority, settlement authority, and
production authority remain unavailable

## Purpose

Spot V7 receipt authentication, local full-blob checking, checkpoint-finality
policy checking, and atomic economic storage are separate authority surfaces.
None can substitute for another.

The required operational progression is:

```text
governed V7 receipt and exact Firecracker execution
  -> private governed Spot V7 settlement facts

governed LocalFullBlobPolicyV1
  + exact FullBlobDataAvailabilityCertificateV1 and blob bytes
  -> exact policy satisfaction
  -> same-transaction blob and certificate persistence plan

protocol-specific authenticated external-finality evidence
  + governed CheckpointFinalityPolicyV2
  + rollback-resistant prior checkpoint cursor
  -> exact CheckedCheckpointFinalityTransitionV2
  -> authenticated checkpoint-finality transition

all three exact capabilities
  + governed operational policy identity
  + cross-binding checks
  + one combined durable transaction
  -> future atomic economic commit capability
```

The present implementation exercises the combined durable transaction through
both an explicitly test-only packet and
`_SpotV7AtomicEconomicCommitCapabilityV2`. The V2 type accepts only four exact
module-sealed prerequisite objects, retains those objects, and deterministically
reconstructs the permanently authority-false schema packet. The exact DA
prerequisite has a bounded Rust-checker adapter. A governed ZenoLedger adapter
mints the exact checkpoint-finality prerequisite only after cryptographic
quorum, canonical scheduled-header admission, header `app_hash` recomputation,
and the scoped candidate bindings below. This remains a bounded,
authority-false checkpoint result. The policy mint now requires canonical
manifest bytes, a private authenticated release-pin and evaluation-epoch
handoff, active policy and registry revisions, and a verified BLS quorum. No
production path mints that private handoff in this tranche. The Firecracker
settlement mint path also remains absent, so raw caller data cannot reach the
combined binder.

## Existing primitives and their limits

`full_blob_da_v1` validates one complete local blob against a content
certificate and governed policy parameters. Its successful result establishes
only that the exact bytes satisfied that local check in that invocation. It
does not authenticate policy governance, prove future retention, or persist the
bytes.

`checkpoint_finality_v2` checks exact certificate, policy, supplied binding,
and linear application-checkpoint continuity. Its opaque checked result remains
proof-neutral. It does not authenticate external consensus evidence or prove
that the prior cursor came from rollback-resistant durable state.

Spot V7 atomic-store schema revision two has an authority-false operational
profile. One `BEGIN IMMEDIATE` transaction persists:

```text
V7 settlement and exact artifacts
economic cell transitions and replay identities
exact full blob and canonical full_blob_da_v1 certificate bytes
DA roots, policy root, check epoch, and retention horizon
canonical checkpoint_finality_v2 certificate bytes
exact finality-evidence bytes and their digest
prior and next application-checkpoint cursor
economic-state cursor and checkpoint-finality cursor CAS updates
```

Every authority column remains constrained to zero. The external-finality and
provider-retrievability columns also remain constrained to zero.

Schema revision two has no implicit migration path. A revision-one database,
missing operational table, or mismatched schema SQL fails closed on open. An
operator must use a separately reviewed offline migration or rebuild from
canonical history before adopting revision two.

## Process-local prerequisite types

`_zrpf_spot_v7_operational_gate.py` defines private, non-copyable contracts for:

```text
_GovernedSpotV7OperationalPolicyV1
_GovernedLocalFullBlobPolicySatisfactionV1
_AuthenticatedCheckpointFinalityTransitionV2
_SpotV7AtomicEconomicCommitCapabilityV1
```

`_zrpf_spot_v7_operational_capability_v2.py` adds:

```text
_GovernedOperationalPolicyMaterialV2
_GovernedSpotV7OperationalPolicyV2
_GovernedExactFullBlobPolicySatisfactionV2
_AuthenticatedExactCheckpointFinalityTransitionV2
_SpotV7AtomicEconomicCommitCapabilityV2
```

The V1 capability still has no mint path. The V2 binder mints only the
authority-false V2 packet and only from all four exact sealed prerequisites.
`load_governed_spot_v7_operational_policy_v2` is the only production constructor
of `_GovernedSpotV7OperationalPolicyV2`. It checks exact canonical policy
material, application/domain scope, policy and signer-registry revisions,
activation and revocation epochs, the manifest and registry hashes carried by
an exact private authenticated release handoff, and a BLS quorum over the exact
manifest payload hash before using the private policy seal. No acceptance or
authority Boolean is an input. The private handoff has no production mint yet.
`PinnedFullBlobDataAvailabilityCheckerV1` now accepts only an already-sealed V2
policy capability plus exact certificate/blob bytes and explicit epochs. It
executes the manifest-pinned static Rust checker under the shared bounded
pre-exec process contract. The fixed response binds the complete request,
policy root, exact artifact hashes, content roots, and retention horizon before
the adapter constructs `_GovernedExactFullBlobPolicySatisfactionV2`.

The DA capability retains the identical governed policy object and exact
certificate/blob bytes. Substituting a separately sealed policy object is
therefore rejected by the combined V2 binder even when a caller can construct
similar-looking fields. Raw mappings, reports, and acceptance Booleans cannot
stand in for the governed policy or checker result. These are Python
information-hiding boundaries, not protection against hostile code already
executing in the same interpreter.

The ZenoLedger finality adapter authenticates BLS checkpoint signatures against
the exact registry hash pinned by the sealed operational policy. It enforces strict
greater-than-two-thirds active-weight quorum intersection. The checkpoint
signer-registry root remains distinct from the header's validator-set root. The
adapter invokes canonical scheduled-header admission for that validator set,
recomputes `app_hash`, reconstructs the canonical `checkpoint_finality_v2`
certificate through the source-bound Python parity implementation, and binds
the proposed prior cursor. The combined store still performs the durable
prior-cursor compare-and-swap. Direct execution of the Rust policy checker,
canonical body replay and fork choice, validator-set release governance, and
proposer-authorship evidence remain open. Caller booleans, quorum reports, and
certificate bytes never mint either capability.

Separate types whose names begin with `_TestOnly` exercise the completed
storage mechanics. They recompute the Rust-compatible roots and canonical
fixed-field Postcard certificate bytes before entering SQLite. They cannot be
used as governed or production capabilities and report both settlement and
production authority as false.

## Required cross-bindings

Before any future commit capability can be minted, the gate compares the
private facts directly.

The governed operational policy must match the V7 application and domain.

The DA result must match:

```text
application_id
chain_or_domain_id
epoch_id
data_availability_certificate_root
data_root
governed full_blob_da_v1 policy_root
```

The authenticated finality result must match:

```text
application_id
chain_or_domain_id
epoch_id
SHA-256 of the exact receipt-authenticated V7 journal bytes
economic post_state_root
governed checkpoint_finality_v2 policy_root
```

The local finality capability also requires an exact-successor application
checkpoint sequence. Schema revision two durably compares and swaps the exact
prior cursor in the same transaction as economics, replay rows, blob bytes,
certificates, and the next cursor.

Structure-preserving substitution of any shared application, domain, epoch,
certificate root, data root, policy root, journal hash, or post-state root
rejects before SQLite is opened. Exact blob and finality-evidence SHA-256 values
also rebind to their retained bytes. Both protocol certificates are recomposed
from the exact bytes and complete governed policy material.

The V2 store sink performs the complete rederivation twice:

```text
sealed V2 packet
  -> preflight exact-byte and cross-binding recomposition
  -> BEGIN IMMEDIATE
  -> schema and complete-history replay
  -> second exact-byte and cross-binding recomposition
  -> stored governed-policy equality
  -> checkpoint-finality prior-cursor check
  -> one atomic economics + DA + finality + cursor commit
```

The first pass rejects forged or damaged packets before SQLite is opened. The
second pass makes precheck-to-transaction drift fail closed and roll back.

## Current fail-closed frontier

The production gate reports these exact missing conditions:

1. governed V7 receipt and Firecracker settlement capability;
2. independently governed origin and durable distribution of the operational
   policy manifest, signer-registry, revision, and trusted evaluation-epoch pins;
3. canonical, release-backed ZenoLedger finality authority.

The two governed adapters close these bounded subconditions while the third
condition remains open:

```text
exact full_blob_da_v1 invocation and private capability mint
policy-pinned ZenoLedger BLS checkpoint-quorum authentication
canonical scheduled-header admission with separate validator and signer roots
header app-hash recomputation
exact checkpoint_finality_v2 certificate derivation and private capability mint
```

The provenance adapter can mint the sealed operational policy only after an
exact private release handoff plus canonical and cryptographic checks.
Governance must still authenticate the expected manifest digest, registry hash
and revision, and trusted evaluation epoch, then mint that private handoff. The
header's separately committed validator-set root is checked by scheduled-header
admission.

These previously open mechanics are closed for both the test lane and the
authority-false V2 sealed-packet lane:

```text
atomic full-blob and certificate persistence
durable checkpoint-finality cursor compare-and-swap
combined proof-artifact, DA, finality, replay, cursor, and economic schema
pre-open and in-transaction exact V2 packet recomposition
fixed-width exact Rust `full_blob_da_v1` invocation and response rebinding
exact governed-policy identity retained inside the sealed DA capability
```

The existing future Firecracker store sink now terminates at this operational
frontier. A Firecracker capability alone cannot become economic-store
authority, even after its own runner conditions are later closed.

## Evidence

Focused tests establish:

- exact prerequisite types and private seals are required;
- caller booleans, bytes, mappings, and ordinary objects reject;
- every shared V7/DA/finality binding listed above has a named mutation reject;
- exact cross-binding executes before the unavailable-authority reject;
- the reserved atomic commit capability cannot be copied, deep-copied, or
  serialized;
- the binder source contains no construction of that capability;
- the store rejects the governed V7 capability at the operational frontier
  before opening SQLite;
- the combined transaction persists economic state, replay rows, exact blob,
  both exact certificates, finality evidence, and both cursors together;
- a failure after the checkpoint-finality cursor CAS rolls all surfaces back;
- stale checkpoint cursors and duplicate DA/finality identities are typed
  no-op rejects;
- two concurrent submissions from the same economic and checkpoint cursor
  yield one commit and one idempotent replay with one complete row set;
- blob and certificate mutations cannot be resealed, while persisted blob,
  evidence, or cursor tampering fails closed on reopen;
- reopening requires the exact operational policy and reconstructs the entire
  DA/finality cursor history from genesis;
- the existing Spot V7 atomic-store regression suite remains green.
- raw caller mappings, artifact bytes, reports, and Booleans cannot mint the V2
  packet;
- a forged V2 object rejects before SQLite is opened;
- exact blob, DA-certificate, finality-certificate, and finality-evidence
  mutation cannot mint a V2 packet;
- the V2 packet cannot be copied, deep-copied, or serialized and permanently
  reports settlement and production authority as false;
- an injected failure in the second, in-transaction V2 recomposition rolls back
  every surface;
- an injected failure after the finality cursor update rolls back economics,
  exact artifacts, replay identities, and both cursors;
- two concurrent exact V2 submissions produce one commit, one idempotent replay,
  and one complete row set.
- the standalone Rust checker uses the canonical Postcard decoder and calls
  `check_local_full_blob_policy_satisfied_v1` directly;
- request framing, truncation, extension, blob-byte mutation, certificate
  mutation, scope mutation, and exhausted-retention cases reject;
- the pinned Python adapter rejects manifest drift, executable substitution,
  noncanonical JSON, caller mappings, and every one-byte mutation of the fixed
  response before a capability can be minted;
- checker execution uses a sealed executable snapshot, bounded I/O, rlimits,
  `no_new_privs`, socket denial, timeout, and process-group teardown before
  result interpretation;
- the protocol workspace lockfile remains byte-identical because the checker
  has its own additive lockfile and build closure.
- invalid BLS signatures reject before the finality capability constructor is
  reached;
- a registry substitution, header/config substitution, wrong predecessor,
  wrong sequence, wrong V7 journal hash, or wrong post-state root rejects;
- replacing the validator-set root with the checkpoint signer-registry root
  rejects through scheduled-header admission;
- an incorrect `app_hash` and an unscheduled proposer identity reject before
  checkpoint quorum can mint the private capability;
- deeply nested or excessively wide input rejects during an iterative bounded
  structural walk before recursive JSON serialization;
- a signer threshold that is reached but does not exceed two thirds of active
  weight cannot mint finality;
- signature-envelope order is normalized and produces byte-identical canonical
  evidence and certificate bytes;
- embedded checkpoint signature arrays are forbidden, keeping the externally
  verified BLS envelope set as the only signature authority for this profile;
- the exact header, checkpoint, validator set, scheduled-header admission,
  signer registry, BLS envelopes, recomputed quorum admission, application
  binding, and prior cursor are retained in one bounded canonical
  finality-evidence object.
- the operational-policy manifest rejects duplicate keys, floats,
  noncanonical bytes, unknown authority Booleans, scope drift, revision drift,
  inactive or revoked policy and registry contexts, registry substitution,
  revoked signers, and a missing or invalid signature quorum;
- a coherently edited and re-signed policy cannot pass the independently pinned
  manifest digest, while a coherent signer-registry substitution cannot pass
  the independently pinned registry hash;
- caller-constructible pin and epoch data cannot substitute for the exact
  private authenticated release handoff;
- the architecture ratchet admits one production policy constructor call and
  requires manifest binding, lifecycle checks, and BLS quorum verification to
  precede that call.

### Rust/Python parity evidence

An external temporary Rust harness imported the current
`zenodex-zrpf-protocol-v3` crate and emitted the baseline
`full_blob_da_v1` and `checkpoint_finality_v2` roots and canonical Postcard
bytes. The executed command was:

```bash
CARGO_TARGET_DIR=<existing-zrpf-protocol-target> cargo run --offline --quiet
```

The retained Python test binds the vector to SHA-256 digests of both Rust hash,
policy, certificate, and codec modules. It also checks a framed source-closure
digest over all 111 protocol Rust sources, the protocol `Cargo.toml`, and the
workspace `Cargo.lock`, ordered by repository-relative path with length-prefixed
paths and contents. That 113-file closure is:

```text
8160fb28e4a9db1d3287781d50e8538120729d5ddc0c15272292bcf632a5c676
```

Observed vector anchors were:

```text
full_blob_policy_root       9f75936af923bef8ddb6b217756bc11f30220cd70f99595b8c3d9302800df825
full_blob_data_root         43f126a24dde3f2d200094c9c8805005f40eafe5b10f575c044be27a11f8468d
full_blob_chunk_root        a2cca633f2ade5c3350416c3ad0ff3c62a94702f2ec3ff960d90f0de82f580e5
full_blob_certificate_root  6eda12e380d4c9a72b0f85e35bf1542622356ecccd6c273679b65b63db2594d3
full_blob_certificate       232 bytes, SHA-256 fde4fa33a2afc80c8812b84de10c6cc7258b3da27b05562709d40933ef215161
finality_policy_root        8b03b76cc795636960966b84872beb7e83f179450608f75ae9653e332163a9a6
finality_certificate_root   1b6d5c7962859d467abe1cda70fdf4328f9c23959caf30a1866b148956d49e51
finality_certificate        419 bytes, SHA-256 a3812dbfdecfa716f73ec70eb0b8986e693851d9fa268b9c998540a2743a81fa
```

## Explicit nonclaims

This integration contract does not establish current governed V7 receipt
evidence, governed Firecracker execution, an external authority for the trusted
policy and registry pins, a production mint for their private release handoff,
provider retrievability, consensus safety outside the pinned strict-quorum
assumptions, canonical fork choice across conflicting qualified checkpoints,
body-root validation and deterministic body replay, authenticated
proposer authorship, validator-set release governance, production rollback
resistance, governed combined
proof/DA/finality/economic admission, settlement authority, release authority,
privacy, liveness, or production authority. It establishes one
manifest-pinned exact local DA check, scoped BLS checkpoint authentication,
scheduled-header structural admission, app-hash consistency, exact
finality-certificate construction, SQLite atomicity, rollback, exact-byte
persistence, replay rejection, and reopen validation for the authority-false
lanes.

The V2 policy capability does not yet expose or persist a canonical provenance
root covering the manifest, registry, revisions, lifecycle, evaluation epoch,
and accepted quorum report. A future authority-bearing sink must retain that
binding so identical policy material admitted under different release contexts
remains auditable and distinguishable.

The private prerequisite classes are future adapter contracts. Unit tests may
apply their module-private seals to exercise cross-binding logic; those test
fixtures are not authority evidence.
