# Global Economic Durable Publisher V1

Status: `IMPLEMENTED_TESTED_DISCOVERY`, unmounted.

Production authority: `NONE`.

## Obligation

Join receipt verification, exact economic binding checks, complete bundle
construction, and the durable ordinary-epoch compare-and-swap behind one
factory-constructed API. A caller supplies an expected stored source, typed
receipt candidate, and complete body. The caller cannot supply a verified
witness, publication record, bundle, journal token, or persistence operation.

The durable linearization point is the SQLite transaction that inserts the
complete epoch bundle and advances the singleton head. Verification changes no
authoritative state. A crash before the transaction leaves the source head; a
crash after commit can be reconciled by reopening and submitting the exact
candidate against its historical stored source.

Source resolution currently revalidates the bounded durable history. No
throughput or production-latency claim is made.

## Pattern selection record

Domain schema and invariant:

```text
StoredSource x TypedCandidate x CompleteBody
  -> Verify(selected verifier and profile)
  -> Recheck(pre-state, post-state, effects, body, receipt, source)
  -> Derive(PublishedEpoch, DurableBundle)
  -> SQLite CAS
```

The selected profile, activation identity, profile-governed verifier release,
measured verifier binding, private verifier token, journal, and journal write
capability are fixed for the publisher lifetime. The publisher carries no
mutable in-memory economic head; SQLite history owns source identity and replay.

Applicability: this pattern is used because an ordinary epoch must be admitted
and persisted as one candidate identity. Exposing the lower journal or accepting
a caller-built witness would create parallel authority paths.

Mechanical guarantees:

- factory-only construction after genesis admission by an exactly typed bound
  verifier capability;
- exact profile-to-verifier-registry-root and profile-to-root-image selection;
- content-derived verifier release identity with closed `SHADOW` versus
  `ACTIVE_NEW` purposes and evidence requirements;
- exact evidence-manifest, implementation-artifact, backend-protocol, profile,
  deployment, receipt-size, and journal-size binding;
- byte-identical activation reproduction on reopen;
- exact selected-profile comparison;
- exact historical source resolution from one validated SQLite read snapshot;
- verifier-instance, release, measured-binding-root, and publisher-token binding;
- journal-instance-bound write capability checked separately from the CAS token;
- internal publication-record and durable-bundle derivation;
- typed stale and capacity no-effects;
- exact retry and SQLite CAS conflict handling.

Explicit non-guarantees: Python process privacy and module-private names are not
cryptographic capability boundaries. The backend object is an injected
process-local premise, and artifact bytes are supplied to the binding function;
this slice does not load and attest a deployed verifier executable. It provides
no real RISC0 receipt replay, active production verifier release, objective data
availability or finality, migration activation, outbox delivery, destination
acknowledgement, OS-level writer fencing, consensus mount, or production release
authority.

Trusted constructors and boundary: the deployment binder is the only public
constructor for `BoundEconomicReceiptVerifierV1`; `create` and `open` are the
only public publisher constructors. They reverify the genesis admission.
`publish_economic_epoch` owns the verifier-to-journal path. The journal's public
API exposes no ordinary-epoch commit method. Its module-private factory
functions return the journal and an instance-bound write capability together;
both use one inventoried module-private capability issuer.
`GlobalEconomicEpochJournalV1` owns the transaction and exact retry relation.

Staleness, aliasing, concurrency, and crash behavior:

- all caller values are reconstructed into exact typed snapshots;
- bool/int aliases and hostile frozen-object mutation fail during reconstruction;
- a source head must equal a head resolved from durable history;
- the CAS token is captured before receipt verification;
- a competing commit during verification yields exact retry or `STALE_HEAD`;
- restart retry re-verifies the receipt and resolves the historical source;
- lower-journal exception and abrupt-exit tests establish bounded PRE-or-POST
  recovery at each SQLite fault point.

Python enforcement: exact-type checks, frozen typed values, content-derived
release and registry roots, measured artifact hash, closed evidence states,
data-slot-free verifier and write capabilities, private factory mints, private
verifier binding token, sealed publisher selection, canonical bytes,
full-history validation, and SQLite CAS. Same-process reflective mutation and
direct import of underscore-prefixed functions remain outside the capability
claim. The underscore-prefixed structural journal writer remains explicitly
inventoried and blocks `NO_BYPASS` promotion.

Rust enforcement: absent for this adapter. Rust/RISC0 parity and real receipt
replay remain release-blocking gaps.

Serialization, replay, and migration: the existing V1 activation and ordinary
epoch byte formats are unchanged. Replay uses the verifier-derived commit ID
and content-derived publication ID. V1 fixes one genesis activation and profile;
migration requires a separately reviewed durable publisher version.

## Evidence

The focused tests use Arrange/Act/Assert structure and cover:

- create, publish, close, reopen, and exact historical retry;
- fabricated source metadata rejected before epoch receipt verification;
- body-commitment and receipt-root mutation as no-publication failures;
- selected verifier rejection as an exact no-publication failure;
- generic caller-selected verifier rejection before backend use;
- wrong registry, image, deployment, evidence manifest, implementation artifact,
  byte bound, and backend success-shape rejection;
- shadow/active release evidence and unique-selection checks;
- absent public journal commit method, forged write capability rejection, and
  cross-journal capability rejection;
- an executable negative witness showing the private structural journal writer
  remains callable in the same interpreter and blocks `NO_BYPASS`;
- two valid competing publishers and a head change during receipt verification;
- wrong activation on reopen;
- bool/int source-coordinate alias rejection;
- direct constructor rejection;
- exact publication API shape with no caller-supplied witness, record, bundle,
  token, or journal;
- owned activation and historical-head resolution;
- the journal's canonical, capacity, retry, concurrency, schema, and crash suite.

Writer and value-sink manifests classify the API as
`SEPARATE_RESEARCH_NOT_M6` and retain open module, transition, canonical effect,
proof-profile, route, terminal, adapter-promotion, and release-evidence gaps.

## Promotion boundary

This slice narrows verifier selection and the ordinary-epoch portion of VM-10.
It does not close VM-09 sole-authority mounting, complete Rust/RISC0 refinement,
deployed artifact loading and attestation, objective finality, external delivery,
migration, whole-economy terminal coverage, or active release evidence.
`production_authority` remains `NONE`.
