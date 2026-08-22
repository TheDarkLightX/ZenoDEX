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

The selected profile, activation identity, verifier object, binding token, and
journal are fixed for the publisher lifetime. The publisher carries no mutable
in-memory economic head; SQLite history owns source identity and replay.

Applicability: this pattern is used because an ordinary epoch must be admitted
and persisted as one candidate identity. Exposing the lower journal or accepting
a caller-built witness would create parallel authority paths.

Mechanical guarantees:

- factory-only construction after verifier-admitted genesis;
- byte-identical activation reproduction on reopen;
- exact selected-profile comparison;
- exact historical source resolution from one validated SQLite read snapshot;
- verifier-instance and publisher-token binding;
- internal publication-record and durable-bundle derivation;
- typed stale and capacity no-effects;
- exact retry and SQLite CAS conflict handling.

Explicit non-guarantees: Python process privacy is not a cryptographic
capability boundary. The verifier object's implementation determines receipt
assurance. This slice provides no deployed RISC0 verifier registry, objective
data availability or finality, migration activation, outbox delivery,
destination acknowledgement, OS-level writer fencing, consensus mount, or
production release authority.

Trusted constructors and boundary: `create` and `open` are the only public
constructors. They reverify the genesis admission. `publish_economic_epoch`
owns the verifier-to-journal path. `GlobalEconomicEpochJournalV1` owns the
transaction and exact retry relation.

Staleness, aliasing, concurrency, and crash behavior:

- all caller values are reconstructed into exact typed snapshots;
- bool/int aliases and hostile frozen-object mutation fail during reconstruction;
- a source head must equal a head resolved from durable history;
- the CAS token is captured before receipt verification;
- a competing commit during verification yields exact retry or `STALE_HEAD`;
- restart retry re-verifies the receipt and resolves the historical source;
- lower-journal exception and abrupt-exit tests establish bounded PRE-or-POST
  recovery at each SQLite fault point.

Python enforcement: exact-type checks, frozen typed values, private factory
mint, private verifier binding token, sealed publisher selection, canonical
bytes, full-history validation, and SQLite CAS. Same-process reflective mutation
remains outside the capability claim.

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

This slice narrows the ordinary-epoch portion of VM-10. It does not close VM-09
sole-authority mounting, complete Rust/RISC0 refinement, objective finality,
external delivery, migration, whole-economy terminal coverage, or release
evidence. `production_authority` remains `NONE`.
