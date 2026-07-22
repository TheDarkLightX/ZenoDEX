# Rust FCIS Pattern Selection

Date: 2026-07-22

This record governs the first Rust normative-core migration slice. It covers
the value-moving inventory, semantic-source synchronization, authority
demotion, and the future transition-candidate and commit boundaries.

## Decision boundary

The current production-strict profile remains Python authority. Public-testnet
Rust authority is permitted only for a surface whose exact semantic sources,
Rust implementation, formal artifacts, differential evidence, and deployment
facts agree. A stale or incomplete surface is demoted to Python authority.

```text
MappedSourcesFresh && RequiredEvidencePresent && ExplicitPromotion
  -> RustAuthorityWithPythonShadowMayRun
```

The inventory and policy tools are assurance gates. They do not establish the
economic correctness of a transition.

## Pattern 1: immutable typed registry

- Domain relationship: one `SurfaceRecord` owns the complete mapping from a
  value-moving surface to its sources, schemas, authority mode, invariants,
  evidence, callers, commit path, delivery path, audit cases, and blockers.
- Applicability: the mapping is closed, versioned, canonical JSON data with
  stable surface identifiers and exact repository-relative paths.
- Mechanical guarantee: frozen typed records and tuple-valued fields prevent
  checker logic from mutating parsed authority facts; duplicate surface IDs,
  unknown fields, missing paths, and invalid statuses reject deterministically.
- Non-guarantees: a complete registry entry does not prove the listed
  implementation or formal artifact correct.
- Trusted boundary: JSON is untrusted until the strict parser constructs the
  frozen registry. The checker core consumes only parsed records.
- Counterexamples: duplicate IDs, aliased mutable lists, unknown status values,
  a deleted source path, and a new mutation path outside every declared surface.
- Python enforcement: frozen dataclasses, exact scalar types, tuple ownership,
  closed field sets, sorted deterministic diagnostics.
- Rust enforcement: the registry does not enter the Rust transition core. A
  later generated Rust view must reproduce the same canonical bytes and hash.
- Serialization and migration: schema and inventory versions are explicit.
  Schema changes require a new parser branch and migration test.
- Evidence hooks: parser negatives, deterministic output test, mutation-path
  coverage test, deployment-profile synchronization test.

## Pattern 2: functional core and imperative scan shell

- Domain relationship: filesystem acquisition produces immutable `SourceFile`
  facts; a pure classifier maps those facts and the registry to diagnostics.
- Applicability: source discovery and file reads are effects. Classification,
  validation, coverage, and release-readiness reduction are deterministic.
- Mechanical guarantee: equal file bytes plus equal registry bytes produce
  byte-identical sorted JSON results.
- Non-guarantees: syntax scanning cannot prove absence of reflective,
  generated, native, database-trigger, or external value movement.
- Trusted boundary: the shell reads only repository-relative files beneath
  declared roots and passes owned UTF-8 text inward.
- Counterexamples: path traversal, symlink escape, unreadable bytes, parser
  failure, nondeterministic directory order, and diagnostic order drift.
- Python enforcement: `Path.resolve()` containment, immutable source facts,
  pure functions, no wall clock, no environment-derived semantics.
- Rust enforcement: separate Rust source policy scan; no runtime import from
  the Python checker.
- Serialization and migration: stable JSON schema with sorted keys and lists.
- Evidence hooks: repeated-run byte equality and shuffled-input metamorphic
  tests.

## Pattern 3: conservative authority demotion

- Domain relationship: promotion is an explicit reviewed deployment fact;
  demotion is required whenever source synchronization or evidence is stale.
- Applicability: every Rust-authoritative surface in a strict profile.
- Mechanical guarantee: a blocked surface cannot appear in
  `promoted_surfaces` or use a Rust-authoritative mode. Python authority remains
  the fail-closed fallback selected before process startup.
- Non-guarantees: Python authority may itself contain a defect. Demotion only
  prevents stale Rust semantics from retaining decision authority.
- Trusted boundary: deployment profiles are validated before installation as
  process policy. Runtime transitions do not read the filesystem.
- Counterexamples: stale promotion list, blanket Rust default, pure Rust mode,
  missing Rust engine, and Python/Rust disagreement.
- Python enforcement: strict profile validation plus the inventory/source-sync
  checker. Any Rust-authoritative disagreement raises `AuthorityError`.
- Rust enforcement: no Rust-side promotion decision; Rust only returns a typed
  candidate or rejection to the selector.
- Serialization and migration: profile schema remains versioned. Re-promotion
  requires a separate profile change after evidence refresh and sign-off.
- Evidence hooks: profile parser tests, blocked-surface demotion tests, and
  root-preserving rollback replay.

## Pattern 4: typed transition candidate

- Domain relationship: accepted state, effects, receipt, nonce updates, roots,
  and outbox entries form one owned aggregate derived by one transition.
- Applicability: every future Rust value-moving transition.
- Mechanical guarantee: rejection cannot carry partial authority values;
  acceptance cannot mix fields from different candidates; constructors bind
  pre-root, execution context, algorithm version, and policy version.
- Non-guarantees: the aggregate shape alone does not prove economic invariants,
  authorization, canonical encoding, or datastore atomicity.
- Trusted boundary: only checked constructors inside the normative Rust core
  can create an accepted candidate.
- Counterexamples: caller-constructed receipts, shell-recomputed fees, mismatched
  effect roots, reused nonce plans, and outbox entries from another pre-root.
- Python enforcement: shadow result is independently computed and compared;
  Python never reconstructs a Rust-authoritative effect plan.
- Rust enforcement: private fields, domain newtypes, owned canonical vectors,
  typed stable rejection, and `#[must_use]` results.
- Serialization and migration: explicit domain separators and fixed versions;
  no serde-derived authority encoding.
- Evidence hooks: reject-is-empty, candidate-coherence, canonical round-trip,
  cross-language differential, and Kani composition contracts.

## Pattern 5: compare-and-swap atomic commit with transactional outbox

- Domain relationship: one accepted candidate is published against one exact
  pre-state root. State, roots, nonces, effects, receipt, and outbox entries are
  one transaction.
- Applicability: the imperative shell after successful core evaluation.
- Mechanical guarantee: stale-root mismatch publishes nothing; a matching root
  publishes the supplied candidate all-or-none. Deterministic effect IDs make
  retries idempotent.
- Non-guarantees: the abstract pattern does not prove a concrete database
  transaction linearizable or an external provider idempotent.
- Trusted boundary: the datastore transaction owns compare-and-swap and outbox
  persistence. Delivery workers may consume only committed outbox rows.
- Counterexamples: crash before commit, crash after commit before delivery,
  duplicate workers, reordered delivery, stale roots, and partial persistence.
- Python enforcement: current shells remain blocked from Rust production
  promotion until their concrete commit path refines this contract.
- Rust enforcement: future `commit_candidate` takes an opaque checked candidate
  and cannot alter economic fields.
- Serialization and migration: effect IDs bind transition identity, index,
  kind, recipient, asset, and amount. Schema activation requires forward
  recovery and rollback rehearsal.
- Evidence hooks: crash injection, stale-root race, restart, duplicate delivery,
  Loom or equivalent concurrency model, and datastore-specific linearizability
  tests.

## Rejected alternatives

- One giant Rust `step()` owning every protocol domain was rejected because it
  couples unrelated invariant families and makes local proof boundaries
  intractable.
- Typestate for persisted economic lifecycle was rejected because dynamic
  loaded states require exhaustive tagged sums. Typestate remains appropriate
  for small ingress phases such as parsed, authenticated, and authorized.
- Runtime loading of the inventory JSON inside the Rust core was rejected
  because it introduces filesystem authority and configuration drift into the
  deterministic transition.
- Automatic re-promotion after a green checker was rejected because promotion
  also requires soak evidence and explicit sign-off. Automatic enforcement is
  one-way toward demotion or release blocking.

## Current nonclaims

- The value-moving inventory is not yet complete until its source-derived gate
  reports zero unclassified paths.
- No current Rust surface gains production authority from this record.
- The existing zUSD Rust step is not full CBC and is semantically stale against
  PRs #466 and #467.
- Atomic production commit and idempotent delivery are not established by the
  current runtime.
