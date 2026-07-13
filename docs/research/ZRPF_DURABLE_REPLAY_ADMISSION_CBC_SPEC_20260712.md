# ZRPF Durable Replay-Index Admission CBC Specification

Status: implemented partial, local replay-index profile

Date: 2026-07-12

CBC obligation: `RS-CBC-025`

## Scoped positive claim

On one local POSIX data directory owned by one trusted operating-system user,
cooperative writers serialize a previously authenticated recursive-root
admission and durably commit its canonical replay indexes and acceptance
outcome through one SQLite transaction. The transaction uses rollback-journal
`DELETE` mode, `synchronous=EXTRA`, and `BEGIN IMMEDIATE`.

A canonical retry with the same authenticated root, verification request, and
governed provenance returns the stored outcome without adding another entry.
A rejected request or process exit before `COMMIT` preserves the prior cursor.

This claim covers these committed objects:

- root journal identity;
- chain, epoch, and proof-profile slot;
- child verification claim identities;
- accepted receipt identities;
- cross-shard message identities;
- verifier authority-manifest digest;
- sealed verifier executable digest;
- canonical verification-request digest;
- release-binding config digest;
- replay-manifest digest;
- hash-chained replay-index cursor;
- canonical accepted outcome receipt.

The profile applies no balance, collateral, mint, burn, fee, reward, carry,
message-delivery, application-state, or settlement effect.

## Authority flow

```text
externally governed release-binding config digest
  + canonical release-binding bytes
  + canonical authority-manifest bytes and digest
  + sealed static verifier executable
  + canonical proof and recursive input snapshot
        |
        v
PinnedRecursiveStarkVerifier
  -> validates release scope and authority-manifest identity
  -> verifies the receipt and exact trusted expectations once
  -> parses canonical root-bound replay facts
  -> mints one private authenticated value carrying provenance
        |
        v
SQLiteRecursiveStarkAdmissionStore._commit_authenticated_recursive_stark_root
  -> BEGIN IMMEDIATE
  -> reads the durable cursor and indexed conflicts
  -> invokes the shared private core planner
  -> persists admission, identifiers, provenance, and outcome
  -> compare-and-swaps the metadata cursor
  -> COMMIT
        |
        v
data-only durable outcome receipt
```

The public store API accepts no `verified=true` flag, caller-projected policy,
caller-projected next state, or `RecursiveStarkAdmissionResult`. Its mutating
method is private and consumes the private value produced after verification.
The architecture ratchet restricts that call to
`PinnedRecursiveStarkVerifier.verify_and_commit`.

Python module privacy does not defend against hostile same-interpreter access.
The release config digest must come from node-owned governance or release state.
Providing self-consistent release bytes and their digest from the same untrusted
request supplies local test evidence only.

## Shared decision law

The in-memory reference path and SQLite path use the same private planner. Its
reject order is:

```text
trusted policy
state chain scope
canonical idempotent outcome recovery
duplicate root
duplicate slot
duplicate child claim
duplicate accepted receipt
duplicate cross-shard message
index capacity
durable cursor compare-and-swap
```

An exact stored outcome is recognized only when the existing root row carries
the same domain-separated outcome key:

\[
K_{out} = H(D_{out}, F, A, V, Q, R, M)
\]

where:

- \(F\) is the canonical authenticated-facts digest;
- \(A\) is the authority-manifest SHA-256;
- \(V\) is the sealed verifier executable SHA-256;
- \(Q\) is the canonical verification-request SHA-256;
- \(R\) is the release-binding config digest;
- \(M\) is the replay-manifest SHA-256.

The replay-index state root is a hash chain:

\[
S_{n+1} = H(D_{state}, S_n, n+1, scope, F, K_{out}, counts_{n+1})
\]

`S_n` commits to and internally binds the replay-index history. Authenticity is
conditional on an externally trusted head because the local database contains
both the rows and the unkeyed head. It is not an application or economic state
root.

## Transaction contract

Every writer connection reasserts and reads back:

```sql
PRAGMA foreign_keys = ON;
PRAGMA journal_mode = DELETE;
PRAGMA synchronous = EXTRA;
PRAGMA trusted_schema = OFF;
PRAGMA busy_timeout = 5000;
```

The store then performs:

1. `BEGIN IMMEDIATE` to acquire the single SQLite writer lane.
2. Exact schema, application-ID, and user-version checks.
3. One metadata cursor read.
4. Root and slot lookups plus temporary-table joins for identifier overlap.
5. One call to the shared deterministic admission planner.
6. Exact expected-cursor equality for a new accepted root.
7. Admission and identifier inserts protected by primary and unique keys.
8. Metadata update constrained by previous revision and state root.
9. `rowcount == 1` enforcement for the metadata compare-and-swap.
10. `COMMIT`, followed by stored-receipt recovery.

Every store open performs initialization and complete canonical history
validation under one `BEGIN EXCLUSIVE` transaction. This gives every validation
query one stable snapshot and prevents a cooperative writer from committing
between the history and metadata reads. The validator streams admissions and
three revision-ordered identifier cursors. It requires dense revisions and
per-root ordinals, reconstructs each typed fact from stored identifier rows,
recomputes identifier roots and the facts digest, validates the outcome key,
replays every state-root link and cumulative count, and requires the final
replayed cursor to equal the singleton metadata head. This startup check is
linear in the retained history and identifier count, with working memory bounded
by one root's identifier disclosures. The private parent directory is synced
after every successful open, including a retry after an earlier directory-sync
failure.

The temporary incoming-identifier table avoids SQLite bind-variable limits for
the bounded 65,536-item receipt and message sets. Epoch IDs use an eight-byte
big-endian BLOB, preserving the complete unsigned 64-bit protocol domain.

SQLite documents `BEGIN IMMEDIATE` as starting a write transaction immediately.
Its `synchronous=EXTRA` rollback-journal behavior adds a directory sync after
journal deletion. The governed profile uses these exact settings:

- <https://www.sqlite.org/lang_transaction.html>
- <https://www.sqlite.org/pragma.html#pragma_synchronous>

## Construction invariants

### DRA-CBC-001: one verified entry path

`verify_and_commit` requires a static ELF verifier and a release binding loaded
against an externally supplied config digest. It invokes the verifier boundary
once, then invokes the private store commit once.

### DRA-CBC-002: one reject-precedence implementation

Database queries produce only the minimal conflict booleans and counts consumed
by `_plan_authenticated_recursive_stark_root`. SQL constraints are backstops.
They do not define a competing acceptance policy.

### DRA-CBC-003: linearizable writers

All conflict reads and writes occur after `BEGIN IMMEDIATE` on one local SQLite
database. Two cooperative processes cannot both hold the writer transaction.

### DRA-CBC-004: cursor compare-and-swap

A new accepted root requires exact equality between the caller's expected
cursor and the cursor read inside the serialized transaction. The metadata
update repeats revision and state-root equality and requires one changed row.

### DRA-CBC-005: retry-transparent outcome

The accepted outcome is stored in the same transaction as every replay index.
An exact retry returns `IDEMPOTENT_REPLAY` with the original receipt. A root
with different request or authority provenance receives the existing duplicate
root rejection.

### DRA-CBC-006: reject and pre-commit crash are no-ops

Every planned reject rolls back. SQLite recovery removes uncommitted admission
and identifier rows after process death. Tests terminate a child after row
insertion before metadata compare-and-swap and after metadata compare-and-swap
before `COMMIT`, then require exact genesis recovery.

### DRA-CBC-007: bounded canonical storage

All hashes are 32-byte BLOBs. Counts remain within the existing 1,048,576-entry
bound. Chain and proof-profile tokens inherit the core ASCII and byte limits.
No floating-point value enters the schema, cursor, receipt, or hash contract.

### DRA-CBC-008: private local filesystem profile

The immediate data directory must be canonical, owned by the effective user,
and grant no group or world permissions. The database must be a single-link
regular file owned by that user with mode `0600`. Symlinked paths reject.

## Evidence requirements

Required deterministic evidence includes:

- governed release binding plus a static ELF verifier crossing the sole durable
  entry path;
- initialization and exact PRAGMA checks;
- first commit and restart recovery;
- maximum unsigned-64 epoch round trip;
- exact retry returning the same receipt;
- stale cursor rejecting without mutation;
- root, slot, child, receipt, and message conflict precedence;
- two connections racing on one root;
- two processes racing on one root;
- two connections racing on one slot;
- process exit before commit recovering the old cursor;
- process exit after commit recovering the stored outcome;
- restart validation and a concurrent writer sharing one serialized snapshot;
- directory-sync failure requiring a successful sync on retry;
- deterministic parity between in-memory and SQLite conflict decisions;
- unknown schema object and application-ID drift rejection;
- same-count identifier mutation and history-layer mutation rejection at
  restart;
- symlink and non-private-directory rejection;
- architecture tests restricting private authority construction and commit;
- required Ruff, mypy, pytest, and CBC checker coverage in ZRPF CI.

## Explicit non-claims

This profile does not establish:

- atomic replay indexes plus value-moving effects;
- ZenoLedger application-state admission;
- economic action uniqueness across equivalent encodings;
- asset conservation or authorized mint and burn;
- pre-state to post-state continuity;
- schedule, carry, or data-availability validity;
- delivery of committed cross-shard messages;
- settlement or release authority;
- hostile same-UID resistance;
- storage rollback resistance;
- safety on NFS, SMB, or an unverified FUSE/overlay filesystem;
- hardware-backed attestation;
- source-built or cross-host reproducible proof generation;
- production readiness.

The next promotion requires one ledger transaction that applies independently
derived value, carry, reward, and message effects while committing these replay
indexes. That promotion also requires a fresh receipt-authenticated V2 semantic
statement that binds the verified receipt profile and program manifest as one
authority pair.
