# Spot V7 finality-invocation persistence V6 CBC specification

Date: 2026-07-15
Status: implementation contract
Scope: authority-neutral SQLite persistence and deterministic replay

## 1. Exact claim

The V6 operational store atomically persists the exact checkpoint-finality
checker invocation already retained by `_SpotV7OperationalCommitPacketV3`:

```text
canonical authority-manifest bytes
exact request bytes
exact response bytes
authority-manifest SHA-256
checker executable SHA-256
request SHA-256
response SHA-256
```

The stored invocation is bound to one exact settlement commitment, one
checkpoint-finality certificate root, and the SHA-256 of the exact finality
certificate bytes. Commit, idempotent replay, database open, history replay,
and ordinary reads all revalidate the retained bytes and bindings.

V6 does not execute the external checkpoint-finality checker during database
replay. The checker execution happened before `_SpotV7OperationalCommitPacketV3`
was constructed. V6 preserves and rechecks the exact resulting artifacts.

## 2. Explicit non-claims

V6 does not establish any of the following:

```text
release-governed checker identity
hostile-same-interpreter resistance
fresh release evidence
fresh runtime evidence
public data availability or retrievability
proof receipt authority
runtime authority
release authority
settlement authority
production authority
```

All corresponding stored fields and public properties remain exactly false.
No raw mapping, Boolean, database row, or digest can mint an authority-bearing
capability.

## 3. Authority boundary

```text
sealed V5 prerequisite bundle
  -> recompose exact _SpotV7OperationalCommitPacketV3
  -> revalidate invocation artifacts and semantic request/response binding
  -> BEGIN IMMEDIATE
  -> validate complete V5 history and V6 invocation history
  -> persist economics + V4 operational rows + V5 provenance + V6 invocation
  -> compare-and-swap operational and economic cursors
  -> validate complete post-write history
  -> COMMIT
```

Persisted bytes are evidence inputs. They never become a substitute for the
private prerequisite capability. The prerequisite resolver remains outside the
SQLite transaction as in V5. V6 calls no checker process from the store or
history modules.

## 4. Schema contract

`PRAGMA user_version` is exactly `6`. The complete SQLite object set and each
normalized `CREATE TABLE` statement are exact and closed. Unknown tables,
indexes, triggers, views, or schema extensions reject on open and on every
validated read or commit.

V6 adds exactly one table:

```text
spot_v7_checkpoint_finality_invocation_v6
  settlement_commitment                 BLOB(32) PRIMARY KEY, FK
  finality_certificate_root             BLOB(32) UNIQUE
  exact_finality_certificate_sha256     BLOB(32) UNIQUE
  authority_manifest_sha256             BLOB(32)
  checker_executable_sha256              BLOB(32)
  request_sha256                         BLOB(32) UNIQUE
  response_sha256                        BLOB(32) UNIQUE
  exact_authority_manifest               BLOB(1..4096)
  exact_request                          BLOB(886..1461)
  exact_response                         BLOB(330)
  manifest_pinned_cross_check_executed   INTEGER == 1
  release_governed_checker_identity_verified INTEGER == 0
  hostile_same_interpreter_resistance_established INTEGER == 0
  proof_receipt_authority                INTEGER == 0
  runtime_authority                      INTEGER == 0
  release_authority                      INTEGER == 0
  settlement_authority                   INTEGER == 0
  production_authority                   INTEGER == 0
```

The request bounds follow the fixed V1 checker ABI: an 885-byte header plus a
nonempty certificate of at most 576 bytes. The response is exactly 330 bytes.

## 5. Required revalidation

Every V6 boundary performs all applicable checks below.

### 5.1 Artifact integrity

1. `SHA256(exact_authority_manifest) == authority_manifest_sha256`.
2. The authority manifest is bounded canonical JSON with the exact closed V1
   schema.
3. The manifest contains `checker_executable_sha256` exactly.
4. `SHA256(exact_request) == request_sha256`.
5. `SHA256(exact_response) == response_sha256`.
6. All manifest authority fields are exact JSON `false` Booleans.

### 5.2 Finality semantic binding

V6 independently reconstructs the fixed checker request from:

```text
governed policy
authenticated finality projection
exact finality certificate bytes
```

The reconstructed bytes must equal `exact_request`. The fixed checker response
must parse against the independently derived expected response, including:

```text
application and domain
epoch
policy root
certificate root
prior and successor checkpoint cursors
exact certificate SHA-256
request SHA-256
```

### 5.3 Row binding

The stored row must exactly equal the recomposed packet for every byte and
digest field. Its settlement commitment, finality certificate root, and exact
certificate SHA-256 must match the settlement and finality records persisted in
the same transaction.

## 6. Atomicity and replay

V6 preserves all V5 mechanics:

```text
BEGIN IMMEDIATE
exact cursor compare-and-swap
pre-state and epoch checks
operational checkpoint cursor compare-and-swap
economic state and replay/nullifier writes
V4 operational evidence writes
V5 provenance writes
V6 invocation write
post-write complete-history validation
single COMMIT
```

An exact retry after a committed or commit-uncertain attempt returns
`IDEMPOTENT_REPLAY` only when economics, V4 evidence, V5 provenance, and the V6
invocation row all exactly match. Any mutation yields a typed fail-closed store
error or duplicate-settlement rejection. A rejected transition is a no-op.

## 7. Restart and history contract

On open, read, and commit, V6:

1. captures the V5 history anchor and V6 invocation-row count;
2. requires the invocation-row count to equal the economic revision;
3. resolves the existing sealed V5 prerequisites outside the transaction;
4. re-enters a database transaction;
5. verifies the anchor did not change;
6. revalidates every stored V6 invocation row from retained bytes;
7. compares every row with the exact recomposed packet.

The store does not execute or reopen the checker executable. A replay is valid
only from retained artifacts plus the existing sealed prerequisite resolver.

## 8. Disaster states and closure layers

| Disaster state | Closure layer | Required evidence |
| --- | --- | --- |
| Manifest bytes changed with stale digest | Commit/open validation | byte-mutation test |
| Manifest and digest coherently changed | Canonical manifest plus exact packet equality | coherent-mutation test |
| Executable digest differs from manifest | Artifact constructor | digest-mutation test |
| Request or response changed | Artifact constructor and packet equality | per-byte mutation tests |
| Checker request names another finality certificate | Independent request reconstruction | certificate-binding test |
| Response belongs to another request | Exact expected-response parser | response-binding test |
| Partial transaction writes invocation only | One SQLite transaction | rollback test |
| Concurrent duplicate commits | `BEGIN IMMEDIATE`, unique rows, exact replay | concurrent-store test |
| Unknown schema object hides alternate state | Exact schema object-set validation | schema-extension test |
| SQL flips an authority field | SQLite `CHECK(field = 0)` | false-field promotion test |
| Restart reruns native checker | No checker call in V6 replay path | patched-executor reopen test |

## 9. Required tests

The focused V6 suite must cover:

```text
successful atomic commit
exact idempotent replay
reopen and read-history replay
each exact byte field mutated
each of the four digests mutated
coherent byte-plus-digest mutation
finality certificate binding mutation
every persisted false field promotion
unknown schema object insertion
concurrent duplicate attempt
cursor mismatch reject-is-no-op
rollback before commit
commit acknowledgement uncertainty and exact retry, where affordable
no checker process execution during reopen
```

Boundary mutation tests are bug-discovery and regression evidence. They are not
a proof of full SQLite, Python interpreter, or host correctness.

## 10. Promotion rule

This V6 slice may be described only as:

> Exact, authority-neutral persistence and deterministic replay of retained
> checkpoint-finality checker invocation artifacts.

It does not change the production-readiness percentage by itself and must not
change any public production or settlement claim.
