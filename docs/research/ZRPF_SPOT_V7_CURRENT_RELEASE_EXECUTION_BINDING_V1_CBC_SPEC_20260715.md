# Spot V7 Current Release To Execution Binding V1 CBC Specification

Status: implementation prerequisite; authority neutral.

## 1. Scoped claim

This profile may establish only the following observation:

> At one locked Store V3 revision, the exact current nonrevoked release
> candidate bytes were bound to the exact canonical execution-authority
> manifest bytes by the reviewed V1 checker.

The observation does not establish that the candidate remains current when a
later settlement commits. It grants no proof, runtime, release, settlement, or
production authority.

## 2. Authority progression

```text
untrusted Store V3 path and configured identity
  -> exact schema and complete cryptographic history replay
  -> locked current nonrevoked release cursor
  -> exact retained candidate bytes
  -> candidate ID, SHA-256, revision, and SELECT event equality
  -> exact execution-authority manifest bytes
  -> canonical candidate/manifest checker replay
  -> retained authority-neutral observation
  -> no economic commit authority
```

The nominal Python checked-manifest descriptor is not an authentication
capability. Same-interpreter code can construct it by reaching module-private
objects. Every consumer must rerun the exact byte checker and compare the
derived fields.

## 3. Required locked inputs

The binding operation must receive or derive under one Store V3
`BEGIN IMMEDIATE` transaction:

```text
store_identity_hash
database_revision
last_evaluation_epoch
release_state_root
current_candidate_id
current_candidate_sha256
current_release_revision
current_select_input_id
current_revocation_record_id
exact_current_candidate_bytes
```

`current_revocation_record_id` must be absent. Terminally revoked state rejects.
The store must validate its exact schema and replay the complete authenticated
SELECT/REVOKE history before exposing the observation.

## 4. Exact execution binding

The binder receives exact execution-authority manifest bytes and invokes:

```text
check_exact_spot_v7_execution_authority_manifest_v1(
    exact_release_candidate_bytes,
    exact_authority_manifest_bytes,
)
```

It must independently compare the checker output with the locked cursor:

```text
checked.candidate_id              == current_candidate_id
checked.candidate_manifest_sha256 == current_candidate_sha256
checked.release_revision          == current_release_revision
SHA256(exact candidate bytes)     == current_candidate_sha256
SHA256(exact manifest bytes)      == checked.authority_manifest_sha256
```

The current SELECT input ID remains a separate event identity. It must be
retained in the final binding and must never be derived from the candidate or
manifest digest.

## 5. Canonical observation root

The V1 observation root is a domain-separated SHA-256 commitment over one
canonical versioned object containing:

```text
schema
store_identity_hash
database_revision
last_evaluation_epoch
release_state_root
current_candidate_id
current_candidate_sha256
current_release_revision
current_select_input_id
execution_authority_manifest_sha256
exact_candidate_bytes_sha256
exact_authority_manifest_bytes_sha256
```

All roots and digests are exact lowercase 32-byte hexadecimal values. Integers
are bounded non-Boolean unsigned integers. Unknown fields, duplicate keys,
floats, noncanonical JSON, zero roots where forbidden, and over-limit bytes
reject.

## 6. Retained object

The private retained object must:

- have no public constructor;
- be final, immutable, non-copyable, and non-serializable;
- retain the exact candidate and manifest bytes;
- retain every locked cursor field listed above;
- recompute and compare the observation root whenever projected;
- expose only exact false values for every authority claim.

At minimum these properties are always false:

```text
currentness_at_settlement_established
atomic_release_and_settlement_commit_established
external_monotonic_rollback_resistance_established
hostile_same_interpreter_resistance_established
proof_receipt_authority
runtime_authority
release_authority
settlement_authority
production_authority
```

## 7. Temporal rule

The observation is a revision-bound prerequisite, not a lease. A final
authority-bearing consumer must compare-and-swap the exact Store V3 identity,
database revision, release state root, candidate identity, SELECT event, and
unrevoked state in the same durable transaction that applies economic effects.

If release state and economic state remain in different databases, V1 cannot
establish atomic settlement authority. A production profile must use one
transactional authority domain or a separately proven protocol whose
linearization and crash semantics are equivalent.

## 8. Required negative evidence

Tests must reject:

1. no current candidate;
2. terminally revoked current state;
3. candidate ID mismatch;
4. candidate SHA-256 mismatch;
5. release revision mismatch;
6. SELECT event mismatch;
7. candidate substitution with the same authority manifest;
8. authority-manifest substitution;
9. raw runtime-manifest binding mismatch;
10. semantic runtime artifact-set mismatch;
11. forged nominal checked descriptor;
12. schema or persisted-history mutation;
13. concurrent revocation before locked observation;
14. revocation after observation but before a simulated settlement commit;
15. authority-field promotion.

Case 14 must demonstrate that the observation remains authority neutral and
that a final exact release-state CAS would reject.

## 9. Explicit nonclaims

This profile does not establish:

- externally governed release trust roots;
- protection against restoration of an older valid database snapshot;
- same-UID path-substitution resistance;
- hostile same-interpreter capability security;
- live Firecracker execution;
- proof receipt validity;
- data availability or protocol finality;
- atomic economic state transition;
- release, settlement, or production authority.

These nonclaims remain false even when all V1 tests pass.
