# Global Economic Object Nullifier Reference V2

Date: 2026-08-23
Status: research-only semantic reference; unmounted; unproved; no authority

## Claim scope

This slice defines a bounded canonical oracle for the logical rule that one
opaque economic object identifier may be consumed at most once. It exists to
compare later authenticated-set candidates against one small deterministic
meaning.

```text
validated immutable archive + validated immutable claims
  -> Accepted(canonical successor archive)
  | Rejected(typed code, pre-reference digest)
```

The reference has no effects, receipt, authority witness, persistence plan,
release record, proof image, callable port, or state-root field. Its digest is
named `reference_archive_digest`. It is evidence for bounded differential
testing and is not a GlobalSettlementABI commitment.

V1 object consumption remains quarantined. ZDEX purchase-burn routes that need
single-use object consumption remain unmounted. `production_authority=NONE`.

## Frozen reference values

- Schema: `zenodex/global-economic-object-nullifier-reference/v2`.
- Maximum archive entries: 4,096.
- Maximum claims in one reference step: 64.
- Maximum canonical archive bytes: 1,048,576.
- Object and occurrence identifiers: lowercase, nonzero, `0x`-prefixed,
  32-byte hexadecimal strings.
- Object identifiers are opaque already-derived inputs. This slice neither
  derives them nor authenticates their global provenance.
- Archive entries are strictly increasing by decoded object-ID bytes. Each row
  records `object_id` and `first_consumed_by_occurrence_id`.

The immutable Python values are:

- `ReferenceObjectIdV2`
- `ReferenceOccurrenceIdV2`
- `ReferenceConsumptionClaimV2`
- `ReferenceNullifierEntryV2`
- `CanonicalReferenceNullifierArchiveV2`
- `ReferenceRejectCodeV2`
- `ReferenceAcceptedV2`
- `ReferenceRejectedV2`
- `ReferenceResultV2`

## Canonical bytes and reference digest

Canonical archive bytes are compact UTF-8 JSON with lexicographically sorted
object keys and no insignificant whitespace:

```json
{"entries":[{"first_consumed_by_occurrence_id":"0x...","object_id":"0x..."}],"schema":"zenodex/global-economic-object-nullifier-reference/v2"}
```

The reference digest is:

```text
SHA256(
  ASCII("global-economic-object-nullifier-reference")
  || NUL
  || ASCII("2")
  || NUL
  || canonical_archive_bytes
)
```

It is rendered as lowercase `0x`-prefixed hexadecimal. Changing the digest
domain, schema, row fields, sorting rule, JSON rule, or identifier rule creates
a different reference version.

## Transition and rejection precedence

`apply_reference_object_nullifiers_v2(pre_archive, claims)` accepts only the
validated immutable types above. It snapshots the validated primitive values,
sorts fresh claims by decoded object-ID bytes, and returns a newly owned
archive. Empty claims accept as an exact value/bytes/digest no-op, including
when the archive is at capacity.

Rejections are evaluated in this exact order:

| Priority | Code | Condition |
| ---: | --- | --- |
| 1 | `REFERENCE_STEP_LIMIT_EXCEEDED` | more than 64 claims |
| 2 | `REFERENCE_DUPLICATE_IN_BATCH` | one object appears more than once in the claims |
| 3 | `REFERENCE_ALREADY_CONSUMED` | a claimed object is in the pre-archive |
| 4 | `REFERENCE_ARCHIVE_CAPACITY_EXCEEDED` | the successor would exceed 4,096 entries |
| 5 | `REFERENCE_ARCHIVE_BYTE_LIMIT_EXCEEDED` | canonical successor bytes would exceed 1,048,576 bytes |

Every rejection contains the exact pre-reference digest and a stable
diagnostic. It contains no successor archive. The pre-archive is immutable, so
rejection cannot change it.

## Evidence obligations

The candidate must pass:

- AAA happy and rejection cases;
- BVA at claim counts 0, 1, 63, 64, and 65 and archive counts 4,095,
  4,096, and attempted 4,097;
- exact precedence and reject-no-successor observations;
- all subsets and insertion permutations of six object identifiers against an
  independently written set model;
- three-step reuse histories;
- canonical-order metamorphic checks;
- deterministically rendered fixed vectors consumed through closed Python and
  Rust fixture decoders;
- named semantic source mutants with zero survivors;
- retained-alias ownership and pre-limit-work regressions;
- wildcard packaging isolation and byte-identical V1 quarantine artifacts.

The Python oracle lives under `experiments/`. Operator release bundles and
Docker contexts exclude that tree. The standalone Rust crate is unpublished,
has no binary, and is not a workspace member or dependency.

## Verification replay

The candidate was replayed locally with Python bytecode writes disabled and
Cargo targets outside the repository:

```text
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/core/test_global_economic_object_nullifier_reference_v2.py \
  tests/core/test_global_economic_object_nullifier_reference_v2_isolation.py
# 31 passed

python3 -B experiments/render_global_economic_object_nullifier_reference_v2_golden.py \
  --check tests/data/global_economic_object_nullifier_reference_v2_golden.json
# exit 0

CARGO_TARGET_DIR=/tmp/zenodex-nullifier-reference-v2-target \
  cargo test --offline --locked \
  --manifest-path zk/global_economic_object_nullifier_reference_v2/Cargo.toml
# 5 integration tests passed; doc tests passed
```

These are local replay results bound by the source/test hashes in the hygiene
packet. They are not a signed execution receipt, RISC0 receipt, release record,
or production claim.

## Dependency decision

The Rust reference reuses the repository-pinned `sha2 = 0.10.9` dependency for
SHA-256. Its tests reuse exact `serde = 1.0.228` and
`serde_json = 1.0.148`; neither parser dependency is linked into the library.
`Cargo.lock` closes the 21-package build/test graph. These versions already
exist in the V1 ABI dependency family, avoiding a second cryptographic or JSON
stack. Cargo metadata reports permissive transitive licenses including MIT,
Apache-2.0, Unlicense, and Unicode-3.0; the unpublished local crate follows the
repository's MIT license. Network-free locked builds, `unsafe_code = forbid`,
strict fixture decoding, Clippy, and fixed vectors constrain the security and
determinism surface.

Removing `sha2` requires supplying an independently reviewed SHA-256 adapter;
Rust's standard library has no SHA-256 implementation. Removing the two test
parser dependencies is possible by replacing the closed fixture decoder with a
locally maintained parser, at the cost of a larger custom attack surface. The
standalone crate can be deleted without affecting runtime because no workspace,
release, proof, or application target depends on it.

## Representation decision

The full sorted archive is accepted only as this bounded oracle. Its witnesses
are linear in archive size and its finite capacity can halt progress, so it is
rejected as an authoritative ABI representation.

The reviewed naïve fixed-depth sparse map is also rejected: a 64-item batch at
256-bit depth carries 524,288 sibling bytes before framing, and an uncompressed
262,144-key persistent tree can exceed the proposed 512 MiB storage budget.

A canonical full-binary Patricia trie remains a research candidate. It needs a
frozen encoding, nonmembership syntax, version-retention contract, durable
layout, guest-cycle measurements, malformed-witness tests, and differential
equivalence against this oracle before selection.

## Nonclaims and residual risk

This slice does not establish object provenance, alias resistance,
collision-resistance beyond the use of SHA-256, an authenticated membership or
nonmembership proof, durable atomic publication, rollback resistance, complete
historical import, migration continuity, writer retirement, outbox delivery,
RISC0 refinement, Tau authority, settlement safety, scalability, liveness, or
production readiness.

Its fixed limits are research-oracle bounds. They are not production capacity
or performance claims.
