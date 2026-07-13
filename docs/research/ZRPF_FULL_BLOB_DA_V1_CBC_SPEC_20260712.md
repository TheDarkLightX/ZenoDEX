# ZRPF Full-Blob Data Content Certificate V1 CBC Specification

Date: 2026-07-12

Status: proof-neutral full-blob content binding, governed local policy checking,
and bounded local V6 atomic persistence implemented; replication and public
retrievability pending

## Scoped claim

The V1 object binds one complete, nonempty byte string of at most 8 MiB to one
application, chain/domain, epoch, data-schema identifier, storage-policy hash,
and retention epoch.

```text
exact blob bytes
  -> length-bounded data root
  -> ordered 64 KiB chunk hashes
  -> chunk root
  -> fixed-field certificate root
```

The blob content checker recomputes the full data root and every chunk hash.
It returns a private `ValidatedFullBlobContentV1` only when the supplied bytes
match the certificate exactly.

## Canonical hash contracts

All hash domains use a big-endian `u16` length prefix. Integer fields use
fixed-width big-endian encoding.

```text
data_root = H(domain, blob_length_u64, exact_blob_bytes)

chunk_i = H(
    domain,
    chunk_index_u32,
    chunk_length_u32,
    exact_chunk_bytes,
)

chunk_root = H(domain, chunk_count_u32, chunk_0, ..., chunk_n)
```

The certificate root commits, in order:

```text
certificate_version
application_id
chain_or_domain_id
epoch_id
data_schema_id
data_root
blob_length
chunk_size
chunk_count
chunk_root
retention_through_epoch
storage_policy_hash
```

The chunk size is exactly 65,536 bytes. The maximum blob has 128 chunks. The
last chunk may be shorter. Empty blobs, excess bytes, inconsistent chunk
counts, stale versions, reversed retention, substituted derived roots,
trailing bytes, and noncanonical Postcard encodings reject.

## Authority boundary

`FullBlobDataAvailabilityCertificateV1` is a content commitment. It does not
prove that any storage provider retained the bytes. The content-validated type
also supplies no persistence or ledger authority.

The source-opened Spot V6 settlement guest derives this certificate over the
exact reconstructed replay bytes and commits it through the authenticated
settlement certificate and admission journal. SQLite schema V4 persists the
exact replay bytes, certificate bytes, settlement receipt, guest input,
admission journal, certificate, effect plan, and replay indexes in one local
`BEGIN IMMEDIATE` transaction:

```text
validate exact blob content
persist exact blob bytes
persist certificate root
persist settlement certificate and replay indexes
commit all or roll back all
```

Restart validation rehashes the replay bytes and certificate, revalidates their
content relation, and checks their one-to-one association with the authenticated
V6 settlement statement. This is local content persistence evidence. It does
not show that a ZenoLedger validator set, storage provider, or remote reader can
retrieve the bytes.

A public availability claim additionally requires a governed replication or
chain-native DA policy, provider/validator evidence, retrieval tests, and a
retention enforcement mechanism. Those layers must bind this exact certificate
root.

## Governed local policy check

`LocalFullBlobPolicyV1` defines a proof-neutral, fail-closed check over one
exact blob that is present in the checker invocation. The policy binds:

```text
policy_version
application_id
chain_or_domain_id
data_schema_id
expected_storage_policy_hash
minimum_retention_epochs
minimum_remaining_epochs
maximum_blob_bytes
```

Its `policy_root` hashes those fixed-width fields in that order under
`zenodex.zrpf.local_full_blob_policy.root.v1`. The maximum must be in the
closed interval `1..=8 MiB`.

The checker receives the policy, certificate, exact blob bytes, the certificate
epoch expected by the consuming transition, and a checked epoch supplied by a
governed caller. It independently verifies:

```text
certificate self-consistency
exact application, domain, schema, and storage-policy scope
certificate epoch equals the consuming transition epoch
checked epoch is not before the certificate epoch
certificate blob length is within the policy maximum
retention_through_epoch >= certificate_epoch + minimum_retention_epochs
retention_through_epoch >= checked_epoch + minimum_remaining_epochs
exact bytes reproduce the certificate data and chunk roots
```

All epoch additions are checked. Overflow rejects. The API contains no
caller-provided acceptance Boolean and returns only `Result<(), E>`.

A successful check establishes the scoped fact
`local_full_blob_policy_satisfied` for the exact bytes and epochs supplied in
that invocation. The checked epoch and retention metadata remain inputs. This
checker does not authenticate a ledger cursor and does not prove that the
declared future retention will occur. Policy provenance and governance are also
external: successful evaluation does not establish that the supplied policy is
the policy authorized by a ledger, release, or consensus process.

## Evidence

The protocol tests provide:

- independent data, chunk, and certificate hash mirrors;
- every-byte mutation rejection over a bounded corpus;
- exact one-chunk/two-chunk boundary coverage;
- empty, oversized, and reversed-retention rejection;
- exact codec round trip and every-prefix truncation rejection;
- unknown-field, stale-version, count, and root substitution rejection;
- a coherent certificate for different bytes that fails exact content
  validation;
- a compile-fail check preventing direct construction of the validated type;
- an independent local-policy-root mirror and separation of every policy field;
- application, domain, schema, storage-policy, and epoch substitution rejection;
- local blob mutation and policy byte-cap rejection;
- exact-boundary acceptance for both retention horizons;
- initial and remaining retention-horizon rejection, including both overflow
  paths.

The V6 integration tests additionally cover atomic association with the exact
receipt and admission journal, exact retry, restart reconstruction,
concurrency, deletion downgrade, and persisted replay/certificate mutation.
The final retained real settlement-receipt record remains a separate evidence
gate.

## Explicit non-claims

V1 supplies no provider signature, replica quorum, erasure coding, sampling,
network retrieval, consensus replication, externally anchored retention,
general-purpose durable availability service, settlement authority, release
authority, external finality, privacy, throughput, or production authority.
The source-opened V6 profile's guest and local atomic store do not promote the
content certificate into a provider-retrievability or availability claim.
