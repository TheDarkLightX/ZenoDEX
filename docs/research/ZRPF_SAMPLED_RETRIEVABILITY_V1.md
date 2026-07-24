# ZRPF Authenticated Sampled Retrievability V1

Status: implemented as an application-neutral bounded verifier profile with
focused local evidence. It is not connected to settlement admission.

## Exact claim

A successful verification establishes the following scoped statement:

> At least the policy threshold of distinct provider identities signed exact
> responses scoped to the declared checked epoch and deterministic challenges.
> Every response carries valid chunk openings against the exact ordered
> chunk-hash commitment of the expected full-blob V1 certificate, and its
> declared response epoch is within the policy window.

The result exposes this fact as:

```text
authenticated_sampled_response_scoped_to_checked_epoch = true
```

The claim is a bounded sample at one epoch. The following remain false:

```text
governed_policy_provenance_verified = false
governed_beacon_provenance_verified = false
beacon_unpredictability_verified = false
response_timing_provenance_verified = false
provider_independence_verified = false
continuous_availability_verified = false
public_future_availability_verified = false
release_authority = false
settlement_authority = false
production_authority = false
```

Distinct provider keys do not prove distinct operators, hardware, networks, or
failure domains. A successful sample also does not prove that unchallenged
chunks remain available after the checked epoch.

The provider signs its declared response epoch and deadline. This module does
not supply an externally finalized timestamp or inclusion proof showing when
the response was transmitted. The positive result therefore means the signed
sample is exactly scoped to the checked epoch and satisfies its declared
deadline arithmetic. A production adapter must separately authenticate timely
inclusion before treating that scope as historical timing evidence.

## Authority progression

```text
explicit expected policy, full-blob target, beacon, and checked epoch
    -> bounded exact canonical evidence bytes
    -> exact response bytes
    -> deterministic challenge recomputation
    -> exact challenged chunk openings
    -> provider lifecycle checks
    -> BLS response-envelope verification
    -> distinct active-provider quorum
    -> process-local authenticated sampled result
```

The expected policy, full-blob target, beacon, and checked epoch are trusted
expectations supplied by the caller. This V1 module does not authenticate their
governance provenance. A future release adapter must bind them to independently
governed roots before the result can enter an operational gate.

## Existing full-blob ABI

The profile preserves `full_blob_da_v1` without changing its certificate or
hash ABI. It independently reproduces these domains:

```text
zenodex.zrpf.full_blob_da.data_root.v1
zenodex.zrpf.full_blob_da.chunk.v1
zenodex.zrpf.full_blob_da.chunk_root.v1
zenodex.zrpf.full_blob_da.certificate_root.v1
```

The existing `chunk_root` is an ordered commitment over all chunk hashes. It is
not a Merkle root. Consequently, V1 evidence carries one exact bounded ordered
chunk-hash vector. The verifier recomputes the existing root, and every signed
provider response binds the vector digest plus only that provider's challenged
chunk bytes.

The protocol maximum is 128 chunk hashes, so the vector is at most 4 KiB before
canonical JSON framing. This avoids changing an authenticated certificate ABI
while retaining exact sampled openings.

## Deterministic challenges

For provider `p`, challenge slot `s`, and retry counter `a`, the candidate is:

```text
x = SHA256(
    domain
    || beacon commitment
    || beacon source and policy roots
    || beacon epoch
    || retrievability policy root
    || full-blob certificate root
    || provider identity
    || s
    || a
)
```

The verifier uses rejection sampling to avoid modulo bias. A candidate is
accepted only when it is below the largest multiple of the chunk count that
fits in 256 bits. Repeated indices for the same provider are retried. The retry
budget is 4,096 attempts per slot, and failure rejects.

The beacon epoch must equal the checked epoch. The policy binds the expected
beacon source and beacon policy roots. The V1 verifier does not prove that the
beacon was unpredictable, unbiased, final, or governance-authorized.

## Signed provider response

Each canonical response binds:

```text
application_id
chain_or_domain_id
epoch_id
certificate_root
data_root
chunk_root
storage_policy_hash
retention_through_epoch
retrievability policy_root
beacon source, policy, epoch, and commitment
checked_epoch
response_deadline_epoch
response_epoch
provider_id and key_id
deterministic assigned_chunk_indices
ordered chunk-hash-vector digest
exact challenged chunk openings
```

The exact response bytes are domain-hashed, then authenticated using the
existing BLS12-381 G2-Basic signed-artifact envelope verifier. The only shared
signature capability extension is one closed payload-kind identifier:

```text
zrpf_sampled_retrievability_response
```

Signature algorithms, envelope framing, key encoding, and BLS verification are
unchanged.

## Provider lifecycle and quorum

Each provider key has a half-open active interval:

```text
[activation_epoch, revocation_epoch)
```

The key must be active at both the checked epoch and its response epoch. One
provider may rotate keys only through non-overlapping intervals. Provider/key
pairs and public keys must be unique. A provider identity counts at most once
toward quorum, independent of key rotations.

The retrievability policy must also remain active at both the checked epoch and
each accepted response epoch. A response cannot extend authority past a
half-open policy revocation boundary.

The response deadline is derived as:

```text
deadline = checked_epoch + response_window_epochs
```

The response epoch must lie in the closed interval from the checked epoch to
the deadline. The full-blob retention horizon must cover:

```text
blob epoch + minimum initial retention
checked epoch + minimum remaining retention
response deadline
```

All arithmetic is checked against `u64` bounds.

## Bounds

```text
full blob bytes                 <= 8 MiB
full-blob chunks                <= 128
provider lifecycle records      <= 8
challenges per provider         <= 8
response window                 <= 64 epochs
one exact response              <= 2 MiB
one exact evidence object       <= 20 MiB
challenge retries per slot      <= 4,096
```

The provider and evidence bounds are joint. An exact response with eight
maximum-size chunk openings is approximately 1.1 MiB before the outer evidence
encoding. The eight-provider ceiling keeps a maximum-opening quorum
representable inside the 20 MiB exact-evidence cap. Larger provider registries
must use a future evidence encoding that avoids duplicating hex-expanded
response payloads.

The evidence parser rejects non-ASCII JSON, duplicate keys, floating-point or
non-finite values, unknown fields, noncanonical encoding, oversized input, and
integer substitutions for authority booleans.

## Current integration boundary

This implementation does not modify the Spot V7 operational policy capability,
full-blob certificate, atomic store schema, or settlement gate. The separate
private `zrpf_spot_v7_governed_da_prerequisite` adapter now closes the exact
bridge from a governed full-blob result to this sampled-result projection. It
retains the existing operational-policy release provenance and cross-binds the
application, domain, certificate, data, epoch, retention, provider-set result,
and sampled-evidence digest.

Operational use still requires independently authenticated:

1. retrievability policy provenance and lifecycle;
2. beacon source, policy, commitment, and finality provenance;
3. a store field for the exact sampled evidence digest and checked epoch;
4. explicit operational policy deciding whether sampling is mandatory in
   addition to exact local full-blob persistence.

Until those boundaries exist, this profile supplies cryptographic sampled
evidence and no settlement authority.
