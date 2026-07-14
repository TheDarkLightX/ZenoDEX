# Spot V7 Governed DA Prerequisite V1

Status: implemented as a private, authority-false integration capability with
focused local evidence. It is not connected to the Spot V7 operational gate or
atomic store.

## Purpose

Spot V7 already has two separate DA facts:

1. The governed full-blob adapter proves that one exact blob and canonical
   certificate satisfy the release-bound operational policy.
2. The sampled-retrievability verifier proves that a bounded quorum of active
   BLS provider identities signed correct deterministic chunk openings for one
   checked epoch.

The prerequisite joins those facts without reopening their raw inputs or
accepting caller-provided `verified` booleans. Both inputs must be exact private
capabilities minted by their existing verifier paths.

```text
governed operational policy capability
        +
governed exact full-blob capability
        +
authenticated sampled-response capability
        |
        v
exact deterministic cross-binding
        |
        v
private Spot V7 DA prerequisite
```

## Positive scope

A successful join establishes only:

```text
governed_exact_full_blob_policy_satisfied = true
authenticated_sampled_response_scoped_to_checked_epoch = true
operational_policy_release_provenance_bound = true
```

The adapter checks exact equality for:

```text
application ID
chain or domain ID
data epoch
checked epoch
retention-through epoch
storage-policy hash
full-blob data root
full-blob chunk root
full-blob certificate root
exact blob SHA-256
```

It independently rederives the existing full-blob target from the exact blob
retained by the governed adapter. This reconstructs the data, ordered-chunk,
and certificate roots under the existing hash domains. The rederived target
must equal both the governed full-blob projection and the authenticated sampled
projection.

The combined projection also retains:

```text
governed full-blob policy root
sampled retrievability policy root
canonical accepted provider IDs
domain-separated accepted-provider-set root
sampled evidence SHA-256
operational-policy provenance root
operational-policy authority-manifest SHA-256
operational-policy signer-registry root
operational-policy signature-quorum report root
operational-policy revision and evaluation epoch
beacon source, policy, epoch, and commitment
```

The accepted-provider-set root commits only to the canonical accepted provider
IDs. It is meaningful only as a field of the complete sealed projection beside
the sampled-policy root, certificate root, checked epoch, and evidence digest.
It is not a standalone provider-registry or availability certificate.

The operational policy and its signer registry must be active at the sampled
checked epoch. The sampled policy's initial and remaining retention minima may
not be weaker than the governed operational-policy minima.

## Preserved non-claims

The Spot V7 operational policy currently governs the full-blob storage policy.
It does not contain a governed sampled-provider registry or a governed beacon
profile. The adapter therefore binds the exact sampled and beacon identities
without promoting their governance provenance.

These facts remain false:

```text
sampled_policy_governance_provenance_verified = false
current_operational_policy_release_head_verified = false
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

The signed response epoch is provider-declared. The sampled verifier checks its
deadline arithmetic and signature, while no finalized external inclusion proof
currently establishes when the response arrived. Distinct provider identities
also do not prove distinct operators or failure domains.

## Construction boundary

The combined class and binder are module-private. The capability is immutable,
non-copyable, non-serializable, and protected by a module-private seal. Its
constructor recomputes the complete projection from the retained prerequisite
objects. Every downstream projection read repeats the fields consumed by this
join and rejects drift. The exact certificate bytes remain authenticated by the
sealed upstream full-blob capability; this join does not reopen or reparse
those bytes.

Raw bytes, mappings, or booleans cannot mint the capability. Python private
objects are an architectural boundary against accidental misuse, not a defense
against hostile code already executing in the same interpreter.

## Remaining production obligations

Before this prerequisite can enter an operational commit gate, Spot V7 needs:

1. release-governed sampled-policy material and provider-key lifecycle;
2. release-governed beacon source and policy plus finalized beacon evidence;
3. a current trusted operational-policy release head, beyond declared
   lifecycle activity at the checked epoch;
4. authenticated response-time or inclusion provenance;
5. an explicit governed rule requiring the sample in addition to exact local
   full-blob persistence;
6. atomic persistence of the sampled evidence digest, provider-set root,
   checked epoch, and relevant policy roots;
7. one end-to-end test joining the real policy-provenance loader, pinned
   full-blob checker, and sampled verifier mint paths;
8. end-to-end replay proving that the exact stored DA facts bind the same
   settlement envelope.

No operational gate or store file is changed by this tranche.
