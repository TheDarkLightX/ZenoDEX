# FCIS M6 K02 unique publication capability

K02 defines one research publication capability with the following boundary:

```text
publish_v1(unique_port, immutable_port_state, immutable_publication_request)
  -> newly_committed(next_state, response)
  | already_committed(same_state, response)
  | typed_reject
```

The request must contain only an exact `D08CombinedANFAcceptV1` verifier
witness. That witness owns the complete `PublicationAtomV1`, including commit
identity, expected pre-state root, successor state root, authority epoch root,
outbox/effect contents, and contiguous sequence. K02 revalidates D08 verifier
provenance and derives all request fields from the owned atom. The port
recomputes a request fingerprint from all of these derived fields. A
same-identity/same-fingerprint retry
returns `ALREADY_COMMITTED`; a same-identity/different-fingerprint request
returns `COMMIT_COLLISION`.

The port state is immutable and uses one-based commit sequence values. A new
commit advances the head root and sequence in one returned value. Rejection
returns no successor state. The port identity
is a module-owned singleton constructed with a controlled token; direct caller
construction and arbitrary capability objects reject.

## Dependency policy

The companion dependency-rules JSON names the unique port module, forbidden
side-effect imports and effects for core modules, required verified input
fields, and allowed effect-shell roots. K03 is responsible for enforcing those
rules with syntax-aware Python/Rust checks.

## Evidence boundary

K02 is an unmounted research model. The singleton is a Python capability
discipline, not a production security primitive. It does not implement a
database transaction, prove datastore atomicity, prove deployment reachability,
seal every legacy path, or authorize value movement. A production refinement
must preserve the same input witness, single-port topology, CAS/head binding,
and typed rejection behavior.
