# FCIS M6 C07 Migration Review Packet Schema V1

## Purpose

This schema defines a review carrier for one exact unmounted R03
representation migration. It is a reproducibility contract. Its values do
not grant migration authority.

## Packet identity

The packet records:

```text
schema_version
status = TESTED / UNMOUNTED
source_head = {commit, tree}
lineage_commits[name] = {commit, tree}
```

Every commit and tree is a lowercase 40-hex Git identity. The local checker
resolves each pair with `git rev-parse` before accepting the packet.

## Migration identity

The migration key is the complete C02 semantic identity:

```text
asset
fee_distribution_domain_id
semantic_profile_id
fixed_role_order_id
```

The migration carrier records:

```text
migration_map_id
activation_sequence
authority_epoch_root
old_state
new_state
entry_mappings
manifest
```

`old_state` and `new_state` each contain the representation ID, canonical
UTF-8 bytes, and state root. Each mapping is keyed by the complete ordered
entry ID and contains source and target three-coordinate vectors. The target
coordinates must equal the componentwise negation of the source coordinates.

The checker reconstructs both exact `EntitlementStateV1` values, verifies
complete ordering and conservation, recomputes canonical bytes and roots,
and requires the C04 transport to accept the pair. It then constructs and
encodes `RepresentationMigrationManifestV1` and decodes those bytes with the
same exact old and new state objects as witnesses.

## Formal evidence binding

The Lean section records the source SHA-256 and selected declaration digests.
For each listed theorem, the digest spans from its `theorem` keyword through
the next listed theorem keyword or the namespace terminator, with CRLF
normalized to LF. Unlisted helper declarations remain part of the span of the
preceding listed theorem when they occur between listed theorems.

This convention preserves the exact C05 receipt surface while making the
selected theorem set explicit.

## Refinement evidence binding

The B09 section records the SHA-256 of:

```text
TASK_B09_PARITY_RESULT.json
TASK_B09_ARTIFACT_INDEX.json
```

It also records vector counts, output digests, and exact-byte parity flags for
the production and denominator-1..12 campaigns. The checker recomputes both
file hashes, binds the parity result to its artifact-index entry, and compares
the packet fields with the result fields.

## Review boundary

The packet is accepted only when every recomputation and digest check passes.
It is evidence for the declared research carriers. It is not a production
authority witness, runtime mount, datastore proof, migration switch, or value
movement authorization.
