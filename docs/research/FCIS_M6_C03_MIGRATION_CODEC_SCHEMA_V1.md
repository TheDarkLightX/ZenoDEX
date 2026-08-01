# FCIS M6 C03: Entitlement State and Migration Manifest Schema V1

Status: TESTED / UNMOUNTED

## EntitlementStateV1

The canonical state contains:

~~~text
key: EntitlementKeyV1
representation_id: srgd-deficit/v1 | agqe-surplus/v1
entries: ordered tuple of (entry_id, coordinates[3])
~~~

Entry IDs are exact bounded strings. Coordinates are exact integers in the
bounded residual domain [-9999, 9999] and conserve to zero per entry. Entries
are strictly ordered by the UTF-8 bytes of entry_id, with no duplicate or
surplus entry ambiguity.

The canonical state envelope is versioned as:

~~~text
zenodex/fcis/entitlement/state/v1
~~~

The state root is:

~~~text
state_root = sha256(canonical_state_envelope)
~~~

The root commits the complete entry set, key, representation, order, and
coordinates.

## RepresentationMigrationManifestV1

The wire manifest fields are exactly:

~~~text
old_semantic_key
new_semantic_key
old_representation_id
new_representation_id
old_state_root
new_state_root
migration_map_id
authority_epoch_root
activation_sequence
~~~

The in-memory value stores verified old_state and new_state objects plus the
migration map ID, authority epoch root, and activation sequence. The four
identity projections and both state roots are read-only derived properties.
There is no constructor field named new_state_root or old_state_root.

The manifest envelope is versioned as:

~~~text
zenodex/fcis/entitlement/representation-migration/v1
~~~

Decoding requires expected_old_state and expected_new_state. The decoder
recomputes both roots and rejects a wire root that differs. It also rejects
wire semantic keys or representation IDs that differ from the expected states.
This is the C03 boundary that prevents a caller from minting a root by placing
it in a manifest.

The authority epoch root is format-checked as a 32-byte digest. Authentication
and authority provenance remain an outer verifier obligation.

## Evidence boundary

The deterministic vector records exact old/new state bytes, derived roots, and
manifest bytes. Focused negative tests cover schema/field/version drift,
duplicate fields, noncanonical bytes, missing verified states, root
replacement, wrong representations, and entry ordering. No runtime caller,
datastore adapter, authority switch, deployment, or value-moving path is
mounted.
