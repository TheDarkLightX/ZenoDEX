# FCIS M6 Task C03 Plan

TASK_ID: C03
TITLE: Add canonical state and migration codecs

## Scope

Create typed unmounted values for EntitlementStateV1 and
RepresentationMigrationManifestV1. State roots derive from the complete
canonical state projection. Migration manifest identity fields and both state
roots are computed from the supplied verified old/new state objects.

The wire manifest contains:

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

The constructor has no old_state_root or new_state_root parameter. The decoder
requires exact expected old and new states and compares every wire projection
to those states. A caller-provided root is a check value and never an
authority source.

## Fail-closed boundaries

- Supported representation IDs are exactly SRGD and AGQE.
- State entries are an exact, bounded, strictly ordered tuple.
- Every coordinate is an exact bounded integer and each entry conserves to zero.
- Unknown schema versions, unknown envelope/value fields, missing fields,
  duplicate JSON fields, noncanonical bytes, wrong types, and root mismatches
  return typed C03 rejection values.
- Manifest decoding without the verified transported states rejects.

## Nonclaims

C03 does not transport entries, prove trace conjugacy, authenticate the
authority epoch root, mount a datastore, or move value. C04 owns sign-dual
transport and complete entry equality.
