# FCIS M6 C06: Rotation and Reset Mutation Schema V1

Status: TESTED / UNMOUNTED

## Ordinary rotation

`C06RotationSnapshotV1` groups a complete `EntitlementStateV1` with typed
operational configuration:

```text
policy_weights
destinations
custody_account
```

`check_rotation_preserves_history_v1` accepts a before/after pair when the
state key, representation, and complete ordered entry tuple are identical.
Configuration may change. Key substitution, representation substitution, and
history erasure return distinct typed rejection codes.

## Migration authority comparison

`C06AuthorityContextV1` carries a deployment ID, an authority epoch root, and
the complete state. The check requires:

```text
source deployment = current deployment
target deployment = current deployment
source authority epoch = current authority epoch
source state = current state
target state = exact C04 sign-dual transport(source state)
```

The target authority epoch may advance as a migration result. The accepted
value is explicitly a check result and is not a production authority witness.

## Mutation boundary

The permanent tests retain witnesses for policy/destination/custody rotation,
representation migration, zero reset, partial entry sets, and cross-deployment
substitution. No runtime or value-moving path is mounted.
