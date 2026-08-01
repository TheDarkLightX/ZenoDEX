# FCIS M6 Task C01 Plan

TASK_ID: C01
TITLE: Factor semantic profile from representation

## Scope

Use the existing immutable M6 profile registry as the single source for the
semantic entitlement profile and its representation labels. Add the durable
schema note that fixes their meaning and records the boundary to C02.

The semantic profile is:

~~~text
adaptive-global-quota-entitlement/three-role/v1
~~~

The supported representation codecs are:

~~~text
srgd-deficit/v1
agqe-surplus/v1
~~~

The two codecs describe the same transition relation. Their state coordinates
are related by `sigma = -d`; changing the codec label must not create a new
entitlement history or reset a state coordinate.

## Existing implementation consumed by C01

`src/core/fcis_m6_profile_ids.py` was frozen by A02 and already contains the
canonical values. Its focused tests cover exact values, representation/semantic
aliasing, duplicate representation IDs, fixed role order, domain collisions,
and C3 claim-key duplication. C01 does not create a second identifier module.

## Boundary to C02

C01 fixes the identity vocabulary and semantic/representation distinction.
C02 owns the concrete entitlement-key value and its executable rotation
mutants. The C02 key must include the semantic profile and fixed role order,
while excluding the representation codec and rotatable policy dimensions.

## Nonclaims

This task does not add a migration executor, authority witness, datastore
schema, production caller, runtime state key, or value-moving path.
