# FCIS M6 C04: Exact Sign-Dual State Transport V1

Status: TESTED / UNMOUNTED

## Relation

For each ordered entry in a complete SRGD state:

```text
target.coordinates = (-source.coordinates[0],
                      -source.coordinates[1],
                      -source.coordinates[2])
```

The target keeps the exact `EntitlementKeyV1`, changes the representation ID
from `srgd-deficit/v1` to `agqe-surplus/v1`, and contains the same ordered
entry IDs with no omission or addition. The inverse function applies the same
coordinate negation from AGQE to SRGD. Therefore the executable map is
involutive on valid complete states.

## Admission and comparison

The source and any supplied target are exact `EntitlementStateV1` values and
are revalidated before comparison. A supplied target must have the expected
direction-specific representation and source key. Its ordered entry-ID tuple
must equal the source tuple. Each coordinate must equal the derived negation.

Missing, surplus, reordered, or otherwise divergent entries reject.

An all-zero target entry replacing a nonzero source entry is classified as
`zero_reset`. The classification preserves a minimized witness for the
history-erasure mutant while still allowing the mathematically correct
transport of an actually zero source entry.

## Evidence boundary

The retained vector records complete old/new canonical state bytes, both state
roots, and every entry mapping. Focused tests cover involution, key and
representation substitution, missing and surplus entries, coordinate drift,
zero reset, wrong types, and empty-state behavior. This is a functional-core
research verifier. It has no authority constructor, runtime adapter,
datastore, migration switch, or value-moving caller.
