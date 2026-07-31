# FCIS M6 Task B09 three-way parity plan

## Hard-stop scope

- Base head: B08 receipt commit aca4c441aef978ee74d145202c55c556700cbfa3.
- Changed surfaces: parity harnesses and B09 evidence only.
- Authority: Python apply_fee_apportionment_v2 remains the executable
  reference for production-D output; Rust is called through a standalone
  harness; Julia independently recomputes arithmetic and canonical bytes.
- Mount status: all three lanes remain unmounted research evidence.
- No settlement, datastore, authority, migration, effect, API, deployment, or
  value-moving path is changed or enabled.

## Input/output protocol

The production harness uses eight tab-separated fields:

~~~text
id, domains, assets, contribution_amounts, weights, destinations,
deficit_buyback, deficit_treasury
~~~

domains, assets, and contribution_amounts are aligned lists. Domain and asset
lists use a semicolon between candidate keys; amounts use a comma. This
preserves both one-key adaptive vectors and the existing grouped multi-key
fixture. Generated identifiers are ASCII and exclude tabs, pipes, commas, and
semicolons.

Accepted records are pipe-separated:

~~~text
id|A|fractions|bonuses|role_amounts|post_deficits|state_hex|
allocation_hex|result_hex|result_sha256
~~~

When multiple grouped allocations exist, the first four semantic fields use a
semicolon between allocations and a comma between the three roles. Full
canonical bytes are hex encoded so the comparison is independent of terminal
rendering. Rejected records include the exact rejection code and slash-joined
path.

The small-domain lane uses a separate eight-field arithmetic protocol and
compares semantic output only. It does not claim a runtime-configurable
production denominator.

## Required campaigns

1. Re-run all 12 existing shared Python/Rust vectors, including the grouped
   multi-key and aggregate-overflow cases.
2. Generate production-D vectors for zero, one atom, D-1, D, D+1, 2^128,
   2^255, U256_MAX-1, and U256_MAX, plus aggregate overflow.
3. Generate 1,000 adaptive-policy steps at production D=10,000; each step's
   pre-deficit is the prior accepted post-deficit.
4. Exhaust every denominator 1 <= D <= 12, every nonnegative weight triple
   summing to D, every amount 0 <= amount <= D, and every valid three-role
   deficit tuple strictly inside (-D,D) with zero sum. Compare the independent
   Python arithmetic reference and Julia oracle.

## Comparison law

For every production vector:

~~~text
Python decision == Rust decision == Julia decision
Python reject code/path == Rust reject code/path == Julia reject code/path
Python allocations/fractions/bonuses/post-deficits == Rust == Julia
Python canonical state/allocation/result bytes == Rust == Julia
Python result digest/root == Rust == Julia
~~~

Any missing line, malformed field, duplicate ID, solver/tool failure, or
mismatch fails the campaign.

## Evidence retention

The generated corpus is compressed with deterministic gzip level 9. The
artifact index records each compressed SHA-256, decompressed SHA-256, and byte
count. The parity result records the exact campaign counts and shared output
digest.

## Nonclaims

- The parity harness does not mount the kernel into a runtime, datastore,
  authority switch, migration, effect worker, or value-moving path.
- Agreement cannot prove requirements completeness or economic correctness.
- Small-domain evidence is a parameterized arithmetic reference only; the
  production Rust profile remains fixed at D=10,000.
- The Rust carrier remains BigUint; B09 does not prove a fixed-width U256
  implementation.
- No remote publication, CI, draft PR, or production promotion is included.
