# FCIS M5-P4B1 Mounted LP Refinement Report

## Result

```text
outcome: M5_P4B1_COMPLETE_UNMOUNTED
scoped refinement: 24 / 24
authority switch: prohibited
next checkpoint: P4B2 final-mount migration
```

P4B1 closes the three LP-state mismatches reported by P4B0. The mismatch was
caused by the frozen comparison boundary: P4A observed `src.core.dex.step`,
which has no consensus-time input, while the mounted integration applies LP
duration metadata after the accepted settlement and before constructing the
committed `DexState`.

This checkpoint composes with P4B0. P4B0 remains the evidence for command,
settlement, economic output, patch, replay, receipt, outbox, bundle, and
rejection comparison. P4B1 checks the missing accepted post-validation
transition:

```text
validated settlement
-> balance, pool, and LP amount transition
-> consensus-time LP metadata transition
-> nonce and fee transition
-> one eight-field successor state
```

It does not claim full `apply_ops` ingress parity, proof-verifier parity,
datastore linearizability, or mounted FCIS authority.

## Scope

The source-owned profile evaluates six fixtures:

```text
create pool
small and boundary add liquidity
small and boundary remove liquidity
swap with no LP delta
```

Each fixture is evaluated at:

```text
0
1
700
2^63 - 1
```

The final value is an explicit P4B1 evidence-profile bound. It does not alter
the mounted execution-context schema.

Every row binds canonical command bytes, the exact pre-state snapshot, the
explicit execution context, the independently derived settlement, all eight
logical committed-state fields, the canonical successor snapshot, the state
root, and the exact support root. Mounted and exact inputs are constructed from
separate fixture graphs.

## Changed

- `tools/build_fcis_m5_p4b1_mounted_lp_refinement.py` builds and independently
  rechecks the source-bound artifact.
- `tests/integration/test_fcis_m5_p4b1_mounted_lp_refinement.py` supplies parity,
  boundary, and mutation-killing evidence.
- `docs/research/FCIS_M5_P4B1_MOUNTED_LP_REFINEMENT_V1.json` records 24 exact
  rows and the source hashes used to derive them.

No file under `src/` changed. P4A and P4B0 inputs remain byte-for-byte intact.

## Invariant and authority impact

The checkpoint establishes this scoped implication:

```text
P4B0 accepted settlement and shared-observable refinement
and
P4B1 same canonical input plus mounted consensus-time metadata sequence
imply
mounted successor snapshot = exact FCIS successor snapshot
```

Equality covers:

```text
balances
pools
LP balances plus mint and duration-risk metadata
nonces
vault
oracle
fee accumulator
perps
```

The artifact always records `mount_authorized: false`. Its checker rejects a
changed result even when the attacker recomputes the outer artifact hash.

## Evidence

```text
P4B1 focused suite:                         9 passed
P4B1 plus mounted/exact LP regressions:    60 passed
P4B1 deterministic artifact rebuild:       passed
P4B1 scoped rows:                           24 refine, 0 mismatch
Ruff check and format:                      passed
focused mypy:                               passed
state-substrate profile:                    ok=true
authority-graph profile:                    ok=true
exact-replay profile:                       ok=true, compatibility only
exact-consumers profile:                    ok=true, compatibility only
final-mount profile:                        fail-closed, 79 violations
security red-flag scan:                     0 findings
git diff --check:                           passed
```

The mutation suite rejects:

```text
omitted mounted LP timestamp transition
cross-side command substitution
independently rehashed state-root fabrication
independently rehashed row deletion
```

## Commands not run

The broad critical gate remains unavailable in this worktree because its
coverage plugin is missing. ESSO, Tau, Lean, RISC0, Rust parity, production
datastore, crash recovery, and external delivery were outside this bounded
Python comparison checkpoint.

## Residual risk

The final-mount profile still reports 79 violations across legacy admission,
mutable subclass snapshots, seal flags, generic deep freeze, coercive copies,
open authority types, and broad validation in mounted consumers. P4B1 neither
removes nor suppresses them.

The evidence builder mirrors the accepted post-validation section of the
mounted integration. It is protected by source hashes and mutation tests, but
it is not a proof that the full integration entrypoint binds authentication,
proof verification, and settlement selection identically.

## Next safest step

P4B2 should migrate the final mounted authority surface in deletion-oriented
batches. Start with `src/state/legacy_state_snapshots.py`, replacing its mutable
subclasses, generic freezing, reconstruction hooks, and seal flags with the
existing exact committed values and closed admission functions. Then remove the
remaining mounted consumer violations without weakening the checker. Authority
may switch only when:

```text
final-mount violations = 0
P4B0 and P4B1 artifacts rebuild exactly
all mounted/exact semantic rows refine
the mounted dispatch imports only the reviewed exact authority path
```
