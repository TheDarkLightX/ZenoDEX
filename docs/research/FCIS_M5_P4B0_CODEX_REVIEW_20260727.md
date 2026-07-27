# FCIS M5-P4B0 Corrective Review

## Result

```text
reviewed SHA: f6f017cca2257e0873c34a398ee472234a5a3630
evidence-checkpoint verdict: GO
authority-switch verdict: NO-GO
grade: A- (92/100)
```

The corrected P4B0 checkpoint is suitable to retain as honest, source-bound
refinement evidence. It does not authorize P4B, P5, M6, or any mounted authority
change. The artifact remains `BLOCKED` with 21 refining fixtures and three LP
metadata mismatches.

## Grade

| Area | Score | Review conclusion |
| --- | ---: | --- |
| Frozen-design fidelity | 19/20 | Closed bytes-to-owned admission, exact values, code-owned policy, and no-mount boundary are preserved. |
| Authority and provenance binding | 20/20 | Command, pre-state, context, policy, source, artifact, and seven mounted comparison files are bound. |
| Structural and mutation enforcement | 19/20 | Sixty-two named mutants include exact-product substitution, wildcard policy, raw pre-decode inspection, and decoded inspection inside the combinator facade. |
| Semantic evidence | 18/20 | All required shared and exact-only dimensions have executable tests; three LP mismatches remain honestly blocking. |
| Maintainability and reviewability | 16/20 | The dedicated modules are explicit, but the refinement evaluator, schema, admission module, and monolithic structural checker remain large review surfaces. |

## Corrective findings

The first independent review found three blocking classes:

1. structural enforcement did not kill all forbidden admission and policy
   substitutions;
2. an artifact remained valid after mounted comparison source changed;
3. the report and mutation ledger claimed evidence families without direct
   executable witnesses.

The first corrective commit closed source drift and evidence overstatement, and
it killed exact-product and wildcard-policy substitution. A second bounded
review found two surviving placements for manual validation:

```text
raw byte inspection before canonical decode
decoded-value inspection inside _admit_pair_source before combinator dispatch
```

The final checker requires canonical decode to be the first executable ingress
operation and requires `_admit_pair_source` to contain one exact delegation to
the closed combinator. Independent re-review confirmed that the two mutants now
produce:

```text
FCIS_P4B0: decode-admit-prefix-drift:admit_observation_pair_bytes_v1
FCIS_P4B0: closed-engine-facade-drift
```

M61 and M62 preserve both counterexamples. The final bounded re-review found no
new blocker in the corrective delta.

## Evidence

```text
focused P4B0 suite:                         418 passed
mounted/exact LP-duration parity suites:    51 passed
artifact deterministic rebuild:             passed
artifact semantic checker:                  valid, BLOCKED, mount_authorized=false
state-substrate profile:                     ok=true
authority-graph profile:                     ok=true
exact-replay profile:                        ok=true, compatibility findings only
exact-consumers profile:                     ok=true, compatibility findings only
final-mount profile:                         fail-closed, 79 violations
Ruff check and format:                       passed
focused strict mypy:                         passed
git diff --check:                            passed
mounted comparison source byte check:        unchanged
```

The final-mount violations are inherited and remain explicit:

```text
BROAD_ADMISSION             50
SNAPSHOT_SEAL_FLAG          12
OPEN_AUTHORITY_TYPE          5
MUTABLE_BASE                 4
FORBIDDEN_RECONSTRUCTION     4
GENERIC_DEEP_FREEZE          3
COERCIVE_CONTAINER_COPY      1
```

The repository's monolithic structural checker retains 26 pre-existing strict
mypy findings. The corrected P4B0 core, artifact builder/checker, and changed
value tests pass focused mypy. The broad critical quality gate was not promoted
to a pass because `pytest_cov` is unavailable in this environment. No ESSO,
Tau, Lean, RISC0, Rust-parity, production-datastore, crash-recovery, or external
delivery result is claimed by this checkpoint.

## LP mismatch classification

The three mismatches are:

```text
add_liquidity_boundary_valid
add_liquidity_smallest_accepted
create_pool_smallest_accepted
```

All occur at `next_state.lp_balances`. P4A records `src.core.dex.step`, which
does not receive consensus time and therefore preserves pre-existing LP duration
metadata. The mounted integration path applies
`apply_lp_mint_timestamps_after_settlement` with the authoritative block
timestamp before constructing the committed `DexState`. The exact FCIS path
also applies the timestamp as an immutable LP-duration transition.

The existing mounted/exact parity suites passed 51 tests, including first mint,
add/remove sequences, duration-risk grids, rejection precedence, and full
shadow state/root equality. This supports a comparison-boundary correction. It
does not satisfy the frozen P4B0 contract, which explicitly compares the P4A
core-step observation including duration metadata.

## Next safest step

Create a separately versioned mounted-spot refinement checkpoint. Preserve the
P4A and P4B0 artifacts byte-for-byte. The new checkpoint must:

1. define `legacy_core_v1` and `mounted_spot_v1` as distinct source-owned
   comparison profiles;
2. bind consensus time and LP-duration policy in the compared execution
   context;
3. replay create, add, remove, and no-LP-change cases through the mounted
   balance-then-metadata path and the exact immutable transition;
4. compare all eight state fields, effects, rejection precedence, receipt,
   replay, outbox, and roots;
5. include timestamp boundary values `0`, `1`, `700`, and the declared maximum;
6. fail closed on source drift, input substitution, missing metadata updates,
   or any mismatch;
7. keep authority unmounted until the mounted profile refines completely and
   the 79 final-mount violations are removed in a separately reviewed change.

