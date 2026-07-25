# FCIS aggregate perps market-replacement review

## Reviewed source

- Repository: `TheDarkLightX/ZenoDEX`
- Branch: `agent/fcis-pr454-reviewed-port-20260723`
- Exact implementation commit:
  `510925c722fe02635ec477c3c74d48d02008db11`
- Scope: one unmounted pre-M5/M2 exact aggregate transition that replaces one
  committed perps market and returns one canonical compare-and-replace patch.

## Verdict

`GO` for the bounded, unmounted aggregate leaf.

`NO-GO` for M5 mounting, production authority, PR478 effect work, datastore
commit claims, or value-moving parallel execution.

## Defects found during review

### 1. Shallow pre-state validation violated the same-candidate law

The first implementation called `CommittedPerpsStateV1.__post_init__()` and
then looked up the expected market through `OwnedMapV1._index`, while candidate
reconstruction iterated `OwnedMapV1._entries`.

A trusted corruption fixture could rename the market in `_entries` while
leaving `_index` unchanged. The transition returned `Ok`; its patch targeted
`isolated`, while its returned state contained `tampered` and no `isolated`
market.

This was a blocking defect for the slice.

### 2. Nested owned-map corruption was accepted

The aggregate and market `__post_init__` methods checked domain fields from
entries, but did not establish entry/index coherence for every nested
`OwnedMapV1`. Corrupt nested indexes therefore crossed the transition.

### 3. The public success constructor did not enforce same-candidate identity

An exact state and an unrelated exact patch could be combined into
`PerpsAggregateTransitionOkV1`. A later consumer could have treated that
syntactically valid result as authority.

### 4. Tests masked a fresh-process import cycle

The test module imported a core module before the new aggregate module. That
preloaded the inherited eager `src.core` facade. A fresh process importing the
aggregate module first failed through a partially initialized
`state_snapshot_values` cycle.

### 5. The authority checker did not scan the new module

The checker could report `ok: true` without applying its authority rules to
`src/state/perps_aggregate_transitions.py`.

## Repair

- Pre-state, expected market, replacement market, and final candidate now pass
  through the closed `snapshot_perps` schema admission path.
- Re-admission reconstructs owned values and rejects entry/index drift at every
  nested map.
- Patch application rebuilds the returned patch from the exact replacement
  object extracted from the admitted candidate.
- `PerpsAggregateTransitionOkV1` checks that its patch replacement is the
  identical object stored at the patch key in its returned state.
- Permanent negative tests cover aggregate entry/index divergence, nested
  index divergence, corrupt replacement candidates, stale expected values,
  exact-type subclasses, and rejection no-output.
- Differential tests compare the exact result against legacy-to-snapshot
  expected state for isolated, 2-party, 3-party, and N-party markets.
- A v4 isolated-market acceptance and variant-mismatch edge is covered.
- A subprocess test proves standalone import without prior core bootstrap.
- The authority checker default inventory now includes the aggregate module,
  with a regression test for that inventory.

## Grades

| Surface | Grade | Reason |
| --- | --- | --- |
| Bounded leaf architecture | A | Closed admission, exact values, typed reject, same-candidate binding, no effects |
| Adversarial evidence | A | Original counterexample is permanent; nested and constructor variants are covered |
| Differential evidence | A- | All four variants and v4 are covered against the legacy snapshot reference |
| Production integration | C / blocked | The leaf is intentionally unmounted and has no atomic shell commit evidence |
| Overall bounded-slice grade | A- | Ready to retain as pre-M5/M2 infrastructure under its explicit nonclaims |

The initial unchecked implementation would have received a failing grade
because it returned success for the entry/index divergence witness.

## Evidence

- Focused aggregate tests: `19 passed`.
- Full state suite: `508 passed`.
- Authority-checker tests: `109 passed`.
- Authority checker: `ok: true`; the aggregate module appears in
  `checked_paths`.
- Packet checker: `39` requirements, `103` declared and bound test IDs,
  `errors: []`.
- Critical quality gate:
  - acceptance TCB: `539 passed`;
  - critical suite: `782 passed`;
  - all declared branch-coverage floors passed.
- Production-boundary audit: `ok: true`.
- Ruff `0.15.13`, focused mypy, compilation, formatting, and
  `git diff --check`: passed.
- Independent context-drift review: `GO`; no remaining P0/P1 defect in this
  bounded slice.

## Remaining nonclaims

- The exact support-root reader still shares derivation with the legacy mixed
  helper, so independent M4 support-root parity remains open.
- ESSO supplied deterministic design recommendations and obligations. It did
  not prove project semantics or generate the implementation.
- No expected-root datastore compare-and-swap, receipt, nonce, authoritative
  effect, outbox, crash-recovery, Rust-refinement, or release claim is made.
- The production assurance profile remains blocked.

## Implementor rules retained from this review

1. A committed record's `__post_init__` is not a substitute for closed,
   recursive re-admission when owned-container corruption is representable.
2. Never validate through one representation and construct authority from a
   second representation unless their equivalence is checked first.
3. A success aggregate must enforce that every returned authoritative output
   derives from the same candidate object graph.
4. Add new authority modules to the checker inventory in the same change.
5. Run a fresh-process import test when a module participates in an inherited
   package cycle.
6. Preserve M5, shell, effect, and release nonclaims until their separate
   contracts and evidence lanes close.
