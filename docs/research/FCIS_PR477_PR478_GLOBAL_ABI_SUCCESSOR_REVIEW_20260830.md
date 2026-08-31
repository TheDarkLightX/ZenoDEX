# FCIS PR 477 and PR 478 Global ABI Successor Review

Status: `RESEARCH_ONLY_EXACT_SUCCESSOR_DISPOSITION`

## Result

PR 477 and PR 478 remain unsuitable for merge at their current heads. Their
useful objective is now implemented through the admitted Whole-Program Plan
V2.1 seam, `GlobalSettlementABI V1`, rather than through the historical
mutable-table and mutable-record inheritance designs.

The exact successor implementation is:

```text
base:   484f09a528d5a7f2aff99e9d0b50b67d95ae3b42
commit: efcf1ca1f496343e984c1ccdfa813b3eab8de3ed
tree:   4ee98361f6b98a68f3e9bcc767ea1de92829c625
gate-compatibility commit: c50985e92730f5d99da5cb0ac10dc679d6b23d54
gate-compatibility tree:   561f246ea18e798e812ce176e824b05eb853c5b0
```

The implementation enforces exact primitive, exact tuple, exact nested-record,
outer snapshot, and accepted-effect ownership at the global settlement seam.
It preserves eight minimized subclass and behavior-hook counterexamples. This
is successor-bound repair evidence; it does not close a finding at either
historical PR head.

## PR disposition

| PR | Current exact head | Disposition |
| --- | --- | --- |
| 477 | `576c7bb8a61012858db14d7d1092244ed4e9f2b3` | Preserve as a historical donor. Do not merge or mount its pre-M5 shadow state model. |
| 478 | `6dbb9b36237d982515777caae04a296d0ebac040` | Supersede. Its mutable-base frozen subclasses and stale stack must not be rebased as the authority design. |

The machine-readable successor mapping is
`FCIS_PR477_PR478_FINDING_DISPOSITION_V1.json`. It classifies every one of the
34 audit findings exactly once without modifying their historical `OPEN`
statuses.

## What the successor changes

- scalar fields require exact `str`, `int`, and `bool` values before behavior;
- canonical mappings and sequences require exact built-in containers;
- nested state, effect, registry, lane, terminal, and outbox records require
  exact declared types before key access or canonical projection;
- state, effect, occurrence, lane-journal, and route-journal snapshots reject
  outer subclasses before dataclass reflection or reconstruction;
- accepted and rejected transitions require exact effect-plan types;
- public factories reject subclass dispatch and return only exact declared
  values;
- rejection remains pre-root equal to post-root with an empty effect plan;
- diagnostics added by this repair do not include attacker-controlled class
  names or representations.

## Retained counterexamples

The new test file retains these failure families:

1. behavior-bearing string subclasses;
2. mapping subclasses with iteration hooks;
3. sequence subclasses with iteration hooks;
4. nested lane-state subclasses with forged canonical projections;
5. nested effect-row subclasses with behavior-bearing key access;
6. outer global-state and effect-plan subclasses at snapshot boundaries;
7. effect-plan subclasses embedded in accepted transitions;
8. subclass dispatch through closed state-root, effect-plan, and rejection
   factories.

Before the repair, the first six test functions produced six failures. The
sequence and factory-dispatch families were added during repair review. All
eight now pass.

## Evidence

```text
focused shared Python closure:    1,337 passed, 1 deselected
affected Python test files:       218 passed
runtime-disaster test suite:      192 passed
new FCIS counterexamples:         8 passed
rejection-precedence regressions: 7 passed
Rust GlobalSettlementABI suite:   passed
test-hygiene gate:                6 critical paths, 15 nodes passed
Ruff:                             passed
Ruff format, changed tests:       passed
Ruff format, inherited sources:   baseline not clean; no bulk rewrite
strict mypy:                      passed
Python compilation:               passed
git diff --check:                 passed
remote CI:                        live external evidence; query exact PR head
```

The repository-wide critical-quality gate is not green on the successor base.
Its first unambiguous blocker is a committed invocation of
`tools/bva/check_critical_surface_coverage.py`, which is absent from base
`484f09a5...` and has no tracked Git history. A machine-local untracked copy was
inspected but was not imported into this successor as trusted source.

Running the next acceptance-TCB stage directly produced 414 passes and 19
failures. None of the nine failing test files is changed by this successor, and
the runtime paths implicated by the failures are byte-identical to the
successor base. The failures include tests that still call removed mutable
`Intent.set_field` behavior or assign through a frozen dataclass. This is
base-branch gate debt, remains a hard red status, and is not counted as passing
evidence for the successor. A clean base replay was not performed, so the
classification is deliberately narrower than a proof that every failure
already executes identically at the base commit.

Hosted run `33350595043` at `d0d2a7ca...` rejected the candidate because
`global_economic_refinement_snapshot_v1.py` lacked current diff-aware hygiene
evidence. `THV1-20260830-global-settlement-exact-ownership-v1` now pins both
source files and the eight counterexample nodes.

Hosted run `33350792610` at `da50cdb5...` passed that gate and then rejected
two literal invisible Unicode source characters inherited from the integration
base. The successor expresses the same hostile-input checks through explicit
`\\u200b` and `\\ufeff` escapes and regenerates the disaster-discovery source
pin through the contract's recorded command. Current hosted status is live
external evidence and must be queried for the exact PR head.

The single deselected shared-closure node is
`test_withdraw_refines_candidate_rows_into_complete_conservation`. Its stale
effect-plan golden root fails identically at successor base `484f09a5...` and
at this successor. It is inherited evidence debt outside the PR diff, not a
passing result and not repaired by this successor.

## Remaining successor gaps

The repair intentionally leaves six gaps explicit:

1. close or privatize the generic `to_canonical` protocol surface;
2. bind canonical traversal to one cycle, depth, item, and byte budget;
3. define typed ownership-admission rejection precedence;
4. generate command parsing and ownership from one closed kind registry;
5. close exact local ownership for every pool, perps, fill, and delta language;
6. obtain complete mutation, mount, sole-publisher, no-bypass, durability, and
   independent exact-head evidence.

No production, settlement, release, or value-movement authority follows from
this review or implementation.
