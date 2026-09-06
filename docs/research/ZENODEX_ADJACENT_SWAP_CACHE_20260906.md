# ZenoDEX adjacent swap suffix cache, 2026-09-06

This record describes a bounded implementation refactor for the repeated
adjacent-swap refinement pass, with finite verification of the deterministic
Python core. The production release claim remains closed.

The candidate binds
`refine_b_ordering_with_simulator` to the existing reserve simulator only while
the ordering module's evaluator is the canonical fold of that simulator. A
rebound evaluator continues through the existing generic callback seam. The
cache does not select a policy, alter a wire shape, or authorize an economic
effect.

## Contract and cache rule

For fixed intent and pool inputs, the simulator premise uses ordinary integer
contributions and exact `(int, int)` reserve tuples. The simulator is a pure
deterministic partial function: it returns `(a, b, new_reserves)` or raises an
input-dependent exception. This candidate makes no totality claim about a real
simulator or its external environment.

The cache stores the canonical fold state after every prefix of one ordering.
The state contains total `(A, B)` and the current reserves. An intent contributes
its simulated `(a, b)` and advances reserves only when `a > 0`, matching the
existing evaluator. The caller's list is copied and its intent objects are
preserved.

When adjacent positions `i` and `i + 1` are considered, the prefix before `i`
is unchanged and the pair is simulated from the cached prefix state. The suffix
starts from the pair's post-state. Its cached totals are reused only when the
pair's post-pair reserves equal the cached post-pair reserves exactly. A reserve
difference causes the complete suffix to be simulated again. After an accepted
swap, the pair and any recomputed suffix become the new cache entries; a reused
suffix is shifted by the pair's total delta. The scan remains left-to-right and
accepts only a strict lexicographic `(A, B)` improvement, with the existing pass
and tie behavior.

## Evidence surface

The focused test file is a finite differential and stateful check against the
unchanged generic evaluator. It covers every permutation of the fixed catalogue,
120 deterministic random batches, zero/one-intent boundaries, fee and rounding
neighbors, mixed directions, impossible minimum outputs, duplicate object
references, and nonpositive synthetic contributions.

The checks instrument reuse, full resimulation, and accepted cache updates. A
hand-computed fee-free counterexample rejects unconditional stale-suffix reuse.
The accepted-swap fixtures compare the updated cache with a fresh rebuild. Three
partial input-dependent exception locations compare exact exception type,
arguments, and message. Independent deep snapshots cover pool values, nested
intent fields, list order, and object identity. A deliberate nested-mutation
oracle demonstrates that the snapshot detects caller-preservation violations;
that control is separate from the pure simulator premise.

The settlement case runs through the existing settlement dispatcher and compares
the complete recursive `Settlement`, canonical serialization, metadata, events,
fill reasons, and `_settlement_commitment_dict` bytes between cached and generic
paths. Input snapshots cover balances, pools, and intents before either path and
are checked after each computation.

The earlier worker runs reported 140 passing cases across the cache and four
donor suites, then 55 focused cases during the snapshot corrections. Root's
final integration replay independently passed 144 cases across the final cache
file, the four donor suites, and production ordering containment. The root
critical quality gate passed its 433 acceptance tests and 834 critical tests,
including the required coverage floors, Ruff, and mypy. The production-boundary
scanner passed all 14 checks. Both broader pytest phases reported the existing
Hypothesis collection warning about the ignored `.hypothesis` directory.

The final root replay used `python3 -m pytest -q` with
`tests/core/test_batch_clearing_refinement_cache_v1.py`,
`tests/core/test_batch_clearing.py`,
`tests/core/test_batch_clearing_b_refinement.py`,
`tests/core/test_batch_clearing_properties.py`,
`tests/core/test_batch_clearing_global_refinement.py`, and
`tests/integration/test_production_settlement_ordering_containment.py`.
Broader validation used `bash tools/run_critical_quality_gate.sh` with the
existing development Python environment selected by `PYTHON`, and
`python3 tools/check_production_boundary.py --json`. These results qualify the
implementation for integration; release qualification remains open.

## Work bound and claim ceiling

The implementation performs `n` simulator calls to build the initial cache. A
candidate performs two pair calls and, when reserves differ, up to `n - i - 2`
suffix calls. The worst case is `O(n^2)` simulator calls per pass, with the same
pass count as the generic refiner. The finite tests observe reductions on their
fixtures. They do not establish an `O(n)` pass bound, universal near-linear
behavior, optimality, or production throughput and latency.

The cache is not a generic callback optimizer. No default, cap, rounding, wire,
policy, or tie-break change is introduced. No Lean theorem or universal
Python/Rust/compiler refinement is supplied. Native builds, deployment, live
resource behavior, and release qualification remain outside this source-bound
candidate.

## Pinned replay

The accompanying packet is rendered by:

```bash
python3 -B -m experiments.v3_adjacent_swap_cache_v1.render_evidence
```

The focused behavior check is:

```bash
pytest -q tests/core/test_batch_clearing_refinement_cache_v1.py
```

Rendering only records exact source and test bytes. It does not execute tests or
promote a production claim. The packet pins the three changed core/test paths,
the reserve simulator and curve/quote dispatch, settlement dispatcher,
commitment and canonical encoders, and the four declared donor suites.
