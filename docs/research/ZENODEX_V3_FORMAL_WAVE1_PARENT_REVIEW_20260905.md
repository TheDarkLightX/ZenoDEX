# V3 formal wave: parent review and executable evidence

This review covers the wave assigned at
`04f0d32b6b6679aa23da645263ec6575f7872c4e` and integrated on parent
`37f56bb9b`. It advances W07/W08/W09 evidence and adds a W10 image-drift guard.
It does not close any lane or whole-program gate. The formal core, publication
qualification, and whole-product completion remain open.

## Accepted scope

| Surface | Result | Remaining boundary |
| --- | --- | --- |
| Managed-asset V2 | Actual Lean transition/report compared with Python outcomes on 37 scenarios and an eight-step history; explicit root-token relations and three semantic mutants | One-asset abstraction and finite corpus; no universal Python/Rust, hash, codec, receipt, or publisher refinement |
| Purchase and burn | Conservation derives equal acquired/burned amounts under the modeled plan shape; finite runtime checks cover exact keyed ZDEX rows, occurrence consumption, and independently isolated conservation failures | Aggregate equations do not establish occurrence authentication or authorized ownership; accepted composer-to-model refinement remains open |
| zUSD owner close | Actual Python and Lean outcomes compared with independent integer expectations, including complete ordered rejects, terminal debt discharge, and projected effects | The Lean request has one price and cannot represent a split risk/TCR price; owner identities, roots, and index-removal target are not represented directly |
| Finite global trace | Conditional `Run` composition retains the single-step `Verified` obligations, derives replay uniqueness and height accounting, and has a nonempty advancing witness | Observed runtime roots/replay data establish only necessary trace conditions; no runtime-derived `Run`, durable atomicity, or publisher client-outcome proof |
| Asset child image | Plain Rust test compares the linked child method ID with the pinned coordinator child ID; existing proving-path assertion retained | Actual guest build and linked test unrun; eight Python source/pin checks do not certify built image equality |

The managed-asset module binds the types of imported claims through explicit
Lean consumers. Its table evaluates model definitions rather than printing
literal expected results. Roots remain opaque equality tokens. The owner-close
gate runs the unchanged definitions and proofs below the source import line
using three checked members of `Mathlib.Tactic`'s import closure from an existing
local installation. This is a focused compilation, not a fresh full Mathlib build.

## Parent corrections

The image test was reduced to a direct `assert_eq!`. The discarded wrapper
could classify placeholder methods as a passing unexecuted outcome. An all-zero
placeholder now fails equality with the nonzero pin. No image constant changed.

Independent Astra review confirmed the burn derivation and owner-diversion
counterexample at aggregate scope. The row-only Lean model omits the runtime
plan's `occurrence_consumptions`; claims that all effect-plan occurrence data was
absent were corrected. The harness now checks the retained singleton occurrence,
exact selected-pool principal/domain, and the supply principal/domain. Its
acquisition-only negative rebinds the post-supply and journal to the no-burn plan
and requires the owned-total/supply error, so an earlier root mismatch cannot
stand in for the conservation check. The ownership example passes the narrow
state refiner, not the route composer.

The coordinator report was advisory. Some reported mutations ran temporarily
on shared sources outside worker ownership. Parent required private scratch
copies for all subsequent mutations and independently replayed the candidates.
Collection or setup failures are not treated as precise semantic mutant kills.

The trace harness now binds every returned root to the submitted subject and
derives replay insertions from predecessor/successor registries. Rejection roots
and consumed occurrences are read directly from the result. A returned-root
corruption is detected even when fixture endpoints are equal. A duplicate replay
ID is rejected while independent step, chain, occurrence-uniqueness, and height
checks still pass. The fixture named as a retry is correctly labeled reanchored
replay reuse; exact committed publisher retry remains outside this core model.

Removing `TraceRefines.outboxClosed` previously survived the companion tests.
The repaired gate first shows that the weakened module and bundle still compile,
then requires a fixed-type consumer of all ten promised bundle fields to fail.
Mutants and fresh compilation operate on private source copies. All 19 original
single-step `Verified` dimensions remain present in the trace theory.

## Replayed commands

```bash
python3 -m pytest -q tests/formal/test_lean_managed_asset_runtime_parity_v2.py tests/formal/test_lean_zdex_acquisition_burn_occurrence_v2.py tests/formal/test_lean_zusd_owner_close_runtime_v1.py
python3 -m pytest -q tests/zk/test_asset_lane_image_id_guard_v1.py
python3 -m pytest -q tests/formal/test_lean_zdex_acquisition_burn_occurrence_v2.py
python3 -m pytest -q tests/formal/test_lean_global_economic_refinement_trace_v2.py
python3 -m ruff check tests/formal/test_lean_managed_asset_runtime_parity_v2.py tests/formal/test_lean_zdex_acquisition_burn_occurrence_v2.py tests/formal/test_lean_zusd_owner_close_runtime_v1.py tests/zk/test_asset_lane_image_id_guard_v1.py
python3 -m mypy tests/formal/test_lean_managed_asset_runtime_parity_v2.py tests/formal/test_lean_zdex_acquisition_burn_occurrence_v2.py tests/formal/test_lean_zusd_owner_close_runtime_v1.py tests/zk/test_asset_lane_image_id_guard_v1.py
rustfmt --check --edition 2021 zk/asset_lane_coordinator_risc0/host/tests/real_composition.rs
python3 -m ruff check tests/formal/test_lean_global_economic_refinement_trace_v2.py
python3 -m mypy tests/formal/test_lean_global_economic_refinement_trace_v2.py
```

The first suite passed **263 tests** with no skips. Parent then narrowed
documentation claims and strengthened the burn assertions; the burn suite was
replayed and passed **12 tests**. The image source/pin suite passed **8 tests**.
Ruff, targeted mypy, and Rust formatting passed. These are evidence counts, not
completed capabilities or a completion percentage.

The repaired trace suite independently passed **18 tests** in 56.48 seconds.
Its Lean source and test hashes below were unchanged before and after that run.

## Source subject

| Artifact | SHA-256 |
| --- | --- |
| `lean-mathlib/Proofs/ManagedAssetRuntimeParityV2.lean` | `70c873e9b5b68635c412f5a06d333c543cbc70bfa20178a687b7d747904561b2` |
| `lean-mathlib/Proofs/ZDEXAcquisitionBurnOccurrenceV2.lean` | `8684e12ee47961ceaad030a1859946d7ff4a4f1c19d41912631585985a9981be` |
| `tests/formal/test_lean_managed_asset_runtime_parity_v2.py` | `9056fea5299f289cfb8b7e417a2807330c5627c749f0855202ad5b862e21cc02` |
| `tests/formal/test_lean_zdex_acquisition_burn_occurrence_v2.py` | `ecd9d69e652e69172cc827791c4044b8239be414ef2049b4d85424566f270454` |
| `tests/formal/test_lean_zusd_owner_close_runtime_v1.py` | `a2ff1e73e45986eb27a2f2c4173bd1fa4235771389c9c6e768fc7de80fcd9206` |
| `tests/zk/test_asset_lane_image_id_guard_v1.py` | `d68901fc1252bf8d0dfcad03ae25c00a277490cc28855b2d85b6cb7f62e1b370` |
| `zk/asset_lane_coordinator_risc0/host/tests/real_composition.rs` | `7e31bdcbfe14dd2ee7badde577ca64b4fcffc416d9bda154ae1ba05a94dd6d94` |
| `lean-mathlib/Proofs/GlobalEconomicRefinementTraceV2.lean` | `3401bb224f7afb9ad0343d7670c755838afcd2f46d1b494df1270ae42372b548` |
| `tests/formal/test_lean_global_economic_refinement_trace_v2.py` | `f939798cebf49f649235126669b80edf6fea23d8cd5b462c722e9da4256dbcb2` |

## Open acceptance work

The finite trace observational projection cannot by itself construct a
runtime-derived formal `Run`. Source/compiler refinement and actual mounted
state-transition correspondence remain open after these evidence repairs.

Full guest/proving builds, full Mathlib, CUDA, live Tau, and production activation
were not run. The broader critical-quality gate stops because `pytest_cov` is
missing. The existing production-boundary replay passed its 14 checks after
optional production optimizations were restored to their admitted source; those
checks do not discharge the missing implementation or deployment obligations.

The next mathematical step for the burn route is a theorem deriving its exact
keyed footprint and singleton occurrence from accepted receipt/terminal bindings
and materialization. This would connect authorized source ownership to the
aggregate accounting theorem already checked here.
