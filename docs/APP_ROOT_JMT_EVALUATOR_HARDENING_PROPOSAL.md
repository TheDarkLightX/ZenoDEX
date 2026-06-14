# Proposal: harden the `app_root_jmt` promotion-lane evaluator to re-derive roots

Status: **proposal for review** (not implemented). Owner: the production-promotion
/ JMT-keystone (J6) program. Raised by the autonomous Phase-3 review; the finding
is backed by `tests/integration/test_app_root_jmt_promotion_lane.py` and PopperPad
`K86ebdc24`.

## Finding (the gap)

`evaluate_production_app_root_jmt_evidence_v1`
(`src/integration/production_promotion_evidence.py`) validates, per live-root
check: schema, `root_system == typed_app_root_jmt_v1`, lane coverage, freshness,
`source_kind`/`live_path` labels, the self-binding `evidence_hash`, and
`observed_root == recomputed_root`. It does **not** independently re-derive the
roots from source state — both `observed_root` and `recomputed_root` are taken
from the submitted evidence. So a *well-formed* record with arbitrary matching
filler roots passes. The repo's own fixture demonstrates this:
`tests/integration/test_production_promotion_evidence.py::_valid_app_root_jmt_evidence`
uses `11/12/13`-filler roots and `test_app_root_jmt_valid_baseline_is_ready`
asserts `production_ready` over it.

Consequence: for this lane, gate acceptance is **consistency-only**. The real
authenticity of the all-lane `typed_app_root_jmt_v1` root rests on the *producer*
(`tools/build_app_root_jmt_evidence.py::build_evidence`, which does exercise the
real replay paths), not on the gate. The five other lanes are gated on external
evidence; this lane is the one whose evidence is locally producible, which makes
closing this gap worthwhile.

## Proposed hardening

Bind each live-root check to **replayable source material** and re-derive inside
the evaluator, so forged-but-well-formed evidence fails closed.

1. **Evidence schema (`APP_ROOT_JMT_EVIDENCE_SCHEMA_V1` → v2).** Add to each
   `live_root_checks[i]` a canonical, self-describing `source_payload` (the exact
   input the named `live_path` consumes) — e.g. the canonical Dex snapshot object
   for `plain_dex_snapshot_live_root`, the canonical Tau app-state object for
   `tau_app_state_wrapper_live_root`, and the local-block pre-snapshot inputs for
   `local_block_pre_snapshot_header`. Keep `source_state_hash` as the canonical
   hash of `source_payload` (now verifiable, not just asserted).

2. **Producer (`build_evidence`).** It already computes each root from a real
   source object; attach that object as `source_payload` and set
   `source_state_hash = canonical_hash(source_payload)`.

3. **Evaluator.** For each check: (a) verify `source_state_hash ==
   canonical_hash(source_payload)`; (b) re-derive the root by calling the SAME
   real function named in `live_path` (`_state_root_for_state_file_obj_v0` /
   `compute_tau_app_state_app_root_v0` / the local-block header path) on
   `source_payload`; (c) require `re_derived == observed_root == recomputed_root`.
   Reject (fail closed) on any mismatch, unknown `live_path`, or missing payload.
   Keep all existing checks.

   To avoid a hard `tools/` import from the gate, expose the three root functions
   through a small `src/`-level adapter (or move the canonical root helpers into
   `src/`) so the evaluator depends only on `src/` code.

## Migration (the cascade — why this is deliberate, not autonomous)

- Bump the evidence schema version; gate the re-derivation behind v2 and
  **require** v2 for promotion (v1 records no longer satisfy the lane).
- Update `_valid_app_root_jmt_evidence` and the app-root mutation tests in
  `tests/integration/test_production_promotion_evidence.py` to carry real
  `source_payload`s (the `11/12/13` filler roots must go).
- Update `tests/integration/test_app_root_jmt_promotion_lane.py`: the
  `..._evaluator_is_consistency_only...` characterization test should flip to
  assert the forged record now **FAILS**, renamed to a positive
  `..._rejects_forged_roots` test.

## Test plan (acceptance)

- Positive: `build_evidence` output (with `source_payload`) → evaluator `ok`.
- Negative (the fix's whole point): a record whose `observed_root` is tampered
  away from the re-derived value → `production_ready: False` with a root-mismatch
  gap.
- Negative: `source_state_hash` not matching `canonical_hash(source_payload)` →
  fail closed.
- Regression: the five external lanes and the aggregate bundle gate behavior are
  unchanged.

## Why it is deferred to review

This changes the shared production-promotion **authority** (evidence schema +
evaluator) and migrates its fixtures, and the lane is owned by the JMT-keystone
J6 program. Per the CBC promotion discipline, a change to the gate that decides
production-readiness claims should be deliberate and human-reviewed, not made
autonomously. Codex concurred. This document is the actionable spec for that
review; the producer already emits real roots, so the lift is the schema/evaluator
re-derivation and the fixture migration above.
