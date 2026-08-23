# App-root JMT V2 evaluator hardening

Status: **implemented and locally verified on 2026-08-23**. Owner: the
production-promotion / JMT-keystone (J6) program. The original finding was
raised by the autonomous Phase-3 review and is backed by
`tests/integration/test_app_root_jmt_promotion_lane.py` and PopperPad
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

## Implemented hardening

Bind each live-root check to **replayable source material** and re-derive inside
the evaluator, so forged-but-well-formed evidence fails closed.

1. **Evidence schema (`APP_ROOT_JMT_EVIDENCE_SCHEMA_V1` → v2).** Each
   `live_root_checks[i]` a canonical, self-describing `source_payload` (the exact
   input the named `live_path` consumes) — e.g. the canonical Dex snapshot object
   for `plain_dex_snapshot_live_root`, the canonical Tau app-state object for
   `tau_app_state_wrapper_live_root`, and the local-block pre-snapshot inputs for
   `local_block_pre_snapshot_header`. Keep `source_state_hash` as the canonical
   hash of `source_payload` (now verifiable, not just asserted).

2. **Producer (`build_evidence`).** It computes each root from a real
   source object; attach that object as `source_payload` and set
   `source_state_hash = canonical_hash(source_payload)`.

3. **Evaluator.** For each check it: (a) verifies `source_state_hash ==
   canonical_hash(source_payload)`; (b) re-derive the root by calling the SAME
   real function named in `live_path` (`_state_root_for_state_file_obj_v0` /
   `compute_tau_app_state_app_root_v0` / the local-block header path) on
   `source_payload`; (c) require `re_derived == observed_root == recomputed_root`.
   Reject (fail closed) on any mismatch, unknown `live_path`, or missing payload.
   Keep all existing checks.

   To avoid a hard `tools/` import from the gate, expose the three root functions
   through a small `src/`-level adapter (or move the canonical root helpers into
   `src/`) so the evaluator depends only on `src/` code.

## Migration

- V2 is required for promotion. V1 records fail closed.
- Manifest fixtures now use the real replay producer instead of filler roots.
- The former consistency-only characterization is a negative regression that
  requires self-consistent forged roots to fail evaluator re-derivation.
- Negative lane-tamper evidence now carries baseline and mutated payloads, and
  the evaluator independently derives both roots and the rejection result.

## Test plan (acceptance)

- Positive: `build_evidence` output (with `source_payload`) → evaluator `ok`.
- Negative (the fix's whole point): a record whose `observed_root` is tampered
  away from the re-derived value → `production_ready: False` with a root-mismatch
  gap.
- Negative: `source_state_hash` not matching `canonical_hash(source_payload)` →
  fail closed.
- Regression: the five external lanes and the aggregate bundle gate behavior are
  unchanged.

## Claim boundary

This change hardens one local replay evidence lane. It does not establish
external finality, mounted proof authority, whole-economy value-movement safety,
or global production readiness. Independent review of the V2 schema and gate
remains required before a release claim.
