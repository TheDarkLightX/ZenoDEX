# FCIS M6 Task D02 Plan

TASK_ID: D02
TITLE: Embed source-derived SLNF roots in evaluation evidence

## Scope

D02 closes the evaluator-side source-binding gap identified by D01. The
source-bound evaluation entry point accepts one exact, freshly verified
`SourceBoundFeeOccurrenceV1`. The evaluator retains the exact source-derived
segment in a controlled `FCISFeeOccurrenceBindingV1`, validates its projection
before the fee transition, and carries the same binding object in both the
candidate and the evaluation evidence.

The source-bound decision adapter derives the decision from that same
source-bound evaluation. The existing four-field `FCISFeeAllocationV1` wire
schema remains unchanged; the source binding is candidate/evidence provenance,
not an extra commit-plan allocation field.

## Required outputs

- `src/core/fcis_step_evaluation_values.py`
- `src/core/fcis_step_evaluator.py`
- `src/core/fcis_decision_derivation.py`
- `src/core/fcis_source_bound_lineage.py`
- `tests/core/test_fcis_m6_d02_source_bound_evaluation.py`
- `experiments/fcis_m6_d02_source_bound_evaluation_check.py`
- `docs/research/m6_tasks/TASK_D02_SOURCE_BOUND_EVALUATION_VECTOR.json`
- `docs/research/FCIS_M6_D02_SOURCE_BOUND_EVALUATION_SCHEMA_V1.md`
- this plan, report, evidence JSON, and source manifest

## Fail-closed acceptance

```bash
python3 -m py_compile src/core/fcis_step_evaluation_values.py src/core/fcis_step_evaluator.py src/core/fcis_decision_derivation.py src/core/fcis_source_bound_lineage.py tests/core/test_fcis_m6_d02_source_bound_evaluation.py experiments/fcis_m6_d02_source_bound_evaluation_check.py
python3 -m ruff check src/core/fcis_step_evaluation_values.py src/core/fcis_step_evaluator.py src/core/fcis_decision_derivation.py src/core/fcis_source_bound_lineage.py tests/core/test_fcis_m6_d02_source_bound_evaluation.py experiments/fcis_m6_d02_source_bound_evaluation_check.py
python3 -m ruff format --check src/core/fcis_step_evaluation_values.py src/core/fcis_step_evaluator.py src/core/fcis_decision_derivation.py src/core/fcis_source_bound_lineage.py tests/core/test_fcis_m6_d02_source_bound_evaluation.py experiments/fcis_m6_d02_source_bound_evaluation_check.py
python3 -m mypy --strict src/core/fcis_step_evaluation_values.py src/core/fcis_step_evaluator.py src/core/fcis_decision_derivation.py src/core/fcis_source_bound_lineage.py tests/core/test_fcis_m6_d02_source_bound_evaluation.py experiments/fcis_m6_d02_source_bound_evaluation_check.py
pytest -q tests/core/test_fcis_m6_d02_source_bound_evaluation.py tests/core/test_fcis_source_bound_lineage.py tests/core/test_fcis_step_evaluator.py tests/core/test_fcis_decision_derivation.py
python3 -m json.tool docs/research/m6_tasks/TASK_D02_SOURCE_BOUND_EVALUATION_VECTOR.json
python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
```

The negative cases must retain fresh source verification, controlled binding
construction, exact segment projection, and candidate/evidence identity
checks. A foreign or crossed segment must reject before a candidate is
accepted.

## Nonclaims

D02 does not authenticate the outer caller, mount a datastore or transaction,
prove the B06 allocator is the production fee transition, bind the source
roots into receipts/bundles/outboxes, prove proof-context validity, establish
migration authority, or move value. The regular unbound evaluator remains a
legacy research API; the new source-bound path is the only path covered by the
D02 source/evaluator equality claim.
