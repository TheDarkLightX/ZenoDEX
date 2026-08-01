# FCIS M6 Task D03 Plan

TASK_ID: D03
TITLE: Bind ANF into the acceptance receipt

## Scope

D03 extends the receipt binding with the pinned Authority Normal Form version
and the freshly recomputed ANF root. The source-bound decision path requires an
exact ANF value, checks every ANF field that is derivable from the evaluation,
the source-bound SLNF segment, the budget, and the commit plan, and then places
the ANF identity in the canonical receipt bytes.

The ANF contains an acceptance_receipt_root field, so the binding uses an
explicit acyclic order: that ANF field must equal the root of the receipt
binding before ANF identity fields are added. The final receipt root then
commits to the ANF root. This relation is recorded as a research invariant;
D04 owns the later bundle/final-receipt closure.

Legacy receipt values retain optional empty ANF fields for compatibility. The
ANF-required source-bound entry point rejects a missing or wrong exact ANF.

## Required outputs

- src/core/fcis_decision_values.py
- src/core/fcis_authority_schema.py
- src/core/fcis_authority_dispatch.py
- src/core/fcis_decision_derivation.py
- tests/core/test_fcis_m6_d03_anf_receipt_binding.py
- experiments/fcis_m6_d03_anf_receipt_binding_check.py
- docs/research/m6_tasks/TASK_D03_ANF_RECEIPT_BINDING_VECTOR.json
- docs/research/FCIS_M6_D03_ANF_RECEIPT_BINDING_SCHEMA_V1.md
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

    python3 -m py_compile src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
    python3 -m ruff check src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
    python3 -m ruff format --check src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
    python3 -m mypy --strict src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
    pytest -q tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_decision_derivation.py tests/core/test_fcis_source_bound_lineage.py
    python3 -m json.tool docs/research/m6_tasks/TASK_D03_ANF_RECEIPT_BINDING_VECTOR.json
    python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check

The negative cases must reject missing ANF, wrong exact ANF type, and a foreign
source-derived ANF field. Canonical receipt bytes must retain the ANF fields.

## Nonclaims

D03 does not independently derive the TCG inventory, proof context, DRA
history, migration epoch, bundle, outbox, datastore state, caller authority,
or production value movement. Those later fields are committed by the ANF root
and remain downstream independent-derivation obligations. Legacy unbound
receipts remain available only as an unmounted compatibility path.
