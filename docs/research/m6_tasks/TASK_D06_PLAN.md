# FCIS M6 Task D06 Plan

TASK_ID: D06
TITLE: Validate the C3 lineage rule manifest

## Scope

D06 replaces the implicit fixed C3 rule tuple with a typed manifest validated
at module construction. The validator proves the declared research relation has
one writer per derived key, complete coverage, canonical dependency order,
acyclic closure, a bounded fixed-point loop, and a manifest root that binds all
of those choices.

The production closure remains bound to the validated private manifest. A
private permutation seam is retained only for deterministic confluence tests.

## Required outputs

- src/core/fcis_lineage_closure.py
- experiments/fcis_m6_d06_rule_manifest_check.py
- tests/core/test_fcis_m6_d06_rule_manifest.py
- docs/research/m6_tasks/TASK_D06_RULE_MANIFEST_VECTOR.json
- docs/research/FCIS_M6_D06_LINEAGE_RULE_MANIFEST_SCHEMA_V1.md
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

    python3 -m py_compile <all changed D06 Python files>
    python3 -m ruff check <all changed D06 Python files>
    python3 -m ruff format --check <all changed D06 Python files>
    python3 -m mypy --strict <all changed D06 Python files>
    python3 -m pytest -q tests/core/test_fcis_m6_d06_rule_manifest.py
    python3 experiments/fcis_m6_d06_rule_manifest_check.py
    python3 -m json.tool docs/research/m6_tasks/TASK_D06_RULE_MANIFEST_VECTOR.json

The checker and tests must cover all 24 rule permutations and reject duplicate
writers, omitted coverage, cycles, noncanonical ordering, root substitution,
and foreign test-seam rules.

## Nonclaims

D06 is tested unmounted C3 closure evidence. It does not prove a general
production rule registry beyond the closed enum in this module, a Lean theorem,
a datastore adapter, runtime reachability, TCG completeness, proof-context
mounting, migration authority, recovery atomicity, destination idempotency, or
value movement. Existing source-bound and artifact builders remain private
research seams until their production boundaries are separately mounted.
