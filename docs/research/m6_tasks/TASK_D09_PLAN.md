# FCIS M6 Task D09 Plan

TASK_ID: D09
TITLE: Add crossed-axis and temporal mutants

## Scope

D09 adds deterministic adversarial evidence for the D08/D07 composition
boundary. It builds two distinct valid D08 transitions, crosses their
authoritative axes, and verifies exact rejection codes. It also checks that
new commit and migration operations remain visible transitions rather than
stutters.

## Required outputs

- experiments/fcis_m6_d09_crossed_axis_temporal_check.py
- tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
- docs/research/m6_tasks/TASK_D09_CROSSED_AXIS_VECTOR.json
- docs/research/FCIS_M6_D09_CROSSED_AXIS_SCHEMA_V1.md
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

    python3 -m py_compile <all changed D09 Python files>
    python3 -m ruff check <all changed D09 Python files>
    python3 -m ruff format --check <all changed D09 Python files>
    python3 -m mypy --strict <all changed D09 Python files>
    python3 -m pytest -q tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
    PYTHONPATH=. python3 experiments/fcis_m6_d09_crossed_axis_temporal_check.py
    python3 -m json.tool docs/research/m6_tasks/TASK_D09_CROSSED_AXIS_VECTOR.json

The vector must record two distinct valid transition roots, all eight named
mutants, and their exact closed rejection codes.

## Mutants

- semantic from transition 1 plus receipt from transition 2;
- receipt from transition 1 plus bundle from transition 2;
- bundle from transition 1 plus outbox from transition 2;
- TCG receipt from foreign topology;
- DRA atom with foreign authority epoch;
- same semantic root plus different lineage root;
- stutter hiding a new commit;
- stutter hiding a migration step.

## Nonclaims

D09 is tested unmounted mutation evidence. It does not prove production
datastore isolation, caller/no-bypass coverage, TCG completeness, proof
soundness, destination idempotency, migration authority, deployment identity,
or value movement.

