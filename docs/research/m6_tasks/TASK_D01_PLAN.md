# FCIS M6 Task D01 Plan

TASK_ID: D01
TITLE: Define Authority Normal Form

## Scope

Define one immutable, canonical, unmounted `FCISAuthorityNormalFormV1`
carrier for the complete M6 R04 root tuple. The carrier covers source-bound
command/context/pre-state, complete SLNF semantic and lineage roots,
candidate/next-state roots, C3 closure roots, acceptance and durability roots,
TCG topology and instance roots, optional proof-context binding, DRA history
roots, and the migration authority epoch.

The root is derived from every field’s canonical bytes. It is never accepted
as a caller-selected cached field. Proof-context absence is represented by an
explicit closed enum and checked against the optional proof root.

## Required outputs

- `src/core/fcis_authority_normal_form_v1.py`
- `tests/core/test_fcis_authority_normal_form_v1.py`
- `experiments/fcis_m6_d01_vector_check.py`
- `docs/research/m6_tasks/TASK_D01_AUTHORITY_NORMAL_FORM_VECTOR.json`
- `docs/research/FCIS_M6_D01_AUTHORITY_NORMAL_FORM_SCHEMA_V1.md`
- this plan, report, evidence JSON, and source manifest

## Fail-closed acceptance

```bash
python3 -m py_compile src/core/fcis_authority_normal_form_v1.py tests/core/test_fcis_authority_normal_form_v1.py
python3 -m ruff check src/core/fcis_authority_normal_form_v1.py tests/core/test_fcis_authority_normal_form_v1.py
python3 -m mypy --strict src/core/fcis_authority_normal_form_v1.py tests/core/test_fcis_authority_normal_form_v1.py
pytest -q tests/core/test_fcis_authority_normal_form_v1.py
python3 -m experiments.fcis_m6_d01_vector_check
```

The final receipt additionally runs the task-packet validator and exact source
manifest check. Unknown fields, duplicate fields, missing fields, noncanonical
bytes, root type drift, proof-context mismatch, and any per-field root change
must remain covered by negative evidence.

## Nonclaims

D01 does not authenticate a supplied root, construct authority, bind a mounted
caller, update the acceptance receipt, change commit bundle/outbox behavior,
prove TCG inventory completeness, prove proof-context validity, or move value.
Those obligations remain D02-D10 and the later runtime lanes.
