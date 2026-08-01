# FCIS M6 Task D04 Plan

TASK_ID: D04
TITLE: Bind ANF into the commit bundle and outbox

## Scope

D04 closes the R04 edge from the D03 ANF-bound acceptance receipt to a
canonical outbox and commit bundle. Legacy unbound V1 canonical bytes remain
unchanged. ANF-bound outbox and bundle claims use distinct V2 schema identities
with one required ANF root.

The controlled builder retains the exact `FCISAuthorityNormalFormV1`. The
reference commit port recomputes that value's root, the outbox plan and root,
and the bundle bytes and root before publication. Store validation repeats the
same checks for every retained publication before retry classification.

## Preflight record

```text
owned authority:
  canonical bundle/outbox identity and reference publication eligibility

construction boundary:
  controlled decision and exact retained ANF -> immutable bundle

failure law:
  any ANF, outbox, bundle, patch, receipt, or store mismatch
  -> INVALID + exact unchanged store + zero new publications

canonical compatibility:
  legacy V1 bytes and roots are frozen
  ANF-bearing fields exist only under V2 schema IDs

claim level:
  tested unmounted Python reference evidence
```

## Required outputs

- `src/state/state_snapshot_schema.py`
- `src/state/state_admission_profile.py`
- `src/core/fcis_outbox_values.py`
- `src/core/fcis_commit_bundle_values.py`
- `src/core/fcis_authority_schema.py`
- `src/core/fcis_authority_dispatch.py`
- `src/core/fcis_commit_bundle_derivation.py`
- `src/core/fcis_commit_reference.py`
- `tests/core/test_fcis_commit_bundle_derivation.py`
- `tests/core/test_fcis_commit_reference.py`
- `tests/core/test_fcis_m5_authority_admission.py`
- `experiments/fcis_m6_d04_anf_bundle_outbox_check.py`
- `docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json`
- `docs/research/FCIS_M6_D04_ANF_BUNDLE_OUTBOX_SCHEMA_V1.md`
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

```text
python3 -m py_compile <all changed D04 Python files>
python3 -m ruff check <all changed D04 Python files>
python3 -m ruff format --check <all changed D04 Python files>
python3 -m mypy --strict <D04 source, derivation test, checker>
python3 -m pytest -q <D04 focused and dependency suites>
python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
python3 -m json.tool docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json
git diff --check <declared-base>..<receipt>
```

## Permanent negative cases

- missing or foreign exact ANF at the controlled builder;
- missing required V2 ANF root;
- crossed outer, receipt, or outbox ANF roots;
- crossed decision or outbox from another accepted candidate;
- missing or corrupted retained ANF at the reference commit port;
- corrupted ANF in an already retained publication before retry;
- stale cached bundle root after any mutation;
- any change to the frozen legacy V1 canonical vector.

## Nonclaims

D04 is tested unmounted Python evidence. It does not prove an authenticated
caller, production datastore transaction, crash recovery, destination
idempotency, TCG inventory, proof-context validity, DRA history, migration
authority, no-bypass reachability, or production value movement. The ANF
carrier and verifier adapters remain research premises until later independent
checks and runtime mounting tasks complete.
