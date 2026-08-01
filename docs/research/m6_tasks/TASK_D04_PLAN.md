# FCIS M6 Task D04 Plan

TASK_ID: D04
TITLE: Bind ANF into the commit bundle and outbox

## Scope

D04 closes the next R04 edge after the D03 acceptance receipt. The canonical
bundle claim and outbox plan now carry the same optional ANF root at their
outer schema boundaries. Admission checks that the bundle root equals the
nested decision receipt root and that the outbox root equals the same value.

The controlled ANF-bound builder also retains the exact
`FCISAuthorityNormalFormV1` value inside the authoritative bundle wrapper. Its
recomputed root is compared with the decision receipt before a bundle is
returned. Legacy unbound bundle construction remains available for existing
unmounted compatibility tests; the ANF-required entry point rejects a missing
ANF value or a crossed exact value.

The reference publication path already recomputes the outbox from the retained
decision. D04 exposes independent receipt-root, ANF-root, outbox-plan,
outbox-root, and bundle-root checks and adds crossed decision/outbox mutants.

## Required outputs

- `src/core/fcis_outbox_values.py`
- `src/core/fcis_commit_bundle_values.py`
- `src/core/fcis_authority_schema.py`
- `src/core/fcis_authority_dispatch.py`
- `src/core/fcis_commit_bundle_derivation.py`
- `tests/core/test_fcis_commit_bundle_derivation.py`
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
python3 -m mypy --strict <derivation, test, checker>
python3 -m pytest -q tests/core/test_fcis_commit_bundle_derivation.py
python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
python3 -m json.tool docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json
```

The broad regression slice must include M5 admission, reference commit,
lineage, D02, D03, source-bound lineage, and decision tests.

## Negative cases

The focused evidence must reject:

- a missing ANF at the ANF-required builder;
- a foreign ANF value whose root does not match the decision receipt;
- an outbox plan crossed from a different accepted candidate;
- a decision crossed from a different accepted candidate;
- a stale cached bundle root after any such mutation.

## Nonclaims

D04 is tested unmounted Python evidence. It does not prove an authenticated
caller, production datastore transaction, crash recovery, destination
idempotency, TCG inventory, proof-context validity, DRA history, migration
authority, no-bypass reachability, or production value movement. The ANF
carrier and verifier adapters remain research premises until later independent
checks and runtime mounting tasks complete.

