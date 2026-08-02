# FCIS M6 Task D08 Plan

TASK_ID: D08
TITLE: Build the combined ANF checker

## Scope

D08 composes the source-bound lineage/C3, TCG, proof-context, durable-retraction,
and ANF-bound decision/bundle stages into one fail-closed executable relation.
Every stage recomputes or verifies its own source and binds the next stage to
that source. A root produced by a later stage cannot replace an earlier source.

The implementation remains a research-only verifier. It does not mount a caller,
API, datastore, proof system, worker, destination, migration switch, or
value-moving path.

## Required outputs

- src/core/fcis_m6_d08_combined_anf.py
- experiments/fcis_m6_d08_combined_anf_check.py
- tests/core/test_fcis_m6_d08_combined_anf.py
- docs/research/m6_tasks/TASK_D08_COMBINED_ANF_VECTOR.json
- docs/research/FCIS_M6_D08_COMBINED_ANF_SCHEMA_V1.md
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

    python3 -m py_compile <all changed D08 Python files>
    python3 -m ruff check <all changed D08 Python files>
    python3 -m ruff format --check <all changed D08 Python files>
    python3 -m mypy --strict <all changed D08 Python files>
    python3 -m pytest -q tests/core/test_fcis_m6_d08_combined_anf.py
    PYTHONPATH=. python3 experiments/fcis_m6_d08_combined_anf_check.py
    python3 -m json.tool docs/research/m6_tasks/TASK_D08_COMBINED_ANF_VECTOR.json

The checker and tests must cover valid composition, wrong exact type, source
extraction failure, TCG substitution, C3 substitution, missing or foreign
proof context, publication and PRE/POST history mismatch, later decision/root
substitution, and malformed TCG evidence that must become typed rejection.

## Composition invariants

- Source-bound lineage and C3 closure are recomputed before later stages.
- TCG expectations bind topology, instance, source, lineage, sinks, gates, and
  the D05 inventory identity.
- Required proof context binds command, execution, state, authority epoch,
  verifier profile, proof root, and context root.
- DRA accepts only the exact canonical PRE history plus one expected atom as
  the canonical POST history.
- The final ANF decision and bundle are freshly recomputed and compared exactly.
- Accept results contain one verifier-minted ANF root and the complete
  recomputed `PublicationAtomV1` owned by that acceptance. Downstream ports
  derive publication fields from this aggregate and revalidate acceptance
  provenance at point of use.

## Nonclaims

D08 is tested unmounted composition evidence. It does not prove cryptographic
proof soundness, TCG completeness, source-input authentication, production
datastore transactions, crash recovery, destination idempotency, API no-bypass
coverage, migration authority, deployment identity, hosted CI, remote
publication, or value movement.
