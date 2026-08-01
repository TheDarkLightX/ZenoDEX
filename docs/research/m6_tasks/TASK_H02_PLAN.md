# H02 plan: single atomic publication transaction

Status: implementation in progress; research-only and unmounted.

## Objective

Refine the H01 logical publication tables into one isolated SQLite publication
operation. The operation must expose either the complete durable POST state or
the unchanged PRE state.

The acceptance boundary is:

    one commit exposes complete POST or no change

This is an adapter refinement exercise. It does not authorize a production
datastore, a runtime caller, value movement, or a deployment configuration.

## Dependencies and inputs

- E05 and src/core/fcis_durable_retraction.py
- H01 table matrix and its explicit ANF-root boundary
- D08 combined ANF verifier and its verifier-produced acceptance
- pinned ANF profile identifier ANF_VERSION_V1

PublicationAtomV1 has no ANF root field. H02 therefore adds a checked
ANFPublicationWitnessV1 relation rather than identifying the ANF root with an
unrelated atom, bundle, or replay root.

## Transaction protocol

1. Open the SQLite connection with foreign-key enforcement enabled.
2. Start one BEGIN IMMEDIATE transaction.
3. Reconstruct the complete PRE state from every logical table.
4. Require the durable retraction fixed-point check.
5. Compare the expected snapshot root, publication root, current state root,
   authority epoch, and authority root.
6. Require that the verifier-minted D08 witness names the exact PRE snapshot.
7. Derive the successor authority history, atom history, ANF row, ANF-set
   root, and publication root.
8. Require the verifier witness POST snapshot to equal the derived successor.
9. Apply a SQL compare-and-set against the expected PRE roots and authority
   head.
10. Insert the optional authority successor, atom, evidence, nullifier,
    outbox rows, and ANF row.
11. Reopen the uncommitted rows through read_state and compare the complete
    result with the derived POST state.
12. Commit and return the H02 commit result.
13. Convert validation, integrity, and SQLite failures into a typed rejection
    after rollback.

The SQL compare-and-set is checked inside the same transaction as the row
inserts. A failed comparison returns a stale-CAS rejection without changing
the durable layout.

## Invariants

- Every atom has one canonical sequence and one unique commit identity.
- Nullifier roots and commit identities are unique.
- Evidence rows use the closed evidence-kind registry.
- Outbox rows reference an existing atom and have unique commit/ordinal pairs.
- ANF rows have one exact commit-to-atom binding and the pinned ANF version.
- ANF row cardinality equals atom row cardinality.
- Authority epochs and allowed writers are fully reconstructed and ordered.
- Cached authority-head, ANF-set, and publication roots rederive from rows.
- A complete canonical reopen must succeed before a commit can be accepted.

## Typed rejection surface

H02CodeV1 distinguishes COMMITTED, INVALID_REQUEST, STALE_SNAPSHOT_CAS,
STALE_STATE_CAS, STALE_AUTHORITY_CAS, REOPEN_REJECTED, and SQL_ROLLBACK.

The experiment does not introduce an indeterminate durable outcome. A lost
client response remains a client-knowledge problem; a fresh canonical reopen
determines whether the durable transaction is PRE or POST.

## Focused evidence

The focused tests cover complete POST publication, stale snapshot/state/
authority CAS no-op behavior, forced SQLite abort after partial evidence
insertion, foreign verifier acceptance rejection, atom-bearing seed rejection
without an ANF row, and crossed atom/witness rejection.

Required local commands:

    PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py
    python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py
    python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py
    python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py
    python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py

## Follow-up and nonclaims

H03 must add deterministic crash points. H04 must reopen after every crash and
compare exactly with PRE or POST. H05 must test concurrent linearization. H06
must bind production durability settings. H07 must produce the concrete
refinement report. H08 must perform independent attack review.

This model does not prove filesystem durability, WAL/fsync behavior,
process-crash recovery, concurrent linearizability, authenticated production
callers, no-bypass coverage, destination idempotency, migration mounting,
whole-system accounting, or production value movement. M6 remains unmounted
and non-promotable after H02.
