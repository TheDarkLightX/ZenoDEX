# FCIS M6 Task I01 Report

TASK_ID: I01
BASE_SHA: ebf34a5a89dce664e914ffc0052289dea685f3f4
SOURCE_HEAD_SHA: bfa943f924d0ea6aaa79eebd0c519fd9109c6505
SOURCE_HEAD_TREE: 8e96b4555ca0b3b48e60fcdef1fe57ed2d90a528
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- docs/research/m6_tasks/TASK_I01_EFFECT_ID_VECTORS_V1.json
- tests/core/test_fcis_m6_i01_effect_identity.py
- docs/research/m6_tasks/TASK_I01_PLAN.md

IMPLEMENTATION_HEAD_SHA: bfa943f924d0ea6aaa79eebd0c519fd9109c6505
IMPLEMENTATION_TREE: 8e96b4555ca0b3b48e60fcdef1fe57ed2d90a528
IMPLEMENTATION_PARENT: ebf34a5a89dce664e914ffc0052289dea685f3f4

CLAIM_IMPLEMENTED: I01 freezes two canonical effect-identity vectors and
checks the semantic preimage contract. The identity is derived from
commit_id, ordinal, destination, payload_root, and writer_profile_root.
Adapter-profile rotation is validated as operational-only and cannot mint a
second semantic effect identity.

COMMANDS_RUN:
- python3 -m ruff format tests/core/test_fcis_m6_i01_effect_identity.py
- python3 -m ruff check tests/core/test_fcis_m6_i01_effect_identity.py
- python3 -m mypy --strict tests/core/test_fcis_m6_i01_effect_identity.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i01_effect_identity.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I01
- sha256sum --check --strict docs/research/m6_tasks/TASK_I01_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Frozen vector recomputation and repeatability passed.
- Adapter-profile rotation preserved both semantic identities.
- Commit, ordinal, destination, payload, and writer-profile mutations each
  changed the derived identity.
- Focused suite passed: 3 passed.
- Ruff, strict mypy, packet validation, and the source manifest pass.

MUTANTS_ADDED: None. The focused suite contains semantic mutation checks for
each preimage field and the operational adapter-profile rotation case.

FORMAL_EVIDENCE: None. I01 supplies executable vector and mutation evidence;
it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I01 does not prove committed outbox insertion, safe leasing, destination
  idempotency, acknowledgment provenance, or lost-ack recovery.
- I01 does not prove concurrent linearizability, production datastore
  behavior, runtime reachability, migration, no-bypass coverage, accounting,
  or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The identity function already existed in the isolated DRA core;
I01 freezes its current preimage and vectors. Production adapters still need
to carry the same identity without caller selection and preserve operational
profile provenance separately.

