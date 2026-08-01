# FCIS M6 Task I08 Report

TASK_ID: I08
BASE_SHA: 61bed1d774358a7a506fbd9342e3c1f0c617845d
SOURCE_HEAD_SHA: bd23066ce004b821baba956b93f0b6e2f23a8cb5
SOURCE_HEAD_TREE: d1e556bd7c42f2db7da5a15ecc6c1915bbd53f73
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- tools/check_fcis_m6_i08_honest_contract.py
- tests/core/test_fcis_m6_i08_honest_delivery_contract.py
- docs/research/m6_tasks/TASK_I08_HONEST_DELIVERY_CONTRACT_V1.json
- docs/research/m6_tasks/TASK_I08_HONEST_DELIVERY_CONTRACT_V1.md
- docs/research/m6_tasks/TASK_I08_PLAN.md

IMPLEMENTATION_HEAD_SHA: bd23066ce004b821baba956b93f0b6e2f23a8cb5
IMPLEMENTATION_TREE: d1e556bd7c42f2db7da5a15ecc6c1915bbd53f73
IMPLEMENTATION_PARENT: 61bed1d774358a7a506fbd9342e3c1f0c617845d

CLAIM_IMPLEMENTED: I08 adds a fail-closed honest delivery contract. The
machine-readable claim registry and human contract document use exactly these
positive terms: atomic enqueue, at-least-once attempts, stable idempotent
semantic identity, and provenance-bound acknowledgment. The checker rejects
unsupported exactly-once wording in positive claims or API names, requires the
explicit destination/mounting nonclaims, and requires the document to contain
exactly four positive Claim lines.

COMMANDS_RUN:
- python3 tools/check_fcis_m6_i08_honest_contract.py docs/research/m6_tasks/TASK_I08_HONEST_DELIVERY_CONTRACT_V1.json
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i08_honest_delivery_contract.py
- python3 -m ruff check tools/check_fcis_m6_i08_honest_contract.py tests/core/test_fcis_m6_i08_honest_delivery_contract.py
- python3 -m ruff format --check tools/check_fcis_m6_i08_honest_contract.py tests/core/test_fcis_m6_i08_honest_delivery_contract.py
- python3 -m mypy --strict tools/check_fcis_m6_i08_honest_contract.py tests/core/test_fcis_m6_i08_honest_delivery_contract.py
- python3 -m py_compile tools/check_fcis_m6_i08_honest_contract.py tests/core/test_fcis_m6_i08_honest_delivery_contract.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I08
- sha256sum --check --strict docs/research/m6_tasks/TASK_I08_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- The I08 checker accepted the exact four supported claims and the explicit
  research-only/unmounted status.
- Focused I08 suite passed: 5 passed.
- A positive claim mutation to network-level exactly-once wording rejected.
- An API-name mutation to exactly-once delivery rejected.
- Missing claim documentation, missing exactly-once nonclaim, and malformed
  claim surface mutations rejected.
- Ruff, formatting, strict mypy, Python compilation, packet validation, the
  source manifest, and diff whitespace checks pass.

MUTANTS_ADDED: None. The focused checker suite uses targeted in-memory
mutations as negative witnesses for unsupported positive wording, API naming,
documentation completeness, and nonclaim removal.

FORMAL_EVIDENCE: None. I08 supplies a machine-checked claim boundary and
human contract document; it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I08 does not prove atomic datastore behavior, destination idempotency,
  receipt bytes, local journal durability, or network delivery.
- I08 does not prove filesystem or power-loss durability, concurrent
  linearizability, runtime reachability, migration, no-bypass coverage,
  accounting, backing, or zUSD safety.
- The honest vocabulary gate does not promote I02-I07 research models to a
  mounted runtime.
- No caller, API, worker, destination, datastore, migration, or value-moving
  path is mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: The checker governs the declared contract document and API
vocabulary. It does not scan every historical repository sentence or prove
that an external destination honors the stated idempotency relation. Future
mounted adapters must retain the same claims and add mechanism-specific
refinement evidence before any broader delivery claim is made.
