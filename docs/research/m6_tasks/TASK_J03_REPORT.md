# FCIS M6 Task J03 Report

TASK_ID: J03
BASE_SHA: add3233005c6695a02b1b1bc4207bc837062ec32
SOURCE_HEAD_SHA: 88750b214de53623fcdca105fc37b5a90ff0c885
SOURCE_HEAD_TREE: 69f2f1c5f3e5532c5ea77cdbcea6653f2746ff41
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- tools/check_fcis_m6_j03_transport_map.py
- tests/core/test_fcis_m6_j03_transport_map.py
- docs/research/m6_tasks/TASK_J03_TRANSPORT_MAP_V1.json
- docs/research/m6_tasks/TASK_J03_PLAN.md

IMPLEMENTATION_HEAD_SHA: 88750b214de53623fcdca105fc37b5a90ff0c885
IMPLEMENTATION_TREE: 69f2f1c5f3e5532c5ea77cdbcea6653f2746ff41
IMPLEMENTATION_PARENT: add3233005c6695a02b1b1bc4207bc837062ec32

CLAIM_IMPLEMENTED: J03 adds a fail-closed eight-artifact migration transport
map covering state, configuration, residual fee history, proof contexts,
receipts, nullifiers, history, and outbox effects. Each row freezes a
preserve, recompute, proved-transport, invalidation, or forbidden decision,
source/target profile policy, boundary condition, checker/root obligations,
required evidence, acceptance gate, and unmounted nonclaims. Transport rows
cannot omit checker/root obligations; preserved rows cannot omit a preservation
condition; profile-sensitive mappings must match the frozen policy.

COMMANDS_RUN:
- python3 tools/check_fcis_m6_j03_transport_map.py docs/research/m6_tasks/TASK_J03_TRANSPORT_MAP_V1.json
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_j03_transport_map.py
- python3 -m ruff check tools/check_fcis_m6_j03_transport_map.py tests/core/test_fcis_m6_j03_transport_map.py
- python3 -m ruff format --check tools/check_fcis_m6_j03_transport_map.py tests/core/test_fcis_m6_j03_transport_map.py
- python3 -m mypy --strict tools/check_fcis_m6_j03_transport_map.py tests/core/test_fcis_m6_j03_transport_map.py
- python3 -m py_compile tools/check_fcis_m6_j03_transport_map.py tests/core/test_fcis_m6_j03_transport_map.py
- python3 -m json.tool docs/research/m6_tasks/TASK_J03_TRANSPORT_MAP_V1.json
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks J03
- sha256sum --check --strict docs/research/m6_tasks/TASK_J03_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- The J03 checker accepted all eight required artifact classes in exact order.
- Focused J03 suite passed: 5 passed.
- Missing checker/root transport evidence rejected.
- Unconditioned preservation rejected.
- A configuration mapping that silently preserved source configuration rejected.
- The schema parsed as valid JSON.
- Ruff, formatting, strict mypy, Python compilation, packet validation, the
  source manifest, and diff whitespace checks pass.

MUTANTS_ADDED: None. The focused suite contains negative witnesses for missing
transport roots, unconditioned preservation, and profile-boundary mapping
drift.

FORMAL_EVIDENCE: None. J03 supplies a machine-checked migration obligation
registry; it adds no machine-checked theorem or transport proof.

REMAINING_NONCLAIMS:
- J03 does not prove any state, fee, receipt, nullifier, history,
  proof-context, configuration, or outbox transport relation.
- J03 does not implement migration, writer exclusion, rollback, datastore
  behavior, runtime reachability, no-bypass coverage, accounting, backing, or
  zUSD safety.
- The checker does not promote a named checker ID or root placeholder into a
  proof receipt; those are future refinement obligations.
- No production migration, datastore, caller, worker, destination, or
  value-moving path is mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: J03 freezes policy and evidence requirements while transport
proofs remain open. Historical preservation rows need exact source-profile and
history-position binding, and transported rows need independent map checkers
with real roots before a migration authority switch can rely on them.
