# FCIS M6 Task I04 Repair Report

TASK_ID: I04
BASE_SHA: f2cfbeef28f64a570e20aea97fb30a6af17ef75e
SOURCE_HEAD_SHA: 5e7c0824e06bfbafb8af6ba28e10dfa5cf1c48fb
SOURCE_HEAD_TREE: 1c9414653acd65cce22b6f89c90befc88ce80013
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_i04_destination_dedup.py
- tests/core/test_fcis_m6_i04_destination_dedup.py
- docs/research/m6_tasks/TASK_I04_DESTINATION_DEDUP_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_I04_PLAN.md

IMPLEMENTATION_HEAD_SHA: 5e7c0824e06bfbafb8af6ba28e10dfa5cf1c48fb
IMPLEMENTATION_TREE: 1c9414653acd65cce22b6f89c90befc88ce80013
IMPLEMENTATION_PARENT: f2cfbeef28f64a570e20aea97fb30a6af17ef75e

CLAIM_IMPLEMENTED: I04 retains the verifier-gated deterministic destination
deduplication model and now closes the destination-record collection at 8,192
records. Construction and explicit revalidation reject over-capacity state;
delivery at exact capacity returns CAPACITY_EXCEEDED without changing state.
Duplicate attempts retain the original receipt root, while payload,
destination, adapter-profile, unsupported-mechanism, and forged-contract
crossings reject.

COMMANDS_RUN:
- `python3 -m ruff format --check experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py`
- `python3 -m ruff check experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py`
- `python3 -m mypy --strict experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py`
- `python3 -m py_compile experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py`
- `PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i04_destination_dedup.py`
- `python3 -m json.tool docs/research/m6_tasks/TASK_I04_DESTINATION_DEDUP_SCHEMA_V1.json`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I04`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_I04_SOURCE_MANIFEST.sha256`
- `git diff --check`

RESULTS:
- Focused I04 suite passed: 7 passed.
- All three declared dedup mechanisms retain observational duplicate
  idempotence with stable effect, payload, and receipt roots.
- Same-ID payload mutation, destination crossing, and adapter-profile crossing
  reject without changing destination state.
- Over-capacity construction and revalidation reject with the typed I04Error.
- A new effect at exactly 8,192 records returns CAPACITY_EXCEEDED and leaves
  the state unchanged.
- Ruff, formatting, strict mypy, Python compilation, packet validation, source
  manifest verification, and diff whitespace checks pass.

MUTANTS_ADDED: Over-capacity construction, over-capacity revalidation, and
exact-capacity delivery are retained as negative witnesses in addition to the
existing payload, destination, adapter-profile, forged-contract,
unsupported-mechanism, duplicate, order, and invalid-effect witnesses.

FORMAL_EVIDENCE: None. I04 supplies executable deterministic adapter evidence;
it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I04 does not prove any external destination's native idempotency, query, or
  application receipt-table implementation.
- I04 does not verify acknowledgment provenance, destination receipt bytes,
  lost acknowledgments, worker delivery, retry recovery, or production
  concurrency.
- I04 does not prove runtime reachability, migration, no-bypass coverage,
  accounting, or zUSD safety. No production path is mounted.
- M6 remains research-only and non-promotable.

REVIEW_RISKS: The bound is enforced by the immutable reference state model. A
production adapter must preserve the same capacity, ordering, transaction,
and deduplication semantics through its own storage and destination evidence.
