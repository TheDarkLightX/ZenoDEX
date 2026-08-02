# FCIS M6 Task I04 Repair Report

TASK_ID: I04
BASE_SHA: 8cf31c666babeca23b50c67b4fd3438669a08997
SOURCE_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
SOURCE_HEAD_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_i04_destination_dedup.py
- tests/core/test_fcis_m6_i04_destination_dedup.py
- docs/research/m6_tasks/TASK_I04_DESTINATION_DEDUP_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_I04_PLAN.md

IMPLEMENTATION_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
IMPLEMENTATION_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
IMPLEMENTATION_PARENT: c3213000060d3224e1291d2bbf9992e41f8fd74b

CLAIM_IMPLEMENTED: I04 retains the verifier-gated deterministic destination
deduplication model and now closes the destination-record collection at 8,192
records. Verified contracts are minted only by the verifier boundary,
registered with an immutable snapshot, and revalidated freshly at delivery;
direct, forged, or mutated exact-class contracts return UNMOUNTABLE.
The exported verifier-provenance predicate is used by downstream I05 and I06
consumers at their own points of use.
Destination state recursively revalidates every nested record. Construction
and explicit revalidation reject over-capacity state; delivery at exact
capacity returns CAPACITY_EXCEEDED without changing state. Duplicate attempts
retain the original receipt root, while payload, destination, adapter-profile,
unsupported-mechanism, and forged-contract crossings reject.

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
- Direct constructor, exact-class forgery, and mutated-witness delivery
  rejection passed.
- Downstream point-of-use consumers reject exact-class forged contracts.
- Nested destination-record field revalidation passed.
- Focused I04 suite passed: 8 passed.
- All three declared dedup mechanisms retain observational duplicate
  idempotence with stable effect, payload, and receipt roots.
- Same-ID payload mutation, destination crossing, and adapter-profile crossing
  reject without changing destination state.
- Over-capacity construction and revalidation reject with the typed I04Error;
  forged invalid state presented to delivery returns STATE_INVALID and a safe
  empty state.
- A new effect at exactly 8,192 records returns CAPACITY_EXCEEDED and leaves
  the state unchanged.
- Ruff, formatting, strict mypy, Python compilation, packet validation, source
  manifest verification, and diff whitespace checks pass.

MUTANTS_ADDED: Over-capacity construction, over-capacity revalidation, forged
state revalidation, exact-capacity delivery, direct verified-contract
construction, exact-class contract forgery, mutated registered contract, and
malformed nested record fields are retained as negative witnesses in addition
to the existing payload, destination, adapter-profile, unsupported-mechanism,
duplicate, order, and invalid-effect witnesses.

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

REVIEW_RISKS: The bound and witness registry are enforced by the immutable
reference state model. A production adapter must preserve the same capacity,
ordering, transaction, provenance, and deduplication semantics through its own
storage and destination evidence. The registry is a research-model verifier
premise and is not external authentication.
