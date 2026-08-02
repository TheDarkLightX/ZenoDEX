# FCIS M6 Task I06 Report

TASK_ID: I06
BASE_SHA: 95bf4f1e426886129682f822dbefd43e488deb4a
SOURCE_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
SOURCE_HEAD_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_i06_lost_ack_recovery.py
- tests/core/test_fcis_m6_i06_lost_ack_recovery.py
- docs/research/m6_tasks/TASK_I06_LOST_ACK_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_I06_PLAN.md

IMPLEMENTATION_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
IMPLEMENTATION_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
IMPLEMENTATION_PARENT: c3213000060d3224e1291d2bbf9992e41f8fd74b

CLAIM_IMPLEMENTED: I06 adds a deterministic lost-ack recovery state machine
for one committed effect. The simulated crash retains the destination record
and drops the local acknowledgment. Recovery redelivers the exact original
effect, requires the destination to return ALREADY_ACCEPTED, verifies the
receipt through I05, and writes one local acknowledgment journal entry. State
construction and revalidation require a live I04 verifier-registered contract,
so an exact-class copied contract cannot enter recovery. A later redelivery
verifies the same acknowledgment without appending a second local write.

COMMANDS_RUN:
- python3 -m ruff check experiments/fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py experiments/fcis_m6_i06_lost_ack_recovery.py tests/core/test_fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i06_lost_ack_recovery.py
- python3 -m ruff format --check experiments/fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py experiments/fcis_m6_i06_lost_ack_recovery.py tests/core/test_fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i06_lost_ack_recovery.py
- python3 -m mypy --strict experiments/fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py experiments/fcis_m6_i06_lost_ack_recovery.py tests/core/test_fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i06_lost_ack_recovery.py
- python3 -m py_compile experiments/fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py experiments/fcis_m6_i06_lost_ack_recovery.py tests/core/test_fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i06_lost_ack_recovery.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i06_lost_ack_recovery.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i06_lost_ack_recovery.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I06
- sha256sum --check --strict docs/research/m6_tasks/TASK_I06_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Focused I06 suite passed: 9 passed.
- Combined I04/I05/I06 suite passed: 26 passed.
- The crash state preserves the destination record and original effect ID,
  payload root, destination, and adapter profile while containing no local ack.
- Redelivery returns the I04 ALREADY_ACCEPTED outcome, preserves the receipt
  root, passes I05 provenance verification, and records exactly one local ack.
- Repeated redelivery returns an already-durable no-op and leaves the local
  journal write count at one.
- Forged destination receipt roots, phase skipping, malformed state, and u32
  attempt-counter exhaustion reject without accepting a new semantic effect.
- Exact-class copied I04 contracts without verifier provenance reject during
  recovery-state construction.
- Ruff, formatting, strict mypy, Python compilation, packet validation, the
  source manifest, and diff whitespace checks pass.

MUTANTS_ADDED: The focused suite contains negative witnesses for
ack-before-delivery phase skipping, forged receipt provenance, attempt-counter
overflow, exact-class contracts without I04 verifier provenance, malformed
state, and repeated local-ack writes.

FORMAL_EVIDENCE: None. I06 supplies executable deterministic crash and
redelivery evidence; it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I06 does not prove filesystem or power-loss durability of the destination
  record or local journal.
- I06 does not implement a production worker, network transport, retry
  scheduler, destination adapter, or local durable datastore.
- I06 does not prove concurrent linearizability, runtime reachability,
  migration, no-bypass coverage, accounting, backing, or zUSD safety.
- No caller, API, destination, worker, datastore, or value-moving path is
  mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: The reference state treats the I04 destination record as
surviving the simulated crash and treats the local journal as the lost part of
the response. A production refinement must prove those distinct durability
profiles, retain the same effect ID through lease and retry logic, and bind
the real destination receipt to the I05 subject before writing its local ack.
The I04 registry is a research-model verifier premise and is not external
authentication.
