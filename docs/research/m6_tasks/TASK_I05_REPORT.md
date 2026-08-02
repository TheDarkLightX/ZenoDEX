# FCIS M6 Task I05 Report

TASK_ID: I05
BASE_SHA: 2c16013cd34fc76edec607004f883df63bb0245a
SOURCE_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
SOURCE_HEAD_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_i05_ack_provenance.py
- tests/core/test_fcis_m6_i05_ack_provenance.py
- docs/research/m6_tasks/TASK_I05_ACK_PROVENANCE_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_I05_PLAN.md

IMPLEMENTATION_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
IMPLEMENTATION_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
IMPLEMENTATION_PARENT: c3213000060d3224e1291d2bbf9992e41f8fd74b

CLAIM_IMPLEMENTED: I05 adds a verifier-gated acknowledgment provenance
model. An acknowledgment is accepted only when its effect, destination,
payload, destination receipt, adapter profile, verifier profile, and subject
root agree, and the exact destination record is present in the deterministic
I04 delivery state. I05 also requires a live I04 verifier-registered contract
at point of use, so an exact-class copied contract without verifier provenance
cannot enter the verifier. An acknowledgment before delivery, a foreign
receipt, a crossed effect and receipt, a foreign profile, an invalid candidate,
or a forged subject root rejects without creating an accepted acknowledgment.

COMMANDS_RUN:
- python3 -m ruff check experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i05_ack_provenance.py
- python3 -m ruff format --check experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i05_ack_provenance.py
- python3 -m mypy --strict experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i05_ack_provenance.py
- python3 -m py_compile experiments/fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i04_destination_dedup.py experiments/fcis_m6_i05_ack_provenance.py tests/core/test_fcis_m6_i05_ack_provenance.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i05_ack_provenance.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i04_destination_dedup.py tests/core/test_fcis_m6_i05_ack_provenance.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I05
- sha256sum --check --strict docs/research/m6_tasks/TASK_I05_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Focused I05 suite passed: 9 passed.
- Combined I04/I05 suite passed: 17 passed.
- Acknowledgments bind effect ID, destination, payload root, destination
  receipt root, adapter profile, verifier profile, and recomputed subject
  root.
- Acknowledgment-before-delivery, foreign receipt, crossed effect and
  receipt, foreign adapter or verifier profile, invalid candidate, and forged
  subject-root witnesses reject.
- The verifier recomputes the expected I04 receipt root and requires exact
  membership in the delivered destination record set.
- Exact-class copied I04 contracts without verifier provenance reject at I05
  point of use.
- Ruff, formatting, strict mypy, Python compilation, packet validation, the
  source manifest, and diff whitespace checks pass.

MUTANTS_ADDED: The focused suite contains negative witnesses for
ack-before-delivery, foreign receipt roots, crossed effect and receipt,
foreign adapter and verifier profiles, invalid candidate types, exact-class
contracts without I04 verifier provenance, and forged subject roots.

FORMAL_EVIDENCE: None. I05 supplies executable deterministic verifier
evidence; it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I05 does not prove receipt bytes from a real destination or any external
  destination's delivery behavior.
- I05 does not provide a production verifier identity, worker, retry scheduler,
  local durable acknowledgment journal, or lost-ack recovery.
- I05 does not prove concurrent linearizability, production datastore
  behavior, network behavior, runtime reachability, migration, no-bypass
  coverage, accounting, backing, or zUSD safety.
- I05 does not mount a caller, API, destination, worker, or value-moving path.
  M6 remains research-only and non-promotable.

REVIEW_RISKS: The verifier recomputes an I04 reference receipt from the
immutable research destination model and consumes a verifier-registered I04
witness. A production adapter must refine that receipt relation, preserve the
same provenance fields, and reject when it cannot establish delivery
membership. I06 must add local durable acknowledgment recovery after a
response loss. The registry is a research-model verifier premise and is not
external authentication.
