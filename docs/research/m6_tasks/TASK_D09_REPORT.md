# FCIS M6 Task D09 Report

TASK_ID: D09
BASE_SHA: 2504f9c8bd6b9feb31e519eac76a3aa6db27b54b
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C07-exact-migration-review-packet-20260801
FILES_CHANGED:
- experiments/fcis_m6_d09_crossed_axis_temporal_check.py
- tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
- docs/research/m6_tasks/TASK_D09_CROSSED_AXIS_VECTOR.json
- docs/research/FCIS_M6_D09_CROSSED_AXIS_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D09_PLAN.md

CLAIM_IMPLEMENTED: D09 builds two independently valid D08 transition fixtures
with distinct ANF and bundle roots, crosses the required semantic, receipt,
bundle/outbox, TCG, DRA authority, and lineage axes, and checks exact typed
rejection codes. It also sends same-root new_commit and migration candidates to
the D07 stutter verifier and requires forbidden_operation rejection. The
result is a deterministic eight-mutant vector.

IMPLEMENTATION_HEAD_SHA: 6adf03af9124ae17044bce097e460b42211b21d7
IMPLEMENTATION_TREE: 84fe640a06dd79aec99032360aa688c2bd3c82d8
IMPLEMENTATION_PARENT: 2504f9c8bd6b9feb31e519eac76a3aa6db27b54b

COMMANDS_RUN:
- python3 -m py_compile experiments/fcis_m6_d09_crossed_axis_temporal_check.py tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
- python3 -m ruff check experiments/fcis_m6_d09_crossed_axis_temporal_check.py tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
- python3 -m ruff format --check experiments/fcis_m6_d09_crossed_axis_temporal_check.py tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
- python3 -m mypy --strict experiments/fcis_m6_d09_crossed_axis_temporal_check.py tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_d09_crossed_axis_temporal.py
- PYTHONPATH=. python3 experiments/fcis_m6_d09_crossed_axis_temporal_check.py
- PYTHONPATH=. python3 experiments/fcis_m6_d08_combined_anf_check.py
- python3 -m experiments.fcis_m6_d07_stutter_receipt_check
- python3 -m experiments.fcis_m6_d06_rule_manifest_check
- python3 -m experiments.fcis_m6_d05_tcg_inventory_check
- python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- python3 -m json.tool docs/research/m6_tasks/TASK_D09_CROSSED_AXIS_VECTOR.json
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D09
- sha256sum --check --strict docs/research/m6_tasks/TASK_D09_SOURCE_MANIFEST.sha256

RESULTS:
- D09 focused tests passed: 3 passed.
- The D09 checker passed: D09_CROSSED_AXIS_MATCH.
- Two valid transitions were independently accepted by D08 and had distinct
  ANF roots and base bundle roots.
- All eight required mutants were killed with exact codes:
  source_lineage_mismatch for the three crossed source/base axes,
  tcg_rejected for foreign TCG topology, publication_rejected for the
  foreign DRA authority epoch, anf_base_binding_mismatch for semantic/lineage
  crossing, and forbidden_operation for new commit and migration stutters.
- D08 rechecked successfully: D08_COMBINED_ANF_MATCH.
- Upstream deterministic checkers passed: D07_STUTTER_RECEIPT_MATCH,
  D06_LINEAGE_RULE_MANIFEST_MATCH, D05_TCG_INVENTORY_MATCH,
  D04_ANF_BUNDLE_OUTBOX_MATCH, D03_ANF_RECEIPT_BINDING_MATCH,
  D02_SOURCE_BOUND_EVALUATION_MATCH, D01_VECTOR_MATCH, and
  C07_REVIEW_PACKET_MATCH.
- Python compilation, Ruff, Ruff formatting, and strict mypy passed for both
  D09 Python files.
- The D09 vector parsed successfully.
- No Lean proof, Julia execution, private ESSO run, hosted CI run, remote
  publication, runtime mount, authority switch, deployment, migration, or
  value movement is claimed.

MUTANTS_ADDED: D09 adds semantic-transition-1/receipt-transition-2,
receipt-transition-1/bundle-transition-2, bundle-transition-1/outbox-
transition-2, foreign TCG topology, foreign DRA authority epoch,
same-semantic/different-lineage, stutter-hidden new commit, and
stutter-hidden migration. Every named mutant is rejected by the relevant D08
or D07 verifier.

FORMAL_EVIDENCE: None. D09 supplies two finite valid transition fixtures, a
frozen eight-case vector, exact rejection codes, and focused mutation tests.
It does not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- D09 is tested unmounted mutation evidence over two finite research fixtures.
- The three crossed-axis cases are rejected at D08 source/base lineage
  coherence; they do not prove production row-level isolation or transaction
  atomicity.
- D09 does not prove TCG completeness, proof soundness, datastore isolation,
  crash recovery, destination idempotency, API no-bypass coverage, migration
  authority, deployment identity, or value movement.
- No Lean, Julia, ESSO, production adapter, remote implementation commit,
  hosted CI run, draft PR, merge, deployment, migration, or runtime authority
  change is claimed.

REVIEW_RISKS: The second transition is assembled through a controlled fixture
input swap and the D08 builder. The bundle/outbox mutant uses the complete
foreign base bundle so the D08 lineage boundary rejects before outbox
reconstruction. A future production mutant lane must cross actual independently
stored rows and concurrent transactions, then retain the same named invariant
and exact rejection boundary.

