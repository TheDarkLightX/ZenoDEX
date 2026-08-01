# FCIS M6 Task D07 Report

TASK_ID: D07
BASE_SHA: 789ec7338b3ea75f49deb56ef38406141f85ce66
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C07-exact-migration-review-packet-20260801
FILES_CHANGED:
- src/core/fcis_stutter_receipt.py
- experiments/fcis_m6_d07_stutter_receipt_check.py
- tests/core/test_fcis_m6_d07_stutter_receipt.py
- docs/research/m6_tasks/TASK_D07_STUTTER_RECEIPT_VECTOR.json
- docs/research/FCIS_M6_D07_RQAG_STUTTER_RECEIPT_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D07_PLAN.md

CLAIM_IMPLEMENTED: D07 adds a controlled StutterReceiptV1 for the four
eligible RQAG observational identities: same-commit retry, canonical
reopen/re-encode, same-effect destination deduplication, and repeated pure
verification. The verifier requires exact canonical pre/post equality, exact
observable pre/post equality, a closed operation-kind enum, and canonical
lowercase 0x roots. It derives the pinned checker ID and verification root,
and the receipt exposes a derived receipt root. New commits, acknowledgment
publication, and migration are explicit non-stutter operation kinds and reject
before receipt construction. Direct receipt construction requires a private
verification token, and receipt revalidation recomputes checker and
verification bindings.

IMPLEMENTATION_HEAD_SHA: bb67fe7661e33f3c5f852779dfedc1dc8dcecb21
IMPLEMENTATION_TREE: 5c892af058607a38afb75fa79a0a6fcd799d77dc
IMPLEMENTATION_PARENT: 789ec7338b3ea75f49deb56ef38406141f85ce66

COMMANDS_RUN:
- python3 -m py_compile src/core/fcis_stutter_receipt.py tests/core/test_fcis_m6_d07_stutter_receipt.py experiments/fcis_m6_d07_stutter_receipt_check.py
- python3 -m ruff check src/core/fcis_stutter_receipt.py tests/core/test_fcis_m6_d07_stutter_receipt.py experiments/fcis_m6_d07_stutter_receipt_check.py
- python3 -m ruff format --check src/core/fcis_stutter_receipt.py tests/core/test_fcis_m6_d07_stutter_receipt.py experiments/fcis_m6_d07_stutter_receipt_check.py
- python3 -m mypy --strict src/core/fcis_stutter_receipt.py tests/core/test_fcis_m6_d07_stutter_receipt.py experiments/fcis_m6_d07_stutter_receipt_check.py
- python3 -m pytest -q tests/core/test_fcis_m6_d07_stutter_receipt.py
- python3 -m pytest -q tests/core/test_fcis_m6_d07_stutter_receipt.py tests/core/test_fcis_m6_d06_rule_manifest.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m6_d05_tcg_inventory.py tests/core/test_fcis_tree_chord_gate_authority.py tests/core/test_fcis_authority_normal_form_v1.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_source_bound_lineage.py tests/core/test_fcis_decision_derivation.py tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 -m experiments.fcis_m6_d07_stutter_receipt_check
- python3 -m experiments.fcis_m6_d06_rule_manifest_check
- python3 -m experiments.fcis_m6_d05_tcg_inventory_check
- python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- python3 -m json.tool docs/research/m6_tasks/TASK_D07_STUTTER_RECEIPT_VECTOR.json
- git diff --check

RESULTS:
- D07 focused tests passed: 9 passed.
- D07 plus C3, D01-D06, profile, and entitlement regression tests passed: 197 passed.
- The D07 checker passed: D07_STUTTER_RECEIPT_MATCH.
- Upstream deterministic checkers passed: D06_LINEAGE_RULE_MANIFEST_MATCH, D05_TCG_INVENTORY_MATCH, D04_ANF_BUNDLE_OUTBOX_MATCH, D03_ANF_RECEIPT_BINDING_MATCH, D02_SOURCE_BOUND_EVALUATION_MATCH, D01_VECTOR_MATCH, and C07_REVIEW_PACKET_MATCH.
- Python compilation, Ruff, Ruff formatting, and strict mypy passed for all three D07 Python files.
- The D07 vector parsed successfully.
- All four eligible operation kinds produced revalidatable receipts. New commit,
  acknowledgment publication, and migration mutants rejected with the stable
  forbidden-operation code.
- No Lean proof, Julia execution, private ESSO run, hosted CI run, remote
  publication, runtime mount, authority switch, deployment, migration, or
  value movement is claimed.

MUTANTS_ADDED: D07 covers new commit classified as stutter, acknowledgment
publication classified as stutter, migration classified as stutter, canonical
root change, observable root change, wrong operation-kind type, invalid root,
checker substitution, verification-root substitution, and direct receipt
construction. The focused tests and checker kill these mutants.

FORMAL_EVIDENCE: None. D07 supplies a closed typed executable relation,
derived roots, a frozen vector, deterministic rejection codes, and
mutation-killing tests. It does not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- D07 is tested unmounted evidence for the finite RQAG receipt language.
- The model trusts an upstream classifier to truthfully identify the concrete
  operation kind and operation identity; it does not inspect a production
  database or runtime trace.
- Same-effect destination deduplication remains a contract premise until a
  destination adapter proves idempotency and acknowledgment provenance.
- D07 does not prove TCG quotient completeness, C3/ANF composition, durable
  publication, recovery, migration authority, proof-context mounting, or value
  movement.
- No Lean, Julia, ESSO, production adapter, remote implementation commit,
  hosted CI run, draft PR, merge, deployment, migration, or runtime authority
  change is claimed.

REVIEW_RISKS: The receipt construction token is a research-layer boundary and
does not replace a production verifier or authenticated shell. Future RQAG
operation kinds require a new pinned checker, explicit semantic proof, vector,
mutants, and review. The operation-kind enum and external classifier must remain
synchronized before any quotient path is trusted.
