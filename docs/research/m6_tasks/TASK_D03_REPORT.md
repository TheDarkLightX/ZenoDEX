# FCIS M6 Task D03 Report

TASK_ID: D03
BASE_SHA: 0c5c6c822dee5ed1c18ccd83e9b15cd760a9703c
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C07-exact-migration-review-packet-20260801

IMPLEMENTATION_HEAD_SHA: a37698ba5aadd77c7fac192e52d8bcc5131d6788
IMPLEMENTATION_TREE: b3d3d320dd496589712481c787e26c127fa9b1e5
IMPLEMENTATION_PARENT: 0c5c6c822dee5ed1c18ccd83e9b15cd760a9703c

FILES_CHANGED:

- src/core/fcis_decision_values.py
- src/core/fcis_authority_schema.py
- src/core/fcis_authority_dispatch.py
- src/core/fcis_decision_derivation.py
- tests/core/test_fcis_m6_d03_anf_receipt_binding.py
- experiments/fcis_m6_d03_anf_receipt_binding_check.py
- docs/research/m6_tasks/TASK_D03_ANF_RECEIPT_BINDING_VECTOR.json
- docs/research/FCIS_M6_D03_ANF_RECEIPT_BINDING_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D03_PLAN.md

CLAIM_IMPLEMENTED: D03 extends the exact receipt binding with optional
compatibility fields for the pinned Authority Normal Form version and root.
The ANF-required source-bound decision path requires an exact ANF, cross-checks
all source-derived command/context/state/support/SLNF/budget/patch/plan fields,
and places the fresh ANF root in the canonical acceptance receipt bytes. The
canonical projector and dispatch retain the fields through admission and
round-trip. The acyclic pre-ANF receipt-root relation is explicit.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
- python3 -m ruff check src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
- python3 -m ruff format --check src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
- python3 -m mypy --strict src/core/fcis_decision_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_decision_derivation.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py experiments/fcis_m6_d03_anf_receipt_binding_check.py
- python3 -m pytest -q tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_decision_derivation.py tests/core/test_fcis_source_bound_lineage.py
- python3 -m json.tool docs/research/m6_tasks/TASK_D03_ANF_RECEIPT_BINDING_VECTOR.json
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- python3 -m pytest -q tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D03
- sha256sum --check --strict docs/research/m6_tasks/TASK_D03_SOURCE_MANIFEST.sha256

RESULTS:

- D03 focused plus M5/decision/lineage tests passed: 32 passed.
- D03 deterministic checker passed: D03_ANF_RECEIPT_BINDING_MATCH.
- D02 deterministic checker passed: D02_SOURCE_BOUND_EVALUATION_MATCH.
- D01 deterministic vector checker passed: D01_VECTOR_MATCH.
- C07 deterministic packet checker passed: C07_REVIEW_PACKET_MATCH.
- The focused C01-C04/C06 dependency regression suite passed: 53 passed.
- Python compilation passed for the four changed source modules, focused test,
  and deterministic checker.
- Ruff check and format checks passed for all six D03 Python files.
- Strict mypy passed for all six D03 Python files.
- The D03 JSON vector parsed successfully.
- The deterministic fixture retained ANF root
  0xb55b6560d00eace98a04119f35df3d256f26be510299845b8d1655ef915c919c.
- The fixture pre-ANF receipt binding root is
  0x4fd244d1dd5ee20ba5450021b4942b9e4ea614c9b56dff3db3ad26846b686ad0.
- Task validator and source-manifest checks are run after the receipt files are
  created.
- No remote implementation commit, hosted CI run, draft PR, merge,
  deployment, production migration, or value movement is claimed.

MUTANTS_ADDED: Assertion-backed D03 cases cover missing ANF, wrong exact ANF
type, crossed command/source fields, omitted ANF fields from canonical
projection, ANF-root loss from the final receipt, and receipt-root
recomputation drift. The deterministic checker repeats the source-field,
identity, canonical round-trip, and acyclic-root assertions. No production
mutation runner was used.

FORMAL_EVIDENCE: None added. D03 supplies typed executable receipt-schema
evidence, a deterministic ANF vector, and negative source-bound tests. The
formal ANF theorem and independently derived later authority roots remain open.

REMAINING_NONCLAIMS:

- D03 is tested unmounted evidence for the ANF-bound Python receipt path.
- Legacy receipts may carry empty compatibility ANF fields; the new
  ANF-required source-bound entry point rejects a missing or wrong exact ANF.
- D03 independently cross-checks source-derived fields only. TCG inventory,
  proof-context validity, DRA history, migration epoch, bundle, outbox,
  datastore state, caller authentication, and no-bypass reachability remain
  downstream obligations.
- The ANF acceptance_receipt_root field names the pre-ANF receipt binding root
  in this acyclic construction. It is not claimed to equal the final receipt
  root until later bundle/receipt closure.
- No remote implementation commit, hosted CI run, draft PR, merge, deployment,
  production migration, or value movement is claimed.

REVIEW_RISKS: The D03 receipt fields are structurally optional for legacy
compatibility, so production promotion still requires the no-bypass audit to
prove every committable path uses the ANF-required entry point. The D01 ANF
carrier remains caller-constructible research data; D03 binds and cross-checks
its identity without independently authenticating later TCG, proof, DRA, or
migration roots. The encrypted worktree has no remote publication or hosted
CI evidence.
