# FCIS M6 Task D04 Report

TASK_ID: D04
BASE_SHA: 64db43c26683c529157d32b8c02a6df30e3bd24c
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C07-exact-migration-review-packet-20260801

IMPLEMENTATION_HEAD_SHA: 3acf6285f8a3feef32c838b2a459d18fd721ae8d
IMPLEMENTATION_TREE: 74df77d2830005d2faf5469a0a602e8b274228ae
IMPLEMENTATION_PARENT: 64db43c26683c529157d32b8c02a6df30e3bd24c

FILES_CHANGED:

- src/core/fcis_authority_dispatch.py
- src/core/fcis_authority_schema.py
- src/core/fcis_commit_bundle_derivation.py
- src/core/fcis_commit_bundle_values.py
- src/core/fcis_outbox_values.py
- tests/core/test_fcis_commit_bundle_derivation.py
- tests/core/test_fcis_m5_authority_admission.py
- experiments/fcis_m6_d04_anf_bundle_outbox_check.py
- docs/research/FCIS_M6_D04_ANF_BUNDLE_OUTBOX_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json
- docs/research/m6_tasks/TASK_D04_PLAN.md

CLAIM_IMPLEMENTED: D04 binds the exact Authority Normal Form root into the
commit-bundle and outbox planning layers. The ANF-bound bundle wrapper retains
the exact verified ANF, requires the receipt ANF root, recomputes that root
from the retained value, and derives the outbox from the same decision and ANF
identity. Bundle, decision, outbox, and outbox-root cross-field bindings are
checked before canonical bytes and roots are accepted. Legacy optional fields
remain available only for the compatibility path; the ANF-required builder
fails closed when the exact ANF is missing, foreign, or inconsistent.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_outbox_values.py src/core/fcis_commit_bundle_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_m5_authority_admission.py experiments/fcis_m6_d04_anf_bundle_outbox_check.py
- python3 -m ruff check src/core/fcis_outbox_values.py src/core/fcis_commit_bundle_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_m5_authority_admission.py experiments/fcis_m6_d04_anf_bundle_outbox_check.py
- python3 -m ruff format --check src/core/fcis_outbox_values.py src/core/fcis_commit_bundle_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_m5_authority_admission.py experiments/fcis_m6_d04_anf_bundle_outbox_check.py
- python3 -m mypy --strict src/core/fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_bundle_derivation.py experiments/fcis_m6_d04_anf_bundle_outbox_check.py
- python3 -m pytest -q tests/core/test_fcis_commit_bundle_derivation.py
- python3 -m pytest -q tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_source_bound_lineage.py tests/core/test_fcis_decision_derivation.py
- python3 -m json.tool docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json
- python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- python3 -m pytest -q tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D04
- sha256sum --check --strict docs/research/m6_tasks/TASK_D04_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:

- D04 focused commit-bundle tests passed: 30 passed.
- D04 focused plus upstream decision, lineage, source-bound, and reference
  regression tests passed: 105 passed.
- D04 deterministic checker passed: D04_ANF_BUNDLE_OUTBOX_MATCH.
- D03 deterministic checker passed: D03_ANF_RECEIPT_BINDING_MATCH.
- D02 deterministic checker passed: D02_SOURCE_BOUND_EVALUATION_MATCH.
- D01 deterministic vector checker passed: D01_VECTOR_MATCH.
- C07 deterministic packet checker passed: C07_REVIEW_PACKET_MATCH.
- The focused C01-C04/C06 dependency regression suite passed: 53 passed.
- Python compilation passed for all eight D04 Python files.
- Ruff check and format checks passed for all eight D04 Python files.
- Strict mypy passed for the three directly checked D04 files.
- The D04 JSON vector parsed successfully.
- The deterministic vector retained ANF root
  0xb55b6560d00eace98a04119f35df3d256f26be510299845b8d1655ef915c919c.
- The deterministic vector retained decision receipt root
  0xd955702494c885d179750b92df711e47be1a52d58218855f1c3156520797130a.
- The deterministic vector recomputed outbox root
  0xf08adde03a8f239cba555525c23809d99b5f8d3d62f4ed298a3dedf827528fd5.
- The deterministic vector recomputed bundle root
  0xc4867b171856122375350694f9ecb27341fb2d0e51d2b8d13e8f5c8125debcac.
- The deterministic bundle bytes digest is
  0xe34fc3cee259db69b12625c88a7b44c1e8239d7702684df47ec803a11443814a.
- The deterministic outbox record count is zero for the empty fixture.
- Task validator and source-manifest checks are run after the receipt files are
  created.
- No Lean proof, Julia execution, private ESSO run, production datastore
  adapter, mounted caller, runtime authority switch, remote implementation
  commit, hosted CI run, draft PR, merge, deployment, migration, or value
  movement is claimed.

MUTANTS_ADDED: Assertion-backed D04 cases cover missing exact ANF, foreign ANF
identity, crossed outbox plan, crossed decision, and stale cached bundle bytes
or root. The deterministic checker repeats the ANF, receipt, outbox, bundle,
canonical-root, and crossed-evidence assertions. These are research-model
mutants; no production mutation runner was used.

FORMAL_EVIDENCE: None added. D04 supplies typed executable bundle/outbox
binding evidence, a deterministic vector, canonical recomputation checks, and
negative tests. The general ANF theorem, TCG proof-context theorem, durable
datastore refinement, and production effect proof remain open.

REMAINING_NONCLAIMS:

- D04 is tested unmounted evidence for the ANF-bound Python bundle and outbox
  planning path.
- The retained ANF is a verified research-model value supplied to the builder;
  D04 does not authenticate its upstream construction or make caller data an
  opaque production authority witness.
- Optional legacy bundle and outbox fields remain compatibility surfaces. A
  no-bypass audit is required to show that every committable production path
  uses the ANF-required builder.
- D04 does not establish TCG inventory, proof-context validity, DRA history,
  migration epoch, datastore atomicity, caller authentication, destination
  acknowledgment provenance, no-bypass reachability, or value movement.
- The Python verifier adapters and deterministic fixtures are not production
  datastore, worker, network, or authority implementations.
- No Lean proof, Julia execution, private ESSO run, remote implementation
  commit, hosted CI run, draft PR, merge, deployment, migration, or value
  movement is claimed.

REVIEW_RISKS: The D04 core is a research-model binding layer and remains a
large audit hotspot. Optional compatibility fields and caller-supplied
research ANF values require downstream no-bypass and authority-witness
closure before promotion. The bundle/outbox roots demonstrate canonical
recomputation in the model; they do not refine a transactional datastore,
durable recovery, destination idempotency, or a mounted runtime path.
