# FCIS M6 Task D04 Repair Report

TASK_ID: D04
BASE_SHA: 3acf6285f8a3feef32c838b2a459d18fd721ae8d
SOURCE_HEAD_SHA: d8f4206f3a16ed61cdaaf5231bd8f62bcbe38c0f
SOURCE_HEAD_TREE: 38c3673fc185bd88ad5d452a099c65b44a965447
BRANCH: codex/task-D04-anf-bundle-outbox-repair-20260801

IMPLEMENTATION_HEAD_SHA: d8f4206f3a16ed61cdaaf5231bd8f62bcbe38c0f
IMPLEMENTATION_TREE: 38c3673fc185bd88ad5d452a099c65b44a965447
IMPLEMENTATION_PARENT: 22099f578978d621831bead94dede4a85d75305b
ORIGINAL_D04_BASE: 64db43c26683c529157d32b8c02a6df30e3bd24c

FILES_CHANGED:

- src/state/state_snapshot_schema.py
- src/state/state_admission_profile.py
- src/core/fcis_outbox_values.py
- src/core/fcis_commit_bundle_values.py
- src/core/fcis_authority_schema.py
- src/core/fcis_authority_dispatch.py
- src/core/fcis_commit_bundle_derivation.py
- src/core/fcis_commit_reference.py
- src/core/fcis_lineage_closure.py
- tests/core/test_fcis_commit_bundle_derivation.py
- tests/core/test_fcis_commit_reference.py
- tests/core/test_fcis_m5_authority_admission.py
- tests/core/test_fcis_lineage_closure.py
- experiments/fcis_m6_d04_anf_bundle_outbox_check.py
- docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json
- docs/research/FCIS_M6_D04_ANF_BUNDLE_OUTBOX_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D04_PLAN.md

CLAIM_IMPLEMENTED: D04 now preserves the exact legacy V1 outbox-plan and
commit-bundle canonical ABI while placing ANF-bound claims under distinct V2
schema identities with a required authority-normal-form root. The controlled
builder retains the exact ANF value. The reference commit port recomputes and
verifies the ANF, outbox plan, outbox root, bundle bytes, and bundle root before
publication. Store validation repeats the same complete check over every
retained publication before retry classification. V1 bundle admission rejects
ANF-bound decisions, and lineage closure hashes each outbox through its exact
V1 or V2 schema.

COMMANDS_RUN:

- python3 -m py_compile experiments/fcis_m6_d04_anf_bundle_outbox_check.py src/core/fcis_authority_dispatch.py src/core/fcis_authority_schema.py src/core/fcis_commit_bundle_derivation.py src/core/fcis_commit_bundle_values.py src/core/fcis_commit_reference.py src/core/fcis_lineage_closure.py src/core/fcis_outbox_values.py src/state/state_admission_profile.py src/state/state_snapshot_schema.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m5_authority_admission.py
- python3 -m ruff check experiments/fcis_m6_d04_anf_bundle_outbox_check.py src/core/fcis_authority_dispatch.py src/core/fcis_authority_schema.py src/core/fcis_commit_bundle_derivation.py src/core/fcis_commit_bundle_values.py src/core/fcis_commit_reference.py src/core/fcis_lineage_closure.py src/core/fcis_outbox_values.py src/state/state_admission_profile.py src/state/state_snapshot_schema.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m5_authority_admission.py
- python3 -m ruff format --check experiments/fcis_m6_d04_anf_bundle_outbox_check.py src/core/fcis_authority_dispatch.py src/core/fcis_authority_schema.py src/core/fcis_commit_bundle_derivation.py src/core/fcis_commit_bundle_values.py src/core/fcis_commit_reference.py src/core/fcis_lineage_closure.py src/core/fcis_outbox_values.py src/state/state_admission_profile.py src/state/state_snapshot_schema.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m5_authority_admission.py
- python3 -m mypy --strict src/state/state_snapshot_schema.py src/state/state_admission_profile.py src/core/fcis_outbox_values.py src/core/fcis_commit_bundle_values.py src/core/fcis_authority_schema.py src/core/fcis_authority_dispatch.py src/core/fcis_commit_bundle_derivation.py src/core/fcis_commit_reference.py src/core/fcis_lineage_closure.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_lineage_closure.py experiments/fcis_m6_d04_anf_bundle_outbox_check.py
- python3 -m pytest -q tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_source_bound_lineage.py tests/core/test_fcis_decision_derivation.py tests/state/test_state_snapshot_schema_drift.py tests/state/test_state_admission_profile.py
- python3 -m pytest -q tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 -m json.tool docs/research/m6_tasks/TASK_D04_ANF_BUNDLE_OUTBOX_VECTOR.json
- python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- git diff --check 3acf6285f8a3feef32c838b2a459d18fd721ae8d..HEAD
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D04
- sha256sum --check --strict docs/research/m6_tasks/TASK_D04_SOURCE_MANIFEST.sha256

RESULTS:

- The focused D04, bundle, reference-port, authority-admission, lineage,
  decision, and state-schema suite passed: 148 passed.
- The focused C01-C04/C06 dependency regression suite passed: 53 passed.
- D04 deterministic checker passed: D04_ANF_BUNDLE_OUTBOX_MATCH.
- D03 deterministic checker passed: D03_ANF_RECEIPT_BINDING_MATCH.
- D02 deterministic checker passed: D02_SOURCE_BOUND_EVALUATION_MATCH.
- D01 deterministic checker passed: D01_VECTOR_MATCH.
- C07 deterministic checker passed: C07_REVIEW_PACKET_MATCH.
- Python compilation passed over 14 files; Ruff check and format passed over
  the same 14 files; strict mypy passed over 12 files.
- The deterministic V2 vector and legacy V1 golden vector passed.
- The legacy V1 outbox root remains
  0xf7ac577051aaac3bf3704a9a699c2174235c262c62716c1663b792d32cacc0e9.
- The legacy V1 bundle root remains
  0x0626a082ff542b69fd1a14f9384dd1b5aa54025633a460de37dd372416827ee0.
- The ANF-bound V2 outbox root is
  0xb11f4139cf327a3029fb2a789c7e5e8157344c28b071b41bf3ce8e943d659858.
- The ANF-bound V2 bundle root is
  0x7e6a1f04bb04e514c8fde2b2419845382ab7e2fabbbfd68da2a371f946bed9e1.
- An additional broad FCIS/state diagnostic produced 1360 passes and one
  inherited failure in the stale fee-apportionment source-hash fixture. The
  same failure exists at the reviewed D04 implementation base and was not
  regenerated during this focused repair.
- Task validation and source-manifest validation passed with 19 manifest
  entries. The exact-range whitespace gate is run after the receipt commit so
  it covers both the implementation and receipt trees.
- PR #502 is the review surface. No merge, runtime mount, deployment,
  authority switch, or value movement is claimed.

MUTANTS_ADDED: Permanent tests and the deterministic checker reject missing or
foreign retained ANF values at initial commit, corruption of a retained ANF
before retry, missing required V2 ANF roots, crossed V2 outer roots, crossed
decision or outbox lineage, stale cached roots, ANF-bound decisions admitted
through the V1 bundle schema, V2 outboxes hashed through the V1 schema, and any
drift from the frozen legacy V1 canonical bytes and roots.

FORMAL_EVIDENCE: None added. D04 supplies typed executable canonical-schema,
commit-port, replay, and mutation evidence. It does not add a Lean theorem or
claim production datastore refinement.

REMAINING_NONCLAIMS:

- D04 remains tested, unmounted Python reference evidence.
- The V2 schema registrations do not mount a production writer or acceptance
  path.
- Caller authentication, store-current state authority, atomic production
  publication, crash recovery, destination idempotency, TCG inventory,
  proof-context validity, DRA history, migration authority, and no-bypass
  reachability remain downstream obligations.
- The inherited fee-apportionment source-hash fixture remains stale and is
  outside this D04 authority surface.
- PR #502 is the review surface. No merge, deployment, production migration,
  authority switch, runtime mount, or value movement is claimed.

REVIEW_RISKS: The public wrapper remains named `CommitBundleV1` for compatibility
while its exact canonical claim and outbox values select V1 or V2 by retained
type and receipt binding. Production promotion still requires a no-bypass audit
that proves every ANF-bound committable path reaches the complete reference
verification relation, followed by a concrete datastore refinement. The broad
suite retains one unrelated stale source-hash failure.
