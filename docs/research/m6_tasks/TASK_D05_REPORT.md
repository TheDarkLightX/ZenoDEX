# FCIS M6 Task D05 Report

TASK_ID: D05
BASE_SHA: 8601a61154a00aafb1c7ba84d88939b0af4a2685
SOURCE_HEAD_SHA: 379e0717137fb122175995de7c20250856375151
SOURCE_HEAD_TREE: 5ff6f00973a948315d1c25575eab6c348055c5b2
BRANCH: codex/task-m6-receipt-rebind-20260802

IMPLEMENTATION_HEAD_SHA: cc6627f5d07ecbba27594650c9bd367850fb80a4
IMPLEMENTATION_TREE: 7af5f9e993e21b3fe7be03248adbe5a66e48eade
IMPLEMENTATION_PARENT: e52c52207b6f7df432331830f66f7ee294827f00

DEPENDENCY_REFRESH: The reviewed `.docker/entrypoint.sh` credential repair
changed a D05 deployment-source digest. The D05 vector was regenerated at the
exact functional head above; D05 implementation code is unchanged.

FILES_CHANGED:

- config/deploy/fcis_m6_tcg_inventory_v1.json
- .docker/entrypoint.sh (dependency source refresh)
- src/core/fcis_tcg_inventory.py
- tools/build_fcis_m6_d05_tcg_inventory.py
- experiments/fcis_m6_d05_tcg_inventory_check.py
- tests/core/test_fcis_m6_d05_tcg_inventory.py
- docs/research/m6_tasks/TASK_D05_TCG_INVENTORY_VECTOR.json
- docs/research/m6_tasks/FCIS_M6_D05_TCG_INVENTORY_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D05_PLAN.md

CLAIM_IMPLEMENTED: D05 adds a typed, source-derived publisher inventory for
the research Tree-Chord-Gate boundary. The imperative builder reads the
reviewed deployment/build configuration, hashes the exact configuration and
every declared source file, and constructs the typed inventory without taking
a runtime certificate, candidate topology root, or candidate instance root as
input. The closed inventory covers API, CLI, administrator, migration worker,
recovery worker, proof verifier, legacy runtime, background outbox worker, and
direct datastore adapter kinds. It derives a publisher inventory root and a
domain-separated anchored topology root for later external TCG checking.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_tcg_inventory.py tools/build_fcis_m6_d05_tcg_inventory.py experiments/fcis_m6_d05_tcg_inventory_check.py tests/core/test_fcis_m6_d05_tcg_inventory.py
- python3 -m ruff check src/core/fcis_tcg_inventory.py tools/build_fcis_m6_d05_tcg_inventory.py experiments/fcis_m6_d05_tcg_inventory_check.py tests/core/test_fcis_m6_d05_tcg_inventory.py
- python3 -m ruff format --check src/core/fcis_tcg_inventory.py tools/build_fcis_m6_d05_tcg_inventory.py experiments/fcis_m6_d05_tcg_inventory_check.py tests/core/test_fcis_m6_d05_tcg_inventory.py
- python3 -m mypy --strict src/core/fcis_tcg_inventory.py tools/build_fcis_m6_d05_tcg_inventory.py experiments/fcis_m6_d05_tcg_inventory_check.py tests/core/test_fcis_m6_d05_tcg_inventory.py
- python3 -m pytest -q tests/core/test_fcis_m6_d05_tcg_inventory.py
- python3 tools/build_fcis_m6_d05_tcg_inventory.py --check
- python3 experiments/fcis_m6_d05_tcg_inventory_check.py
- python3 -m json.tool docs/research/m6_tasks/TASK_D05_TCG_INVENTORY_VECTOR.json
- python3 -m pytest -q tests/core/test_fcis_m6_d05_tcg_inventory.py tests/core/test_fcis_tree_chord_gate_authority.py tests/core/test_fcis_authority_normal_form_v1.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_source_bound_lineage.py tests/core/test_fcis_decision_derivation.py
- python3 -m experiments.fcis_m6_d05_tcg_inventory_check
- python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- python3 -m pytest -q tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D05
- sha256sum --check --strict docs/research/m6_tasks/TASK_D05_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:

- D05 focused inventory tests passed: 6 passed.
- D05 plus TCG and D01-D04 upstream regression tests passed: 129 passed.
- D05 deterministic checker passed: D05_TCG_INVENTORY_MATCH.
- The source-derived builder vector check passed: D05_TCG_INVENTORY_MATCH.
- The D05 JSON vector parsed successfully.
- Python compilation passed for all four changed D05 Python files.
- Ruff check and format checks passed for all four changed D05 Python files.
- Strict mypy passed for all four changed D05 Python files.
- D04 deterministic checker passed: D04_ANF_BUNDLE_OUTBOX_MATCH.
- D03 deterministic checker passed: D03_ANF_RECEIPT_BINDING_MATCH.
- D02 deterministic checker passed: D02_SOURCE_BOUND_EVALUATION_MATCH.
- D01 deterministic vector checker passed: D01_VECTOR_MATCH.
- C07 deterministic packet checker passed: C07_REVIEW_PACKET_MATCH.
- The focused C01-C04/C06 dependency regression suite passed: 53 passed.
- The generated vector contains nine required publisher kinds and nineteen
  exact source-manifest entries.
- The source-derived inventory was regenerated at the exact implementation
  tree after the stacked runtime-source changes; no D05 constructor or verifier
  semantics changed in this refresh.
- The independently derived publisher inventory root is
  fe407a21588db0932df41b224234a5a5950478aa12cc1c564857b7a5bbc41ac2.
- The independently derived anchored topology root is
  9b2db149fd06876cf9e9fa592d891042320e52dcf0640c952431d913f12402e1.
- No Lean proof, Julia execution, private ESSO run, production deployment scan,
  mounted caller, runtime authority switch, merge, migration, deployment, or
  value movement is claimed.

MUTANTS_ADDED: D05 covers an inserted publisher changing both external roots,
omitted required publisher rejection, source-digest substitution changing both
roots, configuration substitution changing both roots, duplicate publisher ID
rejection, unanchored source rejection, and rejection of a payload that tries
to carry a runtime certificate or instance root. These are research-model
mutants; no production mutation runner was used.

FORMAL_EVIDENCE: None added. D05 supplies typed source-manifest evidence,
canonical root recomputation, a generated vector, and adversarial tests. The
formal TCG completeness theorem, deployment reachability proof, and no-bypass
closure remain open.

REMAINING_NONCLAIMS:

- D05 is tested unmounted evidence for a reviewed source inventory and its
  anchored topology root.
- The configuration is a reviewed input and the generator proves exactness
  relative to that input. D05 does not prove the configuration contains every
  production publisher, worker, direct write, deployment target, or effect
  sink.
- Source-file hashing does not prove runtime reachability, build inclusion,
  process isolation, caller authentication, datastore authority, or effect
  application semantics.
- The inventory does not yet bind a concrete TCG certificate, C3 claim set,
  proof context, DRA history, migration epoch, recovery transition, or
  destination acknowledgment to the topology root.
- No Lean proof, Julia execution, private ESSO run, production deployment scan,
  mounted caller, runtime authority switch, merge, migration, deployment, or
  value movement is claimed.

REVIEW_RISKS: D05 improves the external-anchor boundary while preserving the
main completeness risk: a manually reviewed configuration can omit a real
publisher. The source set includes research-model adapters for recovery,
outbox, and direct durable state because the production FCIS worker/datastore
mount is not present in this lane. Later R12 inventory and no-bypass work must
derive and audit the complete deployment/build surface before any promotion.
