# FCIS M6 Task D08 Report

TASK_ID: D08
BASE_SHA: f721d3bc11929c7649f93655f362e7ee0cc13a07
SOURCE_HEAD_SHA: cc6627f5d07ecbba27594650c9bd367850fb80a4
SOURCE_HEAD_TREE: 7af5f9e993e21b3fe7be03248adbe5a66e48eade
BRANCH: codex/task-D08-replayable-accept-20260802
FILES_CHANGED:
- src/core/fcis_m6_d08_combined_anf.py
- experiments/fcis_m6_d08_combined_anf_check.py
- tests/core/test_fcis_m6_d08_combined_anf.py
- docs/research/m6_tasks/TASK_D08_COMBINED_ANF_VECTOR.json
- docs/research/FCIS_M6_D08_COMBINED_ANF_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D08_PLAN.md

CLAIM_IMPLEMENTED: D08 composes source-bound lineage and C3 closure, anchored
TCG evidence, structural proof-context binding, durable PRE/POST history
reconstruction, and ANF-bound decision/bundle evaluation into one fail-closed
research verifier. Each stage recomputes its own source before the later stage
is evaluated. A successful result owns the complete canonical
`PublicationAtomV1` used by the later publication port, rather than returning
an ANF root alongside caller-selected publication fields. The acceptance
result retains the complete exact verifier instance. Every authority-bearing
use freshly replays that instance and compares the recomputed ANF root and
publication atom. No weak-reference registry, object-ID snapshot table, or
other mutable process-global acceptance state remains. After restart, the
retained exact instance can be verified again to mint a new process-local
acceptance wrapper. D08 rejects
later-root substitution, crossed or malformed TCG evidence, missing proof
context, publication/history mismatch, and source extraction failures.

IMPLEMENTATION_HEAD_SHA: cc6627f5d07ecbba27594650c9bd367850fb80a4
IMPLEMENTATION_TREE: 7af5f9e993e21b3fe7be03248adbe5a66e48eade
IMPLEMENTATION_PARENT: e52c52207b6f7df432331830f66f7ee294827f00

COMMANDS_RUN:
- python3 -m py_compile src/core/fcis_m6_d08_combined_anf.py tests/core/test_fcis_m6_d08_combined_anf.py experiments/fcis_m6_d08_combined_anf_check.py
- python3 -m ruff check src/core/fcis_m6_d08_combined_anf.py tests/core/test_fcis_m6_d08_combined_anf.py experiments/fcis_m6_d08_combined_anf_check.py
- python3 -m ruff format --check src/core/fcis_m6_d08_combined_anf.py tests/core/test_fcis_m6_d08_combined_anf.py experiments/fcis_m6_d08_combined_anf_check.py
- python3 -m mypy --strict src/core/fcis_m6_d08_combined_anf.py tests/core/test_fcis_m6_d08_combined_anf.py experiments/fcis_m6_d08_combined_anf_check.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_d08_combined_anf.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_d08_combined_anf.py tests/core/test_fcis_m6_d09_crossed_axis_temporal.py tests/core/test_fcis_m6_k02_commit_port.py tests/core/test_fcis_m6_d07_stutter_receipt.py tests/core/test_fcis_m6_d06_rule_manifest.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m6_d05_tcg_inventory.py tests/core/test_fcis_tree_chord_gate_authority.py tests/core/test_fcis_authority_normal_form_v1.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_source_bound_lineage.py tests/core/test_fcis_decision_derivation.py tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h04_crash_recovery.py tests/tools/test_fcis_m6_k05_bypass_mutation.py
- PYTHONPATH=. python3 experiments/fcis_m6_d08_combined_anf_check.py
- PYTHONPATH=. python3 experiments/fcis_m6_d08_combined_anf_check.py --write-vector
- python3 -m experiments.fcis_m6_d07_stutter_receipt_check
- python3 -m experiments.fcis_m6_d06_rule_manifest_check
- python3 -m experiments.fcis_m6_d05_tcg_inventory_check
- python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- python3 -m json.tool docs/research/m6_tasks/TASK_D08_COMBINED_ANF_VECTOR.json
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D08
- sha256sum --check --strict docs/research/m6_tasks/TASK_D08_SOURCE_MANIFEST.sha256

RESULTS:
- D08 focused tests passed: 7 passed.
- D08, D09, K02, and upstream dependency regression tests passed: 224 passed.
- H02/H03/H04/K05 publication, crash, recovery, and bypass regression tests
  passed: 50 passed.
- The D08 checker passed: D08_COMBINED_ANF_MATCH.
- The checker killed five targeted mutants: foreign TCG topology, foreign C3 root,
  foreign proof root/context, foreign publication authority state, and base
  decision substituted for the later ANF decision.
- The successful acceptance retains the complete verifier input and owns the
  exact recomputed publication atom. A second fresh verification produces the
  same ANF root and atom without consulting process-global registration.
- Point-of-use replay rejects a crossed retained instance even when the outer
  acceptance fields are left unchanged; downstream K02 rejects a forged
  exact-class acceptance object.
- The focused tests additionally covered wrong exact type, source extraction
  failure, missing proof context, PRE/POST history mismatch, later decision
  substitution, and malformed TCG evidence.
- Upstream deterministic checkers passed: D07_STUTTER_RECEIPT_MATCH,
  D06_LINEAGE_RULE_MANIFEST_MATCH, D05_TCG_INVENTORY_MATCH,
  D04_ANF_BUNDLE_OUTBOX_MATCH, D03_ANF_RECEIPT_BINDING_MATCH,
  D02_SOURCE_BOUND_EVALUATION_MATCH, D01_VECTOR_MATCH, and
  C07_REVIEW_PACKET_MATCH.
- The D08 vector parsed and matched regenerated roots exactly.
- Python compilation, Ruff, Ruff formatting, and strict mypy passed for all
  three D08 Python files.
- No Lean proof, Julia execution, private ESSO run, runtime mount, authority
  switch, merge, deployment, migration, or value movement is claimed.

MUTANTS_ADDED: D08 covers TCG topology substitution, C3 claim-root
substitution, proof-context substitution, publication authority substitution,
later decision substitution, wrong exact instance type, source extraction
failure, missing proof context, crossed PRE/POST history, and malformed TCG
certificate, and crossed retained verifier instance. Focused tests and the
deterministic checker reject each named mutation at the relevant stage. The
downstream publication witness also retains the exact-class
acceptance-forgery negative case.

FORMAL_EVIDENCE: None. D08 supplies a typed executable composition relation, a
canonical output vector, deterministic rejection codes, and mutation-killing
tests. The proof-context field is structural evidence and is not a
machine-checked or cryptographic proof.

REMAINING_NONCLAIMS:
- D08 is tested unmounted evidence for the finite composition language.
- The acceptance wrapper is process-local. Restart recovery re-verifies the
  retained exact instance; it does not deserialize or trust a prior wrapper.
- TCG inventory, certificate, and proof context remain supplied research
  premises until their production sources and verifiers are mounted.
- The DRA snapshot relation does not refine a production datastore transaction,
  crash protocol, recovery worker, or concurrent CAS.
- D08 does not prove source-input authentication, TCG completeness, destination
  idempotency, API no-bypass coverage, migration authority, deployment
  identity, or value movement.
- No Lean, Julia, ESSO, production adapter, merge, deployment, migration, or
  runtime authority change is claimed.

REVIEW_RISKS: The combined verifier is an 821-line research hotspot and uses
pre-ANF base artifacts to keep TCG and DRA roots acyclic. Review should preserve
that stage order. The structural proof-context check must not be promoted to
proof verification. Production refinement still requires authenticated source
inputs, a transactional datastore adapter, crash injection, effect-worker
provenance, caller/no-bypass audit, and a mounted authority lifecycle.
