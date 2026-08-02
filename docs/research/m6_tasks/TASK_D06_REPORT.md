# FCIS M6 Task D06 Report

TASK_ID: D06
BASE_SHA: 4120fbd0a6cf52fb7ea3dc8595ab4b14143a67fb
SOURCE_HEAD_SHA: bdb8781861084a775a4c48a70afabc0545396354
SOURCE_HEAD_TREE: e114841afd3a06745c9780865a5af18de802f8a0
BRANCH: codex/task-m6-receipt-rebind-20260802
FILES_CHANGED:
- src/core/fcis_lineage_closure.py
- experiments/fcis_m6_d06_rule_manifest_check.py
- tests/core/test_fcis_m6_d06_rule_manifest.py
- docs/research/m6_tasks/TASK_D06_RULE_MANIFEST_VECTOR.json
- docs/research/FCIS_M6_D06_LINEAGE_RULE_MANIFEST_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D06_PLAN.md

CLAIM_IMPLEMENTED: D06 replaces the implicit C3 fixed rule tuple with a
private typed lineage rule manifest. The manifest validates exact rule IDs,
closed claim-key enum values, canonical unique dependency tuples, one writer
per derived key, complete derived-key coverage, acyclic dependencies, and
canonical topological order. Its domain-separated manifest root binds the
closed registry, rule definitions, and the bounded rule_count + 1 fixed-point
round limit. Authoritative closure delegates to this validated manifest. A
private test seam accepts only permutations of that exact rule set so bounded
rule-order independence can be exercised without adding caller-selected
production rules.

IMPLEMENTATION_HEAD_SHA: d8f4206f3a16ed61cdaaf5231bd8f62bcbe38c0f
IMPLEMENTATION_TREE: 38c3673fc185bd88ad5d452a099c65b44a965447
IMPLEMENTATION_PARENT: 22099f578978d621831bead94dede4a85d75305b

COMMANDS_RUN:
- python3 -m py_compile src/core/fcis_lineage_closure.py tests/core/test_fcis_m6_d06_rule_manifest.py experiments/fcis_m6_d06_rule_manifest_check.py
- python3 -m ruff check src/core/fcis_lineage_closure.py tests/core/test_fcis_m6_d06_rule_manifest.py experiments/fcis_m6_d06_rule_manifest_check.py
- python3 -m ruff format --check src/core/fcis_lineage_closure.py tests/core/test_fcis_m6_d06_rule_manifest.py experiments/fcis_m6_d06_rule_manifest_check.py
- python3 -m mypy --strict src/core/fcis_lineage_closure.py tests/core/test_fcis_m6_d06_rule_manifest.py experiments/fcis_m6_d06_rule_manifest_check.py
- python3 -m pytest -q tests/core/test_fcis_m6_d06_rule_manifest.py
- python3 -m pytest -q tests/core/test_fcis_m6_d06_rule_manifest.py tests/core/test_fcis_lineage_closure.py
- python3 -m pytest -q tests/core/test_fcis_m6_d06_rule_manifest.py tests/core/test_fcis_lineage_closure.py tests/core/test_fcis_m6_d05_tcg_inventory.py tests/core/test_fcis_tree_chord_gate_authority.py tests/core/test_fcis_authority_normal_form_v1.py tests/core/test_fcis_commit_bundle_derivation.py tests/core/test_fcis_commit_reference.py tests/core/test_fcis_m5_authority_admission.py tests/core/test_fcis_m6_d03_anf_receipt_binding.py tests/core/test_fcis_source_bound_lineage.py tests/core/test_fcis_decision_derivation.py tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 experiments/fcis_m6_d06_rule_manifest_check.py
- python3 -m experiments.fcis_m6_d06_rule_manifest_check
- python3 -m experiments.fcis_m6_d05_tcg_inventory_check
- python3 -m experiments.fcis_m6_d04_anf_bundle_outbox_check
- python3 -m experiments.fcis_m6_d03_anf_receipt_binding_check
- python3 -m experiments.fcis_m6_d02_source_bound_evaluation_check
- python3 -m experiments.fcis_m6_d01_vector_check
- python3 -m experiments.fcis_m6_c07_review_packet_check
- python3 -m json.tool docs/research/m6_tasks/TASK_D06_RULE_MANIFEST_VECTOR.json
- git diff --check

RESULTS:
- D06 focused tests passed: 6 passed.
- D06 plus existing C3 lineage tests passed: 16 passed.
- D06 plus C3, D01-D05, profile, and entitlement regression tests passed: 188 passed.
- The D06 checker passed: D06_LINEAGE_RULE_MANIFEST_MATCH.
- Upstream deterministic checkers passed: D05_TCG_INVENTORY_MATCH, D04_ANF_BUNDLE_OUTBOX_MATCH, D03_ANF_RECEIPT_BINDING_MATCH, D02_SOURCE_BOUND_EVALUATION_MATCH, D01_VECTOR_MATCH, and C07_REVIEW_PACKET_MATCH.
- The manifest contains four derived writers and the vector covers all 24 rule permutations.
- Python compilation, Ruff, Ruff formatting, and strict mypy passed for all three D06 Python files.
- The JSON vector parsed successfully.
- The D06 packet was rebound after the independently reviewed D04 repair
  changed the shared lineage-closure source. The D06 manifest checker and all
  24 declared rule permutations still pass at the exact source head.
- No Lean proof, Julia execution, private ESSO run, runtime mount, authority
  switch, merge, deployment, migration, or value movement is claimed.

MUTANTS_ADDED: D06 covers duplicate derived writer, missing derived-key writer,
cyclic dependency, reversed noncanonical rule order, manifest-root substitution,
foreign private closure rule set, and wrong dependency collection type. Each
mutation is rejected by focused tests or the deterministic checker and is
bound to a named manifest or closure invariant.

FORMAL_EVIDENCE: None. D06 supplies typed executable validation, a frozen
canonical vector, all-permutation bounded exploration, and mutation-killing
tests. It does not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- D06 is tested unmounted evidence for the concrete C3 rule registry in this
  module.
- The bounded permutation result is evidence on the declared finite rule set;
  it is not a general confluence theorem for arbitrary future registries.
- The manifest does not prove that all production claim producers, callers,
  datastores, deployment targets, or effect sinks are enumerated.
- D06 does not mount proof context, TCG completeness, DRA history, recovery,
  publication, outbox delivery, migration authority, destination idempotency,
  or value movement.
- No Lean, Julia, ESSO, production adapter, merge, deployment, or runtime
  authority change is claimed.

REVIEW_RISKS: The C3 module remains a high-complexity research hotspot. The
manifest is private and source-local, so future claim-key or rule additions
must update the closed registry, manifest, root vector, checker, and tests
together. D06 does not supply the production datastore or no-bypass reachability
proof required for M6 promotion.
