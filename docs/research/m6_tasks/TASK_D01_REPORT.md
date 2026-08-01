# FCIS M6 Task D01 Report

TASK_ID: D01
BASE_SHA: efa09ef7bc54c7f3c0ddede193e921c753563e99
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C07-exact-migration-review-packet-20260801

IMPLEMENTATION_HEAD_SHA: 2848840b20630aff2103083c42090b23b8b1d404
IMPLEMENTATION_TREE: e18eb488e35dc266894a3470f660a2b3de438f21
IMPLEMENTATION_PARENT: efa09ef7bc54c7f3c0ddede193e921c753563e99

FILES_CHANGED:

- src/core/fcis_authority_normal_form_v1.py
- tests/core/test_fcis_authority_normal_form_v1.py
- experiments/fcis_m6_d01_vector_check.py
- docs/research/m6_tasks/TASK_D01_AUTHORITY_NORMAL_FORM_VECTOR.json
- docs/research/FCIS_M6_D01_AUTHORITY_NORMAL_FORM_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_D01_PLAN.md
- docs/research/m6_tasks/TASK_D01_REPORT.md
- docs/research/m6_tasks/TASK_D01_EVIDENCE.json
- docs/research/m6_tasks/TASK_D01_SOURCE_MANIFEST.sha256

CLAIM_IMPLEMENTED: D01 defines one immutable unmounted
`FCISAuthorityNormalFormV1` carrier for the M6 R04 root tuple. It includes
source-bound command/context/pre-state and support roots, complete SLNF
boundary/policy/witness/semantic/lineage roots, candidate and next-state
roots, C3 claim/closure roots, acceptance and durability roots, TCG topology
and instance roots, an explicit proof-context presence policy, DRA pre/post
history roots, and the migration authority epoch root. The complete root is
freshly derived from canonical bytes; no cached root field is accepted.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_authority_normal_form_v1.py tests/core/test_fcis_authority_normal_form_v1.py experiments/fcis_m6_d01_vector_check.py
- python3 -m ruff check src/core/fcis_authority_normal_form_v1.py tests/core/test_fcis_authority_normal_form_v1.py experiments/fcis_m6_d01_vector_check.py
- python3 -m mypy --strict src/core/fcis_authority_normal_form_v1.py tests/core/test_fcis_authority_normal_form_v1.py experiments/fcis_m6_d01_vector_check.py
- pytest -q tests/core/test_fcis_authority_normal_form_v1.py
- python3 -m json.tool docs/research/m6_tasks/TASK_D01_AUTHORITY_NORMAL_FORM_VECTOR.json
- python3 -m experiments.fcis_m6_d01_vector_check
- pytest -q tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 -m experiments.fcis_m6_c07_review_packet_check
- git diff --cached --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D01
- sha256sum --check --strict docs/research/m6_tasks/TASK_D01_SOURCE_MANIFEST.sha256

RESULTS:

- D01 focused tests passed: 7 passed.
- D01 vector checker passed: D01_VECTOR_MATCH.
- C07 dependency packet checker passed: C07_REVIEW_PACKET_MATCH.
- Python compilation passed for the D01 module, tests, and vector checker.
- Ruff passed for the D01 module, tests, and vector checker.
- Strict mypy passed for the D01 module, tests, and vector checker.
- The focused C01-C04/C06 dependency regression suite passed: 53 passed.
- The retained D01 root is
  0x1a2ac6e298b57f8068c0f5b88e55ea1f7802e4771d28b20f9267bd6529c26433.
- Task validator passed: 19 manifest entries.
- Source-manifest check passed.

MUTANTS_ADDED: Assertion-backed D01 cases cover wrong exact input type,
unknown field, missing field, duplicate field, wrong schema, noncanonical
bytes, wrong root type, per-field root drift, required-proof-without-root,
and forbidden proof root when proof is not required. The metamorphic root
test changes each registered root field and requires a different complete ANF
root. No production mutation runner was used.

FORMAL_EVIDENCE: None added. D01 supplies typed executable carrier evidence,
canonical encode/decode evidence, and a deterministic root vector. C07 remains
the exact unmounted migration packet; later D10 owns the abstract ANF theorem.

REMAINING_NONCLAIMS:

- D01 checks supplied roots and recomputes the ANF carrier root; it does not
  authenticate the supplied roots or establish that upstream stages derived
  them from the same command and current state.
- D01 does not bind ANF into evaluation, acceptance receipts, commit bundles,
  outboxes, proof public inputs, TCG inventory, DRA publication, or any runtime
  caller.
- D01 does not prove TCG completeness, proof-context validity, datastore
  durability, migration authority, or value movement.
- No remote implementation commit, hosted CI run, draft PR, merge, deployment,
  production migration, or value movement is claimed.

REVIEW_RISKS: D01 is a scalar root carrier. A caller can still construct a
well-typed value from foreign roots until D02-D10 establish source-derived
recomputation and cross-axis equality. The optional proof-context policy is
closed at the value boundary but its authenticity remains a downstream
obligation.
