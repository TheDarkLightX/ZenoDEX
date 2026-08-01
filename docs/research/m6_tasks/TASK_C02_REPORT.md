# FCIS M6 Task C02 Report

TASK_ID: C02
BASE_SHA: 5a34e7ac21f1c435b2fffd7e6a7693cff47f13b2
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C02-entitlement-key-20260801

IMPLEMENTATION_HEAD_SHA: dd76d0a2aacf4061a263bdf8a0c0a2f5bcb8597e
IMPLEMENTATION_TREE: 748078e8ca4b6316ed87e79c2bc0afa9c8becea7
IMPLEMENTATION_PARENT: 5a34e7ac21f1c435b2fffd7e6a7693cff47f13b2

FILES_CHANGED:

- src/core/fcis_entitlement_key_v1.py
- src/core/fcis_entitlement_key_codec_v1.py
- tests/core/test_fcis_entitlement_key_v1.py
- docs/research/FCIS_M6_C02_ENTITLEMENT_KEY_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_C02_PLAN.md
- docs/research/m6_tasks/TASK_C02_KEY_VECTOR.json
- docs/research/m6_tasks/TASK_C02_REPORT.md
- docs/research/m6_tasks/TASK_C02_EVIDENCE.json
- docs/research/m6_tasks/TASK_C02_SOURCE_MANIFEST.sha256

CLAIM_IMPLEMENTED: C02 adds the unmounted EntitlementKeyV1 value with exactly
the four fields fee_distribution_domain_id, asset, semantic_profile_id, and
fixed_role_order_id. The canonical codec emits only those fields under the
versioned entitlement-key schema. Semantic-profile and role-order values are
checked against the C01 registry. Domain changes change the key; destination,
custody, ordinary policy, and representation dimensions are absent from both
the value and codec.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_entitlement_key_v1.py src/core/fcis_entitlement_key_codec_v1.py tests/core/test_fcis_entitlement_key_v1.py
- python3 -m ruff check src/core/fcis_entitlement_key_v1.py src/core/fcis_entitlement_key_codec_v1.py tests/core/test_fcis_entitlement_key_v1.py
- python3 -m pytest -q tests/core/test_fcis_entitlement_key_v1.py
- python3 -m mypy --strict src/core/fcis_entitlement_key_v1.py src/core/fcis_entitlement_key_codec_v1.py tests/core/test_fcis_entitlement_key_v1.py
- python3 -c '<C02 vector parity command>'
- python3 -m json.tool docs/research/m6_tasks/TASK_C02_KEY_VECTOR.json
- git diff --check
- python3 .claude/skills/zenodex-style-map/scripts/which_style.py <C02 paths>
- python3 .claude/skills/zenodex-security-analysis/scripts/trust_surface.py
- python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py <C02 paths>
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks C02
- sha256sum --check --strict docs/research/m6_tasks/TASK_C02_SOURCE_MANIFEST.sha256

RESULTS:

- Python compilation passed.
- Ruff passed.
- Focused C02 tests passed: 12 passed.
- Strict mypy passed with no issues in all three new Python files.
- The canonical vector matched the codec bytes and digest exactly.
- The vector JSON parsed successfully.
- Git diff check passed.
- The repository-local style-map and security-analysis scripts are absent
  from this isolated repair tree; those commands are unavailable.
- The packet validator and manifest check are run after the receipt files are
  created.

MUTANTS_ADDED: Seven assertion-backed C02 mutants are covered: domain omitted
from the projection, destination inserted into the key, custody inserted into
the key, ordinary policy weights inserted into the key, representation inserted
into the key, role permutation accepted, and semantic-profile alias accepted.
No external mutation runner was used.

FORMAL_EVIDENCE: None added. The C02 result is executable typed-value and
canonical-byte evidence. The C01/Morph/M5 relation material is research input,
not a machine-checked theorem.

REMAINING_NONCLAIMS:

- C02 does not implement C03 migration manifests, C04 entry transport, or C05
  trace conjugacy.
- C02 does not rewire the existing FeeApportionmentKeyV2 B09 protocol.
- C02 does not establish authority, authentication, datastore durability,
  runtime integration, deployment, or value movement.
- No remote implementation commit, hosted CI run, draft PR, or production
  promotion is claimed.

REVIEW_RISKS: The new key is intentionally unmounted and additive. C03 must
bind it into a root-bound migration manifest without accepting caller-provided
state roots. Later runtime integration must preserve the exact four-field
projection and keep deployment replay protection in the surrounding
authority/context root.
