# FCIS M6 Task J05 Report

TASK_ID: J05
BASE_SHA: bd42cd9bb7f09009e955cf8c105bb6925598ddb7
SOURCE_HEAD_SHA: e85ec2aecc51221dad9624d05683b8e8d550c47b
SOURCE_HEAD_TREE: f9f392bf06548f089bf1d675624827d1769e90d7
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_j05_shadow_dual_check.py
- tests/core/test_fcis_m6_j05_shadow_dual_check.py
- docs/research/m6_tasks/TASK_J05_SHADOW_DUAL_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_J05_PLAN.md

IMPLEMENTATION_HEAD_SHA: e85ec2aecc51221dad9624d05683b8e8d550c47b
IMPLEMENTATION_TREE: f9f392bf06548f089bf1d675624827d1769e90d7
IMPLEMENTATION_PARENT: bd42cd9bb7f09009e955cf8c105bb6925598ddb7

CLAIM_IMPLEMENTED: J05 adds a deterministic shadow replay and dual-check
model bound to the J04 manifest root, activation sequence, and target profile.
Exact equality or the one declared reviewed refinement relation may allow phase
progression. Divergence is retained as non-authoritative evidence and blocks
progression. Shadow output cannot carry authority; forged relation roots,
foreign profiles, sequence crossings, and unknown modes reject.

COMMANDS_RUN:
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_j05_shadow_dual_check.py
- python3 -m ruff check experiments/fcis_m6_j05_shadow_dual_check.py tests/core/test_fcis_m6_j05_shadow_dual_check.py
- python3 -m ruff format --check experiments/fcis_m6_j05_shadow_dual_check.py tests/core/test_fcis_m6_j05_shadow_dual_check.py
- python3 -m mypy --strict experiments/fcis_m6_j05_shadow_dual_check.py tests/core/test_fcis_m6_j05_shadow_dual_check.py
- python3 -m py_compile experiments/fcis_m6_j05_shadow_dual_check.py tests/core/test_fcis_m6_j05_shadow_dual_check.py
- python3 -m json.tool docs/research/m6_tasks/TASK_J05_SHADOW_DUAL_SCHEMA_V1.json
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks J05
- sha256sum --check --strict docs/research/m6_tasks/TASK_J05_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Exact equality produced a match with phase progression allowed.
- The declared reviewed refinement produced a match with phase progression
  allowed.
- Divergent target output was retained with `phase_advance_allowed = false`
  and an explicit non-authoritative divergence record.
- Forged relation roots rejected.
- Authoritative shadow output construction rejected.
- Foreign target profile and activation-sequence crossings rejected.
- Focused J05 suite passed: 6 passed.
- The schema parsed as valid JSON.
- Ruff, formatting, strict mypy, Python compilation, packet validation, the
  source manifest, and diff whitespace checks pass.

MUTANTS_ADDED: None. The focused suite contains negative witnesses for forged
relation roots, authoritative shadow output, profile crossing, sequence
crossing, and retained divergence.

FORMAL_EVIDENCE: None. J05 supplies executable replay/comparison evidence; it
adds no machine-checked theorem or production refinement proof.

REMAINING_NONCLAIMS:
- J05 does not run a production shadow runner or prove the reviewed refinement
  relation for real state.
- J05 does not implement phase advancement, quiescence, writer exclusion,
  migration transport, rollback, datastore behavior, runtime reachability,
  no-bypass coverage, accounting, backing, or zUSD safety.
- The reviewed relation is a bounded model relation and does not authorize
  target state by itself.
- No production migration, caller, API, worker, datastore, deployment, or
  value-moving path is mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: The reviewed refinement branch is intentionally narrow and
deterministic. A production migration must replace it with an independently
reviewed semantic relation and bind its receipt to the J04 manifest and
authority epoch before phase progression.
