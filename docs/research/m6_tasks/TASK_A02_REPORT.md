# FCIS M6 Task A02 Report

TASK_ID: A02
BASE_SHA: `760a65eee950421148be615bb7c837b1ad737a83`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-A02-profile-ids-20260731`

FILES_CHANGED:

- `src/core/fcis_m6_profile_ids.py`
- `tests/core/test_fcis_m6_profile_ids.py`
- `docs/research/m6_tasks/TASK_A02_REPORT.md`
- `docs/research/m6_tasks/TASK_A02_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_A02_SOURCE_MANIFEST.sha256`

CLAIM_IMPLEMENTED: One immutable shared M6 identifier module records the
semantic allocator profile, SRGD and AGQE representation profiles, fixed role
order, fee domain, SLNF/source-bound/lineage versions, C3 claim keys, TCG
versions, DRA versions, proof-context version, and ANF version. The module
contains constants and immutable tuples only. Focused tests cover duplicate,
alias, order, and domain-collision identifier mutants.

COMMANDS_RUN:

- `python3 --version`
- `git --version`
- `python3 -m ruff --version`
- `python3 -m pytest --version`
- `python3 -m ruff check src/core/fcis_m6_profile_ids.py tests/core/test_fcis_m6_profile_ids.py`
- `python3 -m pytest -q tests/core/test_fcis_m6_profile_ids.py`
- `python3 -m py_compile src/core/fcis_m6_profile_ids.py tests/core/test_fcis_m6_profile_ids.py`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks A02`
- `git diff --check`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_A02_SOURCE_MANIFEST.sha256`

RESULTS:

- Python: `3.12.3`.
- Git: `2.54.0`.
- Ruff: `0.16.0`, focused check passes.
- Pytest: `7.4.4`, focused registry tests pass: `6 passed`.
- Python compilation passes for the new module and tests.
- Six assertion-backed identifier mutant cases cover duplicate semantic IDs,
  representation/semantic aliasing, duplicate representation IDs, role-order
  substitution, domain collision, and duplicate C3 claim keys.
- The selected A02 evidence packet validates through the shared A03 validator.

MUTANTS_ADDED: Six named identifier mutants are represented by exact
regression assertions. No external mutation runner was used.

FORMAL_EVIDENCE: None added. A02 freezes identifiers for later adapters; it
does not prove the semantic relation between the branch certificates.

REMAINING_NONCLAIMS:

- Existing M6 modules are not rewired to import this registry by A02.
- The registry does not establish authority, authenticate a caller, or mount a
  runtime transition.
- The `/v2` source-bound occurrence domain remains explicitly versioned; A02
  records the mapping and does not silently rename the inherited source.
- No datastore, API, migration, deployment, or value-moving path changed.

REVIEW_RISKS: Later integration must replace duplicate local constants only
through field- and preimage-reviewed adapters. A registry import alone does
not prove that existing hash preimages are unchanged.
