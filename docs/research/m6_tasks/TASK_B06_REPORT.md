# FCIS M6 Task B06 Report

TASK_ID: B06
BASE_SHA: `5f24fae3587bb5a2262a9655ba8258b1b4272cde`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-B06-python-postconditions-20260731`

IMPLEMENTATION_HEAD_SHA: `cd88bc4b528feb3b03ebbd0e0aaff006eebe72dd`
IMPLEMENTATION_TREE: `11833bef96ae185d4cced814b67387d5c877247c`

FILES_CHANGED:

- `src/core/fcis_fee_apportionment_postconditions.py`
- `src/core/fcis_fee_apportionment_allocator.py`
- `tests/core/test_fcis_fee_apportionment_postconditions.py`
- `docs/research/m6_tasks/TASK_B06_REPORT.md`
- `docs/research/m6_tasks/TASK_B06_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_B06_SOURCE_MANIFEST.sha256`

CLAIM_IMPLEMENTED: The unmounted Python SRGD allocator now calls a separate
typed postcondition relation after computing an allocation and before creating
the controlled allocation value. The relation independently recomputes the
Euclidean quotas, checks the fixed role profile, zero-weight support, local
quota equality, aggregate conservation, bonus count and support, deterministic
score/tie selection, post-deficit recurrence, post-deficit conservation, and
the strict deficit bound. Any failure maps to the existing closed internal
relation rejection and produces no candidate.

COMMANDS_RUN:

- `python3 -m py_compile src/core/fcis_fee_apportionment_postconditions.py src/core/fcis_fee_apportionment_allocator.py tests/core/test_fcis_fee_apportionment_postconditions.py`
- `python3 -m ruff check src/core/fcis_fee_apportionment_postconditions.py src/core/fcis_fee_apportionment_allocator.py tests/core/test_fcis_fee_apportionment_postconditions.py`
- `python3 -m mypy --strict src/core/fcis_fee_apportionment_postconditions.py src/core/fcis_fee_apportionment_allocator.py src/core/fcis_fee_apportionment_transition.py`
- `python3 -m pytest -q tests/core/test_fcis_fee_apportionment_postconditions.py tests/core/test_fcis_fee_apportionment_allocator.py tests/core/test_fcis_fee_apportionment_selector.py tests/core/test_fcis_fee_apportionment_transition.py tests/core/test_fcis_fee_apportionment_width_mutants.py`
- `python3 tools/check_fcis_durable_retraction_model.py --self-test`
- `git diff --check`
- `git diff --cached --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks B06`

RESULTS:

- Python compilation: pass.
- Ruff: pass on the touched implementation and test files.
- Strict mypy: pass on the postcondition, allocator, and quota source
  boundary.
- Focused tests: `41 passed`.
- Public durable-retraction model self-test: pass; `14` actions, `10`
  invariants, `56` reachable states, and `268` enabled transitions. The
  current public self-test reported four model mutants killed.
- The selected B06 evidence validator passed after the final receipt commit.
- No caller, datastore adapter, authority switch, deployment, or value-moving
  path was mounted.

MUTANTS_ADDED: Seven named executable postcondition witnesses are included:

- `B06_SUM_ALLOCATIONS`: a changed role amount violates aggregate amount
  conservation.
- `B06_LOCAL_QUOTA`: a sum-preserving role amount outside its Euclidean
  lower-plus-bonus result is rejected.
- `B06_POST_DEFICIT_RECURRENCE`: a changed post deficit is rejected even when
  its sum remains zero.
- `B06_BONUS_ORDER`: a positive-support bonus with the wrong score/order is
  rejected.
- `B06_ZERO_WEIGHT_SUPPORT`: a mutated zero-weight role amount is rejected.
- `B06_FIXED_ROLE_PROFILE_DRIFT`: a changed shared role profile is rejected.
- `B06_NO_CANDIDATE_ON_RELATION_REJECT`: an injected postcondition rejection
  maps to an internal transition rejection before result construction.

FORMAL_EVIDENCE: None added. B06 supplies a closed executable relation and
negative witnesses. The B03-B05 Lean theorem chain remains a separate proof
lane and is not promoted by this Python check.

REMAINING_NONCLAIMS:

- B06 does not prove the general SRGD theorem or refine the Lean relation.
- B06 does not implement the Rust transition, U256/Kani proof, Python/Rust/
  Julia parity campaign, or grouping-compatibility theorem.
- B06 does not prove production consensus, API, datastore, authority,
  migration, effect, or value-moving behavior.
- B06 remains an unmounted research kernel and authorizes no value movement.
- The repository-local style classifier and security red-flags scripts were
  absent from this packet worktree and contribute no evidence.
- No remote implementation commit, hosted CI run, draft PR, or publication is
  claimed.

REVIEW_RISKS: The postcondition module deliberately duplicates the essential
  quota and selector calculations so a construction path cannot rely only on
  its producer's intermediate values. The relation is a 383-line critical
  hotspot and remains a research adapter with Python arbitrary-width integer
  semantics. Production-width and cross-runtime refinement remain open. The
  historical all-packet validator limitation remains; this selected B06 packet
  is validated independently.
