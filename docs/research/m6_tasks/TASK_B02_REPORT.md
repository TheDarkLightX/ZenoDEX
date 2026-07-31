# FCIS M6 Task B02 Report

TASK_ID: B02
BASE_SHA: `d00cbaf35aea6d86c49ff4d2f58c906330df0198`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-B02-exact-selector-20260731`

IMPLEMENTATION_HEAD_SHA: `ff1da03a4be13a87390466f5f60c2dbb7254d2d4`
IMPLEMENTATION_TREE: `b97456cf8abb25a579699535706f52d8d8c9936f`

FILES_CHANGED:

- `src/core/fcis_fee_apportionment_selector.py`
- `src/core/fcis_fee_apportionment_allocator.py`
- `tests/core/test_fcis_fee_apportionment_selector.py`
- `tools/build_fcis_fee_apportionment_v2_golden.py`
- `tests/fixtures/fcis_fee_apportionment_v2_golden.json`
- `docs/research/m6_tasks/TASK_B02_REPORT.md`
- `docs/research/m6_tasks/TASK_B02_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_B02_SOURCE_MANIFEST.sha256`

CLAIM_IMPLEMENTED: The SRGD selector is now a typed exact three-role
relation. It computes `h = sum(fractions) // D`, admits only positive-
remainder roles, ranks `deficit + fraction`, and resolves equal scores by the
frozen buyback, treasury, rewards order. The result is a three-bit immutable
selection value or a stable typed rejection. The allocator uses the selector
through a compatibility wrapper, and the golden-vector source closure hashes
the selector module.

COMMANDS_RUN:

- `python3 -m py_compile` over the B02 selector, allocator, and selector tests
- `python3 -m ruff check` over the B02 source, tests, and golden builder
- `python3 -m mypy --strict` over the selector, quota primitive, and allocator
- `python3 -m pytest -q` over the four inherited fee-apportionment tests, the
  B01 tests, and the B02 selector tests
- `python3 tools/build_fcis_fee_apportionment_v2_golden.py`
- `python3 tools/build_fcis_fee_apportionment_v2_golden.py --check`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_B02_SOURCE_MANIFEST.sha256`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks B02`
- `git diff --check`
- `git diff --cached --check`

RESULTS:

- Focused FCIS fee-apportionment tests: `45 passed`.
- Golden fixture regeneration and freshness check: pass; 12 cases.
- Ruff: pass.
- Strict mypy: pass for 3 touched source modules.
- Python compilation: pass.
- Exact tie, current-fraction score, positive-support, seat-count, fixed-role
  order, shape, type, and stable-rejection witnesses pass.
- No runtime caller, datastore adapter, authority switch, deployment, or
  value-moving path was mounted.

MUTANTS_ADDED: Five named selector mutation witnesses are encoded in the B02
tests:

- `B02_OMIT_CURRENT_FRACTION`: score ranking must include the current fraction.
- `B02_REVERSE_FIXED_TIE_ORDER`: equal scores select the frozen role order.
- `B02_SELECT_ZERO_REMAINDER_ROLE`: bonus bits require positive support.
- `B02_SELECT_WRONG_SEAT_COUNT`: bonus-bit sum equals the exact residual seat
  count.
- `B02_UNORDERED_ROLE_MAPPING`: the selector contains no unordered mapping
  construction and returns the fixed three-bit tuple.

The typed invalid-shape and stable-rejection cases also cover wrong arity,
Boolean values, denominator failure, nondivisible residuals, and deficit or
fraction bounds. No external mutation runner was used.

FORMAL_EVIDENCE: None added. B02 supplies executable selector and refinement
evidence; the general Lean selector and conservation theorem remain B03.

REMAINING_NONCLAIMS:

- B02 does not prove the general R02 theorem or adaptive trace properties.
- B02 does not prove Rust, datastore, consensus, API, migration, or runtime
  refinement.
- B02 remains an unmounted Python research kernel and does not authorize value
  movement.
- No remote implementation commit, hosted CI run, draft PR, or publication is
  claimed.

REVIEW_RISKS: The selector accepts any positive exact denominator for the
  finite theorem and refinement tests; production callers use the 10,000 BPS
  profile. The compatibility wrapper retains the allocator’s existing
  transition-level internal-relation rejection while the selector exposes its
  stable typed rejection classes. The shared all-packet validator currently compares historical packets against the current checkout; B01 remains pinned to its own implementation head and therefore needs historical-Git-object validation before an all-packet gate can be claimed. The exact three-role relation still needs
  its Lean theorem and Rust refinement.
