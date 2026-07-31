# FCIS M6 Task B01 Report

TASK_ID: B01
BASE_SHA: `7f70c0133ecd0873147ac4903215473f95f93dc6`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-B01-overflow-safe-quota-20260731`

IMPLEMENTATION_HEAD_SHA: `9b290540e96b840ee07795f35dac938e7d524cf2`
IMPLEMENTATION_TREE: `5e3108bb88b1f619beb9cb84a1d68cef0933913a`

FILES_CHANGED:

- `src/core/fcis_fee_apportionment_transition.py`
- `src/core/fcis_fee_apportionment_allocator.py`
- `tests/core/test_fcis_fee_apportionment_transition.py`
- `tests/core/test_fcis_fee_apportionment_width_mutants.py`
- `tools/build_fcis_fee_apportionment_v2_golden.py`
- `tests/fixtures/fcis_fee_apportionment_v2_golden.json`
- `docs/research/m6_tasks/TASK_B01_REPORT.md`
- `docs/research/m6_tasks/TASK_B01_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_B01_SOURCE_MANIFEST.sha256`

CLAIM_IMPLEMENTED: The unmounted SRGD fee allocator now derives each role
quota through a typed `FeeQuotaV2` primitive. For amount `A`, production
denominator `D = 10_000`, and weight `w`, it computes `q, r = divmod(A, D)`,
then `base = q*w + (r*w)//D` and `remainder = (r*w)%D`. The full `A*w`
product is never formed. Exact-type, U256, weight, denominator, relation, and
successor-width checks fail closed through typed rejection or controlled value
construction. The golden-vector builder now hashes the new primitive as part
of its source closure.

COMMANDS_RUN:

- `python3 -m py_compile` over the B01 source and test modules
- `python3 -m ruff check` over the B01 source, tests, and golden builder
- `python3 -m mypy --strict src/core/fcis_fee_apportionment_transition.py src/core/fcis_fee_apportionment_allocator.py`
- `python3 -m pytest -q` over the four existing fee-apportionment tests plus
  the B01 transition and width-mutant tests
- `python3 tools/build_fcis_fee_apportionment_v2_golden.py`
- `python3 tools/build_fcis_fee_apportionment_v2_golden.py --check`
- `git diff --check`
- `git diff --cached --check`

RESULTS:

- Focused FCIS fee-apportionment tests: `35 passed`.
- Golden fixture regeneration and freshness check: pass; 12 cases.
- Ruff: pass.
- Strict mypy: pass for both touched source modules.
- Python compilation: pass.
- Boundary vectors cover amounts `0`, `1`, `D-1`, `D`, `D+1`, `U256_MAX-1`,
  and `U256_MAX`, with zero, middle, and full weights.
- Explicit witnesses cover Boolean rejection, unsupported denominator,
  out-of-range amount and weight, full-product avoidance, unchecked base
  growth, and allocator bypass of the quota primitive.
- Implementation commit is local and cleanly based on the completed A04
  receipt commit. No runtime caller, datastore adapter, authority switch,
  deployment, or value-moving path was mounted.

MUTANTS_ADDED: Seven named regression witnesses are encoded in the B01 tests:

- `B01_BOOL_AMOUNT`: Boolean amount is rejected as the wrong exact type.
- `B01_BOOL_WEIGHT_AND_DENOMINATOR`: Boolean width parameters are rejected.
- `B01_FLOAT_QUOTA`: exact U256 vectors forbid lossy floating arithmetic.
- `B01_TRUNCATED_MACHINE_WIDTH`: U256 maximum vectors preserve exact values.
- `B01_FULL_AMOUNT_WEIGHT_PRODUCT`: an AST guard rejects the full product.
- `B01_UNCHECKED_BASE_GROWTH`: controlled value construction rejects growth
  outside the canonical relation.
- `B01_ALLOCATOR_BYPASS`: replacing the primitive with a rejection preserves
  the allocator's fail-closed result.

No external mutation runner was used.

FORMAL_EVIDENCE: None added. B01 supplies executable arithmetic and boundary
evidence; it does not add the general Lean theorem or a Rust refinement.

REMAINING_NONCLAIMS:

- The primitive is a Python research kernel and remains unmounted.
- Python arbitrary-precision execution does not prove a production Rust or
  datastore U256 implementation until the later refinement tasks pass.
- B01 does not prove adaptive selector laws, cumulative discrepancy, grouping
  compatibility, or the full R02 theorem; those are B02-B09 obligations.
- No production API, datastore, recovery, migration, authority, effect, or
  value-moving path changed.
- No remote implementation commit, hosted CI run, draft PR, or publication is
  claimed by this local branch.

REVIEW_RISKS: The allocator's strict-mypy repair uses casts immediately after
runtime exact-type guards. The primitive fixes the production denominator to
the reviewed BPS profile; generic-denominator theorem work remains outside
B01. The golden fixture records the new source in its closure, while the
cross-language and production-width refinements remain open.
