# FCIS M6 Task A04 Report

TASK_ID: A04
BASE_SHA: `99b4d635e1fb72f24c213d034f4bfb1ab7d35686`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-A04-reviewed-integration-20260731`

INTEGRATION_INPUTS:

- A02 base: `99b4d635e1fb72f24c213d034f4bfb1ab7d35686`.
- PR498 exact head: `a94a1fa0586107a0a48aebbe4cd18c0d1029d481`, tree
  `0504abdf4c4b493a97baf06cfd73d4a3922d4cfb`.
- PR499 and DRA surfaces are inherited through the A02/#501 ancestry.
- `git merge-tree --write-tree --messages` result tree:
  `5c5234d755101353a7ae63f5d72da651de99e738`.
- Conflict-free merge commit: `485b58a83105a995d2db9eb3805e4710520b3b29`.
- Strict-mypy repair commit: `f3eeddd9e5a58f72d290f13c2d40129aef8f10cc`.
- Final integration head before the A04 receipt child:
  `f3eeddd9e5a58f72d290f13c2d40129aef8f10cc`, tree
  `5c26eb9dfc7e884e72ff82f307768502fb876b9f`.

FILES_CHANGED:

- `src/core/fcis_lineage_closure.py` (three explicit type-boundary casts).
- `docs/research/m6_tasks/TASK_A04_REPORT.md`
- `docs/research/m6_tasks/TASK_A04_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_A04_SOURCE_MANIFEST.sha256`

INTEGRATED_PR498_INVENTORY:

- `.github/workflows/fcis-m6-r04-lineage-closure.yml`
- `docs/research/FCIS_M6_R01_R04_SOURCE_BOUND_LINEAGE_20260730.md`
- `docs/research/FCIS_M6_R04_LINEAGE_CERTIFICATE_CLOSURE_20260730.md`
- `src/core/fcis_fee_occurrence_extractor.py`
- `src/core/fcis_lineage_closure.py`
- `src/core/fcis_source_bound_lineage.py`
- `tests/core/test_fcis_fee_occurrence_extractor.py`
- `tests/core/test_fcis_lineage_closure.py`
- `tests/core/test_fcis_source_bound_lineage.py`

CLAIM_IMPLEMENTED: A synthetic exact-head research integration branch contains
the conflict-free PR498 additions on the A02/#501 base, with the inherited
PR499 Tree–Chord–Gate and DRA surfaces preserved. All required local A04 gates
are green after three explicit casts close the integrated lineage-closure
module’s strict-mypy Any leaks. No runtime mount is performed.

COMMANDS_RUN:

- `git merge-tree --write-tree --messages HEAD a94a1fa0586107a0a48aebbe4cd18c0d1029d481`
- `git merge --no-ff --no-edit a94a1fa0586107a0a48aebbe4cd18c0d1029d481`
- `python3 -m py_compile` over the seven integrated research modules and
  seven focused test modules
- `python3 -m ruff check` over the seven integrated research modules and seven
  focused test modules
- `python3 -m mypy --strict` over the seven integrated research modules
- `python3 -m pytest -q` over the seven focused test modules
- `cd lean-mathlib && lake build` with a temporary local symlink to the existing
  `../external/mathlib4` checkout; the symlink was removed afterward
- `julia experiments/julia/fcis_tree_chord_gate_oracle.jl`
- `julia experiments/julia/fcis_durable_retraction_oracle.jl`
- workflow-name extraction with `awk` and duplicate detection by sorted output
- immutable-domain uniqueness check using `M6_DOMAIN_IDENTIFIERS_V1`
- `python3 tools/check_fcis_durable_retraction_model.py --self-test`
- `git diff --check`

RESULTS:

- Merge-tree result: conflict-free, result tree
  `5c5234d755101353a7ae63f5d72da651de99e738`.
- Python compile: pass.
- Ruff: pass.
- Strict mypy: pass on 7 source files after the type-only repair.
- Focused tests: `96 passed`.
- Lean: `Build completed successfully (8153 jobs)`; existing linter warnings
  remain outside this task’s scope.
- Julia 1.12.6 TCG oracle: pass, 9 gates, safe baseline, all five targeted
  TCG mutations violated their named invariants.
- Julia DRA oracle: pass, 49 states, 254 transitions, seven mutants killed.
- Workflow names: four distinct names, no duplicate.
- Shared M6 domain identifiers: 16 unique values, no collision.
- Public durable-retraction model: pass, 56 states, 268 transitions, 10
  invariants, four public self-test mutants killed.

MUTANTS_ADDED: None. A04 integrates and gates existing research models; it adds
no new semantic mutant family.

FORMAL_EVIDENCE: The complete Lean build and the inherited Julia/ESSO/Python
model evidence are recorded as integration results. The three casts only make
existing helper return types explicit and do not alter the hash formulas.

REMAINING_NONCLAIMS:

- A04 proves direct Git/path/build coexistence for the selected exact heads;
  it does not prove the unresolved C-05 SLNF/source-bound version migration,
  C-06 lineage-closure-to-TCG certificate binding, or C-07 TCG-to-DRA ANF
  relation from the A01 map.
- The integrated branch remains research-only and unmounted. No production
  caller, datastore, API, authority switch, deployment, migration, or
  value-moving path was changed.
- Lean success uses the existing local mathlib checkout through a temporary
  workspace symlink; no dependency was committed.
- No production readiness, M6 promotion, or exact remote implementation commit
  is claimed by this local A04 task branch.

REVIEW_RISKS: The merge is syntactically and operationally green while the
cross-certificate semantic bindings remain explicit follow-up obligations.
Later integration must consume the A02 registry and prove the A01 schema
relations before any mounted or value-moving path is considered.
