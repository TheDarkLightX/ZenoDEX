# FCIS M6 Task A04 Report

TASK_ID: A04
BASE_SHA: `99b4d635e1fb72f24c213d034f4bfb1ab7d35686`
SOURCE_HEAD_SHA: `e7c827d2a206f6bed6fc59fe9e6bbdfe679e34d2`
SOURCE_HEAD_TREE: `fcae7f28ae277c1e62402269a253f80531972bf0`
BRANCH: `codex/task-H03-deterministic-crash-20260801`

INTEGRATION_INPUTS:

- A02 base: `99b4d635e1fb72f24c213d034f4bfb1ab7d35686`.
- PR498 exact head: `a94a1fa0586107a0a48aebbe4cd18c0d1029d481`, tree
  `0504abdf4c4b493a97baf06cfd73d4a3922d4cfb`.
- PR499 and DRA surfaces are inherited through the A02/#501 ancestry.
- `git merge-tree --write-tree --messages` result tree:
  `5c5234d755101353a7ae63f5d72da651de99e738`.
- Conflict-free merge commit: `485b58a83105a995d2db9eb3805e4710520b3b29`.
- Historical strict-mypy repair commit: `f3eeddd9e5a58f72d290f13c2d40129aef8f10cc`.
- Current A04 revalidation parent: `e6fcd803da178342920a90e69d4b8bfa7a340cf1`,
  tree `82d00e8cdf116b10e14f1f29c1db4c772d353352`.
- Current A04 source-quality repair commit:
  `19dc60b0e27bf9878fa2c9192c517a23a61a08d2`, tree
  `34290096df16f5a63c17494360abf8b24bd90d89`.
- Reviewed D04 repair head:
  `5e4677c30210cdbaa1adb0c5775f112eb25f140e`.
- D04/continuation merge commit:
  `e7c827d2a206f6bed6fc59fe9e6bbdfe679e34d2`, tree
  `fcae7f28ae277c1e62402269a253f80531972bf0`.
- No hosted CI run is claimed for the merged continuation head.

FILES_CHANGED:

- Current source-quality repair:
  - `src/core/fcis_fee_occurrence_normal_form.py` (Ruff formatting).
  - `src/core/fcis_m6_profile_ids.py` (Ruff formatting).
  - `src/core/fcis_source_bound_lineage.py` (redundant-cast removal).
  - `src/core/fcis_tree_chord_gate_authority.py` (Ruff formatting).
  - `tests/core/test_fcis_fee_occurrence_normal_form.py` (Ruff formatting).
  - `tests/core/test_fcis_m6_profile_ids.py` (Ruff formatting).
  - `tests/core/test_fcis_tree_chord_gate_authority.py` (Ruff formatting).
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

CLAIM_IMPLEMENTED: The A04 research packet is revalidated against the exact
local source head recorded above. The D04 V1/V2 outbox-lineage repair composes
with the later lineage-closure implementation. The seven integrated source
modules and seven focused test modules pass Python compilation, Ruff check,
Ruff format check, strict mypy, and focused tests. The inherited
Tree–Chord–Gate, DRA, Julia, public-model, and domain-identifier evidence is
retained with its declared scope. The current Lean rerun is blocked by the
read-only shared mathlib checkout. No runtime mount is performed.

COMMANDS_RUN:

- `git merge-tree --write-tree --messages HEAD a94a1fa0586107a0a48aebbe4cd18c0d1029d481`
- `git merge --no-ff --no-edit a94a1fa0586107a0a48aebbe4cd18c0d1029d481`
- `python3 -m py_compile` over the seven integrated research modules and
  seven focused test modules
- `python3 -m ruff check` over the seven integrated research modules and seven
  focused test modules
- `python3 -m ruff format --check` over the seven integrated research modules
  and seven focused test modules
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
- `python3 .claude/skills/zenodex-style-map/scripts/which_style.py` was
  unavailable because the repository-local script is absent in this worktree.
- `python3 .claude/skills/zenodex-security-analysis/scripts/trust_surface.py`
  and `redflags.py` were unavailable for the same reason.

RESULTS:

- Historical merge-tree result: conflict-free, result tree
  `5c5234d755101353a7ae63f5d72da651de99e738`.
- Python compile: pass.
- Ruff: pass.
- Ruff format check: pass, 14 files already formatted.
- Strict mypy: pass on 7 source files after the type-only repair.
- Focused tests: `97 passed`.
- Lean: blocked on the current isolated rerun because the shared mathlib
  checkout is read-only and cannot create
  the shared Mathlib checkout's `.lake/config/mathlib/lakefile.olean.lock`
  (errno 30). The temporary symlink was removed. The earlier 8153-job result
  remains historical evidence and is not re-promoted for this exact head.
- Julia 1.12.6 TCG oracle: pass, 9 gates, safe baseline, all five targeted
  TCG mutations violated their named invariants.
- Julia DRA oracle: pass, 49 states, 254 transitions, seven mutants killed.
- Workflow names: four distinct names, no duplicate.
- Shared M6 domain identifiers: 16 unique values, no collision.
- Public durable-retraction model: pass, 56 states, 268 transitions, 10
  invariants, four public self-test mutants killed.

MUTANTS_ADDED: None. A04 integrates and gates existing research models; it adds
no new semantic mutant family.

FORMAL_EVIDENCE: The inherited Julia, ESSO/public-model, and Python evidence is
recorded with its bounded scope. The current Python source-quality repair does
not alter the hash formulas or authority rules. A current exact-head Lean
replay remains unavailable because the shared mathlib checkout cannot be
written in this environment.

REMAINING_NONCLAIMS:

- A04 records exact local Git/path and Python quality-gate evidence for the
  selected source head;
  it does not prove the unresolved C-05 SLNF/source-bound version migration,
  C-06 lineage-closure-to-TCG certificate binding, or C-07 TCG-to-DRA ANF
  relation from the A01 map.
- The integrated branch remains research-only and unmounted. No production
  caller, datastore, API, authority switch, deployment, migration, or
  value-moving path was changed.
- The current Lean rerun was blocked by the read-only shared mathlib checkout;
  no dependency path was committed.
- No production readiness, M6 promotion, or exact remote implementation commit
  is claimed by this local A04 task branch.

REVIEW_RISKS: The Python quality gates and bounded model evidence are green,
while the current exact-head Lean replay remains blocked. Cross-certificate
semantic bindings remain explicit follow-up obligations. Later integration must
consume the A02 registry and prove the A01 schema relations before any mounted
or value-moving path is considered. The D04 merge adds exact V2 outbox schema
selection to lineage closure; the focused lineage suite retains this as a
permanent regression.
