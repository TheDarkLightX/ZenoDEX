# FCIS M6 Task A01 Report

TASK_ID: A01
BASE_SHA: `5a20a601eee353ea39a7702ed30db7182662a741`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-A01-semantic-conflict-map-20260731`

FILES_CHANGED:

- `docs/research/FCIS_M6_STACK_CONFLICT_MAP_20260731.md`
- `docs/research/FCIS_M6_TASK_A01_EVIDENCE_20260731.json`
- `docs/research/FCIS_M6_TASK_A01_REPORT_20260731.md`
- `docs/research/FCIS_M6_TASK_A01_SOURCE_MANIFEST_20260731.sha256`

CLAIM_IMPLEMENTED: The reviewed exact heads are compared across paths, blobs,
Lean roots, exported symbols, schema/root domains, workflows, and ancestry.
Every observed collision in that scope has a classification. Unresolved
semantic relationships remain isolated and are not auto-merged.

COMMANDS_RUN:

- `git status --short --branch`
- `git rev-parse HEAD`
- `git rev-parse HEAD^{tree}`
- `git fetch origin codex/fcis-p4b5a-agqe-srgd-refinement-20260730`
- `git show --format=fuller --stat <exact-head>` for each reviewed head
- `git ls-tree -r <exact-head>` for each reviewed head
- `git merge-base <head-a> <head-b>` for the recorded ancestry pairs
- `git diff --name-status <merge-base> <head>` for direct path comparison
- `git grep` audits for public symbols, root domains, schema versions, and
  workflow names
- `python3 -m json.tool docs/research/FCIS_M6_TASK_A01_EVIDENCE_20260731.json`
- `sha256sum` over the A00 ledgers and A01 receipt files
- `python3 tools/check_fcis_durable_retraction_model.py --self-test`

RESULTS:

- Shared historical report path: `IDENTICAL`, same blob at all five heads.
- `lean-mathlib/Proofs.lean`: `IDENTICAL`, same blob at all five heads.
- `lean-mathlib/lakefile.lean`: `COMPATIBLE_ADDITIVE`; occurrence, TCG, and
  durable-retraction roots must be unioned and rebuilt.
- Lean declaration roots and audited exported Python symbols: no duplicate
  meaning was found.
- SLNF to source-bound lineage: `SCHEMA_MIGRATION_REQUIRED` because the
  source-bound version constant is named V1 while its encoded domain is V2.
- Lineage closure to TCG: `UNKNOWN_REQUIRES_REVIEW`; no checked certificate
  binding was found.
- TCG to DRA: `SCHEMA_MIGRATION_REQUIRED`; the authority-instance and
  authority-state roots require an explicit ANF relation.
- Workflow names and root-domain strings are distinct. This is additive
  evidence, not a semantic compatibility proof.
- PRs #498 and #499 are parallel R04 branches and require explicit later
  integration review.

MUTANTS_ADDED: None. A01 is a classification and evidence task; it adds no
executable semantics.

FORMAL_EVIDENCE: No theorem is added. The A00 exact-head and workflow ledgers,
plus the public durable-retraction self-test, remain the available executable
evidence.

REMAINING_NONCLAIMS:

- No branch was merged and no semantic conflict was resolved by selection.
- No production datastore, mounted caller, authority switch, deployment path,
  migration, or value-moving path was changed.
- The map does not prove the missing schema relations, Lean integration, or
  production refinement.
- A later source-head change invalidates this map and its manifest.

REVIEW_RISKS: The map is bounded by the exact heads and audit queries recorded
in the evidence JSON. The two schema relations marked for migration and the
one unknown certificate relation are the highest-risk A01 handoff items.
