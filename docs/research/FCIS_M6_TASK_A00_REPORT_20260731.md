# FCIS M6 Task A00 Report

TASK_ID: A00
BASE_SHA: `babffa56dcbddc5886487fbb6e62740b15370000`
HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
BRANCH: `luna/task-A00-exact-head-ledger-20260731`
FILES_CHANGED:

- `docs/research/FCIS_M6_EXACT_HEAD_LEDGER_20260731.json`
- `docs/research/FCIS_M6_WORKFLOW_EVIDENCE_LEDGER_20260731.json`
- `docs/research/FCIS_M6_TASK_A00_REPORT_20260731.md`
- `docs/research/FCIS_M6_TASK_A00_EVIDENCE_20260731.json`
- `docs/research/FCIS_M6_TASK_A00_SOURCE_MANIFEST_20260731.sha256`

CLAIM_IMPLEMENTED: The packet records immutable exact source heads, parent/tree identities, changed-file inventories, and workflow evidence for PRs #496, #497, #498, #499, and #501.

COMMANDS_RUN:

- `git fetch origin agent/fcis-m6-r04-tree-chord-gate-authority-20260730`
- `git switch -c luna/task-A00-exact-head-ledger-20260731`
- `git status --short --branch`
- `git rev-parse HEAD`
- `git rev-parse HEAD^{tree}`
- `git rev-parse origin/agent/fcis-m6-r04-tree-chord-gate-authority-20260730`
- GitHub connector PR metadata and changed-filename queries for #496, #497, #498, #499, #501
- GitHub connector workflow-run queries for each exact PR head
- GitHub connector workflow-job query for run `30648508074`
- `python3 -m json.tool` on both ledgers and task evidence
- `sha256sum` on both ledgers and the source manifest
- `python3 tools/check_fcis_durable_retraction_model.py --self-test`

RESULTS:

- Exact source head: `476ec022e755ff049c39bf9f08c6606ac87532ca`
- Exact source tree: `a1d495eae0b26a369487ceb48cad5472abec74db`
- Exact implementation parent: `ecf26f987c3d6393501fec66ddfc3429fb8634c7`
- Exact implementation tree: `fdf154ac143a9f9a9e840fbbf49761190d138920`
- Dedicated workflow `30648508074`: success
- Dedicated jobs: Python, Lean, Julia, and packet delivery all success
- Public model self-test: pass; 56 reachable states, 268 enabled transitions, 10 invariants, four mutants killed
- Ledger generation is deterministic for unchanged GitHub state.

MUTANTS_ADDED: None. A00 records exact-head evidence and does not alter executable semantics.

FORMAL_EVIDENCE: Existing exact-head Lean workflow evidence is recorded as successful in `FCIS_M6_WORKFLOW_EVIDENCE_LEDGER_20260731.json`. A00 adds no theorem.

REMAINING_NONCLAIMS:

- This task does not prove production authority, datastore refinement, runtime mounting, no-bypass completeness, or M6 promotion.
- Historical broad-workflow failures are recorded as observations and are not reclassified as dedicated M6 failures.

REVIEW_RISKS: GitHub workflow inventories are external state and must be regenerated if any referenced PR head changes. The ledger records the query scope and exact heads used.
