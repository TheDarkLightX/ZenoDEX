# FCIS M6 Task A03 Report

TASK_ID: A03
BASE_SHA: `5b5a6000250b4009e1ddafebd383927348a8cd75`
SOURCE_HEAD_SHA: `476ec022e755ff049c39bf9f08c6606ac87532ca`
SOURCE_HEAD_TREE: `a1d495eae0b26a369487ceb48cad5472abec74db`
BRANCH: `codex/task-A03-evidence-directory-20260731`

FILES_CHANGED:

- `docs/research/m6_tasks/TASK_REPORT_SCHEMA_V1.md`
- `docs/research/m6_tasks/TASK_EVIDENCE_SCHEMA_V1.json`
- `docs/research/m6_tasks/TASK_SOURCE_MANIFEST_CONTRACT_V1.md`
- `docs/research/m6_tasks/validate_task_packet.py`
- `docs/research/m6_tasks/TASK_A03_REPORT.md`
- `docs/research/m6_tasks/TASK_A03_EVIDENCE.json`
- `docs/research/m6_tasks/TASK_A03_SOURCE_MANIFEST.sha256`

CLAIM_IMPLEMENTED: The M6 task directory now has a deterministic report
contract, evidence JSON schema, source-manifest contract, and fail-closed
sample validator. The A03 sample packet validates and its declared hashes
reproduce exactly.

COMMANDS_RUN:

- `python3 --version`
- `git --version`
- `sha256sum --version | head -1`
- `python3 -m json.tool docs/research/m6_tasks/TASK_EVIDENCE_SCHEMA_V1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_A03_EVIDENCE.json`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_A03_SOURCE_MANIFEST.sha256`
- deterministic sorted manifest regeneration followed by byte comparison
- python3 -m ruff check docs/research/m6_tasks/validate_task_packet.py
- `git diff --check`

RESULTS:

- Python: `3.12.3`.
- Git: `2.54.0`.
- GNU coreutils `sha256sum`: `9.4`.
- Report and evidence schema JSON parse successfully.
- The sample validator defines fail-closed rejection branches for malformed paths, missing source files,
  duplicate manifest entries, manifest self-hashing, and digest mismatches; this task does not claim a separate mutation campaign.
- Ruff focused check passes for validate_task_packet.py.
- The A03 sample packet validates with six manifest entries.
- The validator supports selected-task and all-packet modes; selected A03 validation passes.
- Repeated deterministic manifest generation is byte-identical.
- The directory contract does not change production runtime behavior.

MUTANTS_ADDED: None. A03 supplies a reusable validator and its rejection
branches; behavior mutants for M6 semantics remain task-specific.

FORMAL_EVIDENCE: None added. This task establishes provenance tooling and does
not prove any M6 theorem or runtime refinement.

REMAINING_NONCLAIMS:

- The directory contract does not promote any task from `IMPLEMENTED` to
  `PROVED`, `MOUNTED`, or production-ready.
- The validator is a research evidence tool and is not a production authority
  gate or datastore adapter.
- Existing A00/A01 packets are not rewritten into this directory; future task
  packets must follow the contract, and later migration may be audited
  separately.

REVIEW_RISKS: The JSON schema is a declarative contract and the local validator
implements the bounded checks needed for this sample. A future task may add
fields only through a versioned schema change with corresponding validator and
manifest evidence.
