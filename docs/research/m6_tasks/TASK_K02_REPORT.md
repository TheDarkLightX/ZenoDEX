# FCIS M6 Task K02 Report

TASK_ID: K02
BASE_SHA: b41d7954586c4cf0e309a625f40a9aff2e2a8999
SOURCE_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
SOURCE_HEAD_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
BRANCH: codex/task-H03-deterministic-crash-20260801

FILES_CHANGED:

- config/deploy/fcis_m6_k02_dependency_rules_v1.json
- src/core/fcis_m6_k02_commit_port.py
- experiments/fcis_m6_k02_commit_port_check.py
- tests/core/test_fcis_m6_k02_commit_port.py
- docs/research/m6_tasks/FCIS_M6_K02_UNIQUE_COMMIT_PORT_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K02_PLAN.md

IMPLEMENTATION_HEAD_SHA: 0ff89fb723da5e0ef5a2b1887c00eb28bef16cc6
IMPLEMENTATION_TREE: 5b0c6efa409f12cb62cd84b0e24aa3c373458273
IMPLEMENTATION_PARENT: c3213000060d3224e1291d2bbf9992e41f8fd74b

CLAIM_IMPLEMENTED: K02 defines one research unique commit-port capability
with identity `fcis/m6/unique-atomic-commit-port/v1`. The request contains only
an exact D08 verifier acceptance witness. K02 obtains the complete
`PublicationAtomV1` from that witness and derives commit, pre/post state,
authority, effect, and sequence fields from the owned aggregate; callers cannot
select a second publication tuple alongside the witness. D08 provenance is
revalidated at point of use. It returns newly-committed, already-committed, or
typed rejection results. Same-commit retries preserve state, changed
fingerprints reject as collisions, and stale heads or sequence crossings fail
closed. A module-owned construction token prevents ordinary caller
construction of another port instance.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_m6_k02_commit_port.py experiments/fcis_m6_k02_commit_port_check.py tests/core/test_fcis_m6_k02_commit_port.py
- python3 -m ruff check src/core/fcis_m6_k02_commit_port.py experiments/fcis_m6_k02_commit_port_check.py tests/core/test_fcis_m6_k02_commit_port.py
- python3 -m ruff format --check src/core/fcis_m6_k02_commit_port.py experiments/fcis_m6_k02_commit_port_check.py tests/core/test_fcis_m6_k02_commit_port.py
- python3 -m mypy --strict src/core/fcis_m6_k02_commit_port.py experiments/fcis_m6_k02_commit_port_check.py tests/core/test_fcis_m6_k02_commit_port.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_k02_commit_port.py
- python3 experiments/fcis_m6_k02_commit_port_check.py
- python3 -m json.tool config/deploy/fcis_m6_k02_dependency_rules_v1.json
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K02
- sha256sum --check --strict docs/research/m6_tasks/TASK_K02_SOURCE_MANIFEST.sha256

RESULTS:

- Unique port identity and singleton identity checks passed.
- First publication classified as `NEWLY_COMMITTED` and advanced the
  immutable sequence/head state.
- Same request classified as `ALREADY_COMMITTED` without changing state.
- Same commit ID with a changed durable fingerprint rejected as
  `COMMIT_COLLISION`.
- Stale expected head, wrong sequence, arbitrary capability, caller-minted
  capability, and raw ANF witness all rejected.
- Publication-field ownership, state-bound collision, and sequence witnesses
  passed.
- Focused K02 suite passed: 6 passed.
- Python compilation, Ruff, formatting, strict mypy, JSON parsing, and diff
  whitespace checks passed.

MUTANTS_ADDED: K02 covers a forged capability object, direct capability
construction without the controlled token, raw and exact-class-forged D08
inputs, caller-selected publication-field substitution, same-identity
fingerprint collision, stale head, sequence crossing, and retry-state mutation
witnesses.

FORMAL_EVIDENCE: None. K02 supplies an executable typed capability model and
dependency policy. It adds no Lean theorem, datastore transaction proof,
deployment reachability proof, or production authority certificate.

REMAINING_NONCLAIMS:

- The Python singleton is a research capability discipline, not a production
  cryptographic or process-isolation primitive.
- K02 does not implement or refine SQLite/PostgreSQL/RocksDB transactions,
  durable recovery, CAS behavior under concurrency, or crash atomicity.
- K02 does not run the K03 syntax-aware dependency checker or Rust parser.
- No mounted caller, API, worker, migration, datastore, runtime switch,
  deployment, or value movement is claimed. M6 remains unmounted.

REVIEW_RISKS: A production capability must be owned by one deployment-level
commit port and must prevent alternate adapters from writing protected state.
K03 must enforce the dependency rules with syntax-aware checks, and K04-K08
must bind the port to the complete inventory, topology, deployment, and
mounted theorem surfaces.
