# FCIS M6 Task K05 Report

TASK_ID: K05
BASE_SHA: a0d651d6bddf0b6f4e59c07a1085ccd489ed072e
SOURCE_HEAD_SHA: edca73303b2f8201483c35dfee55ed84752e650c
SOURCE_HEAD_TREE: 69ee9ed990a95a69727809870972cb78219a3351
BRANCH: codex/task-H03-deterministic-crash-20260801

FILES_CHANGED:

- src/core/fcis_m6_k05_bypass_mutants.py
- experiments/fcis_m6_k05_bypass_mutation_check.py
- tests/tools/test_fcis_m6_k05_bypass_mutation.py
- docs/research/m6_tasks/FCIS_M6_K05_BYPASS_MUTATION_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K05_PLAN.md

IMPLEMENTATION_HEAD_SHA: edca73303b2f8201483c35dfee55ed84752e650c
IMPLEMENTATION_TREE: 69ee9ed990a95a69727809870972cb78219a3351
IMPLEMENTATION_PARENT: a0d651d6bddf0b6f4e59c07a1085ccd489ed072e

CLAIM_IMPLEMENTED: K05 builds a deterministic six-mutant matrix for every
one of the fifteen K01 entrypoint identities. All 90 cases are killed. The
matrix binds return-success-without-commit, direct-state-write,
direct-outbox-write, skipped proof context, skipped current-root CAS, and
legacy-writer bypass to named invariant outcomes. The current-root mutant is
actually passed through K02 and receives `STALE_HEAD`.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_m6_k05_bypass_mutants.py experiments/fcis_m6_k05_bypass_mutation_check.py tests/tools/test_fcis_m6_k05_bypass_mutation.py
- python3 -m ruff check src/core/fcis_m6_k05_bypass_mutants.py experiments/fcis_m6_k05_bypass_mutation_check.py tests/tools/test_fcis_m6_k05_bypass_mutation.py
- python3 -m ruff format --check src/core/fcis_m6_k05_bypass_mutants.py experiments/fcis_m6_k05_bypass_mutation_check.py tests/tools/test_fcis_m6_k05_bypass_mutation.py
- python3 -m mypy --strict src/core/fcis_m6_k05_bypass_mutants.py experiments/fcis_m6_k05_bypass_mutation_check.py tests/tools/test_fcis_m6_k05_bypass_mutation.py
- PYTHONPATH=. python3 -m pytest -q tests/tools/test_fcis_m6_k05_bypass_mutation.py
- python3 experiments/fcis_m6_k05_bypass_mutation_check.py
- python3 tools/check_fcis_m6_k03_static_no_bypass.py
- python3 tools/build_fcis_m6_k04_topology_anchor.py --check
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K05
- sha256sum --check --strict docs/research/m6_tasks/TASK_K05_SOURCE_MANIFEST.sha256

RESULTS:

- K03 protected static scan passed before the matrix ran.
- K01 provided 15 canonical entrypoint identities.
- K05 produced exactly 90 results: 15 entrypoints x 6 mutations.
- Every result was killed by its expected named invariant.
- The K02 current-root CAS witness rejected the forged expected head as
  `STALE_HEAD`.
- Focused K05 suite passed: 2 passed.
- Python compilation, Ruff, formatting, strict mypy, and diff whitespace
  checks passed.

MUTANTS_ADDED: K05 covers all six required bypass classes for each K01
entrypoint identity. The matrix preserves negative witnesses for missing
commit evidence, direct state/outbox writes, missing ANF context, stale CAS,
and legacy writer use.

FORMAL_EVIDENCE: None. K05 supplies bounded executable mutation evidence. It
does not add a source-to-source mutation runner, formal theorem, deployment
proof, or mounted integration test.

REMAINING_NONCLAIMS:

- K05 is a research mutation matrix over reviewed identities, not execution of
  every production caller.
- K05 does not prove dynamic reachability, datastore enforcement, worker
  behavior, credential isolation, or legacy sealing.
- No mounted caller, runtime authority switch, deployment, migration, or value
  movement is claimed. M6 remains unmounted.

REVIEW_RISKS: The matrix can show the intended invariant response for each
named surface while the actual callers remain unmounted. K06-K08 must connect
these mutant classes to real source, build, deployment, and runtime paths.
