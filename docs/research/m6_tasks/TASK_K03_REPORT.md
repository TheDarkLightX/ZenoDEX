# FCIS M6 Task K03 Report

TASK_ID: K03
BASE_SHA: c3f4578562b73c9b2e054dbebb2759a21ed5c520
SOURCE_HEAD_SHA: 0460c9be4dba9c3a2d7a1a3c6430bfeb17d08ed7
SOURCE_HEAD_TREE: 5223e558c5f6119ee6dd99e3777e06ee805c885c
BRANCH: codex/task-H03-deterministic-crash-20260801

FILES_CHANGED:

- config/deploy/fcis_m6_k03_static_no_bypass_policy_v1.json
- tools/check_fcis_m6_k03_static_no_bypass.py
- experiments/fcis_m6_k03_static_no_bypass_check.py
- tests/tools/test_check_fcis_m6_k03_static_no_bypass.py
- docs/research/m6_tasks/FCIS_M6_K03_STATIC_NO_BYPASS_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K03_PLAN.md

IMPLEMENTATION_HEAD_SHA: 0460c9be4dba9c3a2d7a1a3c6430bfeb17d08ed7
IMPLEMENTATION_TREE: 5223e558c5f6119ee6dd99e3777e06ee805c885c
IMPLEMENTATION_PARENT: c3f4578562b73c9b2e054dbebb2759a21ed5c520

CLAIM_IMPLEMENTED: K03 adds a syntax-aware Python AST and Rust
comment/string-aware token checker for the reviewed M6 protected source
slice. It rejects forbidden core imports and effect calls, protected-table SQL
write literals, legacy publisher calls, direct authoritative constructors,
and direct `publish_v1` calls outside the unique port module. The current
protected slice has four Python files and no declared M6 Rust publisher.

COMMANDS_RUN:

- python3 -m py_compile tools/check_fcis_m6_k03_static_no_bypass.py experiments/fcis_m6_k03_static_no_bypass_check.py tests/tools/test_check_fcis_m6_k03_static_no_bypass.py
- python3 -m ruff check tools/check_fcis_m6_k03_static_no_bypass.py experiments/fcis_m6_k03_static_no_bypass_check.py tests/tools/test_check_fcis_m6_k03_static_no_bypass.py
- python3 -m ruff format --check tools/check_fcis_m6_k03_static_no_bypass.py experiments/fcis_m6_k03_static_no_bypass_check.py tests/tools/test_check_fcis_m6_k03_static_no_bypass.py
- python3 -m mypy --strict tools/check_fcis_m6_k03_static_no_bypass.py experiments/fcis_m6_k03_static_no_bypass_check.py tests/tools/test_check_fcis_m6_k03_static_no_bypass.py
- PYTHONPATH=. python3 -m pytest -q tests/tools/test_check_fcis_m6_k03_static_no_bypass.py
- python3 experiments/fcis_m6_k03_static_no_bypass_check.py
- python3 tools/check_fcis_m6_k03_static_no_bypass.py
- python3 -m json.tool config/deploy/fcis_m6_k03_static_no_bypass_policy_v1.json
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K03
- sha256sum --check --strict docs/research/m6_tasks/TASK_K03_SOURCE_MANIFEST.sha256

RESULTS:

- Current protected-source scan passed with zero issues.
- Four Python protected files were scanned with AST rules.
- Rust checked file count was zero, and the report explicitly recorded
  `unmounted_no_m6_rust_publisher`.
- The mutation campaign killed forbidden-import, direct-write,
  legacy-publisher, authoritative-constructor, direct-port, and Rust effect
  mutants; a clean pure-core witness remained accepted.
- Focused K03 suite passed: 4 passed.
- Python compilation, Ruff, formatting, strict mypy, JSON parsing, and diff
  whitespace checks passed.

MUTANTS_ADDED: K03 covers forbidden `sqlite3` import, direct `execute` plus
`INSERT INTO`, legacy `evaluate_refinement_v1`, direct
`D08CombinedANFAcceptV1` construction, direct `publish_v1`, and Rust
`std::fs`/`commit` witnesses.

FORMAL_EVIDENCE: None. K03 supplies syntax-aware structural evidence and
negative mutation checks. It adds no formal theorem, deployment proof, or
complete runtime call-graph proof.

REMAINING_NONCLAIMS:

- The policy names a protected source slice and does not prove that it is the
  complete production build or deployment surface.
- The Rust scanner is a bounded token-aware check; no M6 Rust publisher is
  mounted in this slice, so no Rust runtime closure is claimed.
- K03 does not prove process/credential isolation, datastore table ownership,
  dynamic reachability, or unique deployed capability identity.
- No mounted caller, runtime authority switch, deployment, migration, or
  value movement is claimed. M6 remains unmounted.

REVIEW_RISKS: The static checker can catch structural drift only within its
reviewed policy. K04 must anchor the inventory/topology root, K05 must add
entrypoint-level dynamic bypass mutants, and K06-K08 must audit legacy and
deployment reachability before an R12 mounted claim.
