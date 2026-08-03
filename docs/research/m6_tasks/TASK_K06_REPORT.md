# FCIS M6 Task K06 Report

TASK_ID: K06
BASE_SHA: 0b307ca01bfaa14d961ded7842b8023ad80e280b
SOURCE_HEAD_SHA: 92040e214c4dcd36c4e5172e7098f19e26f0300f
SOURCE_HEAD_TREE: 89b4704ef62940fcfd24f568f8f74152420a0e5a
BRANCH: codex/task-m6-receipt-rebind-20260802

DEPENDENCY_REFRESH_HEAD: 92040e214c4dcd36c4e5172e7098f19e26f0300f
DEPENDENCY_REFRESH_TREE: 89b4704ef62940fcfd24f568f8f74152420a0e5a
DEPENDENCY_REFRESH_PARENT: 4ecbc7b6992ea66dfd0f15d1f1ead6d4b84227e6

DEPENDENCY_REBIND: The J07 switch and post-context roots changed after the
J06/K01 rebind. K06 was regenerated at the exact dependency-refresh head
above; K06 implementation code is unchanged.

FILES_CHANGED:

- config/deploy/fcis_m6_k06_legacy_seal_v1.json
- src/core/fcis_m6_k06_legacy_seal.py
- tools/build_fcis_m6_k06_legacy_seal.py
- experiments/fcis_m6_k06_legacy_seal_check.py
- tests/tools/test_fcis_m6_k06_legacy_seal.py
- docs/research/m6_tasks/TASK_K06_LEGACY_SEAL_V1.json
- docs/research/m6_tasks/FCIS_M6_K06_LEGACY_SEAL_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K06_PLAN.md

CLAIM_IMPLEMENTED: K06 provides a bounded, verifier-owned legacy-path seal.
The checked builder regenerates the current K03 scan, D05 inventory/topology,
and K01 inventory, then checks the J07 switch and target-profile roots. The
terminal seal binds those roots, the complete K03 legacy symbol set, the
allowed legacy paths, a disabled feature flag, and the unique target writer
ID. Fresh runtime admission rejects legacy writers and stale, crossed, forged,
mutated, or pre-terminal inputs.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_m6_k06_legacy_seal.py tools/build_fcis_m6_k06_legacy_seal.py experiments/fcis_m6_k06_legacy_seal_check.py tests/tools/test_fcis_m6_k06_legacy_seal.py
- python3 -m ruff check src/core/fcis_m6_k06_legacy_seal.py tools/build_fcis_m6_k06_legacy_seal.py experiments/fcis_m6_k06_legacy_seal_check.py tests/tools/test_fcis_m6_k06_legacy_seal.py
- python3 -m ruff format --check src/core/fcis_m6_k06_legacy_seal.py tools/build_fcis_m6_k06_legacy_seal.py experiments/fcis_m6_k06_legacy_seal_check.py tests/tools/test_fcis_m6_k06_legacy_seal.py
- python3 -m mypy --strict src/core/fcis_m6_k06_legacy_seal.py tools/build_fcis_m6_k06_legacy_seal.py experiments/fcis_m6_k06_legacy_seal_check.py tests/tools/test_fcis_m6_k06_legacy_seal.py
- python3 -m json.tool config/deploy/fcis_m6_k06_legacy_seal_v1.json
- python3 -m json.tool docs/research/m6_tasks/TASK_K06_LEGACY_SEAL_V1.json
- python3 tools/build_fcis_m6_k06_legacy_seal.py --check
- PYTHONPATH=. python3 experiments/fcis_m6_k06_legacy_seal_check.py
- PYTHONPATH=. python3 -m pytest -q tests/tools/test_fcis_m6_k06_legacy_seal.py
- python3 tools/build_fcis_m6_k01_entrypoint_inventory.py --check
- python3 experiments/fcis_m6_k03_static_no_bypass_check.py
- python3 tools/build_fcis_m6_d05_tcg_inventory.py --check
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K06 --expected-head 91bce42607c2c2365087976bed1bee4a38cc1812

RESULTS:

- K06 deterministic seal root: `fa7707f4bb75a01643bdc375ab74cbcf9f108162bdbf462868b707f12e96a753`.
- K03 policy and scan roots matched the K06 pins; the scan reported zero
  issues over four protected Python files and zero protected Rust files.
- D05 regeneration matched the current K06 inventory and topology roots
  `fe407a21588db0932df41b224234a5a5950478aa12cc1c564857b7a5bbc41ac2` and
  `9b2db149fd06876cf9e9fa592d891042320e52dcf0640c952431d913f12402e1`.
- K01 regeneration matched the current K06 entrypoint inventory root
  `c8be9fb9b9ef3a997f062752b829c4a2f887e439276d938628da59ae63902df2`.
- K04 current topology root matched
  `6644cae606656411d0da64461d80a13030be65905cfd31916a33f1143bc25ee3`.
- J07 switch, post-context, epoch, and target writer-profile pins matched.
- Target admission passed; legacy admission rejected with
  `legacy_writer_disabled`.
- Focused K06 suite passed: 1 passed.
- Adjacent J07/J08/J09/K03/K05 regression passed: 45 passed.
- The current K04 dependency check passed after the D05/K01 rebind.
- Ten named adversarial mutants were killed by the independent checker.
- Python compilation, Ruff, formatting, strict mypy, JSON parsing, and diff
  whitespace checks passed.
- The packet lineage gate passed: Git objects, commit/tree pairs,
  report/evidence identities, and ancestry resolve to expected packet head
  `91bce42607c2c2365087976bed1bee4a38cc1812`.

UPSTREAM_REFRESH: The K06 packet now records the current D05, K01, and K04
roots after the entrypoint credential repair. The K04, K06, and K07 dependency
checks pass at the exact functional head above.

MUTANTS_ADDED: K06 kills legacy writer after terminal seal, stale authority
epoch, pre-terminal phase, crossed topology root, crossed inventory root,
`object.__new__` forged certificate, mutated feature flag, nonempty reachable
legacy set, caller certificate constructor, and unknown target writer.

FORMAL_EVIDENCE: None. K06 supplies typed construction checks, canonical root
recomputation, verifier-owned provenance checks, and adversarial executable
evidence. It adds no Lean, SMT, TLA, production build, or deployment theorem.

REMAINING_NONCLAIMS:

- K06 is a research-only model over the named reviewed inputs.
- It does not remove legacy symbols from a production artifact or authenticate
  a production process.
- It does not prove complete dynamic call-graph closure, image inclusion,
  credential isolation, datastore authority, or worker reachability.
- K04 is now rebound against current D05/K01 inputs, while K07 still requires
  its deployment and runtime audit evidence.
- No mounted caller, authority switch, migration deployment, or value movement
  is claimed. M6 remains unmounted and non-promotable.

REVIEW_RISKS: The core module is a 606-line research hotspot. The exact object
identity registry protects this bounded verifier model, while production
refinement still requires a real build attestation, process authentication,
deployment audit, and runtime integration test.
