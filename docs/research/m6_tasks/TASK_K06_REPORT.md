# FCIS M6 Task K06 Report

TASK_ID: K06
BASE_SHA: 0b307ca01bfaa14d961ded7842b8023ad80e280b
SOURCE_HEAD_SHA: 7824b451eaabf3b2649b7a9f7cb09dddffe225ac
SOURCE_HEAD_TREE: af89e4e284135681f24b471afa236a4ec665fc8a
BRANCH: codex/task-m6-receipt-rebind-20260802

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

RESULTS:

- K06 deterministic seal root: `139a29f1938dfffb9ea4c72b5f6e99765bb9d1d0254654941ddf3c9f20a82ab0`.
- K03 policy and scan roots matched the K06 pins; the scan reported zero
  issues over four protected Python files and zero protected Rust files.
- D05 regeneration matched the current K06 inventory and topology roots.
- K01 regeneration matched the current K06 entrypoint inventory root.
- J07 switch, post-context, epoch, and target writer-profile pins matched.
- Target admission passed; legacy admission rejected with
  `legacy_writer_disabled`.
- Focused K06 suite passed: 1 passed.
- Adjacent J07/J08/J09/K03/K05 regression passed: 41 passed.
- The 3 K04 tests failed at the pre-existing D05 pin check; this is the
  upstream drift recorded below, not a K06 failure.
- Ten named adversarial mutants were killed by the independent checker.
- Python compilation, Ruff, formatting, strict mypy, JSON parsing, and diff
  whitespace checks passed.

UPSTREAM_DRIFT: At the K06 freeze, the older K04 packet did not pass its own
current `tools/build_fcis_m6_k04_topology_anchor.py --check` command because
its D05 pin was `95fbc474...` while current D05 regeneration was
`e3b8fc99092de0fb56d08bf68ccb2f03278c776b684939765f86f1284fa9379e`. K06
recorded the current D05 topology root directly. A separate K04 rebind was
then completed at functional head
`26da7c198a43e0c248cd5823d98c6ce3037c2813` with docs receipt
`547901913c2090d19507b8b993f88276ff7f6a62`; its current-input gates pass.

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
