# FCIS M6 Task E07 report: transport-loss campaign

TASK_ID: E07
BASE_SHA: 2b452bd5f4aaccd4cd3acb0c938c0283cd7df31b
SOURCE_HEAD_SHA: fe2fce12353f6dd4a6accc15764102a91a486345
SOURCE_HEAD_TREE: db1437e7135e1d45547e3a93714c8b7e42b962bb
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_e07_transport_loss_v1.json
- experiments/fcis_m6_e07_transport_loss.py
- experiments/fcis_m6_e07_transport_loss_check.py
- tests/core/test_fcis_m6_e07_transport_loss.py
- tools/build_fcis_m6_e07_transport_loss.py
- docs/research/m6_tasks/FCIS_M6_E07_TRANSPORT_LOSS_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_E07_TRANSPORT_LOSS_V1.json
- docs/research/m6_tasks/TASK_E07_PLAN.md
- docs/research/m6_tasks/TASK_E07_REPORT.md
- docs/research/m6_tasks/TASK_E07_EVIDENCE.json
- docs/research/m6_tasks/TASK_E07_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: fe2fce12353f6dd4a6accc15764102a91a486345
IMPLEMENTATION_TREE: db1437e7135e1d45547e3a93714c8b7e42b962bb
IMPLEMENTATION_PARENT: 2b452bd5f4aaccd4cd3acb0c938c0283cd7df31b

CLAIM_IMPLEMENTED: E07 models four transport-loss points around E05 and
resolves every point through a fresh E04 lookup. Loss before server entry and
after validation leave PRE and resolve to ABSENT_RETRYABLE. Loss after commit
and after response generation leave POST and resolve to ALREADY_COMMITTED.
All fresh lookups retain INDETERMINATE client knowledge. Blind retries after
PRE loss commit once; blind retries after POST loss receive stale predecessor
rejection and do not create a second publication.

COMMANDS_RUN:
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e07_transport_loss.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e07_transport_loss.py`
- `python3 tools/build_fcis_m6_e07_transport_loss.py`
- `python3 tools/build_fcis_m6_e07_transport_loss.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_e07_transport_loss_check.py`
- `python3 -m py_compile experiments/fcis_m6_e07_transport_loss.py experiments/fcis_m6_e07_transport_loss_check.py tools/build_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e07_transport_loss.py`
- `python3 -m ruff check experiments/fcis_m6_e07_transport_loss.py experiments/fcis_m6_e07_transport_loss_check.py tools/build_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e07_transport_loss.py`
- `python3 -m ruff format --check experiments/fcis_m6_e07_transport_loss.py experiments/fcis_m6_e07_transport_loss_check.py tools/build_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e07_transport_loss.py`
- `python3 -m mypy --strict experiments/fcis_m6_e07_transport_loss.py experiments/fcis_m6_e07_transport_loss_check.py tools/build_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e07_transport_loss.py`
- `python3 -m json.tool config/deploy/fcis_m6_e07_transport_loss_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_E07_TRANSPORT_LOSS_V1.json`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks E07`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_E07_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused E07 suite passed: 2 passed.
- Combined E05/E06/E07 suite passed: 16 passed.
- Independent checker passed: `E07_TRANSPORT_LOSS_CHECKS_PASS 4`.
- Source-bound vector regeneration and check passed:
  `E07_TRANSPORT_LOSS_VECTOR_MATCH`.
- Before request reaches server: fresh outcome `ABSENT_RETRYABLE`, blind retry
  `COMMITTED`, final counts 1/1/1.
- After validation before transaction: fresh outcome `ABSENT_RETRYABLE`, blind
  retry `COMMITTED`, final counts 1/1/1.
- After transaction commit before response: fresh outcome
  `ALREADY_COMMITTED`, blind retry `STALE_SNAPSHOT_CAS`, final counts 1/1/1.
- After response generation during transport: fresh outcome
  `ALREADY_COMMITTED`, blind retry `STALE_SNAPSHOT_CAS`, final counts 1/1/1.
- Two complete campaigns produced byte-identical summaries.
- Ruff, Ruff formatting, strict mypy, Python compilation, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: E07 covers skipped server entry, validation without a
   transaction, response loss after commit, response loss during transport,
blind duplicate retry after POST, incorrect durable outcome after PRE loss,
and incorrect client-knowledge collapse. The fresh E04 lookup and E05 retry
tests preserve the transport/durable separation.

FORMAL_EVIDENCE: None. E07 supplies a deterministic transport-shell model,
fresh lookup replay, source-bound vector, and mutation-killing tests. It does
not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- E07 simulates loss points locally and does not prove real network behavior,
  response buffering, process crashes, filesystem durability, or production
  retry middleware.
- Fresh lookup uses E04 verifier-owned research values; E07 does not prove
  external datastore authenticity or receipt freshness.
- E07 does not mount runtime callers, destination idempotency, migration
  authority, no-bypass coverage, accounting, backing, zUSD safety, or value
  movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The transport shell intentionally reuses the E05 model database
and E04 model lookup. Production response-generation boundaries, network
timeouts, process restarts, and cross-service idempotency remain unrefined.
