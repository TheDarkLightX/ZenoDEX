# FCIS M6 Task H06 Report

TASK_ID: H06
BASE_SHA: e55be951bd043a1b212c6ba8e0ddd75646fc8523
SOURCE_HEAD_SHA: 1405df9e8a8787b27630c53f3d2aac0190a16698
SOURCE_HEAD_TREE: 4372d0fa4b8237e947399e7d2ef0a7aa7a23cc43
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_h06_durability_config.py
- tests/core/test_fcis_m6_h06_durability_config.py
- docs/research/m6_tasks/TASK_H06_PLAN.md
- docs/research/m6_tasks/TASK_H06_DURABILITY_PROFILE_V1.json

IMPLEMENTATION_HEAD_SHA: 1405df9e8a8787b27630c53f3d2aac0190a16698
IMPLEMENTATION_TREE: 4372d0fa4b8237e947399e7d2ef0a7aa7a23cc43
IMPLEMENTATION_PARENT: e55be951bd043a1b212c6ba8e0ddd75646fc8523

CLAIM_IMPLEMENTED: H06 adds a closed SQLite durability-profile observation
and fail-closed checker for the isolated M6 adapter. The required profile is a
file-backed database with WAL, synchronous FULL, foreign keys enabled, a
minimum 5000 ms busy timeout, and normal locking mode. A research fixture
helper can apply that profile and then passes through the same checker. Weak
settings, an in-memory database, an open transaction, and invalid connection
types are rejected with stable typed codes.

COMMANDS_RUN:
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h06_durability_config.py
- python3 -m py_compile experiments/fcis_m6_h06_durability_config.py tests/core/test_fcis_m6_h06_durability_config.py
- python3 -m ruff check experiments/fcis_m6_h06_durability_config.py tests/core/test_fcis_m6_h06_durability_config.py
- python3 -m ruff format --check experiments/fcis_m6_h06_durability_config.py tests/core/test_fcis_m6_h06_durability_config.py
- python3 -m mypy --strict experiments/fcis_m6_h06_durability_config.py tests/core/test_fcis_m6_h06_durability_config.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H06
- sha256sum --check --strict docs/research/m6_tasks/TASK_H06_SOURCE_MANIFEST.sha256

RESULTS:
- Focused H06 suite passed: 11 passed.
- The closed profile configured and rechecked successfully on a file-backed
  database.
- In-memory and open-transaction configurations rejected before acceptance.
- Journal mode, synchronous level, foreign-key enforcement, busy timeout, and
  locking mode weakening mutants were all rejected with their named codes.
- The JSON profile matrix matches the module's closed constants.
- Python compilation, Ruff, formatting, and strict mypy pass.

MUTANTS_ADDED: None. The focused negative matrix exercises each named profile
weakening and typed-boundary rejection.

FORMAL_EVIDENCE: None. H06 supplies executable configuration evidence and does
not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- H06 does not prove filesystem power-loss durability, SQLite WAL/fsync
  behavior, or storage hardware semantics.
- H06 does not implement or check a PostgreSQL deployment profile.
- H06 is not mounted into production startup, H02 publication, or any value-
  moving caller.
- H06 does not prove concurrent linearization, migration, outbox delivery,
  no-bypass coverage, whole-system accounting, or zUSD safety.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The checker observes local SQLite pragmas and the fixture helper
mutates a research connection only. A production adapter must bind this
profile to deployment startup and prove the selected storage engine's actual
durability contract before promotion.
