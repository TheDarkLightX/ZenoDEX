# FCIS M6 Task H08 Report

TASK_ID: H08
BASE_SHA: 1b08782266211354cd59e6976475da27fb9e4516
SOURCE_HEAD_SHA: f190abcc85acb27550d35f216ea9348f57613496
SOURCE_HEAD_TREE: e9ade01701b3006f307aca122db68abc46059ee2
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- tests/core/test_fcis_m6_h08_independent_review.py
- docs/research/m6_tasks/TASK_H08_PLAN.md
- docs/research/m6_tasks/TASK_H08_REVIEW_MATRIX_V1.json

IMPLEMENTATION_HEAD_SHA: f190abcc85acb27550d35f216ea9348f57613496
IMPLEMENTATION_TREE: e9ade01701b3006f307aca122db68abc46059ee2
IMPLEMENTATION_PARENT: 1b08782266211354cd59e6976475da27fb9e4516

CLAIM_IMPLEMENTED: H08 executes an independent exact-head attack suite over
the frozen H02/H03 research adapter. It covers two-connection stale CAS,
every ordinary H03 crash boundary, missing evidence, surplus orphan evidence,
and contaminated initialization. The first four attack families reject or
recover safely. The initialization attack produces a blocking witness, so the
review verdict is GAP and no atomicity approval is granted.

COMMANDS_RUN:
- python3 -m ruff format tests/core/test_fcis_m6_h08_independent_review.py
- python3 -m ruff check tests/core/test_fcis_m6_h08_independent_review.py
- python3 -m mypy --strict tests/core/test_fcis_m6_h08_independent_review.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h08_independent_review.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H08
- sha256sum --check --strict docs/research/m6_tasks/TASK_H08_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Focused H08 suite passed: 20 passed.
- All 16 ordinary H03 crash points reopened as exact PRE except the
  post-COMMIT/pre-response point, which reopened as exact POST.
- A second connection using the same stale request received
  STALE_SNAPSHOT_CAS and left its observed state unchanged.
- Deleting a committed evidence row and inserting an orphan evidence row were
  both rejected by canonical reopen.
- A pre-existing authority row outside snapshot_meta caused initialize_database
  to commit the seed and then fail canonical reopen, leaving snapshot_meta plus
  the unrelated row durable. This is the H08 blocker.
- Ruff, strict mypy, packet validation, and the source manifest pass.

MUTANTS_ADDED: None. The suite preserves the contaminated-initialization
witness as an explicit negative review result. Existing H02-H04 transaction
mutants remain covered by their prior packets.

FORMAL_EVIDENCE: None. H08 adds no machine-checked theorem. It adds
independent executable attack evidence and a review verdict.

REMAINING_NONCLAIMS:
- H08 does not repair the contaminated initialization boundary.
- H08 does not cover the four authority-helper-only crash points with a full
  verifier-produced authority-transition atom.
- H08 does not prove operating-system power-loss recovery, filesystem
  durability, production concurrent linearizability, destination delivery,
  migration, no-bypass coverage, whole-system accounting, or zUSD safety.
- No production datastore, caller, or value-moving path is mounted.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: `initialize_database` must reject any nonempty durable table
before the seed commit, or make the complete seed plus post-write canonical
reopen failure atomic. Until that repair is separately receipted and this
attack is rerun, H08 cannot approve R09. The H02 adapter remains a large
research hotspot, and the authority-transition fixture gap remains open.

