# FCIS M6 J09 Migration Crash Campaign V1

J09 is the bounded public-model and TLA+ campaign for the migration lifecycle
after J08 rollback semantics. The implementation target is:

```text
fdbbe7813621f0f4ae8c393f83ee2a99072bf8cc
tree fe7c15b3c5aca5d25e797d958ee2e47f0460dd64
parent 7a921783a8e0b3e706f4dcaa86bd3a9ad0aa6321
```

The Python model has one complete pending publication aggregate. A successful
publication appends history, residual, nullifier, and outbox evidence together.
The pending aggregate is either discarded by a PRE crash or published by a
POST crash. There is no modeled durable partial publication.

The phase relation is the exact prefix:

```text
LEGACY
-> SHADOW_REPLAY
-> DUAL_CHECK
-> QUIESCED
-> AUTHORITY_SWITCH
-> POST_SWITCH_VALIDATION
-> LEGACY_DISABLED
```

Before the switch, the legacy writer is the only configured writer and the
evidence version is V1. The authority-switch edge changes the epoch, rebinds
all retained evidence to V2 in the one modeled aggregate, and enables only the
target writer. POST_SWITCH_VALIDATION has no active writer until a fresh
authorization; LEGACY_DISABLED allows the target writer after fresh
authorization.

Every commit consumes the fresh authorization latch. Restart clears the active
writer and authorization generation. A retry can confirm an existing commit
only when commit ID, fingerprint, writer, sequence, expected head, and epoch
remain equal. A PRE retry can prepare the same attempt only after reauthorization
while the expected head remains current.

Outbox delivery changes PENDING to DELIVERED and records a destination receipt.
Acknowledgment requires the effect identity to be in the delivered set and
records a separate acknowledgment root. The model therefore checks ordering and
provenance while leaving destination idempotency as a production refinement.

The Python campaign explores every action word through depth 10. The independent
TLA+ model checks the same control obligations with bounded counters. The
permanent negative frontier includes skipped phase, dual writers, missing
residual transport, mixed V1/V2 evidence, restart without fresh authorization,
acknowledgment before delivery, effect-identity rebound, crash partial
observation, old writer after switch, and balance-only rollback.

Commands used for the functional target:

```text
PYTHONPATH=. python3 experiments/fcis_m6_j09_migration_crash_check.py
PYTHONPATH=. python3 tools/build_fcis_m6_j09_migration_crash.py --check
PYTHONPATH=. pytest -q tests/core/test_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash_properties.py
python3 -m ruff check src/core/fcis_m6_j09_migration_crash.py experiments/fcis_m6_j09_migration_crash_check.py tools/build_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash_properties.py
python3 -m ruff format --check src/core/fcis_m6_j09_migration_crash.py experiments/fcis_m6_j09_migration_crash_check.py tools/build_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash_properties.py
python3 -m mypy --strict src/core/fcis_m6_j09_migration_crash.py experiments/fcis_m6_j09_migration_crash_check.py tools/build_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash_properties.py
```

The exact TLC command used the repository-local TLA tools jar from the known
good main checkout because this isolated recovery worktree does not contain
that external dependency:

```text
java -cp "${REPO_ROOT:?}/external/tla-tools/tla2tools.jar" tlc2.TLC -cleanup -workers 1 -config formal/tla/FCISM6J09MigrationCrash.cfg formal/tla/FCISM6J09MigrationCrash.tla
```

The TLA claim registry and generated summary remain scoped to this bounded
control model. No production mount, datastore adapter, runtime authority
switch, deployment, or value-moving path was changed.
