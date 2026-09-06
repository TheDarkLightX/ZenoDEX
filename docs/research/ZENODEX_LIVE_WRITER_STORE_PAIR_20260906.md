# Live epoch and authority store identity

This W11 follow-up starts at `5bc940e04a4f3cf29ea923fd8214cb8db9d3801a`.
It extends the earlier authority-file repair to the economic epoch database.
The qualification scope is an isolated verified publisher on the current Linux
host contract. It supplies no release, migration or production authority.

## Reproduced failure

The verified publisher retained the identity of its attached authority file,
while its main SQLite epoch connection had no corresponding retained identity.
A live publisher could therefore read a detached epoch database after the epoch
pathname was replaced with another valid database.

The retained regression first commits an epoch, prepares an independent valid
sequence-zero replacement, replaces the live pathname, and confirms that a
fresh structural reader sees sequence zero. The old publisher must refuse to
describe the detached database as the current head. Before the guard repair,
that expectation failed because the live publisher returned its old head.
This is a local namespace-control failure; no remote trigger is established.

## Implemented contract

The writer owns one fixed pair of epoch and authority identities for its
lifetime. Each identity is a retained descriptor acquired without following a
symbolic link or blocking on a nonregular file. Each observation requires:

```text
regular file + current service UID + mode 0600 + one link
+ live pathname device/inode = retained descriptor device/inode
```

Source acquisition, capability minting, validated writer observations, exact
retries and publication gates check the pair. All failed construction paths
and normal close release both descriptors. The pair is local shell state; it
does not add a field to an economic journal, wire format or authority root.

A specifically typed failure before the first economic write establishes a
known no-effect refusal for that attempt. A general identity observation
failure after commit remains indeterminate. Such a failure cannot erase the
committed bundle or be reported as a rejected transition. Anchor observation
retains its separate indeterminate outcome. Same-inode authority revocation
continues to reject new work while permitting an exact historical retry.

## Evidence and replay

Independent root replay passed **145 tests in 157.11 seconds** on Python 3.12.3
and SQLite 3.45.1:

```bash
python3 -B -m pytest -q \
  tests/integration/test_global_economic_epoch_journal_v1.py \
  tests/integration/test_global_economic_durable_publisher_v1.py \
  tests/integration/test_global_economic_known_outcomes_v1.py \
  tests/integration/test_global_economic_publication_outcomes_v1.py
```

Before the repair, the new detached-head regression failed with `DID NOT RAISE`
after confirming that an independent reader observed the valid replacement.
The final controls cover replacement before proof, at source-read exit, during
proof and during an exact committed retry. They compare complete metadata,
current-head and epoch rows from both the replacement pathname and the
publisher's actual retained main connection. This second observation matters:
an unchanged replacement alone cannot establish that the detached database was
unchanged. Root review required that correction before accepting the tests.

The postcommit control decodes the exact committed bundle before replacement,
checks its receipt, body, source and head, then confirms the retained rows are
unchanged while the public outcome remains indeterminate. Descriptor controls
check both closures, failure after partial acquisition and failure while opening
SQLite. The FIFO control asserts nonblocking acquisition flags before opening.
The existing authority revocation and anchor controls remain green.

Both production files pass MyPy, and the touched Python files pass Ruff.
The publisher test file has one existing MyPy `Path`/bytes diagnostic. An
independent `--shadow-file` comparison against the base source produces that
same diagnostic; no new test typing error is reported under this environment.

The shared critical-quality gate passed Ruff, its 25-source MyPy scope,
433 acceptance tests and 834 critical tests with 89% coverage for its declared
scope. These suites overlap other evidence and are not a completion metric.
All 14 production-boundary checks pass while retaining
`m6_production_mounted=false`, `release_ready=false` and
`BLOCKED_OPEN_COVERAGE`.

```bash
bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
```

The critical gate used the existing qualified development environment; no
dependency installation was needed. Source/test hashes are declared by
`tests/evidence/test_hygiene/THV1-20260906-live-writer-store-pair-v1.json`.
Regenerate its declaration with
`python3 -B -m experiments.v3_completion_followup_v1.render_evidence`.
Rendering does not execute the tests or qualify a release.

The retained transaction method remains above the normal complexity budget.
Its identity gates stay adjacent to the single write sequence so prewrite and
postcommit failures remain visibly distinct. Broader journal decomposition is
outside this repair. No RISC0, GPU, full Lean/Mathlib or solver build was run for
the datastore change.

## Trusted boundary and remaining work

The pair compares live paths with retained identities. Python's SQLite API
does not expose its internal main and attached database descriptors. Namespace
stability during acquisition, SQLite open/attach and after the final check is
still required. These checks do not establish filesystem linearizability or
protect a compromised publisher process, operating system or filesystem.

Restoring valid old bytes into the same inode, rollback before a fresh restart,
authenticated monotonic storage, migration retirement and complete exclusion
of old writers remain separate W11 obligations. Structural readers and SHADOW
observations do not gain publication authority. Genuine proof-chain and
deployment qualification remain open.
