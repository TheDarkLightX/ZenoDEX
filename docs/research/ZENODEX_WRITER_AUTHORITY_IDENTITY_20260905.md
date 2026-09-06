# Live writer authority identity

This W11 repair follows `d92dfa9b99ce973d9a410dd0ef70709ce8ea8bff`.
It closes an observed live pathname-detachment failure under the host
assumptions below. It does not close W11 or qualify production publication.

## Failure and repair

The retained baseline regression created a publisher attached to an ACTIVE
authority database, replaced its pathname with an independently validated
REVOKED successor database, and observed the open publisher commit using its
detached ACTIVE attachment. That regression passed on the baseline while
explicitly asserting the unsafe behavior. It is retained as an inverted
rejection regression in this repair.

A verified writer now owns an authority identity descriptor for its journal's
lifetime. Acquisition and subsequent checks require a regular file owned by
the current user, mode 0600, one filesystem link, and matching device/inode
identity between the retained descriptor and live pathname. Acquisition does
not follow a symbolic link. The descriptor is released on close and failed
writer construction.

The journal checks identity during source acquisition and validated reads. It
checks again inside the publication transaction, including before an exact
retry is returned and immediately before the first economic write. Detachment,
absence and metadata drift fail closed. These checks change no committed wire
format, economic constant, rounding rule or authority generation.

## Outcome contract

`DurableEconomicWriterAuthorityIdentityChangedV1` describes an identity
observation failure. The journal constructs the narrower
`DurableEconomicWriterAuthorityPrecommitIdentityChangedV1` only while the
current commit transaction can still establish that it has made no economic
write. The publisher handles this narrower result separately from response
projection.

A failed observation after a successful commit retains the existing
`GlobalEconomicPublicationIndeterminateV1` contract. Failure while reconciling
or advancing the monotonic anchor retains
`GlobalEconomicAnchorAdvanceIndeterminateV1`. Neither outcome asserts that
the economic commit was rolled back. A known refusal still means no change to
the attempt's economic state, history, replay or outbox; filesystem housekeeping
is outside that logical no-effect contract.

Revocation performed through the same retained authority inode still produces
`AUTHORITY_STALE` for new publication. An exact committed retry under that
same-inode revocation retains its historical result. A detached live writer
cannot use the old attachment to claim a current retry observation.

## Evidence and replay

Independent root replay passed all 137 journal, publisher and outcome tests in
142.09 seconds on the frozen production-source tuple. The meaningful baseline
evidence is the retained test that
observed COMMITTED. An early collection failure while introducing the new
exception type is not counted as reproduction evidence.

```bash
python3 -B -m pytest -q \
  tests/integration/test_global_economic_epoch_journal_v1.py \
  tests/integration/test_global_economic_durable_publisher_v1.py \
  tests/integration/test_global_economic_known_outcomes_v1.py \
  tests/integration/test_global_economic_publication_outcomes_v1.py
```

The regressions observe complete logical economic-store snapshots for refused
attempts. Postcommit controls retain and decode the committed occurrence's
source, body and receipt; an anchored control also checks that failed identity
observation leaves the external anchor unchanged. Receipt replies in this
suite remain isolated synthetic fixtures.

The complete critical-quality gate also passed: Ruff, the gate's 25-file MyPy
scope, 433 acceptance tests and 834 critical tests, with 89% coverage for its
declared scope. The publication sources separately pass MyPy. The publisher
test module retains the same 11 MyPy errors as the baseline; a source-snapshot
comparison confirmed no added diagnostics. Two new byte observations were
narrowed explicitly during root review. A test-only FIFO assertion also
ensures that a future blocking-open regression fails before opening the FIFO.
All three affected tests passed again after these test-only changes. No full
Lean/Mathlib or RISC0 workspace build was performed for this Python repair.

The production-boundary check passed all 14 checks while retaining
`m6_production_mounted=false` and `BLOCKED_OPEN_COVERAGE`.
Source/test hashes and replay commands are declared
in `tests/evidence/test_hygiene/THV1-20260905-writer-authority-identity-v1.json`.

The existing transaction methods remain large. The publication error paths
were separated to preserve their distinct knowledge contracts; the journal's
prewrite checks remain beside its single economic write sequence so that their
ordering is directly reviewable. Broader structural cleanup is outside this
repair.

## Trusted boundary and remaining work

The retained descriptor pins an identity for comparison. Python's SQLite API
does not expose its attached database descriptor, so this repair does not
directly prove that SQLite holds that exact descriptor. A stable namespace
during descriptor acquisition/ATTACH remains a premise, as does namespace
stability between the last prewrite identity check and COMMIT. Cooperative
database locks do not establish those filesystem premises.

The publisher process, operating system, filesystem and exclusive service
ownership remain trusted. In-place restoration of valid old bytes, epoch-file
rollback or replacement, restart rollback, migration retirement and complete
old-writer exclusion remain separate obligations. Fresh genuine receipt
qualification and deployment-complete mediation also remain open.

The next W11 boundary is authenticated monotonic storage and migration/writer
fencing over one exact deployment subject. This local guard must not be used
to claim resistance to a compromised operating system or publisher process.
