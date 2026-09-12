# Fable sprint: September 12, 2026

Baseline: `8a99c42344de742ecceb4459711170563aa3784f`.
Accepted source: `2863bde5ff100b2bd1aa091706d30af805dce3f1`.
Scope: bounded W02/W03/W06 implementation and review. No complete lane,
workstream, formal core or value-movement qualification is claimed. Score change
is `NOT_RESCORED`. Authority remains `NONE`.

## Delivered behavior and code value

| Change | Before | Accepted behavior |
| --- | --- | --- |
| Oracle revision preflight | A lifecycle-valid increase from three to four reporters had no supplied-capacity check. | Explicit query/current/candidate context with only three distinct eligible reporters rejects that candidate. Canonical identity, lineage, bounded input and trace-first rejection are checked. This is an offline necessary condition under an unauthenticated premise. |
| Custody prover selection | The SDK could panic on an unknown selector; actor also omitted the session limit. | A native guard admits only unset, empty or case-insensitive IPC selection. Other and non-Unicode selectors receive `ProverConfiguration`. The existing proof, image, journal and receipt-kind checks remain. |
| Publication design review | The first packet incorrectly centered the M6 filesystem store. | Rejected that proposed second ledger. Confirmed the global SQLite publisher/authority/CAS seam and the distinct fresh-isolated versus same-lineage migration requirements. No V2 store was implemented. |

The source commit adds 730 physical lines and removes three: 223 additions and
three removals in tooling, 439 additions in the new Python test file, and 68
additions in the Rust host file. The latter includes 37 lines of native tests.
There are no new proof lines or dependencies. Evidence/docs and subsequent
productivity metadata are accounted separately by their full commit diffs.

Simplification removed a redundant second scalar-policy validation pass and a
single-caller lineage helper. Existing lifecycle behavior and JSON output remain
unchanged. The older tool's long functions remain inherited debt; they were not
rewritten for this patch.

## Verification and corrections

Commands on the accepted implementation:

```sh
python3 -m pytest -q tests/test_zenodex_oracle_query_policy_preflight_v1.py tests/test_zenodex_oracle_query_policy.py tests/test_zenodex_oracle_query_policy_chaos.py
python3 -m ruff check tools/zenodex_oracle_query_policy.py tests/test_zenodex_oracle_query_policy_preflight_v1.py
python3 -m mypy --follow-imports=silent tools/zenodex_oracle_query_policy.py tests/test_zenodex_oracle_query_policy_preflight_v1.py
cargo +1.90.0 test --locked --offline --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml -p zenodex-asset-lane-custody-global-risc0-host --lib
cargo +1.90.0 clippy --locked --offline --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml -p zenodex-asset-lane-custody-global-risc0-host --lib --tests --no-deps -- -D warnings
git diff --check
```

Results: 72 Python tests and 12 native Rust tests passed; Ruff, focused MyPy,
host Clippy and diff checks passed. Native builds used two jobs and zero debug
information in a task-owned cache. These commands do not build the actual guest.
The independent small-grid oracle test covers 48 quorum/population combinations.

The first oracle candidate passed 67 tests. Additional tests then demonstrated
acceptance of a duplicate trace key and masking of trace rejection by malformed
context. A further CLI regression demonstrated masking by an unreadable context.
All three counterexamples now reject with the intended outcome. A deep-context
control already passed before the repair; it is not counted as a discovered
failure. New preflight parsing now uses actual bounded byte reads and strict
duplicate-key hooks for both inputs. Legacy `verify` loading stays unchanged.
The existing `_unknown_fields` annotation was corrected to admit untrusted key
types, preserving its runtime rejection instead of deleting it for MyPy.

Astra reviewed the patches and corrected the parser/rejection behavior and an
overstatement in the Rust comment. Daybreak independently reviewed the prover
transport and the repaired oracle implementation. The SDK actor ignores proving
options, but the host still checks the resulting receipt kind; the report does
not claim that actor could bypass that final check. Scanning found no new runtime
red flags; the Rust scanner's 20 matches are existing test-fixture operations.
Model reviews are advisory and do not substitute for execution evidence.

## Fleet execution and usage

Three Fable 5.1 Max jobs initially ran concurrently. Two implementation jobs hit
output limits without producing patches and were interrupted for recovery. This
was an output-failure response, not an elapsed-time cutoff. Their outputs were
not accepted. The review completed, but its M6-based design was rejected.
The launcher also had three schema-initialization failures before model execution
and an output-write permission mismatch. Those failures remain in the records.

Two replacement Fable High jobs edited isolated source copies directly. The
Rust candidate took 48,297 ms and 4,265 reported output tokens; the oracle candidate
took 250,750 ms and 24,568 output tokens. These are candidate-generation
observations, not integration duration. The failed Max jobs reported 101,072 and
67,023 output tokens; the initial review reported 62,183. Do not infer a general
model speed ratio: the replacement contracts, effort and output method changed.

The last refreshed CLI screen reported Fable 84% used, all models 47%, reset
September 13 at 6 p.m. America/New_York. Paid overage remained off. The change
from the initial 75% Fable observation is an account-level observation, not exact
attribution to this sprint. Provider token counters retain their separate input,
cache and output categories; CLI list-price estimates are not subscription bills.
The [sanitized evidence](../../tests/evidence/fable_sprint_20260912.json) retains
per-worker metadata and separately reported CLI helper-model activity.

## Remaining work

The prover guard assumes stable process environment: the SDK reads the selector
again. The external IPC server's provenance and its honest enforcement of the
cycle limit remain operational premises; cycle count is not attested by the final
receipt check. Actual guest compilation, rebuilt image qualification, genuine
receipt production/verification, Kani, Lean, ESSO and full release gates were not
run in this batch. No new formal theorem is claimed. Runpod was unavailable.

The next W06 implementation is a fresh isolated V2 publication contract using the
global SQLite design, complete global/lane state and current authority. The
[continuity entry](../ZENODEX_SESSION_CONTINUITY.md#september-12-sprint-checkpoint)
records the reviewed scope and publication-history binding. Keep migration,
external anchoring, finality and live activation as distinct obligations.
