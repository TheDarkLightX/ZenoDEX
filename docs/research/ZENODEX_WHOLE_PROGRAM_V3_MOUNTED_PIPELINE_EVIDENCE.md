# V3 isolated publication integration evidence

2026-09-05. Baseline: `d02e2693476e597bbbb7cae75fb2905e004b0fff` plus
the exact subjects in the linked reviews. Authority: `NONE`.

The isolated SQLite publisher now requires the factory-owned raw-evidence
pipeline. Every attempted publication reauthenticates the actual BLS envelope,
recomputes the module, verifies the module/coordinator/route receipts, derives
allocation from the acquired committed predecessor, and verifies the ROOT
statement before the existing atomic commit. Caller-supplied route witnesses
are discarded. Acquisition authenticates the store snapshot; the core remains
pure and receives the snapshot explicitly.

An explicit signature-verifier purpose permits honestly labelled SHADOW
qualification. Production authentication retains its stricter release/evidence
requirements and historical signed bytes and binding roots. Isolated intent,
occurrence and verifier identities additionally commit their distinct purpose.
The public Python publisher API now requires `raw_evidence` and a minted
pipeline at construction. Existing wire formats and stored journal layouts
remain unchanged.

## Verification

The [independent mounted review](ZENODEX_WHOLE_PROGRAM_V3_MOUNTED_PIPELINE_REVIEW.md)
records exact hashes, the repaired pre-snapshot bounds check and its two
retained failing-then-passing controls. It discloses fixture/port self-review.
Its focused runs passed 150 authentication/BLS/pipeline tests and nine final
publication tests. The broader publisher/source/legacy suite passed 84 tests
before the two additional bounds controls; the final narrow rerun covers that
repair. These tests use real BLS signatures with synthetic RISC0 process replies.
They do not replace the genuine receipt batch.

The [purpose preparation record](ZENODEX_WHOLE_PROGRAM_V3_BLS_PROOF_PREPARATION.md)
records 173 purpose/authentication tests and 98 retained ASSET/PERPS compatibility
tests, with unchanged production golden bytes. Counts overlap other runs and
must not be added as distinct obligations.

The combined source was frozen for these parent checks:

```bash
PYTHON='<existing pinned project venv>/bin/python' bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
python3 -m ruff check src/integration/global_economic_durable_publisher_v1.py \
  tests/integration/test_isolated_asset_publication_v1.py
python3 -m mypy src/integration/global_economic_durable_publisher_v1.py
git diff --check
```

The critical gate passed Ruff, its configured 25-source mypy set, test hygiene,
bounded coverage checks, 433 acceptance tests and 834 critical tests. Its report
still lists incomplete product surfaces and `production_complete=false`.
The boundary checker passed all 14 checks while retaining
`BLOCKED_OPEN_COVERAGE`, `release_ready=false` and no production authority.
Scoped publisher Ruff/mypy and the diff check passed.

| Retained report | SHA-256 |
| --- | --- |
| `zenodex-v3-mounted-pipeline-critical01.log` | `37ebb72636ec7e15c68113ab57582aca3dca5857bb4d532e2e0b44fccac682e9` |
| `zenodex-v3-publisher-mount-boundary02.json` | `3e63df25d274f0fc3f0dc13c3d991968de4796cf58ffc95e5e6830afc3958d06` |
| `OPUS_V3_MOUNTED_PIPELINE_REVIEW.md` | `1bd5929a2ac9fe640d1433c7cede77786fd4c7c55bfda8ad7ea2a956d64ad262` |

An earlier boundary attempt rejected changing discovery inputs while concurrent
source edits were active. It was retained as a failed attempt; the later frozen
run passed without regenerating or weakening its discovery gate.

## Opus review disposition

An additional Opus 5 read-only review reached its 20-tool-turn cap and then
provided a final verdict from the inspected files. It ran no tests, did not
check the supplied source hashes and left several commit/receipt internals
unread. It found no demonstrated bypass in the mounted isolated path. Parent
review separates its suggestions from established defects:

- Purpose-neutral generic module admission is an explicit lower-level contract.
  A future production pipeline must freshly authenticate with production
  purpose. Merely accepting an existing module witness cannot establish that
  condition. An expected-purpose guard is a possible additional misuse check;
  it does not discharge deployment mediation or historical replay.
- The signed message commits the complete signature registry root and selected
  release. SHADOW and production status are registry content. Cross-purpose
  signature separation therefore depends on this existing registry binding,
  in addition to the new purpose-specific witness identities. Production
  message bytes were deliberately preserved. Four subsequently added real-BLS
  controls in `test_economic_command_signature_purpose_separation_v1.py` passed
  in 6.53 seconds: duplicate same-ID status entries refuse, status transitions
  refuse the other purpose's signature in both directions, and two selected
  releases in one profile sign distinct messages. The independent
  [SPOT/FARM discovery review](ZENODEX_WHOLE_PROGRAM_V3_SPOT_FARM_DISCOVERY.md)
  also reviewed and replayed these tests. They add bounded evidence without
  changing the production message or claiming a universal cryptographic proof.
- The suggested earlier duplicate port-identity check has no demonstrated
  acceptance impact: the exact sealed pipeline mounts its own retained ports,
  and the publisher checks identity before committing and again after ROOT
  verification. Source/process corruption is not excluded by another check.
- The ordinary pipeline result is intentionally data. Its individual module
  witnesses are opaque; the publisher acquires the result only from its owned
  pipeline and accepts no caller replacement. Adding another token would not
  strengthen that acquisition path under the stated interpreter boundary.
- The publisher is restricted to isolated qualification. Its module contract,
  typed constructor and this evidence packet state that limit. Its general
  historical class name supplies no production authority.

These are reviewed dispositions, not an Opus endorsement of whole-program
completeness or a mathematical safety proof.

## Remaining obligations

The [epoch-position extension](ZENODEX_WHOLE_PROGRAM_V3_EPOCH_POSITION_EVIDENCE.md)
qualifies a pure fold up to 64 commands with Python/Rust parity and a small Lean
control-flow theorem. The mounted raw pipeline and currently qualified route
guest remain restricted to one occurrence. Nonzero custody has a retained
module/coordinator totals disagreement. Neither limit counts as a completed
product capability.

Fresh genuine receipts for the new BLS-bound profile, source/dependency closure,
genesis ownership, historical authentication replay, restart authorization,
uniform indeterminate-response handling, writer fencing, migration and remaining
lane/route lifecycles remain open. Existing receipts continue to verify for their
historical images and exact inputs; they do not authenticate the newly prepared
profile. No heavy proof build, remote job, live activation, migration or
production promotion occurred in this integration.
