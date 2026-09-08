# Real AutoTrader signal migration with the Tau Artifact Workbench

The compact V2 signal adapter is implemented in the existing AutoTrader
producer/parser path. On the fixed 14-observation corpus, it saves 40.4% of raw
JSON bytes and uses more CPU. Native Tau generates valid independent choices
for the two code owners, while ordinary cached exhaustive checking is much
faster for this small problem. This is a useful bounded application and a
measured limit on the previous workbench's practical value.

The [normative specification](tau_signal_migration_spec_20260908.md) and
[reviewed replay](tau_signal_migration_20260908/replay/report.json) define the
scope. Previous reports remain historical evidence. The new publication uses
main's existing registry, Tau runner and witness modules, and records their
current hashes separately from the historical baseline. The composition, swarm
and artifact workbench implementation bytes are preserved. This cycle adds no
Tau internals, binary redistribution or
third-party dependencies. It retains the earlier research's provenance and
license/patent claim limits; this report supplies no legal clearance.

## What is mounted

`ExternalSignalObservation.to_compact_dict()` opts into schema
`zenodex/autotrader-external-signal/v2`. The existing
`external_signal_observation_from_dict()` and bulk loader accept V2, decode its
seven metadata bits and call the original observation constructor. The existing
`to_dict()` still emits V1. The constructor, source registry and Tau policy
receipt builder keep their existing decisions.

```python
from src.integration.autotrader_signals import external_signal_observation_from_dict

signal = external_signal_observation_from_dict({
    "schema": "zenodex/autotrader-external-signal/v1",
    "signal_id": "signal.alpha", "source_id": "provider.alpha",
    "source_kind": "advisory_external", "trust_tier": "advisory",
    "freshness_ok": True, "auth_ok": False, "advisory_only": True,
    "tags": ["market"],
})
compact = signal.to_compact_dict()  # profile_code = 83
restored = external_signal_observation_from_dict(compact)
assert restored.to_dict() == signal.to_dict()
```

The finite kernels are the actual functions imported by the typed profile
adapter. They permute a semantic metadata word into the wire layout and back.
Tau's source-derived relation requires exact field preservation on 0..127 and
the rejection sentinel on 128..255. It does not cover arbitrary Python,
monetary amounts, identifier strings, JSON implementations or network delivery.
Those wrapper boundaries receive separate tests.

V1-shaped objects retain inherited permissive handling of extra keys and
unknown schema labels. A V2-schema object has an exact closed field set. The
new codec never changes the registry/provenance numeric ABIs, which use different
source-kind projections from the transport layout.

## Neuro-symbolic user stories

A trader and their advisory agent swarm collect external observations. The
producer emits compact V2 objects to an upgraded reader. The reader reconstructs
the same metadata, and registry checks still determine which observations may
be used. The compact profile gives the swarm no signing, trading or settlement
authority. A malformed object rejects without returning a partial batch;
corrected input can be retried deterministically.

A developer and two agent teams maintain the encoder and decoder. The workbench
binds their exact source bytes, evaluates the complete byte domain, and generates
local Tau gates for compatible choices. Each owner can choose either of two
equivalent implementations; all four combinations preserve the original
contract. Changing to a different bit layout requires coordination. These are
bounded program alternatives, not arbitrary agent-generated repository patches.

A release engineer and their swarm plan adoption. The old parser, reexecuted
from public base `e1838293c839d4f830f1f1501205b55bc88c8975`, rejects all 14
valid V2 objects. Upgrade readers first, then explicitly enable compact
producers. Cancelling adoption requires no stored-state migration because V1
production remains available. Removing V1 support would be separate work.

## Measurements

Python 3.12.3 and zlib 1.3; five alternating-order timing trials, 1,000 batches
per action per trial, 20 warm-up batches. Each batch contains the 14 metadata
states accepted by the original constructor, fixed short identifiers and one
tag. The timings are local measurements on a shared workstation. They do not
estimate production throughput or agent labor saved.

| Measurement | V1 | V2 |
| --- | ---: | ---: |
| Sum of individual JSON object sizes | 3,346 B | 1,993 B |
| Complete JSON batch | 3,361 B | 2,008 B |
| Same batch with gzip level 6 | 256 B | 193 B |
| Median encode + JSON per observation | 6.98 us | 9.44 us |
| Median JSON decode + original guard per observation | 18.23 us | 24.03 us |

Raw individual objects save 1,353 bytes, or 40.44%. Gzip reduces the incremental
saving to 63 bytes per batch, or 24.61% of the compressed V1 size. Gzip was a
size-only comparison. CPU cost increases for both serialization and parsing;
there is no measured latency improvement. V1 with ordinary batch compression
is already a strong baseline, and V2 remains opt-in.

| Compatibility computation | Observed work | Time |
| --- | --- | ---: |
| Analyze exact candidate sources | 10 programs, 256 inputs each | 11.42 ms |
| Cached ordinary exhaustive checking | 25 artifact pairs, 6 valid | 0.542 ms |
| Exact behavioral quotient | 16 class pairs, 3 valid | 0.342 ms |
| Native Tau envelope compilation | 9 native queries | 843.95 ms |

The cached baselines exclude source analysis, which is shown separately. Tau
compilation includes rebuilding the source catalog. Two additional native file
stream executions check the exported local gates on all four possible class
codes each. Native CPython separately checks all 2,560 component input results
and replays every candidate pair, stopping each failing pair at its first
counterexample. This checks 1,955 pipeline inputs and agrees with the exhaustive
reference on all 25 pair outcomes. Two same-class replacements and their joint
revision pass fresh source checks with zero additional Tau queries; ordinary
behavioral caching can reuse these equivalences too.

The Tau binary SHA-256 is
`b62c0706f682d305fce461750d2332a473ce1fb0e6e7f45b2bb46e5174d07326`.
The replay binds 67 source/evidence files. Exact source-to-binary build
correspondence is not claimed.

## Evidence and review

The pre-edit fixture contains all 128 metadata states: 14 accepted and 114
rejected, with normalized fields/hashes or exact error type/message. A separate
historical-module replay matched all 128 rows and confirmed old-reader V2
rejection. Its dependency scope is recorded in
[legacy_replay.json](tau_signal_migration_20260908/legacy_replay.json).

Independent review found and corrected two issues. The initial prose overclaimed
rejection of mixed objects under the permissive legacy schema; it now specifies
the exact V2 boundary. The initial benchmark echoed historical source hashes
without anchoring the captured fixture. A minimized test demonstrated a forged
hash still passed. The benchmark now checks immutable baseline and historical
replay digests before comparison; retained tests reject both substitutions.

The integration oracle independently writes the source/trust mapping and wire
layout. It checks all 128 states, every reserved byte, exact types, identifier
and tag boundaries, normalization hashes, packet/registry results, Tau policy
receipt data, legacy schema behavior, atomic batch rejection and recovery. A
named swapped-flags control preserves rejection while changing metadata,
demonstrating why verdict-only parity is insufficient.

The final publication candidate passed 502 selected native-enabled Tau,
workbench and migration tests on an isolated snapshot based on main
`ee9f81a3164b63d63cdafef6e0ca409c9b38a265`. The reported measurements come from
that candidate, with all 67 report hashes independently checked against it.

The shared working checkout also passed 588 scoped research/integration/guard
tests before the final
evidence-binding correction; 216 focused tests passed afterward, including the
two new negative tests. The native existing registry Tau trace passed. Scoped
Ruff and mypy, Tau supported-runtime checks and the production-boundary checker
passed. The assurance status tool reported its existing April snapshot; this
was a status read, not a new release validation. Full critical/release, full
integration, Lean, TLA model and Rust/RISC0 suites were not run. Disk space
briefly exhausted during review, so large builds were avoided.

Publication validation caught a missing core-module import in the initial
research branch's base. The final branch is therefore
`research/tau-signal-migration-20260908`, based on clean main. It includes the
previous Tau research and this migration. Carrying older whole-file adapter
versions would have weakened process-exit validation and broken main's witness
ABIs. That proposal was rejected before publication. Main's existing modules
remain in place; the new native replay binds their actual hashes. Historical
reports retain the hashes of their earlier environments and are not asserted
to match these three current dependency files.

## Reproduction

Use a separately installed compatible Tau executable. The output directory
must not exist. Timing samples can vary; exact finite results and source hashes
must agree.

```bash
python3 tools/benchmark_tau_signal_migration.py \
  --tau "$TAU_COMPOSITION_BIN" --out /tmp/tau-signal-replay-new \
  --repetitions 1000 --trials 5
python3 -m pytest -q tests/test_tau_signal_migration_benchmark.py \
  tests/integration/test_tau_signal_migration.py \
  tests/integration/test_autotrader_signal_profile.py
```

The baseline was captured with `capture_baseline(Path(BASELINE))` from
`tools.tau_signal_migration_case` before the adapter edit. Historical verification
extracted `src/integration/autotrader_signals.py` with `git show` at the public
base above, checked its captured digest, loaded it under a distinct integration
module name, and compared every captured row. This is an original-module replay
with the unchanged constructor guard, not a historical whole-repository build.

## Next higher-value candidate and lessons

The next candidate is a mixed-version rolling-upgrade planner. A developer and
their swarm specify old/new producers, readers, queued formats and required
observations. Source-derived compatibility plus bounded state exploration would
propose a safe upgrade order, or explain why a tagged transition adapter is
required. Local Tau policies could constrain each team's allowed next change.
Deployment permission and message delivery would remain separate runtime checks.

This experiment already supplies a negative result: its three legal format
class pairs are `(0,0)`, `(1,1)` and `(2,2)`. There is no legal edge that changes
one owner at a time. The alternate formats are synthetic future choices, not
additional accepted encodings under the deployed V2 schema.

There is a general reason for this obstruction. Let semantic and wire alphabets
have the same finite size, let both encoders be injective, and let one
deterministic decoder invert both on the complete domain. Then the encoders
must be equal: the first encoder is bijective, fixes the decoder as its inverse,
and forces the second encoder to be identical. Identity versus `x xor 1` gives
a two-state counterexample to a proposed shared decoder: wire 0 would mean both
0 and 1. This elementary argument and the finite graph are scoped evidence,
not a new foundational theorem or a Lean-checked result.

The next experiment should first enumerate an actual V1/V2 compatibility matrix
and compare a simple graph search with Tau-derived local rollout gates. It must
include outstanding old messages, rejection/no-effect behavior, unknown-schema
legacy fallback, rollback, and the version/sentinel alphabet budget. Promote it
only if it finds a concrete rollout failure or enables a safe upgrade that the
current pairwise workbench cannot express. Stop the Tau-specific lane if simple
exhaustive checking supplies the same result more cheaply without a useful
reusable local-policy benefit.

Lessons: mount exact source before claiming practical use; preserve metadata
instead of only acceptance bits; freeze historical evidence; compare compressed
transport and cached ordinary code; distinguish static compatible bundles from
safe deployment paths. The measured compression tradeoff is complete. Dramatic
trading gains, reduced human review time, Tau Net execution, production release
and research novelty remain unestablished.
