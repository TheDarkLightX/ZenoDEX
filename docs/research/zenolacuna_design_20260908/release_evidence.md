# ZenoLacuna first-release evidence

The five implementation packages in [completion_plan.md](completion_plan.md)
are implemented for the supported finite profile. The signed CLI takes the real
AutoTrader migration through a witnessed missing decision, owner-signed answer,
protected requirement revision, unsafe candidate rejection, guarded candidate
verification, durable storage and fresh-process archive replay.

The [32-scenario ledger](release_coverage.md) maps all acceptance obligations to
executed tests. The S22/S29/S32 amendments and host premises are explicit in
[release_contract.md](release_contract.md). The earlier simulated prototype,
frozen design, logo and abstract Lean proofs remain available.

## Frozen subject and results

Qualification used an isolated checkout based on
`4b683914a8328044c57a3fc72fb81771f6ed9247`, with only the owned ZenoLacuna
release files overlaid. Unrelated dirty work in the active DEX checkout was
preserved. The [checker closure](artifacts/checker_closure.json) contains 137
local Python sources, 1,857,984 bytes, with checker identity
`332073a5502b9f3ac59fd867b1060a51d1663fdca61fb890f4fd08dea76bbebc`.

- **277 focused tests passed, zero failures/errors/skips**, including native Tau
  checks, signed lifecycle and subprocess qualification, in 281.78 seconds.
- Ruff passed for the package, tools and focused tests; mypy passed for all
  35 package/tool source files. The security red-flag scan reported zero
  findings on its 33-file core/CLI subject; scanner silence is not proof.
- `lake env lean Proofs/ZenoLacuna.lean` passed in the existing pinned Lean
  4.27/mathlib environment. The unchanged file's twelve theorems use only
  `propext`, `Quot.sound`, and `Classical.choice`. This is abstract filtering
  and identifiability evidence, without a Python refinement theorem.
- The public native qualification completed all 38 CLI subprocess calls and
  replayed an identical saved certificate from a fresh process.
- An independent bounded critical review reproduced the ESSO-root Z3 shadow
  and repository-root import shadow failures, checked their repairs, and
  reported no remaining confirmed blocker in the repaired core. The review
  also checked the 256-source archive-budget repair and the explicit scenario
  amendments. Test and native results above are integrator-run evidence.

The real migration fixes the metadata domain at 128 words and the other payload
fields at declared fixtures. Its graph contains 1,542 canonical states and
208,170 representative command edges. ENQUEUE enumerates all 128 words;
other actions use the representative word 0 because they consume the queued
word instead. The independent runtime/ESSO evaluator also checks 2,304
representable invariant states. The graph includes queued delivery, retry,
cancellation and consumer/producer rollback.

Tau checked the finite relation and eliminated post-consumer variables to derive
this guard:

```text
(p'|b')&(p|a')|q&(v'|b')&(v|a') = 0
```

Here `p`/`v` indicate producer/queued V2 schema, `q` means the queue is occupied,
and `a`/`b` are the proposed consumer's V1/V2 capabilities. A second Tau query
checks equivalence to the declared invariant, and the finite checker compares
all 18 capability states. ESSO then checked initialization plus all eight action
invariant queries with **both Z3 and CVC5 returning UNSAT**, after independent
IR/runtime parity. These are complementary checks of the declared abstraction.

## Benchmark

The [public summary](artifacts/release_summary.json) records the source and tool
pins, certificate, counts and timings. One missing policy requirement underlies
the fixture's two rejected premature-workflow cases. The final owner decision
requires one question; a suitable fixed question also requires one. Runtime LLM
calls are zero. The fixture had zero missed missing-requirement cases, spurious
admitted witnesses or false completions. These are counts for the explicit
fixture, not rates over arbitrary requirements or programs.

| Measured operation | Seconds |
| --- | ---: |
| Direct finite migration checker, including import and omission negative check | 2.134 |
| Signed COMPLETE with runtime and required native verification | 25.091 |
| Fresh-process native archive replay | 17.189 |
| Full 38-command CLI qualification | 155.631 |

This descriptive local run followed the completed focused test suite. Other
host load was uncontrolled, and this was not a repeated timing experiment. The direct baseline performs less work:
it excludes signed ownership/revision, durable history, native solver checks
and independent bundle replay. The measurements establish neither a Tau speed
advantage nor reduced question count. The delivered benefit is the connected,
repeatable acceptance workflow and the concrete failure families it rejects.

## Reproduce

Use the checked release checkout and a Python environment containing the
repository dependencies and Z3. Select CVC5 through PATH or `CVC5_PATH`. Set
`ESSO_ROOT` to a separately installed root containing its `ESSO` package.

```bash
TAU_BIN="$TAU_BIN" python3 -m pytest -q tests/test_zenolacuna*.py
python3 -m ruff check src/zenolacuna tools/zenolacuna*.py \
  tests/test_zenolacuna*.py tests/zenolacuna*.py
python3 -m mypy src/zenolacuna tools/zenolacuna*.py
python3 tools/zenolacuna_qualify.py --out /tmp/zenolacuna-native-replay \
  --tau-bin "$TAU_BIN" --esso-root "$ESSO_ROOT"
```

The qualification directory must be fresh. The runner uses the public CLI and
publicly known test credentials, writes no private signing material into its
artifacts, and emits its final report only after the complete workflow succeeds.
It does not authorize a deployment or act as a real owner.

The [saved canonical bundle](artifacts/native.bundle.json) has SHA-256
`6b4bf83db08e0e7af29e657bef285a750a139ce2df1d5512980a7015bd1c505c`.
Its exact historical revision can be checked with the recorded native tools:

```bash
python3 tools/zenolacuna.py project replaybundle \
  --bundle docs/research/zenolacuna_design_20260908/artifacts/native.bundle.json \
  --owner-key 03a107bff3ce10be1d70dd18e74bc09967e4d6309ba50d5f1ddc8664125531b8 \
  --expected-revision 2014abd4443dc54a9690523a2905f41ca1f0d11c5a0e2b5a10a9718f82bfe4c1 \
  --tau-bin "$TAU_BIN" --esso-root "$ESSO_ROOT"
```

Replay requires the recorded checker and native environment, including the
Python/solver identities and recorded solver metadata. It is a fresh-process
and fresh-checkout result on the qualified host, not a cross-platform result.
Keep the historical tool environment for existing completed projects; updating
checker/tool identities calls for separately qualified project history. An
externally supplied expected revision is needed for latest-head freshness.

The public summary is a curated record of the measured commands. Local paths
and raw internal logs are omitted. Its certificate and canonical bundle retain
their exact source/task/checker/approval bindings; local wall times cannot be
regenerated byte-for-byte. The original local qualification report digest is
included for provenance.

## Review boundaries and residual work

No full repository production gate, remote CI, full Lean project build,
physical power-loss test, hostile-OS isolation, general Python verification,
unbounded-history proof or Tau Net deployment ran for this tool release. The
SQLite locking/sync and protected owner-key premises remain explicit. Metadata
flags are observed inputs; their presence does not authenticate real reporters.
Tau is separately installed under its own license; no framework source or
binary is distributed and no patent/commercial-use clearance is claimed.

The largest code surfaces are the explicit migration transition/IR tables,
canonical approval codec, CLI argument registry and compatible prototype shell.
Their size is retained to keep each transition, encoding and failure result
reviewable in one place, with independent graph oracles and hostile lifecycle
checks. Qualification deliberately lists its scenario sequence rather than
adding another orchestration API. Further restructuring should preserve these
boundaries and be measured separately.

Development source changes caused a discarded shared-checkout test run to
report checker drift. The frozen isolated runs above replace that result.
One requested additional worker could not start because the harness thread
limit was reached; the task was reassigned to an existing agent. Available
Luna/Terra workers implemented bounded pieces and Astra performed architecture,
integration and critical review. No Fable or Opus result is claimed here.

The next candidate is [checked observation synthesis](implementation_lessons.md):
find omitted state/observation distinctions and certify a sufficient finite
projection. It remains a research proposal until it produces a replayed missed
omission or measured reduction beyond ordinary feature selection.
