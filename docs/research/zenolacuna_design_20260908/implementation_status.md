# ZenoLacuna implementation checkpoint

Historical checkpoint. The completed signed first release is recorded in
[release_evidence.md](release_evidence.md) and [release_coverage.md](release_coverage.md).
The assessment below describes the earlier prototype.

Date: 2026-09-08. Status: **implemented and tested finite research prototype**.
The full planned product acceptance remains incomplete. The latest coverage
inventory has 14 `TESTED`, 16 `PARTIAL`, and 2 `UNMOUNTED` scenarios; these are
scenario statuses, not a weighted progress percentage.

The [usage guide](../../../src/zenolacuna/README.md) describes the actual library,
CLI and demo. The [coverage inventory](implementation_coverage.md) records the
remaining workflow and evidence gaps. The
[lessons and next research candidate](implementation_lessons.md) preserve what
the implementation and review taught us.

## Changed and checked

- Immutable finite scope, protected requirements, complete-observation quotient,
  disagreement witnesses, exact filtering and bounded minimax questions.
- Independent finite closure checks, strict canonical JSON, append-only local
  revisions, explicit cancellation/resume, exact retry semantics, and source
  and checker revalidation before publication or runtime-result return.
- Restricted integer-program replay, including a read-only mode bound to the
  assessed candidate and recorded answers at an exact persisted revision.
- Data-only swarm packets; fixed real V1/V2 signal fixture parity; actual codec
  mutation experiments; a separately checked finite queue model; Tau and ESSO
  adapters; twelve abstract Lean filtering/identifiability theorems.
- A fresh-artifact demo, logo and design handoff, independent tree oracle,
  hostile boundary tests and documented implementation coverage.

Independent review found and the implementation repaired an observation-binding
bug: an integer return could previously inherit a caller-supplied rejection
label. It now rejects that unsupported encoding. Review also closed the gap
between recorded answers and the program replay command, preserved exact
empty-family diagnostics, and exposed malformed nested journal JSON that now
rejects deterministically.

## Frozen integration evidence

The new files were copied into an isolated checkout based on published Tau
migration commit `4b683914a8328044c57a3fc72fb81771f6ed9247`. Existing integration
and kernel files in that checkout were retained from that commit. The shared
checkout and its unrelated work were preserved.

| Check | Result |
| --- | --- |
| Ruff on the new package, both CLIs and focused tests | Passed. |
| mypy with `--follow-imports=skip` on those same paths | 31 source files passed. |
| `TAU_BIN=... python3 -m pytest -q tests/test_zenolacuna*.py` in the isolated checkout | 142 passed in 7.09 seconds. |
| Independent shell/program/port/demo review | 57 passed, one optional native Tau test skipped; reviewed hashes stable before/after. |
| Fresh CLI compatibility lifecycle | Analyze, bound simulated answer, identical retry, assessed repair, model replay and fresh status reconstruction passed. |
| Fresh full-byte CLI replay | Both stateless and exact-revision modes checked the unchanged encoder/decoder over all 256 inputs; their runtime claims matched. |
| Native Tau | Three finite relation comparisons passed; queue precondition projected and checked. |
| Native ESSO with Z3 and CVC5 | Unsafe model produced counterexamples; guarded model passed all nine agreed queries. |
| Focused Lean source check | Exit 0; twelve theorems, standard Lean axioms only. See [proof notes](proof_notes.md). |
| Security red-flag scan | 20 Python files scanned, zero findings; this is supplementary evidence. |

The first isolated native demo correctly failed with `ESSO_REPLAY_INCONCLUSIVE`
because that clean checkout did not contain the local ESSO module loader. A
fresh run with the separately installed ESSO source directory explicitly on
`PYTHONPATH` passed. The earlier failed directory has no completion summary.
No dependency was downloaded or silently replaced to obtain that result.

The Lean check reused the existing pinned local dependency artifacts. Its
recorded `lake-manifest.json` is local validation state and is not present in
the published base checkout. The Lean source and `lean-toolchain` bytes match
the isolated candidate; a clean dependency-resolution/build replay was not run.

The semantic test oracle enumerates complete decision trees for 368 small
question families. Six targeted process-local semantic mutants were killed by
assertion failures. This is bounded mutation evidence, not an exhaustive claim
about every possible implementation defect.

## Measured example

The final fresh native demo produced these single-host measurements. Discovery
constructs and checks the declared codec mutation family; finite analysis uses
11 repetitions. Each native comparison below was run once and includes formula
construction, process startup and independent finite replay. Each ordinary
comparison is the median of 11 direct Python set comparisons on the same
relations. There is no cross-host or statistical performance claim.

| Quantity | Result |
| --- | --- |
| Codec discovery | 206,645,036 ns. |
| Finite analysis median | 1,015,014 ns. |
| Candidate interpretations / semantic classes | 8 / 2. |
| Worst-case compatibility question cost | 1; a suitable fixed question also costs 1. |
| Original vs original: Python / Tau plus replay | 3,130 / 106,113,771 ns. |
| Original vs XOR-1: Python / Tau plus replay | 1,850 / 117,064,570 ns. |
| XOR-1 vs XOR-2: Python / Tau plus replay | 5,740 / 126,608,484 ns. |
| Unsafe queue graph | 12 states, 96 transitions, 26 invariant violations and 4 misdecode edges. |
| Guarded queue graph | 8 states, 64 transitions, no invariant violations or misdecode edges. |

All seven nonzero paired codec mutants retain 128 valid self round trips and
128 reserved sentinel returns, yet both mixed-version pairings misdecode all
128 valid words. This is a concrete specification-omission example. The tiny
relation benchmark favors ordinary Python; no Tau speedup or foundational
algorithmic novelty is established.

## Replay commands

From the repository root, the commands for the focused checks are:

```bash
python3 -m ruff check src/zenolacuna tools/zenolacuna.py tools/zenolacuna_demo.py \
  tests/test_zenolacuna*.py tests/zenolacuna_oracle.py
python3 -m mypy --follow-imports=skip src/zenolacuna tools/zenolacuna.py \
  tools/zenolacuna_demo.py tests/test_zenolacuna*.py tests/zenolacuna_oracle.py
python3 -m pytest -q tests/test_zenolacuna*.py
python3 tools/zenolacuna_demo.py --out /tmp/zenolacuna-new-demo \
  --tau-bin "$TAU_BIN" --esso
```

`TAU_BIN` selects a separately installed executable. The ESSO command requires
`python3 -m ESSO` to resolve in the selected environment; for a source checkout,
put its package parent directory on `PYTHONPATH` explicitly. Every demo output
directory must be fresh. The demo records implementation and tool identities;
timing fields are measurements and are not expected to reproduce byte for byte.

## Authority, residuals and publication

All report authority is `NONE`. `SIMULATED` decisions are test inputs.
`REAL_OWNER` remains unavailable until a trusted approval port is implemented.
Model closure covers supplied finite semantics; restricted-program closure
covers the declared integer interpreter. Neither proves complete human intent,
arbitrary Python, a production migration service, or Tau Net deployment.

No full repository production gate, full Tau/TLA claim suite, full Lean build,
Rust/RISC0 suite, hostile-OS filesystem race campaign, or clean-host dependency
installation was run. Existing value-moving runtime paths were not modified by
this implementation. The particular queue model has its own finite graph and
codec premise; it is not a mounted real queue service or a liveness theorem.

The full design's owner authorization, scope evolution, additional recovery
histories and broader runtime-certificate lifecycle remain open in the coverage
inventory. Work is saved; this checkpoint does not mark the whole plan complete
or publish an unfinished product. A publication checkout is prepared, but no
ZenoLacuna commit or push has been made. The user's condition to commit only
finished successful work remains in force.

The next implementation step is to choose the next bounded acceptance slice
from the remaining coverage obligations and close it with negative evidence
and independent replay. The next research opportunity is checked synthesis of
missing observations, detailed in the lessons note.
