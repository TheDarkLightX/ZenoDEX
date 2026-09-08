# Tau artifact workbench: compatible code choices for a developer and swarm

Date: 2026-09-08 UTC. Implemented and locally tested research. Authority: NONE.
This third cycle connects the earlier Tau Swarm compiler to actual Python
source artifacts. Its fixed pilot checks 512 assembled programs, admits six
agent-written replacements, and independently executes all eight combinations
of those replacements. It also measures a 6.46x native compilation improvement
from an equivalent, smaller Boolean representation.

The [final replay](tau_workbench_20260908/replay/report.json),
[validation](tau_workbench_20260908/validation.json),
[integration review](tau_workbench_20260908/integration_review.md), and
[experiment contract](tau_workbench_plan_20260908.md) define the evidence scope.
The program is an original finite artifact workbench. ZenoDEX integration and
Tau Net rule admission remain future work.

## Developer-and-swarm use cases

Alice maintains a message encoder, tag adapter and decoder with three agent
teams. She requires every six-bit payload to survive the assembled pipeline.
Different teams prefer different source implementations and tag versions. Tau
computes a compatible set of behavior choices for each team; exact source
checking connects those choices to the files the agents propose.

| User story | Executable outcome | Rejection and recovery |
|---|---|---|
| Alice and her swarm want to change encoder tags while other teams work independently. | Encoder-first compilation admits eight encoder sources, eight adapters and two tolerant decoders. Every one of the 128 combinations passes actual CPython replay. | An unadmitted decoder is rejected as a local choice. Alice can select another valid anchor or recompile with a different expansion order. |
| Ben and his decoder agents need to retain legacy and version-specific behavior. | Decoder-first gives eight decoder sources and eight adapters while restricting the encoder to two raw-payload implementations. It also permits 128 combinations. | A tagged encoder requires renegotiation; both teams' individually feasible preferences cannot simply be combined. |
| Cara and her coding agents want to rewrite an admitted implementation without repeating Tau compilation. | The checker evaluates all 256 component inputs and recognizes an admitted behavior class. Six newly written source variants pass; their eight assembled combinations are checked against Alice's original table and replayed in CPython. | A new or unadmitted behavior returns `renegotiation_required`. This status does not initiate an automatic change or deployment. |
| Dinesh and his review swarm need to catch a decoder that passes ordinary payload examples. | The supplied negative control agrees on inputs 0 through 63 but leaks a tag bit on reachable intermediate inputs. It fails in 24 of 64 checked contexts. | The first saved counterexample is input 0, expected 0, observed 64. The developer can correct the source or explicitly revise the shared task. |
| Eva and her planning agents want more independent implementation choices. | A bounded exhaustive oracle finds a different valid anchor. Tau then returns 192 compatible source combinations, the largest product in this fixed pilot. | The result concerns this finite relation. General maximum-product synthesis is not implemented. |

These workflows preserve human responsibility for the expected behavior. A
correctly implemented incomplete human specification remains incomplete. The
candidate-authoring agent was deliberately asked for a negative control, so the
six accepted and one rejected proposals do not measure a natural LLM error rate.
Human time, reviewer corrections and developer productivity were not measured.

## Normative semantics

Let `D = {0, ..., 2^bits - 1}` be the complete component domain. Each admitted
source defines a total function from `D` to `D`. Initial inputs `I` are an
explicit nonempty subset of `D`, with a human-supplied expected output `E(x)`.

```text
p equivalent-to q  iff  for every x in D, p(x) = q(x)
C(c1, ..., cn)     iff  for every x in I, (cn o ... o c1)(x) = E(x)

Di := {ci | for every c_-i in the currently admitted other domains, C(c)}
Li := all exact source artifacts whose behavior class belongs to Di

For every p1 in L1, ..., pn in Ln and every x in I:
    (pn o ... o p1)(x) = E(x)
```

Expansion uses the existing sequential universal-cofactor Tau compiler. Later
updates use the domains already expanded earlier in the sweep. Native checks
cover projected equivalence, product safety, anchor membership and the final
exact cofactors. A separate finite class relation checks the returned domains.
Unassigned binary selector patterns are outside the global relation.

Source identity includes exact bytes. Task identity includes ordered stages,
program names and hashes, complete-domain width, initial inputs, expected
outputs, anchor and profile version. Expansion order belongs to the compiled
envelope. All observations and compiled objects are advisory data; their public
constructors cannot issue credentials. Final selection and revision checks
reanalyze source bytes and recheck the original joint behavior.

The [Lean proof](../../lean-mathlib/Proofs/TauArtifactQuotient.lean) establishes
closed-domain pipeline substitution, safety of lifting class products, transfer
of factorwise maximality given representatives, and anchor non-vacuity. It also
formalizes the failure of initial-input-only equivalence. Class correspondence
is an explicit premise. The proof does not verify the interpreter, CPython,
source hashes, Tau binary, or a ZenoDEX runtime refinement.

## Supported source and data profile

- One ordinary function: `def transform(x): return <expression>`.
- Exact integers, arithmetic, bitwise operators, single comparisons and
  conditional expressions. Conditions have Boolean type; output has integer
  type. Division follows Python integer floor/modulo semantics.
- One to eight domain bits, one to four stages, at most 32 sources per stage,
  4,096 artifact combinations and 256 behavior-class combinations.
- At most 8,192 bytes per source, 256 AST nodes, depth 32, integer literal
  magnitude 65,535 and literal shifts from zero through eight.
- Exact UTF-8 source interpretation. Imports, calls, state, loops, attributes,
  defaults, decorators, annotations, general statements and unsupported syntax
  are rejected. The complete tree, including dead branches, must fit the profile.
- Every component is interpreted for every input in `D`; Boolean, out-of-range
  and undefined outputs reject. Task JSON has closed fields and duplicate-key,
  depth, exact-type and byte limits.

The interpreter builds a small immutable expression representation and never
uses `eval`, `exec`, or `compile` on candidate source. The separate replay shell
loads only admitted bytes into CPython, executes full component tables and
assembled bundles, and compares observed values to the human table. Host
composition independently checks the reported first failure and checked-input
count. This is a restricted executable profile, with no general Python sandbox
claim. Timeouts, malformed native results, unsupported queries and expression
limits cannot produce a passing report.

## Measured comparison

The pilot contains 24 original source artifacts, four behavior classes per
stage and two source variants per class. CPython checked all 512 bundles and
agreed with the source interpreter's classification for every bundle.

| Method | Behavior bundles | Source bundles | Meaning |
|---|---:|---:|---|
| Cached centralized checking | 49 accepted of 64 distinct behaviors | 392 accepted of 512 | Complete feasible set; choices require coordination |
| Centralized checking after exact grouping | 64 class checks | Same 392 accepted | Eightfold reduction in checks comes from grouping |
| Tau, encoder-first | 16 | 128 | Every independent combination is compatible |
| Tau, decoder-first | 16 | 128 | Different allocation of agent freedom |
| Tau, oracle-selected valid anchor | 24 | 192 | Largest product in this fixed pilot |

The maximum-product oracle checks all `15^3 = 3,375` nonempty subset products
for the three four-class stages. The winning factors are encoder classes
`{0,1,2,3}`, adapter classes `{1,2,3}`, and decoder classes `{1,2}`. The anchor
names `raw_mask`, `strip_mask`, and `v1_lt`. This is a 50% increase over the
default product; it still covers fewer combinations than the complete relation.

The source-analysis pass performs 6,144 evaluations and took 11.47 ms locally.
Cached artifact checking then took 3.98 ms; grouping plus class checking took
0.63 ms. The three full workbench/Tau compilations took approximately
1.86, 1.94 and 2.04 seconds. Centralized checking is substantially cheaper in
this small one-off workload. Tau supplies compatible choices in advance; this
experiment does not establish a productivity or cost break-even point.

Exact source replacements require 256 local evaluations and zero new native
Tau queries. The centralized quotient baseline can reuse equivalent sources
too. The replay additionally executes all admitted contexts of each proposed
replacement and all eight assembled positive revisions. These extra checks
validate the experiment; they are not counted as a hidden cost saving.

### Boolean representation experiment

Classical Shannon factoring reduces the rendered contract residual from
**4,080 to 541 bytes**, a **7.54x** reduction. Enumeration and factoring agree on
all 64 selector rows and return identical native domains. Two paired runs,
alternating execution order, measured median native compiler times of
**13.089 seconds and 2.025 seconds**, respectively: **6.46x** in this workload.
Each compilation made twelve native queries. This timing excludes source
analysis and relation construction; the report retains every run.

The final replay contains 113 native query/execution records, including 36
local gate trace rows. Measurements were local, without a dedicated machine or
cross-machine replication. They establish an improvement over this enumerated
representation, not superiority over ordinary Boolean code or Tau itself.

## Software and replay

The [package](../../src/tau_workbench/) separates source admission, immutable task
data, exact behavior grouping, Tau compilation and native execution. The
[CLI](../../tools/tau_workbench.py) supports parser-derived machine discovery,
closed task JSON, compilation, exact candidate source exports and local Tau
gate files. CLI compilation interprets source and runs Tau; it does not load
the candidate Python files. The [benchmark](../../tools/benchmark_tau_workbench.py)
performs the separate CPython experiment.

Run from the repository root with `TAU_COMPOSITION_BIN` explicitly set to a
separately installed executable. Each output directory must be new.

```bash
python3 tools/tau_workbench.py describe
python3 tools/tau_workbench.py example > /tmp/workbench-task.json
python3 tools/tau_workbench.py compile --task /tmp/workbench-task.json \
  --tau "$TAU_COMPOSITION_BIN" --out /tmp/workbench-compiled
python3 tools/benchmark_tau_workbench.py --tau "$TAU_COMPOSITION_BIN" \
  --candidates docs/research/tau_workbench_20260908/agent_candidates.json \
  --out /tmp/workbench-replay --pairs 2
```

Saved [CLI artifacts](tau_workbench_20260908/compiled/report.json) include actual
source files and Tau gates. The [replay directory](tau_workbench_20260908/replay/)
contains original and revision tasks, ordered bundle lists, source-bound
CPython observations, original candidate bytes and native query records.
The 49-file source manifest includes the experiment contract and all six new
test files. Source or binary drift fails the replay. Reports are written after
their dependencies; they remain unsigned local observations.

The separately installed Tau executable reports `0.7.0-alpha (d80aa50c)`, with
SHA-256 `b62c0706f682d305fce461750d2332a473ce1fb0e6e7f45b2bb46e5174d07326`.
Source-to-binary correspondence remains unestablished. Parent validation checks
the fifth Lean file with Lean 4.27.0. See the validation record for exact test
commands, results and deliberately unrun release gates.

## Prior art, provenance and next research

[Bryant's Boolean-function paper](https://www.cs.cmu.edu/~wklieber/15817-f08/ieeetc86.pdf)
describes Shannon decomposition and ordered decision diagrams. This application
uses established decomposition with exhaustive parity; it does not implement a
new Boolean decision procedure. [Oracle-guided component synthesis](https://www.csl.sri.com/users/tiwari/papers/icse2010.pdf)
is prior art for composing loop-free components against input/output behavior.
[SafeMerge](https://arxiv.org/abs/1802.06551) addresses semantic conflict freedom
in program merges. Our finite pipeline profile does not reproduce its broader
merge capabilities. The previous cycle records the direct prior art for
maximal products and one-sweep expansion.

Original application source and generated Tau specifications remain separate
from Tau implementation code. No Tau source, binary or new dependency is
vendored. The [previous license-boundary study](tau_composition_20260907.md#tau-net-and-license-boundary)
remains the provenance reference. This research does not establish commercial
permission, patent freedom to operate or Tau Net admission.

An Opus 5 Max candidate-author request was attempted with a 2,062-byte public
task packet and zero repository source files. It timed out without usable code.
A Codex agent supplied the seven candidate artifacts; Luna Max implemented the
profile and CLI, with separate parent integration and critical review. See
[delegations](tau_workbench_20260908/delegations.json). Provider output supplies
proposals; local checkers supply acceptance evidence.

The next ranked opportunity is a real finite ZenoDEX adapter migration with
source-pinned producer and consumer behavior. Measure accepted edits and actual
rework against cached centralized checking before claiming practical lift.
[Lessons and the next target ladder](tau_workbench_lessons_20260908.md) preserve
the representation result, intermediate-domain counterexample, anchor tradeoff,
and the remaining refinement and deployment boundaries.
