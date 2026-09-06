# Bounded Tau economic predicates and conservation elision

Base: `321f122234d1b665d12999289bb133bddce5a0d8`. This continues the V3
Tau/ADT work with actual existing economic predicates. It does not complete
the formal core, authenticate ownership or grant publication authority.
Production Tau sources and their wire contracts are unchanged.

## Qualified behavior

The explicit research CLI in `experiments/tau_economic_qualification_v1/qualify.py`
ran the existing nonce replay, nonce manager, transfer hook and zUSD transfer
guards on measured Tau executable SHA-256
`c061c870b47fa1a6089dac59285e8473b7b789dc600157704007f2d67fd90950`.
The reported version remains `0.7.0-alpha (1c1e58ae)`; source-to-binary
reproducibility is unqualified.

The independent reference contains 43 manually listed witnesses and all 64
binary zUSD input assignments. Every output field was compared, including
standalone outputs whose meaning differs from final admission. Three
three-step nonce histories use caller-maintained state and update that state
only after the observed Tau output accepts. The candidate transfer program
also passed the 11 transfer vectors. These are 118 corpus row evaluations and
nine history rows, apart from timing samples.

The retained cases distinguish:

- nonce expected-value wrap from freshness, and gaps 999, 1000 and 1001;
- acceptance of the maximum nonce followed by exhaustion;
- conserved totals with incorrect transfer deltas;
- modular sender/receiver wrap where the standalone delta predicate can hold
  while the direction predicate and final admission reject;
- zero transfer, maximum amounts, unsigned comparison seams and aggregate
  totals exceeding the width while the individual transfer remains valid;
- every combination of the binary zUSD structural and policy inputs.

Repeating a successful nonce row with stale caller-supplied state produces
acceptance again. This is the specified pointwise predicate behavior. A
ledger must authenticate the predecessor and persist nonce consumption.
Likewise, supplied balance and authorization flags do not establish their
truth. None of these guards supplies an authenticated owner identity.

## Mathematical optimization

`conservation_equivalence.py` checks a manually translated QF_BV32 relation.
Writing the balances as `sb, sa, rb, ra` and the amount as `a`:

```text
sb - sa = a and ra - rb = a  =>  sb + rb = sa + ra  (mod 2^32)
```

Z3 4.15.4 returned UNSAT for a counterexample to this implication and for any
difference across the original and proposed four output predicates. Positive
and independent direction/delta controls returned SAT. UNKNOWN, source drift
and failed controls reject. This trusts Z3 and the reviewed manual translation.

The candidate removes precisely two redundant conservation conjuncts from
the pinned transfer source, preserving all direction, delta and hook checks
and every output biconditional. Its source SHA-256 is
`481d48a947e0dd18d7fb881eb95332863c3738168960ed0b012006b2a552590d`.
Predicate equivalence preserves the complete allowed algebra-valued output
relation, since the original `output = top iff predicate` clauses remain.
Actual engine traces cover only binary inputs/outputs and the declared corpus.

Each timing run used two checked warmups and five alternating pairs, with a
fresh engine process per invocation and the same eight-row transfer batch.

| Run | Original median | Candidate median | Lower median |
| --- | ---: | ---: | ---: |
| Initial subject | 359.0 ms | 304.8 ms | 15.1% |
| Final wording correction | 408.8 ms | 323.3 ms | 20.9% |

Both subjects execute identical economic formulas and vectors; the final
source corrects a reference docstring. The first run misses the declared 20%
threshold and the second clears it. Host load was uncontrolled; these short
runs do not establish a repeatable 20% improvement, cross-machine speed or
peak-memory bounds. The candidate is retained for broader measurement and is
not adopted into production. No preparation cache or persistent interpreter
reuse was introduced.

## Execution and evidence integrity

The existing measured-ELF copier supplies a sealed executable snapshot. Each
input stream receives a separate sealed memfd. A preliminary probe that
opened `/dev/stdin` separately for several inputs emitted no outputs despite
exit zero; the complete-output gate rejects that result. Raw IO remains
bounded by the existing 12-second invocation deadline and output ceilings.

The runner requires exact stream declarations, every output in declared order,
empty stderr and normal exit. Blank LF lines are ignored; CR, non-ASCII,
missing/extra rows and diagnostic lines reject. Raw transcript hashes retain
timing and whitespace. A final gate value cannot hide a wrong standalone
output. There are no timeout retries or negative proof claims from missing
results; flag-search exhaustion is disabled explicitly.

The CLI first atomically installs `INCOMPLETE` at its caller-owned report path,
then atomically replaces it with the result. Initial invalidation failure
prevents execution and explicitly reports uncertain preexisting output. Final
write failure leaves the incomplete marker. This assumes one report writer;
it establishes neither durable publication nor report authenticity.

The final execution receipt has SHA-256
`1537320b669d972d49cfcfc8f4cb18b71b835cd31d917851e23f62c3c01464ad`;
the earlier receipt is
`d1b3c5eca6c6ab80eae6200d21888f9909f1198e27300119c11d8155b03175d1`.
All 138 final repository source bindings matched an independent post-run read.
The reports bind exact executed programs and per-stream input/output hashes.
File-descriptor numbers and timings make fresh transcript/report hashes vary.
Loaded Python/solver code, the OS, loader and libraries remain trusted; disk
hashes are not executed-process attestation.

## Review and replay

Terra implemented the independent reference. Astra reviewed the arithmetic and
proved the candidate relation; parent implemented and reviewed the execution
and comparison layer. Daybreak independently reviewed the four execution/math
source files and four tests. Parent repaired report invalidation, bounded the
standalone proof reader, checked the proved/executed candidate hash, and
corrected whitespace and generated-vector wording. No findings remain within
that reviewed scope. The small hygiene renderer received parent review only.

```bash
python3 -B -m experiments.tau_economic_qualification_v1.conservation_equivalence
python3 -B -m experiments.tau_economic_qualification_v1.qualify \
  --tau-binary "$TAU_BINARY" --output "$TAU_REPORT" --repeats 5
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/tau/test_tau_economic_reference_v1.py \
  tests/tau/test_tau_economic_runner_v1.py \
  tests/tau/test_tau_economic_qualification_v1.py \
  tests/tau/test_tau_transfer_conservation_equivalence_v1.py \
  tests/tau/test_tau_adt_execution_v1.py \
  tests/tau/test_tau_adt_qualification_v1.py \
  tests/tau/test_tau_adt_row_codec_v1.py
python3 -B -m experiments.tau_economic_qualification_v1.render_evidence
python3 -m mypy --explicit-package-bases --follow-imports=silent \
  --cache-dir=/dev/null experiments/tau_economic_qualification_v1
```

The combined test command passed 108 cases: 52 new and 56 retained ADT checks.
Ruff and scoped mypy passed. The source-pinned hygiene packet covers all four
new test paths. `python3 tools/check_production_boundary.py --json` passed its
14 existing checks while retaining `release_ready=false`, unmounted M6 and
`BLOCKED_OPEN_COVERAGE`. Test execution alone does not invoke the measured Tau CLI.
Local sealed execution required the authorized sandbox escalation.

No full Lean/Mathlib, Rust/RISC0, Kani, remote proof build or production
promotion was run. Remaining priorities are authenticated ownership/state
binding, universal runtime refinement and complete publication mediation;
Tau-specific work includes reproducible engine builds, internally stateful
policy qualification and broader controlled performance measurements.
