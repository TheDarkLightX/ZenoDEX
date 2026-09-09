# ZenoLacuna design delivery review

**Result:** design packet completed; engine implementation and theorem proofs
remain planned. The design is a candidate contract for the stated finite scope.

## What exists

- A named product, formal contract, architecture, scope and evidence rules.
- An opaque-background logo PNG and its generation/refinement prompts.
- 32 BDD scenarios with stable machine-readable IDs, obligation links,
  independent oracle descriptions, and named semantic mutants. Every scenario
  remains **PLANNED**. Catalog validation is not acceptance-test execution.
- Risk-based implementation packets: Astra owns semantics and acceptance,
  Luna Max implements frozen interfaces and harnesses, Terra Max implements
  known adapters, and available Opus 5 or fresh Astra supplies independent review.
- Two executable finite illustrations with saved JSON reports.

## Independent review and corrections

The initial Astra high review found five concrete loopholes. The
[initial review](design_review_initial.md) is retained, including its original
subject hash. The revised README passed a bounded manual
[delta review](design_review_final.md) at SHA-256
`1ce63f3c5991d4c30569c34cba5299ed501929ae92173c2d3c590b5ac4837264`.

The corrections require quotient-congruent questions, infinity propagation
through unseparable DP children, preservation of each protected applicability
class, complete-trace nondeterminism, and explicit runtime correspondence.
The review did not execute the proposed engine or prove its theorem targets.

Integration review also corrected a contradictory DP acceptance fixture: a
fixed question language with an unseparable child cannot simultaneously provide
a complete finite policy for the same interpretation family. S27 now checks
unseparability; S31 separately checks an optimal two-question example.

A further authority review confirmed that a writable answer file or shared OS
user cannot establish human approval. The implementation packet now binds a
trusted authorization profile to scope, decisions, and revisions. S32 requires
rejection of simulation-receipt substitution and caller-driven profile downgrade.
The first milestone's simulated oracle makes no human-authorization claim.

The integrator strengthened the illustrative codec runner to execute the exact
allowlisted source bytes it hashes and to preserve the reserved sentinel in
both alternative functions. The runner is an explicit known-source example,
not a sandbox or the future checker for arbitrary agent programs.

## Executed finite evidence

[Codec report](examples/codec_gap_report.json): all 128 metadata words round-trip
in the original and deliberately altered pair. Both mixed-version pairings
misdecode all 128. All 128 reserved byte inputs return the sentinel through
each of the four individual functions. The report records the two actual
repository kernel hashes and the example runner hash. These are component
metadata words, not a claim that all 128 profiles pass the observation guard.

[Design counterexamples](examples/design_counterexamples.json): five small
enumerated examples exhibit the reviewed loopholes and their required guards.
The report explicitly says that the engine is unimplemented and the theorem
targets are not machine checked. It validates the illustrative examples only.

Run from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 docs/research/zenolacuna_design_20260908/examples/codec_gap.py
PYTHONDONTWRITEBYTECODE=1 python3 docs/research/zenolacuna_design_20260908/examples/design_counterexamples.py
python3 -m ruff check docs/research/zenolacuna_design_20260908/examples
python3 -m mypy --follow-imports=skip docs/research/zenolacuna_design_20260908/examples
PYTHONDONTWRITEBYTECODE=1 python3 tools/check_claims_registry.py
PYTHONDONTWRITEBYTECODE=1 python3 -m ESSO guide --help
```

The two examples passed their explicit finite checks. Ruff and scoped mypy
passed. The existing claims-registry structural check returned `ok`; it does
not endorse this proposed tool. ESSO's installed guide command is available;
no new ESSO model has been checked in this delivery.

To regenerate the codec report, parse its stdout JSON and save it with sorted
keys, indentation 2, and a trailing newline. The design-counterexample report
is the runner's stdout verbatim. Reports are derived from their recorded source
bytes. Compare semantic JSON and hashes when independently replaying.

## Limits and next action

No ZenoLacuna engine acceptance suite, native Tau query campaign, ESSO model
verification, Lean build, TLA run, full repository suite, release gate, or
production deployment was performed. No performance, novelty, completeness
outside the frozen domain, or legal-clearance claim is made. The chosen logo
is a generated RGB raster asset; a vector master is not included.

The next implementation is Packet A: Astra defines and implements the finite
semantic core against independent applicability, projection, and witness
oracles. Packet B follows. Luna begins bounded interface implementation after
those contracts are frozen. Protected user workflows and model scope remain
explicit inputs to the future tool.
