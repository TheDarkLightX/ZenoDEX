# FCIS M5-P4B4 exact strong-validator implementation review

## Result

```text
M5_P4B4_COMPLETE_UNMOUNTED
```

P4B4 now provides an exact, immutable, bounded Python strong-settlement
specialization plus source-pinned direct differential evidence. It does not
change mounted authority and does not authorize P4B5, M6, or a production
switch.

Exact checkpoints:

```text
reviewed ancestor
  99da842b6606e6f10ce8ab6b2c94c2d36f2e169f

source implementation
  a9a8c73d281660032a10813ed53ef93ee48d7f0c

source hardening
  bb259f1a0d1f492aafa72692bd023d5207513f61

direct-parity artifact
  5c46d86dad71ade774362008a7f3242d6fee5a3f
```

Tool versions used for the final checkpoint:

```text
Python 3.12.3
pytest 7.4.4
Ruff 0.16.0
mypy 2.1.0
```

## Changed

The exact authority surface now contains:

- final, frozen, slotted exact context, pre-state, candidate, rejection,
  observation, and settlement-index values;
- deterministic settlement indexing with exact command/fill coverage,
  duplicate and wrong-variant rejection, canonical action order, and closed
  CoW pairing;
- an exact strong validator for ordinary swaps, exact-out swaps, routes, CoW,
  pool creation, liquidity addition/removal, proof-carrying reserve witnesses,
  recipient routing, fees, state replay, events, and patch derivation;
- exact committed-state leaf functions for curve configuration, pool identity,
  AMM dispatch, liquidity arithmetic, pool fingerprints, pool-creation events,
  and spot replay;
- source-owned work bounds for admitted collection sizes, canonical byte work,
  integer domains, route/fingerprint dimensions, patches, and events;
- structural checker coverage over all eleven new exact leaf and validator
  modules;
- a deterministic direct-parity builder, fail-closed semantic checker, and
  outer-hash-preserving mutation tests;
- a downstream blocker ledger that prevents P4B4 evidence from being mistaken
  for fee, replay, context, datastore, zUSD, or whole-system closure.

The exact validator composes the domain machines. It does not admit raw maps,
reconstruct legacy mutable state, or duplicate route parsing inside the
orchestrator.

## Invariant and authority impact

The public exact entry performs recursive admission before its first
committed-state read. Exact settlement indexing and command access reject
missing, extra, duplicated, and wrong-variant data through stable typed paths.
Accepted evaluation produces one exact successor and canonical patches from
the same sequential replay. Rejection produces no candidate or patch
authority.

Route handling follows this lineage:

```text
OwnedIntentV1
  -> derive RouteBindingV1
  -> pin exact committed pool fingerprints
  -> replay ordered route legs
  -> apply exact replay deltas
  -> compare direct result, patch, and read evidence
```

The P4B3 route preflight and replay functions preserve their canonical unique
read tuples directly. The P4B4 checker targets route-read re-normalization in
the exact route orchestrator while allowing the distinct generic spot read-set
type to form its protocol-defined canonical set.

During direct parity work, exact-out protocol-fee handling exposed a genuine
semantic divergence. The exact dispatcher had to share the mixed oracle’s
reserve domain, fee treatment, invariant checks, and overdelivery policy.
Those rules are now centralized in the exact AMM leaf and covered at both the
quote layer and the full validator result/patch/read-trace layer. This was a
code defect found by differential evidence, not an evidence exception.

Mounted files remain byte-identical to the reviewed ancestor. The legacy mixed
validator remains the differential oracle with its prior reachability. P4B4
has no mounted importer.

## Automatic NO-GO review

| Requirement | Result | Evidence |
| --- | --- | --- |
| Exact reviewed ancestor | PASS | `99da842b6606e6f10ce8ab6b2c94c2d36f2e169f` |
| Protected paths byte-identical | PASS | exact `git diff --exit-code` over every frozen path |
| Mounted authority unchanged | PASS | no protected runtime diff; final-mount count unchanged |
| Mixed validator unchanged | PASS | protected-file identity check |
| No legacy imports in new exact source | PASS | P4B4 structural checker |
| No open authority fields | PASS | exact value and AST mutation checks |
| No coercive admission/copy/freeze/seal/JSON/broad catch | PASS | all eleven source modules registered and clean |
| Recursive revalidation before reads | PASS | public-entry dataflow checker and focused mutation |
| Route binding rederived from command | PASS | direct route tests and P4B3 binding checker |
| Direct result/rejection/read parity | PASS | 18/18 source-pinned rows refine |
| Source-owned resource bounds | PASS | boundary and over-limit tests across exact leaves |
| Structural mutants killed by intended rule | PASS | checker mutation suite, including syntax-valid mechanism mutations |
| Four pre-mount profiles | PASS | zero violations in all four profiles |
| Final-mount exactly 64 | PASS | 64 inherited violations, zero P4B4 violations |

No automatic NO-GO remains for the scoped unmounted checkpoint.

## Architecture grade

| Area | Score | Evidence |
| --- | ---: | --- |
| Exact value closure | 5 | exact final/frozen/slotted values and recursive graph checks |
| Single admission and recursive revalidation | 5 | one exact public admission path before reads |
| Domain-machine composition | 4 | leaf ownership is explicit; several new modules remain large review surfaces |
| Rejection precedence | 5 | exact wrong-type, variant, index, replay, event, and patch negatives |
| Route command binding | 5 | binding rederived, pinned, ordered, and substitution-tested |
| Read-trace fidelity | 5 | direct tuple comparison; local scratch excluded from committed reads |
| Resource determinism | 5 | source-owned item, byte, integer, route, event, and patch limits |
| Differential completeness | 4 | all required semantic families covered; exhaustive state-space parity is not claimed |
| Mechanism-conformance checker | 5 | eleven-module coverage plus intended-rule mutation kills |
| Mount isolation and evidence honesty | 5 | protected identity, 64 inherited mount blockers, `mount_authorized=false` |

```text
total: 48 / 50
grade: A
```

The two deducted points preserve visible engineering debt: the validator and
some exact leaf modules exceed the preferred review size, and the direct
fixture portfolio is representative rather than exhaustive.

## Required code-reading attacks

1. **Public exact input to first read:** the public entry re-admits the
   settlement, intents, exact pre-state, and context before index derivation or
   state reads.
2. **Candidate lineage:** every candidate field is derived from the accepted
   sequential replay and the canonical patch builders; no shell-side or
   caller-supplied candidate field is accepted.
3. **Reject authority:** every rejection path returns an exact rejection and
   observation only, without successor or patches.
4. **Variant exhaustiveness:** intent and fill variants are source-owned and
   checker-bound; unknown or wrong-variant fields reject.
5. **Missing-field defaults:** exact authority access has no caller-selectable
   default and missing required fields reject.
6. **Comparison strength:** parity compares result kind, rejection reason,
   successor, patches, and read tuples directly; comparison does not sort,
   deduplicate, omit, or default either side.
7. **Scratch reads:** repeated route legs may read private scratch reserves;
   those reads do not become additional committed-state reads.
8. **Final replay equality:** the accepted sequential replay is checked against
   one final atomic exact spot application before candidate construction.
9. **Semantic mutation:** fabricated parity results are rehashed before
   checking; the independent semantic rebuild still rejects them.
10. **Private sinks:** candidate/rejection/observation constructors have exact
    importer allowlists checked structurally.

## Evidence

The source-pinned artifact is:

```text
docs/research/FCIS_M5_P4B4_DIRECT_PARITY_V1.json

implementation_source_sha
  bb259f1a0d1f492aafa72692bd023d5207513f61

source_manifest_sha256
  0x90535ffe001da0f73dd9f4b93921c0dd08721131abbd14f8e9ce3718fe200933

artifact_sha256
  0x649ad1ebb6feb02d50a88f070bece0c1abfca397e56cb263fb72172da61766dd

rows
  18 refine
  0 mismatch

verdict
  REFINES

mount_authorized
  false
```

The rows cover empty acceptance; exact-in/out; pool creation; add/remove
liquidity; ordinary, malformed-fill, delta, and event rejection; proof
witnesses; exact-in/out protocol fees; distinct recipient; exact-in/out route;
and symmetric/asymmetric CoW cases.

Final focused evidence:

```text
526 passed
369 checker and exact-leaf tests passed
4 parity checker/mutation tests passed
mypy: 20 source files, no issues
Ruff: clean
py_compile: clean
packet checker: 39 requirements, 103 declared tests, 103 bound tests, ok=true
state-substrate: ok=true
authority-graph: ok=true
exact-replay: ok=true
exact-consumers: ok=true
final-mount: ok=false with exactly 64 inherited violations
production-boundary audit: ok=true
security red flags: 11 files scanned, 0 findings
```

The style classifier had no path-specific rule for the external `/tmp`
worktree paths, so the stricter value-moving functional-core discipline was
applied manually. Design metrics identified large review surfaces but no new
authority mechanism violation.

## Commands not run

- Full repository pytest was not run.
- The final broad critical-quality gate was not run; the local broad-gate
  environment lacks `pytest_cov`.
- ESSO, Lean/mathlib, Tau, RISC0, formal solver, production datastore,
  crash-recovery, and external-delivery lanes were not converted into passes.
- Rust byte-level refinement was not implemented or claimed in P4B4.

## Residual risk

P4B4 is an exact Python validator specialization and differential checkpoint.
It does not establish that the unchanged mixed oracle is economically correct
outside the parity relation. It does not close per-asset fee units and custody,
nonce policy, evidence recomputation, publication-history continuity,
nullifier enforcement, authenticated context provenance, zUSD debt-cap
semantics, proof-wrapper closure, production compare-and-swap, crash recovery,
idempotent external delivery, or whole-system conservation.

The largest exact modules remain audit-intensive:

```text
fcis_settlement_strong_validator.py  1,757 LOC
fcis_spot_replay.py                    733 LOC
fcis_amm_dispatch.py                   447 LOC
fcis_settlement_index.py               423 LOC
```

Their semantic phases are separated into helpers and leaf modules, but future
work should continue reducing review surface when doing so preserves the
frozen rejection order and direct parity evidence.

## Next safest step

Begin a new reviewed P4B5 checkpoint from this exact unmounted evidence head.
Resolve the downstream safety fibers in the blocker ledger, starting with
per-asset fee units and protocol-owned custody. Do not mount the exact
validator until those fibers, authenticated context, replay enforcement,
datastore atomicity, crash/outbox behavior, and Python/Rust refinement have
their own passing promotion gates.
