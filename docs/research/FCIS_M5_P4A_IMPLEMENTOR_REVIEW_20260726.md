# FCIS M5-P4A Implementor Review

## Review identity

- Implementor branch: `agent/fcis-m5-p4a-readiness-20260726`
- Reviewed implementor SHA: `e83b3c8c7e5d783dcd43868f90de99b5bfb601bb`
- Reviewed start SHA: `c344bac741c1d4a15511b77f8e2b60f93260a449`
- Original result: automatic `NO-GO`
- Corrected result: `M5_P4A_BLOCKED_NO_AUTHORITY_SWITCH`

The implementor correctly stopped before changing mounted authority. The
original evidence packet could not support its readiness claims. Passing its
checker only proved that several JSON files existed and contained the numbers
the checker expected.

## Original automatic no-go findings

### 1. The command inventory was hand-maintained

The original inventory duplicated the mounted command list in the evidence
tool. A newly added `IntentKind` could therefore remain absent while the packet
continued to pass.

Required closure:

```text
IntentKind source enum
  + mounted dispatch references
  -> source-derived closed command inventory
```

### 2. The frozen baseline was not an input to replay

The differential tool rebuilt live fixtures and never consumed the stored
baseline. Baseline substitution, staleness, or provenance drift could not
affect the result.

### 3. Same-input evaluation was not established

Legacy execution ran first over live Python references. The exact path then
received those references without proving that command, state, or context
remained unchanged. The original baseline also recorded some pre-state data
after legacy execution.

### 4. The comparator omitted authoritative outputs

The original comparator checked accept/reject Boolean equality and a subset of
state. It omitted rejection identity and precedence, nonces, fee accumulator,
effects, ordering, fees, dust, replay updates, receipt, outbox, patch, commit
bundle, and version bindings.

Two minimized counterexamples were incorrectly classified as matches:

```text
legacy rejection AUTH  vs exact rejection ARITH -> MATCH
legacy effects A       vs exact effects B       -> MATCH
```

### 5. Divergences did not fail promotion

The original report contained 12 divergences, yet its check mode exited zero
without a separate promotion gate. The divergence categories were free-form
labels rather than a reviewed, code-owned refinement relation.

### 6. The mount ledger overstated its graph evidence

It used a hand-maintained path list and import edges as a call graph. It did not
map every checker violation to an entrypoint, authority type, role, disposition,
owner, and verification obligation.

### 7. Cross-language readiness was inferred from file presence

The original matrix treated implementation-source existence as readiness.
Source presence does not prove byte-level Python/Rust/Tau/proof/verifier
equivalence.

### 8. The checker did not check its central claims

It accepted duplicate JSON keys, unknown fields and statuses, stale generated
content, omitted violation rows, and an empty runtime-mutation result after a
broad exception. `git diff HEAD` also missed committed changes between the
reviewed start and the implementor head.

## Corrective work

The reviewer repair now provides:

1. An AST-derived `IntentKind` inventory with mounted-dispatch evidence.
2. Twenty-four legacy fixtures, including accept and reject coverage for every
   mounted command kind.
3. Command, state, and execution-context bytes captured before execution, with
   mutation rejection and same-input binding on both replay sides.
4. A differential evaluator that consumes and byte-checks the frozen baseline,
   independently reconstructs both input graphs, calls the FCIS decision and
   commit-bundle derivation, and compares every declared observable.
5. Structural rejection atomicity checks. A rejection may carry its canonical
   rejection receipt; it carries no successor, patch, commit plan, effects,
   replay update, outbox plan, or commit bundle.
6. A checker-derived mount ledger mapping all 79 final-mount violations exactly
   once. Static imports and call syntax are explicitly labeled incomplete.
7. A closed cross-consumer matrix covering Python FCIS, Rust runtime, Tau
   adapter, proof guest, and settlement verifier for every command and
   final-mount profile surface.
8. A strict canonical-JSON checker that regenerates every artifact, checks
   source and artifact hashes, rejects undeclared artifacts, compares the full
   reviewed-start delta, and separates packet validity from mount readiness.
9. Eighteen named evidence mutants plus per-observable comparator mutations.

## Current factual result

The corrected packet is structurally valid and remains blocked:

```text
FINAL_MOUNT_STRUCTURAL_VIOLATIONS = 79
DIFFERENTIAL_PARITY_OPEN          = 24
CROSS_CONSUMER_EXACT_BYTES_MISSING = 405 rows
```

All 24 fixtures currently agree on the result kind. They diverge first at the
versioned algorithm identifier. Further differences include legacy-unavailable
patch, receipt, replay, outbox, and bundle values, plus versioned snapshot and
support-root representations. These cannot be relabeled as parity. They require
an explicit, reviewed legacy-to-FCIS refinement relation.

## Grade

### Original implementor checkpoint: 29/100, F

| Review area | Score |
| --- | ---: |
| Frozen-design fidelity | 8/20 |
| Inventory and provenance | 3/15 |
| Legacy golden baseline | 8/15 |
| Differential completeness | 2/20 |
| Mounted graph completeness | 4/15 |
| Cross-language honesty | 3/5 |
| Checker and mutation evidence | 1/10 |

The no-authority-switch decision and useful fixture scaffold receive credit.
The evidence mechanisms did not establish the claims they reported.

### Corrected evidence checkpoint: 94/100, A

The corrected checkpoint earns a high evidence-honesty grade while its mount
verdict remains blocked. Remaining deductions reflect the intentionally
incomplete runtime reachability proof and absence of promoted cross-consumer
replay.

## Evidence executed

```text
47 passed
  strict packet validation
  18 named evidence mutants
  one comparator mutation for each declared observable

201 passed, 4 skipped
  P4A tests
  FCIS evaluator and authority admission
  support-root v5
  decision and commit-bundle derivation
  reference commit semantics
  shadow replay
  execution-context admission
  ESSO-derived result atomicity tests

Ruff: clean
mypy: clean
production boundary: ok=true
security red flags: 0 findings
permissionless assurance: critical lane ready; formal/release lanes unavailable
```

The broad critical gate did not run because the worktree environment lacks
`pytest_cov`. No dependency was installed during review.

## Promotion boundary

This checkpoint does not authorize:

- changes to `src/core/dex.py` mounted authority;
- treating the legacy and FCIS byte representations as equal;
- Python/Rust/Tau/proof/verifier parity claims;
- production datastore linearizability or crash-recovery claims;
- P4B authority switch, P5 promotion, or M6 legacy deletion.

## Next authorized checkpoint

The next bounded implementation task is a legacy-to-FCIS refinement contract.
It must define code-owned, versioned projections for shared semantics and
separate exact-only output obligations. It may classify a fixture as refining
only when the relation is replayable and input-independent. It must preserve
all true mismatches as blockers. It may not change mounted authority.
