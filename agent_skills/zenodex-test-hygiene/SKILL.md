---
name: zenodex-test-hygiene
description: Enforce ZenoDEX Test Hygiene Contract V1 for critical code, proof, state, integration, assurance-tool, CI, and test changes. Use when adding or changing tests, fixing a bug, refactoring a critical path, changing value or authority behavior, editing a checker or release gate, reviewing test adequacy, or preparing evidence for a pull request.
---

# ZenoDEX Test Hygiene

## Authority

Use this skill to construct reviewable evidence. Treat
`tools/check_test_hygiene_v1.py` and required CI as the acceptance authority.
Instructions, agent reports, test counts, and coverage percentages do not clear
the gate.

Read these files before changing critical paths:

- `AGENTS.md` and applicable path overlays;
- `docs/testing/TEST_HYGIENE_CONTRACT_V1.md`;
- `tools/test_hygiene_contract_v1.json`.

If prose and the checker disagree, stop and report the conflict. Do not weaken
the checker to preserve a broader claim.

## Workflow

1. Inspect `git status --short` and preserve unrelated work.
2. Classify every touched path with the local style map.
3. Name the invariant, authority boundary, and concrete failure mode.
4. Add or identify failing evidence before behavior repair.
5. Select evidence by risk shape:
   - focused unit or regression: AAA plus exact observables;
   - workflow: BDD happy, reject, authorization, cancellation, recovery, and
     terminal scenarios;
   - arithmetic: boundary plus property or differential evidence;
   - lifecycle and authority: stateful replay, reorder, duplicate, stale,
     partial-failure, and reject-is-no-op evidence;
   - shared semantics: Rust/Python/Tau/guest/generated-reference parity;
   - checker or gate: structure-preserving mutation-killing negatives.
6. Create a new `THV1-YYYYMMDD-slug.json` packet under
   `tests/evidence/test_hygiene/`. Never edit or delete an existing packet.
7. Pin covered source and test files after the implementation is final. Record
   exact pytest node IDs, named mutants, boundary dimensions, AAA and
   reject-is-no-op decisions, and nonclaims.
8. Run the focused tests, the diff-aware hygiene gate, and the nearest broader
   repository gate.

## Boundary selection

Start with specification-derived points: zero, one atom, lower/equal/upper
thresholds, maximum neighbors, overflow, dust, rounding, epoch boundaries,
Oracle freshness, malformed values, collection cardinalities, and resource
ceilings.

Add structure-preserving one-defect mutations and pairwise interactions. Retain
bounded deeper combinations for named dependency paths. Quality-diversity or
LLM exploration may propose additional boundaries; promote only minimized,
deterministically replayable cases.

## Commands

Validate static artifacts:

```bash
python3 tools/check_test_hygiene_v1.py --json
```

Validate selected local paths and run declared evidence:

```bash
python3 tools/run_test_hygiene_gate_v1.py \
  --changed-file M:src/core/example.py \
  --changed-file A:tests/core/test_example.py
```

Run the permanent checker regressions:

```bash
pytest -q \
  tests/test_check_test_hygiene_v1.py \
  tests/test_run_test_hygiene_gate_v1.py
```

## Reporting

Report the exact invariant, changed critical paths, evidence packet ID, named
negative or mutant, commands and outcomes, unrun gates, and residual risk. A
green hygiene gate means the declared evidence is current and executable. It
does not promote production readiness or whole-economy correctness.
