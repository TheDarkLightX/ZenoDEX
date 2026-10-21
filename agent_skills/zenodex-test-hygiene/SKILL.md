---
name: zenodex-test-hygiene
description: Enforce ZenoDEX Test Hygiene V1 and Test Quality V2 for critical code, proof, state, integration, assurance-tool, CI, and test changes. Use when adding or changing tests, fixing a bug, refactoring a critical path, changing value or authority behavior, editing a checker or release gate, reviewing test adequacy, or preparing evidence for a pull request.
---

# ZenoDEX Test Hygiene

## Authority

Use this skill to route reviewable evidence. Treat
`tools/check_test_hygiene_v1.py`, `tools/check_test_quality_v2.py`, and required
CI as the structural acceptance authority. Instructions, agent reports, test
counts, and coverage percentages do not clear the gate.

Read these files before changing critical paths:

- `AGENTS.md` and applicable path overlays when present;
- `docs/testing/TEST_HYGIENE_CONTRACT_V1.md`;
- `docs/testing/TEST_QUALITY_CONTRACT_V2.md`;
- `tools/test_hygiene_contract_v1.json`.
- `tools/test_quality_contract_v2.json`.

If prose and the checker disagree, stop and report the conflict. Do not weaken
the checker to preserve a broader claim.

## Workflow

1. Inspect `git status --short` and preserve unrelated work.
2. Classify every touched path with the local style map when available.
3. Name one falsifiable obligation, authority boundary, and concrete failure
   mode. Record Reach, Infect, Propagate, and Reveal.
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
7. Create one linked `TQV2-YYYYMMDD-slug.json` packet under
   `tests/evidence/test_quality/`. Record the oracle independence grade,
   representation review, smallest evidence set, and executed falsifier.
8. Pin covered source and test files after the implementation is final. Record
   exact pytest node IDs, named mutants, boundary dimensions, AAA and
   reject-is-no-op decisions, and nonclaims.
9. Run the focused tests, the diff-aware V2 gate, and the nearest broader
   repository gate.

Route focused work to:

- `zeno-semantic-compressor` before testing representable invalid states;
- `zeno-test-architect` for technique and oracle selection;
- `zeno-mutation-hardener` for survivor-driven adequacy;
- `zeno-stateful-adversary` for histories, concurrency, and crash recovery;
- `zeno-zrpf-proof-adversary` for proof and admission equality chains;
- `zeno-suite-distiller` after a mutation campaign or wrapper-growth spike.

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

```bash
python3 tools/check_test_hygiene_v1.py --json
python3 tools/check_test_quality_v2.py --json
python3 tools/run_test_quality_gate_v2.py \
  --changed-file M:src/core/example.py \
  --changed-file A:tests/core/test_example.py
pytest -q tests/test_check_test_quality_v2.py tests/test_run_test_quality_gate_v2.py
```

## Reporting

Report the obligation, changed critical paths, V1/V2 packet IDs, oracle grade,
executed mutant, commands and outcomes, unrun gates, and residual risk. A green
V2 gate means the declared obligation is structurally closed and its pinned
tests pass. It does not prove the prose or oracle is truthful, and it does not
promote production readiness or whole-economy correctness.
