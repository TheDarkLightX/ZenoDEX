---
description: Cross-session math discovery with PopperPad falsification gates and Codex grading
---

# Math Discovery Workflow

Use this workflow when formalizing new game theory, economic bounds, mechanism design,
or any mathematical result that should persist across sessions with falsifiable evidence.

The workflow integrates three systems already in this repo:
- **PopperPad** (`tools/popper_pad.py`): append-only falsification-gated knowledge base
- **Math Discovery Pipeline** (`experimental/math_discovery_pipeline/`): structured discovery loop
- **Codex Review** (`.windsurf/workflows/codex-review.md`): grading and iteration

## Phases

### 1. Pre-work briefing

Before starting any new math work, query PopperPad for the relevant domain:

```bash
python3 tools/popper_pad.py query --domain "<domain>" --format briefing
```

Also check for falsified hypotheses and dead ends that are relevant:

```bash
python3 tools/popper_pad.py check-falsified "<keyword>"
python3 tools/popper_pad.py check-dead-ends "<keyword>"
```

Record what NOT to try. Do not attempt approaches already listed as DEAD_END.
Do not re-propose hypotheses already FALSIFIED.

### 2. Formalize the model

Write the mathematical model as a Lean proof in `internal/proofs/` or `experiments/lean/`.

Key principles (from CBC directive):
- List domain invariants explicitly before writing proofs
- List invalid states that must be impossible
- Use scaled integer arithmetic (BPS = 10000), never floating point
- Encode bounds as preconditions in definitions, not just theorem hypotheses
- Add witnesses for both feasible and infeasible cases
- Move witnesses inside the namespace, not at root scope

Compile after each change:

```bash
cd /home/trevormoc/deps/mathlib4 && lake env lean "<proof_file>"
```

### 3. Implement the verifier

Write a Python verifier tool in `tools/` that:
- Uses exact scaled integer comparisons (no floats)
- Validates all inputs at boundaries (type, range, format)
- Fails closed on any validation error
- Documents rounded summary fields vs exact feasibility fields
- Splits error codes for distinct boundary cases

### 4. Write tests

Write tests in `tests/` that cover:
- Positive (accepted) cases
- Negative (rejected) cases with specific error codes
- Boundary cases (equality, off-by-one)
- Infeasible cases (no valid configuration exists)
- Probabilistic cases (non-deterministic acceptance)
- Direct unit tests for the pure verifier function (not just CLI subprocess)
- Profit summary rounding vs exact feasibility distinction

Run tests:

```bash
python3 -m pytest "<test_file>" -v
```

### 5. Codex grading

Run the Codex review workflow (see `.windsurf/workflows/codex-review.md`).

Embed file contents directly in the Codex prompt using `$(cat <file>)` since the
sandbox cannot read from the checkout path. Iterate until all criteria are A- or better.

### 6. Record to PopperPad

After the work is complete and graded, record the results:

Record the main theorem as KNOWLEDGE with evidence:

```bash
python3 tools/popper_pad.py knowledge \
    --fact "<one-sentence statement of the proven bound>" \
    --evidence "Lean: <proof_file>, Codex grade: <grade>, tests: <count> passed" \
    --domain "<domain>" \
    --agent "cascade" \
    --confidence 0.9 \
    --refs "<proof_file>" "<verifier_file>" "<test_file>"
```

Record any falsified conjectures or approaches that failed during iteration:

```bash
python3 tools/popper_pad.py dead-end \
    --approach "<what was tried>" \
    --reason "<why it failed>" \
    --domain "<domain>" \
    --agent "cascade" \
    --time-spent "<approximate time>"
```

Record key insights that are not falsifiable but are useful:

```bash
python3 tools/popper_pad.py insight \
    --observation "<the observation>" \
    --context "<when/where this matters>" \
    --domain "<domain>" \
    --agent "cascade"
```

If the work proposes a new conjecture that is falsifiable but not yet tested:

```bash
python3 tools/popper_pad.py add-hypothesis \
    --claim "<the testable claim>" \
    --test "<how to test/falsify it>" \
    --domain "<domain>" \
    --agent "cascade" \
    --confidence 0.5
```

### 7. Commit

Stage and commit all new and modified files. Use `git add -f` for git-ignored
paths like `internal/proofs/`. Write a detailed commit message including:
- Mathematical model summary
- Key theorems and witnesses
- Codex grades achieved
- Test count and status

### 8. Save memory

Create or update persistent memories for:
- The mathematical model (definitions, theorems, key values)
- Process learnings (what worked, what failed, what Codex flagged)
- File paths and compilation/test commands

This ensures the next session can resume without re-deriving context.
