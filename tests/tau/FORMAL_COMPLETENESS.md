# Formal Completeness Testing - Enhanced Edition

This folder defines a repeatable process for ensuring Tau specs are **formally complete state machines** with:

1. **Proper base case initialization** for all temporal references
2. **Single-line predicate definitions** (no multi-line)
3. **No unsupported operators** (prime `'`)
4. **Deterministic behavior at all timesteps**
5. **Behavioral verification** via trace tests
6. **Formal invariants** (oracle equivalence + LTL claim coverage)

## Quick Start

```bash
# Full check (lint + trace)
python tests/tau/check_formal_completeness.py

# Summary view - see which specs are complete
python tests/tau/check_formal_completeness.py --summary --lint-only

# Deep analysis of single spec
python tests/tau/check_formal_completeness.py --analyze experiments/my_spec.tau

# Get auto-fix suggestions
python tests/tau/check_formal_completeness.py --fix experiments/my_spec.tau
```

## Tools

### 1) Lint + Trace Runner

```
python tests/tau/check_formal_completeness.py [OPTIONS]
```

**Options:**
| Flag | Description |
|------|-------------|
| `--lint-only` | Run lint checks only, skip trace tests |
| `--trace-only` | Run trace tests only, skip lint |
| `--analyze FILE` | Deep analysis of a single spec |
| `--fix FILE` | Show auto-fix suggestions for missing base cases |
| `--summary` | Show completeness summary with stats |
| `--strict` | Treat warnings as errors |
| `--verbose` | Show detailed predicate information |
| `--no-syntax` | Skip Tau syntax verification |
| `--allow-unverified` | Treat missing oracle/registry entries as warnings |
| `--syntax-timeout` | Per-spec syntax timeout in seconds |

**Defaults:**
- Scans `experiments/` and `src/tau_specs/`
- Excludes `external/` and `experiments/io/` REPL scripts
- Fails on lint errors, syntax errors, invariant violations, or trace mismatches

### 2) Trace Registry

`tests/tau/spec_registry.json` defines short, deterministic traces for specs that
claim verified behavior. Each entry provides:
- `inputs`: list of per-step input maps (`i1`, `i2`, ...).
- `expected`: per-step outputs (`o1`, `o2`, ...).
- Use `null` for steps/outputs that are intentionally skipped (warmup).

Optional fields for invariants:
- `oracle`: `{ "type": "python", "outputs": { "o1": "1 if i1 >= i2 else 0" } }`
- `enumeration`: input domains for INV1, e.g. `"i1": [0,1,2,3]`
- `max_cases`: cap for enumeration size (default 512)
- `ltl`: list of claims, e.g. `{ "id": "no_spike", "expr": "not (o1 == 0)" }`
- `mode`: `repl`, `spec`, or `skip` (with `skip_reason`)
- `spec_timeout`: per-spec timeout (seconds) for `spec` mode

## Formal Completeness Rules (Lint)

- **Single-line predicates**: any `:=` line must end with `.`.
- **No prime operator**: `'` is rejected in spec mode.
- **Warmup required**: if a spec uses `t-k`, every output stream must provide
  explicit initialization for steps `0..k-1`.
- **Warnings**: temporal dependencies on inputs are flagged to highlight the
  need for warmup/gating.

## Formal Invariants (Verifier)

**INV1**: For all input combinations in `enumeration`, spec outputs must match
the `oracle` outputs exactly. Counterexamples are recorded with inputs/outputs.

**INV2**: All documented LTL claims (`# LTL: claim_id` in spec comments) must
have a corresponding `ltl` entry in the registry and must hold for all
enumerated input combinations.

**PRE**: Tau syntax must be valid before invariant checks run.

## Adding a Spec to the Registry

1. Add an entry in `tests/tau/spec_registry.json`.
2. Provide inputs for each time step.
3. Set expected outputs; use `null` when a step is not meant to be checked.
4. Run the checker:
   ```
   python tests/tau/check_formal_completeness.py
   ```

## Notes on Temporal Specs

The current Tau REPL build can segfault on temporal (`t-1`) constraints. For
temporal specs, set `mode: "skip"` with a `skip_reason` until the REPL/runtime
can evaluate temporal traces safely.

## Interpreting Failures

- **Lint errors**: incomplete temporal specs, multi-line predicates, or prime
  operator usage.
- **Trace failures**: output diverges from the intended behavior for a
  concrete trace.
