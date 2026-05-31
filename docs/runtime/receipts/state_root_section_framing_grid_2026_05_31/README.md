# State-root section-framing grid

Date: 2026-05-31

This receipt records a deterministic non-Kani evidence slice for state-root v5
section framing. Kani currently proves scalar state-root guards, while full
section encoding, duplicate detection, BTreeMap traversal, and SHA-256 remain
outside the symbolic tractability boundary.

## Covered finite grid

The runtime test is:

```text
tests/runtime/test_state_root_section_framing_grid.py
```

It builds the production `state_root_preimage`, decodes it with the existing
strict preimage decoder, and checks one-hot section states for:

- all six section labels are present in the fixed v5 order;
- the empty state encodes all section bodies as zero;
- each one-hot state changes exactly one framed section body relative to empty;
- the changed non-FEE section has exactly one entry;
- the FEE one-hot section encodes dust `1`;
- the computed root equals `sha256(preimage)`;
- empty plus six one-hot states have distinct roots;
- Rust `verify-state-root` matches Python on the same seven cases.

One-hot sections:

```text
BAL: one balance entry
POL: one pool entry
LPB: one LP balance entry
LPA: one LP duration-risk metadata entry
NNC: one nonce entry
FEE: fee-accumulator dust = 1
```

This is bounded framing evidence. It does not claim full live-domain
state-root refinement or SHA-256 collision resistance.

## Commands

Focused new grid:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_state_root_section_framing_grid.py
```

Result:

```text
...                                                                      [100%]
3 passed in 0.22s
```

Focused state-root family:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_state_root_section_framing_grid.py \
  tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_disaster_state.py \
  tests/runtime/test_state_root_fuzz_gate.py \
  tests/runtime/test_state_root_injectivity_proof.py \
  tests/runtime/test_state_root_live_path.py \
  tests/runtime/test_state_root_lp_duration_exhaustive_grid.py \
  tests/state/test_state_root_determinism.py
```

Result:

```text
.................................................................        [100%]
65 passed in 2.32s
```

Rust unit focus:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core state_root
```

Result:

```text
running 16 tests
................
test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 158 filtered out; finished in 0.00s
```

Deployment/profile and diff hygiene:

```bash
python3 tools/check_deployment_profiles.py
git diff --check
```

Result:

```text
local-dev: ok
production-strict: ok
public-testnet: ok
git diff --check: no output
```
