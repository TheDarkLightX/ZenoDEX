# State-root curve-config grid

Date: 2026-05-31

This receipt records a deterministic non-Kani evidence slice for state-root v5
curve configuration parsing and normalization.

Python `PoolState` normalizes raw curve configuration before the state root is
computed. The Rust state-root shadow intentionally accepts only already
normalized curve fields at its raw JSON boundary. This grid pins that contract
explicitly.

## Covered finite grid

The runtime test is:

```text
tests/runtime/test_state_root_curve_config_grid.py
```

It checks:

- canonical CPMM, CUBIC_SUM_V1, SUM_BOOST_V1, QUARTIC_BLEND_V1, and
  QUINTIC_BLEND_V1 pool configs;
- BigUint-sized curve parameters above `u128` in the curve-param JSON string;
- zero and nonzero reduced blend ratios;
- Python/Rust state-root parity for all canonical configs;
- Python normalization collapse for equivalent raw curve configs;
- Rust fail-closed rejection of raw non-normalized curve fields.

This is bounded boundary evidence for the curve-config parser/normalizer. It
does not claim full state-root refinement, SHA-256 collision resistance, or full
semantic equivalence of all AMM curve families.

## Commands

Focused new grid:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_state_root_curve_config_grid.py
```

Result:

```text
...                                                                      [100%]
3 passed in 0.24s
```

Focused state-root family:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_state_root_section_framing_grid.py \
  tests/runtime/test_state_root_curve_config_grid.py \
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
....................................................................     [100%]
68 passed in 2.49s
```

Rust focused checks:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core state_root
cargo test -q -p zenodex-runtime-cli state_root
```

Result:

```text
running 16 tests
................
test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 158 filtered out; finished in 0.00s

running 0 tests
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 80 filtered out; finished in 0.00s
```
