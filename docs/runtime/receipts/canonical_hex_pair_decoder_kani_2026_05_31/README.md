# Canonical Fixed-Hex Pair Decoder Kani Receipt

Date: 2026-05-31

This receipt records a canonical-primitives hardening slice. The runtime
`hex_to_bytes_fixed` path validates a `0x`-prefixed fixed-width hex body and
now decodes each byte through an internal checked pair decoder:

```text
decode_hex_pair(high, low) := (hex_nibble(high) << 4) | hex_nibble(low)
```

The old path validated the body and then delegated byte decoding to the
external `hex` crate. The new path keeps the same public behavior while moving
the consensus-critical byte conversion into small runtime helpers that Kani can
check directly.

## Evidence

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core canonical
```

Result:

```text
20 passed; 0 failed; 154 filtered out
```

```bash
cd rust-runtime
cargo kani -p zenodex-runtime-core \
  --harness canonical::kani_contracts::hex_nibble_is_exact \
  --output-format terse
```

Result:

```text
VERIFICATION:- SUCCESSFUL
Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

```bash
cd rust-runtime
cargo kani -p zenodex-runtime-core \
  --harness canonical::kani_contracts::decode_hex_pair_is_exact \
  --output-format terse
```

Result:

```text
VERIFICATION:- SUCCESSFUL
Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

```bash
cd rust-runtime
cargo kani -p zenodex-runtime-core \
  --harness canonical::kani_contracts::fixed_hex_expected_len_covers_are_reachable \
  --output-format terse
```

Result:

```text
VERIFICATION:- SUCCESSFUL
5 of 5 cover properties satisfied
Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

Focused Python/Rust replay:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_canonical_primitives_vectors.py \
  tests/runtime/test_canonical_primitives_disaster_state.py \
  tests/runtime/test_canonical_json_escape_grid.py \
  tests/runtime/test_canonical_framing_grid.py
```

Result:

```text
28 passed in 2.00s
```

Full core Kani sweep after adding the decoder helpers:

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani --lib --output-format terse -j 4 --harness-timeout 10m -Z unstable-options
```

Result:

```text
Manual Harness Summary:
Complete - 86 successfully verified harnesses, 0 failures, 86 total.
```

Final focused canonical/state-root replay:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_canonical_primitives_vectors.py \
  tests/runtime/test_canonical_primitives_disaster_state.py \
  tests/runtime/test_canonical_json_escape_grid.py \
  tests/runtime/test_canonical_framing_grid.py \
  tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_live_path.py
```

Result:

```text
46 passed in 3.06s
```

Final Rust and deployment hygiene:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --check
cd ..
python3 tools/check_deployment_profiles.py
git diff --check
```

Results:

```text
zenodex-runtime-core: 174 passed; 0 failed
cargo clippy: finished clean
cargo fmt --check: clean
local-dev: ok
production-strict: ok
public-testnet: ok
git diff --check: clean
```

## Boundary

This proves the byte-level hex digit and pair-decoding helpers used by the Rust
canonical fixed-hex path. It does not prove the full public
`hex_to_bytes_fixed` wrapper, because that wrapper still uses `str`, `Vec`, and
runtime length/prefix checks. Those wrapper semantics remain covered by unit
tests, Python/Rust canonical primitive vectors, framing grids, disaster tests,
and state-root replay.
