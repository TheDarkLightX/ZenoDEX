# State Root Pool Asset Order Kani Receipt

Date: 2026-05-31

This receipt records a small state-root CBC decomposition slice. Pool asset
ordering is consensus-critical because pool entries are accepted only when
`asset0 < asset1` in decoded-byte order. The state-root encoder now routes that
check through an explicit helper:

```text
pool_assets_in_canonical_order(asset0, asset1) := asset0 < asset1
```

The helper is used by `encode_pools` before a pool entry is admitted into the
state-root preimage.

## Evidence

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core state_root
```

Result:

```text
16 passed; 0 failed; 158 filtered out
```

```bash
cd rust-runtime
cargo kani -p zenodex-runtime-core \
  --harness state_root::kani_contracts::pool_asset_order_guard_matches_fixed_width_byte_order \
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
  --harness state_root::kani_contracts::pool_asset_order_guard_rejects_equal_assets \
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
  --harness state_root::kani_contracts::state_root_guard_covers_are_reachable \
  --output-format terse
```

Result:

```text
VERIFICATION:- SUCCESSFUL
3 of 3 cover properties satisfied
Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

Focused regression:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core state_root::tests::non_canonical_pool_assets_rejected
```

Result:

```text
1 passed; 0 failed; 173 filtered out
```

Full core Kani sweep after adding the helper:

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani --lib --output-format terse -j 4 --harness-timeout 10m -Z unstable-options
```

Result:

```text
Manual Harness Summary:
Complete - 84 successfully verified harnesses, 0 failures, 84 total.
```

Final focused state-root replay gates:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_live_path.py \
  tests/runtime/test_state_root_disaster_state.py \
  tests/runtime/test_state_root_fuzz_gate.py \
  tests/runtime/test_state_root_lp_duration_exhaustive_grid.py \
  tests/runtime/test_state_root_section_framing_grid.py \
  tests/runtime/test_state_root_curve_config_grid.py
```

Result:

```text
46 passed in 5.85s
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

This proves the fixed-width decoded-byte order helper used by state-root pool
admission and its equal-assets rejection behavior. The helper deliberately uses
Rust's standard lexicographic slice ordering. This does not prove the full
state-root encoder. Hex decoding, duplicate detection, heap-backed section
assembly, BigUint curve parsing, and SHA-256 remain covered by vectors,
Python/Rust differentials, fuzz tests, and the existing state-root grids.
