# zUSD liquidation compensation split Kani receipt

Date: 2026-05-31

This receipt records the helper-level CBC hardening added to the Rust zUSD
single-vault core. The liquidation branch now computes the liquidator/stability
pool collateral split through a checked helper:

```text
variable_comp = ceil(liquidated_collateral_e8 * variable_comp_bps / 10000)
requested = fixed_compensation_e8 + variable_comp
liquidator_compensation = min(liquidated_collateral_e8, requested)
stability_pool_gain = liquidated_collateral_e8 - liquidator_compensation
```

The helper returns `None` on invalid `variable_comp_bps` or checked-arithmetic
overflow. The live `step` maps that to the existing bounded-check rejection.

## Machine-checked contract

File:

```text
rust-runtime/crates/zenodex-runtime-core/src/zusd.rs
```

Harnesses:

```text
zusd::kani_contracts::liquidation_compensation_split_total_on_state_domain
zusd::kani_contracts::liquidation_compensation_split_covers_are_reachable
```

The totality harness assumes the same scalar bounds enforced by
`validate_state_shape`:

```text
liquidated_collateral_e8 <= MAX_AMOUNT_E8
fixed_compensation_e8 <= MAX_AMOUNT_E8
variable_comp_bps <= BPS_SCALE
```

Under that runtime state domain it proves:

```text
helper returns Some((liquidator_compensation, stability_pool_gain))
liquidator_compensation <= liquidated_collateral_e8
liquidator_compensation + stability_pool_gain = liquidated_collateral_e8
```

The cover harness proves the main branches are reachable: normal split,
full-collateral compensation cap, zero-compensation split, and out-of-domain
`variable_comp_bps` rejection.

## Replay evidence

Focused Rust tests:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core zusd
```

Result:

```text
9 passed; 0 failed; 166 filtered out
```

Focused zUSD runtime replay:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_zusd_reference.py \
  tests/runtime/test_zusd_golden_trace.py \
  tests/runtime/test_zusd_liquidation_compensation_grid.py \
  tests/runtime/test_zusd_disaster_state.py \
  tests/runtime/test_zusd_semantic_invariants.py \
  tests/runtime/test_zusd_live_path.py \
  tests/runtime/test_zusd_cdp_threshold_grid.py \
  tests/runtime/test_zusd_conformance.py
```

Result:

```text
51 passed
```

Focused Kani:

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani -p zenodex-runtime-core \
  --harness zusd::kani_contracts::liquidation_compensation_split_total_on_state_domain \
  --output-format terse
cargo kani -p zenodex-runtime-core \
  --harness zusd::kani_contracts::liquidation_compensation_split_covers_are_reachable \
  --output-format terse
```

Result:

```text
total_on_state_domain: SUCCESSFUL, 0 of 58 failed
covers_are_reachable: SUCCESSFUL, 0 of 61 failed, 4 of 4 cover properties satisfied
```

Full Kani sweep:

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani --lib --output-format terse -j 4 --harness-timeout 10m -Z unstable-options
```

Result:

```text
Manual Harness Summary:
Complete - 88 successfully verified harnesses, 0 failures, 88 total.
```

Final hygiene gates:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core
cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
cd ..
python3 tools/check_deployment_profiles.py
git diff --check
```

Results:

```text
cargo test -p zenodex-runtime-core: 175 passed
cargo fmt --check: passed
cargo clippy --workspace --all-targets -- -D warnings: passed
check_deployment_profiles: local-dev ok, production-strict ok, public-testnet ok
git diff --check: passed
```

## Scope boundary

This is a proof-linked scalar helper inside zUSD liquidation accounting. It does
not prove the full zUSD `step`, the BigInt CDP ratio arithmetic, redemption
selection, or every liquidation guard. Those remain covered by Python/Rust
differentials, golden traces, semantic invariant tests, disaster tests, CDP
threshold grids, and the existing Lean boundary slice until the BigInt core is
generated or separately verified.
