# zUSD liquidation compensation grid

Date: 2026-05-31

This receipt records a deterministic non-Kani evidence slice for zUSD
liquidation compensation accounting. Kani covers BigInt-free zUSD helper
contracts; this grid targets the value-moving BigInt liquidation split:

```text
liquidator_comp = min(collateral, fixed_comp + ceil(collateral * comp_bps / BPS))
sp_gain = collateral - liquidator_comp
```

Accepted liquidations must conserve the liquidated collateral across stability
pool gain and liquidator compensation. Rejected stability-pool cap cases must be
no-op rejects.

## Covered finite grid

The runtime test is:

```text
tests/runtime/test_zusd_liquidation_compensation_grid.py
```

It checks:

- zero fixed/variable compensation;
- fixed-only compensation;
- variable compensation with ceiling behavior on non-divisible collateral;
- fixed plus variable compensation;
- compensation capped at full collateral;
- stability-pool collateral cap rejection with no post-state;
- curated Python/Rust authority-document parity through `zusd-op`.

This is bounded accounting evidence for a high-value liquidation branch. It does
not claim full zUSD `step` refinement or full live-domain BigInt proof coverage.

## Commands

Focused new grid:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_zusd_liquidation_compensation_grid.py
```

Result:

```text
...                                                                      [100%]
3 passed in 0.25s
```

Focused zUSD family:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_zusd_cdp_threshold_grid.py \
  tests/runtime/test_zusd_liquidation_compensation_grid.py \
  tests/runtime/test_zusd_reference.py \
  tests/runtime/test_zusd_conformance.py \
  tests/runtime/test_zusd_semantic_invariants.py \
  tests/runtime/test_zusd_disaster_state.py \
  tests/runtime/test_zusd_golden_trace.py \
  tests/runtime/test_zusd_live_path.py \
  tests/runtime/test_zusd_redeem_selector_step_differential.py \
  tests/runtime/test_zusd_oracle_commit_mcr_step_differential.py
```

Result:

```text
.......................................................                  [100%]
55 passed in 1.90s
```

Rust focused checks:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core zusd
cargo test -q -p zenodex-runtime-cli zusd
```

Result:

```text
running 8 tests
........
test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 166 filtered out; finished in 0.00s

running 0 tests
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 80 filtered out; finished in 0.00s
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
