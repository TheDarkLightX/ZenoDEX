# zUSD CDP threshold grid

Date: 2026-05-31

This receipt records a deterministic non-Kani evidence slice for the zUSD
single-vault CDP arithmetic that uses Python/Rust big integers:

```text
MCR_OK(c,d,p,m) := d = 0 or c * p * 10000 >= d * m * 1e8
```

Kani remains useful for the BigInt-free scalar helpers. This grid targets the
ratio and floor arithmetic that is outside the current Kani tractability
boundary.

## Covered finite grids

The runtime test is:

```text
tests/runtime/test_zusd_cdp_threshold_grid.py
```

It compares the authoritative Python zUSD transition against an independent
integer oracle for:

- mint MCR admission at and one unit past the exact debt threshold;
- withdraw MCR admission at and one unit past the exact collateral threshold;
- redeem gross-collateral floor arithmetic and post-state accounting;
- liquidation admission at and one unit past the MCR boundary;
- a planted strict-comparator violation to prove the oracle has teeth.

Observed grid counts:

```text
mint:       216 accepted, 180 rejected
withdraw:  135 accepted, 108 rejected
redeem:     30 accepted,  18 rejected
liquidate:  24 accepted,  12 rejected
```

A curated threshold subset also runs through Rust `zusd-op` and compares the
complete authority document, including state roots, receipt hash, post-state,
accept/reject bit, and reject code.

## Lean slice

The same boundary formulas are mirrored in a self-contained Lean file:

```text
lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean
```

Checked claims:

```text
cdpBoundaryGridOk = true
mcrOk (110 * e8) (100 * e8) e8 11000 = true
mcrOk (110 * e8) (100 * e8 + 1) e8 11000 = false
redemptionGrossCollateral 1 (2 * e8) = 0
```

This is bounded checker-backed arithmetic evidence. It is not a full live-domain
proof of `src/core/zusd.py` or `zenodex-runtime-core::zusd::step`.

## Commands

```bash
lean lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean
lean -R lean-mathlib lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean
rg -n "sorry|admit|axiom|unsafe" lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean || true
```

Result:

```text
exit 0 for both Lean commands; placeholder scan empty
```

Focused new runtime grid:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_zusd_cdp_threshold_grid.py
```

Result:

```text
......                                                                   [100%]
6 passed in 0.29s
```

Focused zUSD runtime family:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_zusd_*.py
```

Result:

```text
....................................................                     [100%]
52 passed in 1.82s
```

Rust unit focus:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core zusd
cargo test -q -p zenodex-runtime-cli zusd
```

Result:

```text
zenodex-runtime-core: 8 passed
zenodex-runtime-cli: 0 passed; 80 filtered
```

Deployment profiles:

```bash
python3 tools/check_deployment_profiles.py
```

Result:

```text
local-dev: ok
production-strict: ok
public-testnet: ok
```
