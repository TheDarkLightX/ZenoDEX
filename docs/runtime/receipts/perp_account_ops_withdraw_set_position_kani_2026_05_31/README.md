# Perp account-op withdraw/set-position Kani receipt

Date: 2026-05-31

This receipt records a perps stateful CBC decomposition slice for the actual
Rust `perp_account_ops` core. Before this slice, Kani covered the account-op
domain predicate plus deposit and clear-breaker accept shapes. This slice adds
full-domain accept-shape contracts for the other two account-op arms:

- `withdraw_collateral`
- `set_position`

It also extends the account-op non-vacuity harness so Kani must reach accept and
reject examples for deposit, withdraw, set-position, clear-breaker, and unknown
op dispatch.

## Kani commands

```bash
cd rust-runtime
cargo kani -p zenodex-runtime-core \
  --harness perp_account_ops::kani_contracts::withdraw_collateral_total_and_accept_shape \
  --output-format terse \
  -Z unstable-options \
  --harness-timeout 5m
```

Result:

```text
Checking harness perp_account_ops::kani_contracts::withdraw_collateral_total_and_accept_shape...

VERIFICATION RESULT:
 ** 0 of 573 failed (3 unreachable)

VERIFICATION:- SUCCESSFUL
Verification Time: 10.625787s

Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

```bash
cargo kani -p zenodex-runtime-core \
  --harness perp_account_ops::kani_contracts::set_position_total_and_accept_shape \
  --output-format terse \
  -Z unstable-options \
  --harness-timeout 5m
```

Result:

```text
Checking harness perp_account_ops::kani_contracts::set_position_total_and_accept_shape...

VERIFICATION RESULT:
 ** 0 of 574 failed (4 unreachable)

VERIFICATION:- SUCCESSFUL
Verification Time: 10.221808s

Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

```bash
cargo kani -p zenodex-runtime-core \
  --harness perp_account_ops::kani_contracts::account_op_covers_are_reachable \
  --output-format terse \
  -Z unstable-options \
  --harness-timeout 5m
```

Result:

```text
Checking harness perp_account_ops::kani_contracts::account_op_covers_are_reachable...

VERIFICATION RESULT:
 ** 0 of 639 failed (1 unreachable)

 ** 10 of 10 cover properties satisfied

VERIFICATION:- SUCCESSFUL
Verification Time: 3.0217152s

Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

## Runtime regression commands

```bash
cd rust-runtime
cargo fmt --check
cargo test -q -p zenodex-runtime-core perp_account_ops
cargo clippy --workspace --all-targets -- -D warnings
```

Result:

```text
perp_account_ops tests: 14 passed
clippy: finished clean
```

Python/Rust runtime conformance:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_perp_account_ops_conformance.py \
  tests/runtime/test_perp_stateful_live_shadow.py
```

Result:

```text
......................................................                   [100%]
54 passed in 3.99s
```

Deployment/profile gate:

```bash
python3 tools/check_deployment_profiles.py
```

Result:

```text
local-dev: ok
production-strict: ok
public-testnet: ok
```

## Boundary

These Kani harnesses prove full-domain totality/accept-shape obligations for
the account-op dispatch arms. They do not prove the full live-domain margin
arithmetic implications for withdraw and set-position. Stronger harnesses that
recomputed the maintenance/initial-margin obligations on accepted transitions
timed out under the 5 minute Kani limit. Those deeper arithmetic implications
remain covered by the existing Python/Rust differential, golden traces, and
runtime conformance tests until the margin formulas are further decomposed or
generated from a verified arithmetic kernel.
