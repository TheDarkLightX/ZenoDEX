# Perp partial-close boundary Kani receipt

Date: 2026-05-31

This receipt records a small CBC hardening step on the stateless perps math used
by partial liquidation. The remaining-position helper has simple branch
semantics at the close boundary:

```text
fraction_bps <= 0      -> remaining_position = position
fraction_bps >= 10000  -> remaining_position = 0
```

The division-heavy interior case still relies on property/differential
evidence. The attempted full symbolic Kani proof over arbitrary bridge-domain
`i128` position and symbolic `fraction_bps` was intentionally abandoned because
CBMC spent time in 128-bit multiply/divide reasoning without producing useful
incremental assurance.

## Machine-checked contract

File:

```text
rust-runtime/crates/zenodex-runtime-core/src/perp_math.rs
```

Harness:

```text
perp_math::kani_contracts::remaining_position_signed_boundary_cases_are_exact
```

The harness assumes the public bridge magnitude domain:

```text
abs(position) <= MAX_ABS
```

It proves:

```text
remaining_position_signed(position, -1) = position
remaining_position_signed(position, 0) = position
remaining_position_signed(position, BPS_SCALE) = 0
remaining_position_signed(position, BPS_SCALE + 1) = 0
```

The existing `covers_are_reachable` harness now also covers a concrete partial
close and signed remaining-position case:

```text
partial_close_base(10000, 2500) = 2500
remaining_position_signed(-10000, 2500) = -7500
```

## Property evidence

The Rust property test
`partial_close_remaining_preserves_bounds_on_bounded_domain` covers the bounded
runtime domain:

```text
position in [-MAX_ABS, MAX_ABS]
fraction_bps in [0, BPS_SCALE]
```

It asserts:

```text
abs(remaining_position) <= abs(position)
fraction_bps = 0 -> remaining_position = position
fraction_bps = BPS_SCALE or position = 0 -> remaining_position = 0
position side is preserved before full close
```

## Replay evidence

Focused Rust tests:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core perp_math
```

Result:

```text
10 passed; 0 failed; 166 filtered out
```

Focused Kani:

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani -p zenodex-runtime-core \
  --harness perp_math::kani_contracts::remaining_position_signed_boundary_cases_are_exact \
  --output-format terse
cargo kani -p zenodex-runtime-core \
  --harness perp_math::kani_contracts::covers_are_reachable \
  --output-format terse
```

Result:

```text
remaining_position_signed_boundary_cases_are_exact: SUCCESSFUL, 0 of 21 failed
covers_are_reachable: SUCCESSFUL, 0 of 57 failed, 6 of 6 cover properties satisfied
```

Full Kani sweep:

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani --lib --output-format terse -j 4 --harness-timeout 10m -Z unstable-options
```

Result:

```text
Manual Harness Summary:
Complete - 89 successfully verified harnesses, 0 failures, 89 total.
```

## Scope boundary

This is a boundary-case proof and bounded-domain property test for the
stateless partial-close helper. It does not prove the full partial-liquidation
auto-fraction search, liquidation penalty arithmetic, settle liquidation
accumulation, or stateful materializer wrapper. Those remain covered by the
existing Python/Rust differential and live-shadow evidence until further
decomposition or generated arithmetic kernels are added.
