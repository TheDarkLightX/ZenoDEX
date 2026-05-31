# arith core Kani receipt (iso campaign)

Kani evidence for the checked-arithmetic core `zenodex-runtime-core::arith`, which
previously had **no** Kani harnesses despite being the integer primitive layer
every perp/zUSD/cpmm/fee kernel calls. Added on branch
`claude/runtime-disaster-hardening-iso` (2026-05-31), extending the existing
19-harness CBC core receipt (`cbc_runtime_core_kani_v1`).

## Environment

- Date: 2026-05-31
- Branch: `claude/runtime-disaster-hardening-iso`
- Tool: `cargo-kani 0.60.0`
- Crate: `rust-runtime/crates/zenodex-runtime-core`

## Command

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani --output-format terse -Z unstable-options --harness-timeout 10m -j 4 \
  --harness floor_div_i128_is_total \
  --harness mul_div_floor_is_total \
  --harness checked_add_total_and_exact
```

## Result (see `kani_run.txt`)

```text
Complete - 3 successfully verified harnesses, 0 failures, 3 total.
```

| Harness | Property proved |
|---------|-----------------|
| `floor_div_i128_is_total` | **TOTALITY over the full symbolic i128 × i128 domain**: `floor_div_i128` never panics/overflows/traps for ANY `(numerator, denominator)`. This machine-proves the D-1 fix (commit `c1cb1e2b`): the `i128::MIN / -1` overflow and div-by-zero are excluded by the guards before the `/`/`%`. (44 checks) |
| `mul_div_floor_is_total` | TOTALITY: `mul_div_floor` never panics — the `denominator == 0` guard and `checked_mul` make overflow/div-by-zero typed rejects. (36 checks) |
| `checked_add_total_and_exact` | `checked_add` is total and returns `Ok` iff the native checked op is `Some` (fail-closed on overflow, never wrap/panic). (8 checks) |

## Scope / honest limitation

Floor **correctness** (the `n = q*d + r`, `sign(r)==sign(d)`, `|r|<|d|` relationship)
is **NOT** machine-proved here: relating a symbolic 128-bit quotient back to the
dividend via multiplication is intractable for Kani's bit-blasting SAT backend,
even with concrete divisors (the quotient remains a symbolic 128-bit value;
`bitwuzla` is not a supported solver in this Kani, and SAT solvers time out on
symbolic 128-bit division/multiplication). Floor semantics — including negative
operands and the `MIN/-1` edge — are covered by the unit tests in `arith::tests`.

Kani here contributes the property unit tests cannot: **totality over the entire
input domain** (the no-panic-on-consensus-path CBC contract as a machine proof).
