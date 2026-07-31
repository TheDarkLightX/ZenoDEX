# FCIS M6 B08 arithmetic-refinement plan

## Goal

Check the five bounded arithmetic obligations used by the unmounted SRGD
candidate:

1. `q * w` is inside the admitted amount width.
2. `r * w < D^2`.
3. `base <= amount`.
4. Every selected allocation amount is at most `amount`.
5. A selector score remains inside its admitted signed range.

## Environment

- Rust/Kani: Kani 0.60.0 with the repository Rust toolchain.
- SMT solvers: Z3 and CVC5, both invoked on the same checked SMT-LIB file.
- Production amount: `AmountU256(BigUint)` with admission `0 <= amount < 2^256`.
- Denominator: `D = 10_000`.

## Refinement decomposition

- `formal/fcis_m6_b08_arithmetic` is a dependency-free, heap-free Rust model.
  Its Kani amount carrier is `u16`, and all products use checked `u32` arithmetic.
- The embedding maps a model value `x` to production `BigUint::from(x)`.
  Therefore every Kani model input is a strict subset of the admitted U256
  production domain. Kani evidence is machine evidence for that refinement
  subset, not a claim that it explored all 256-bit values.
- `formal/fcis_m6_b08_arithmetic/srgd_bounds.smt2` states the same equations
  over mathematical integers with `0 <= amount <= 2^256 - 1`, `0 <= w <= D`,
  valid Euclidean decomposition, valid residual-seat selection, and the
  production signed deficit bounds. Each negated obligation must be `unsat`.
- `check_srgd_bounds.py` deterministically renders one query file at a time from the same SMT-LIB source and runs each through Z3 and CVC5,
  rejects any `unknown`, timeout, solver error, or non-`unsat` query, and
  records the solver output in the B08 evidence directory.

## Proof/check sketch

- Establish `amount = D*q + r`, `0 <= r < D`, and `0 <= w <= D`.
- Derive `q*w <= amount` and therefore `q*w < 2^256`.
- Derive `r*w <= (D-1)*D < D^2`; the strict SMT query uses the exact
  production bound `r*w >= D^2` as its contradiction target.
- Define `base = q*w + floor(r*w/D)` and use `w <= D` plus the Euclidean
  decomposition to show `base <= amount`.
- Require selected bonus bits to be supported by a positive residual and to
  have exactly `floor(sum(r_i)/D)` seats. With the three policy weights
  summing to `D`, the resulting amounts sum to `amount`; nonnegative sibling
  amounts then imply each allocation is at most `amount`.
- Bound each selector score as `deficit + fraction` with
  `-D < deficit < D` and `0 <= fraction < D`, giving
  `-D < score < 2*D`.

## Failure policy

Any Kani timeout, unsupported feature, solver `unknown`, solver error, or
failed obligation leaves B08 incomplete. No acceptance gate is weakened to
convert such a result into supporting evidence.

## Open boundary

This task does not replace a fixed-width U256 library refinement, production
mount, runtime authority proof, or value-moving integration. B09 remains
responsible for Python/Rust/independent-oracle parity.
