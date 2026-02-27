# Cubic-sum AMM (K = x*y*(x+y)) — Lean/Mathlib proof plan (exact-out minimality)

## Goal

Prove, for reserves `x>0`, `y>0`, and desired output `dy` with `0 < dy < y`, that the
exact-out quote `dx` produced by the cubic-sum algorithm is **minimal**:

- Let `K0 := K(x,y) = x*y*(x+y)` (baseline `p=q=1`).
- Let `y_target := y - dy`.
- Let `x1 := x + dx`.

Then:
1) `K(x1, y_target) ≥ K0` (sufficient for output `≥ dy` under exact-in semantics), and
2) for any `dx' < dx` (equivalently `x' = x + dx' < x1`), we have `K(x', y_target) < K0`
   (so output `< dy`), i.e. `dx` is minimal.

## Definitions to formalize

- Invariant:
  - `K(x,y) : Nat := x * y * (x + y)` (or general `p,q` later).

- Exact-in (spec definition):
  - `y_after(x,y,dx)` is the minimal `y'` such that `K(x+dx, y') ≥ K(x,y)`.
  - `out_exact_in(x,y,dx) := y - y_after(x,y,dx)`.

- Exact-out quote (algorithmic):
  - `dx` is defined as the minimal `dx` such that `K(x+dx, y_target) ≥ K(x,y)`.
  - Show this equals the “minimal dx such that exact-in output ≥ dy”.

## Key lemmas / structure

1) **Monotonicity in x** (fixed y):
   - For `y>0`, the function `x ↦ K(x,y)` is strictly increasing on `Nat`.
   - This gives a clean minimality argument for scanning/ceil proofs.

2) **Exact-in output condition ↔ K inequality at y_target**:
   - For fixed `x,y,dy` with `y_target = y-dy`:
     - `out_exact_in(x,y,dx) ≥ dy`  ↔  `y_after(x,y,dx) ≤ y_target`
     - `y_after(x,y,dx) ≤ y_target` ↔ `K(x+dx, y_target) ≥ K(x,y)`
   - The last step uses minimality of `y_after`: if `K(x+dx, y_target) ≥ K0` then the
     minimal `y_after` is `≤ y_target`; if `< K0` then every `y' ≤ y_target` fails.

3) **Quadratic form and ceil root** (for algorithm correspondence):
   - Expand `K(x,y_target) = x^2*y_target + x*y_target^2`.
   - For fixed `y_target`, consider the quadratic inequality:
     - `a*x^2 + b*x - K0 ≥ 0` with `a=y_target`, `b=y_target^2`.
   - Define the discriminant `D := b^2 + 4*a*K0`.
   - Show the algorithm’s `x1 = ceil( (-b + sqrt(D)) / (2*a) )` is the minimal `x1`
     satisfying the inequality (requires `Nat.sqrt`/`Int.sqrt` lemmas + ceil-div).

4) **From minimal x1 to minimal dx**:
   - Since `dx = x1 - x`, the minimality of `x1` among `x' ≥ x+1` translates directly
     to minimality of `dx` among positive integers.

## Practical proof strategy in this repo

- Start with the bounded-domain statement (to mirror Morph certification):
  - `∀ x y dy ≤ R, ...` with explicit `R` and `dx` bounded, using `Finset`/`Nat` search.
  - This is often easiest to discharge with `Finset.min'` and monotonicity.

- Then upgrade to the unbounded theorem:
  - Replace bounded search with `Nat.find` over the predicate `K(x+dx,y_target) ≥ K0`,
    using monotonicity to show existence and minimality.

## Notes / TODOs

- If we generalize to `K(x,y)=x*y*(p*x+q*y)`, the same shape applies with:
  - `K(x,y_target) = p*x^2*y_target + q*x*y_target^2` (still quadratic in `x`).
  - Adjust coefficients and discriminant accordingly.

- Hook point for proof-carrying code (optional future):
  - Add a Lean file certificate and fail-closed verification in a domain transition,
    as described in internal notes (not required for the current bounded Morph cert).

