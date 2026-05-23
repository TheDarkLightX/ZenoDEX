# A Locally Verified Slippage-Impermanent Loss Tradeoff in the Power-Family AMM Curve

ZenoDex Research Whitepaper (draft)  
Version: v0.1 (January 16, 2026)

## Abstract

Automated market makers (AMMs) defined by constant-function invariants exhibit a well-known tension between *execution quality* (slippage / price impact) and *liquidity-provider (LP) return risks* (impermanent loss, IL). This document formalizes and **machine-verifies** a precise, *local* tradeoff for the power-family two-asset invariant

```text
K(x,y; α) := x · y · (x + y)^α    where α ∈ ℕ and n := α + 2.
```

We work in the standard frictionless, continuous arbitrage model and analyze second-order behavior around the balanced state `(x,y)=(1,1)` and external price `p=1`. Define:

- `r(p) := y/x`, the post-arbitrage reserve ratio as a function of external price `p`.
- `IL(p)`, the (continuous, fee-free) impermanent loss of an LP who initially deposits `(1,1)`, measured against a HODL baseline.

We prove (in Lean/Mathlib) that:

1) `r'(1) = n/2`, hence a natural “local slippage coefficient” at balance is `S(α) := (r'(1))⁻¹ = 2/n`.  
2) `IL''(1) = -n/8`, hence the positive quadratic IL curvature coefficient is `C(α) := -IL''(1)/2 = n/16`.  
3) The tradeoff product is constant:

```text
S(α) · C(α) = 1/8,
```

so within this family no `α>0` can improve both local slippage and local IL curvature relative to the constant-product market maker (CPMM, `α=0`).

This is a *local* theorem (second-order at balance) for a *specific* invariant family; it does not claim a universal optimality theorem over all AMM curves.

## 1. Background and Related Work

Constant-function market makers (CFMMs) provide on-chain exchange via an invariant `F(x,y)=k` governing reserve state; popular examples include:

- **CPMM (Uniswap v2)**: `x·y = k`.  
- **Constant-mean (Balancer)**: `∏ᵢ xᵢ^{wᵢ} = k`.  
- **Stableswap (Curve)**: a hybrid invariant designed for low-slippage around a target ratio.

Academic treatments of CFMMs and their properties include the general CFMM framework and analyses of loss/slippage tradeoffs and AMM networks.

This whitepaper’s contribution is **formal verification** (Lean/Mathlib) of a concrete local tradeoff identity for the power-family `K(x,y;α)=x·y·(x+y)^α`, which includes the symmetric cubic-sum invariant as the `α=1` special case.

## 2. Model and Definitions

### 2.1 Reserves, invariant, and external price

Let `x,y>0` be reserves of two assets `X,Y`. Consider the invariant family:

```text
K(x,y; α) := x · y · (x + y)^α,     α ∈ ℕ,     n := α + 2.
```

The homogeneous degree is `n`. We analyze price moves around the balanced state `(x,y)=(1,1)` with invariant level `K₀ = 2^α`.

Let `p>0` denote the external price of `X` in units of `Y` (i.e., `p = Y per X`). Under frictionless arbitrage, the pool is assumed to be at a state where the CFMM’s marginal price equals `p`.

### 2.2 Post-arbitrage reserve ratio `r(p)`

Define the reserve ratio

```text
r(p) := y/x.
```

For the power-family above, the equilibrium condition can be solved in closed form, yielding a quadratic formula in `r`. Writing `A := α + 1`, one convenient expression is:

```text
r(p) = ((p - 1)·A + √( (p - 1)^2·A^2 + 4p )) / 2.
```

(This is the `ratio` function in the Lean development.)

### 2.3 LP value and impermanent loss

Assume the LP initially deposits `(1,1)` at price `p=1`. Let `x_res(p)` be the post-arbitrage `x` reserve consistent with invariant `K₀` and ratio `r(p)`; then `y_res(p) = r(p)·x_res(p)`.

Define the LP’s pool value in `Y` units:

```text
V(p) := p·x_res(p) + y_res(p) = x_res(p) · (p + r(p)).
```

Define the HODL baseline value (holding the initial `(1,1)` outside the pool):

```text
V_hodl(p) := p + 1.
```

The (continuous, fee-free) impermanent loss function is:

```text
IL(p) := V(p) / V_hodl(p) - 1.
```

At balance, `IL(1)=0`.

## 3. Local Coefficients and Main Theorem

### 3.1 Local slippage coefficient at balance

We define a simple local “slippage coefficient” as the inverse slope of the post-arbitrage ratio map at balance:

```text
S(α) := (r'(1))⁻¹.
```

For CPMM (`α=0`), `r(p)=p`, so `r'(1)=1` and `S(0)=1`.

### 3.2 Local IL curvature coefficient at balance

Since `IL` is twice differentiable at `p=1`, its local expansion has a quadratic curvature term:

```text
IL(p) = IL(1) + IL'(1)·(p-1) + (1/2)·IL''(1)·(p-1)^2 + O((p-1)^3).
```

Since `IL''(1) < 0`, a natural positive coefficient is:

```text
C(α) := -IL''(1)/2.
```

### 3.3 Theorem (local tradeoff identity)

For the power-family `K(x,y;α)=x·y·(x+y)^α` with `n=α+2`, we have:

```text
r'(1) = n/2,        IL''(1) = -n/8,
S(α) = 2/n,         C(α) = n/16,
S(α)·C(α) = 1/8.
```

In particular, for any `α>0`:

- `S(α) < S(0)` (improved local slippage relative to CPMM), but
- `C(α) > C(0)` (worse local IL curvature relative to CPMM),

so no `α>0` in this family improves both local metrics versus CPMM.

## 4. Formal Verification Artifact (Lean/Mathlib)

The results above are verified in Lean (no `sorry`):

- Proof module: `lean-mathlib/Proofs/ImpossibilityTheorem.lean`
- Key theorems (Lean names):
  - `TauSwap.Impossibility.deriv2_il_one`
  - `TauSwap.Impossibility.tradeoff_coeff`
  - `TauSwap.Impossibility.tradeoff_vs_cpmm`

To check locally:

```bash
cd lean-mathlib
lake build Proofs.ImpossibilityTheorem
```

The repository proof root imports this module so `lake build` also checks it:

- `lean-mathlib/Proofs.lean`

## 5. Implications for Curve Design (ZenoDex)

### 5.1 Interpreting `α`

Within this family, increasing `α`:

- decreases `S(α)=2/n` (locally “deeper” response), and
- increases `C(α)=n/16` (locally worse IL curvature),

with a fixed product `S·C=1/8`. This clean identity is useful as a *design invariant* when exploring parameterized curves:
it makes explicit that local improvements in execution must be “paid for” by local IL curvature in this family.

### 5.2 Cubic-sum as `α=1`

The symmetric cubic-sum invariant corresponds to `α=1`:

```text
K(x,y) = x·y·(x+y),
S(1)=2/3, C(1)=3/16.
```

This aligns with numerical observations that the cubic-sum curve improves near-balance slippage but increases IL for
larger price moves in a fee-free, continuous model. (See `docs/CUBIC_SUM_CURVE_ANALYSIS.md` for empirical sweeps.)

### 5.3 Discrete integer semantics

ZenoDex ultimately uses **integer** arithmetic with deterministic rounding, and “slippage” and “IL” should be understood
as emergent from those discrete semantics plus fee rules. The theorem in this document is continuous and local; it does
not account for discrete rounding effects (e.g., exact-out overdelivery) or fee accumulation over time.

## 6. Limitations and Future Work

1) **Local only:** the theorem is second-order at `p=1`. Extending to global price moves and/or trade-size-dependent
execution metrics is nontrivial.  
2) **Family-specific:** this is not a theorem over all CFMM curves. It is a certified tradeoff identity for a single
parameterized family.  
3) **Asymmetry:** the more general cubic family `x·y·(p·x+q·y)` (directional weights) is not covered here.  
4) **Fees and time horizon:** empirically, a curve with worse IL may still dominate LP returns if lower slippage yields
higher volume and fee accrual. Formalizing such time-integrated comparisons is open work.

## References

- Uniswap v2 Core. *Uniswap v2 Core Whitepaper*, March 2020. https://docs.uniswap.org/whitepaper.pdf
- Balancer Labs. *Balancer Whitepaper*, September 2019. https://balancer.fi/whitepaper/ (PDF via Balancer GitBook)
- Michael Egorov. *StableSwap - Efficient Mechanism for Stablecoin Liquidity*, 2019. https://docs.curve.finance/references/stableswap/
- Angeris, Evans, Chitra. *Replicating Market Makers*. arXiv:2103.14769, 2021. https://arxiv.org/abs/2103.14769
- Engel, Herlihy. *Loss and Slippage in Networks of Automated Market Makers*. arXiv:2107.12484, 2021. https://arxiv.org/abs/2107.12484
- Wu, McTighe. *Constant Power Root Market Makers*. arXiv:2212.08261, 2022. https://arxiv.org/abs/2212.08261
