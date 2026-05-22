# Cubic Sum Curve Analysis: K(x,y) = x·y·(p·x + q·y)

## Executive Summary

Deep analysis of the cubic sum AMM curve reveals a **fundamental impossibility theorem** and identifies the curve's true value proposition: **temporal arbitrage through volume capture**.

### Key Discoveries

1. **Impossibility Theorem**: No static curve can improve both IL and slippage vs CPMM simultaneously
2. **Cubic trades IL for volume**: 33% better slippage but 2-11% worse IL depending on price move
3. **Time heals IL**: For hold periods >90 days with elastic demand, cubic dominates CPMM
4. **Novel primitive**: p/q asymmetry enables directional pools

---

## 1. Mathematical Properties

### The Invariant
```
K(x,y) = x · y · (p·x + q·y) = p·x²·y + q·x·y²
```

### Spot Price
```
P = dy/dx = -y(2px + qy) / (x(px + 2qy))
```

### Key Characteristics
| Property | CPMM | Cubic Sum (p=q=1) |
|----------|------|-------------------|
| Degree | 2 | 3 |
| Curvature at balance | 2/x | 4/(3x) |
| Relative slippage | 1.0x | **0.67x** (33% better) |
| Boundary behavior | xy = k | x²y or xy² ~ K |

---

## 2. The Fundamental Impossibility

### Theorem
> There exists no static AMM curve f(x,y) = K that achieves both:
> - Lower slippage than CPMM for same reserves
> - Lower impermanent loss than CPMM for same price move

### Status (fail-closed)
This repo treats the *global* statement above (“no static curve can improve both IL and slippage vs CPMM” for all curves,
all trade sizes, all price moves) as an **evidence-backed hypothesis** (not a Lean-proved theorem):
- Empirical sweeps over multiple curve families support a monotone IL↔slippage tradeoff (`analysis/curve_family_il_slippage_analysis.py`).
- Prior art connects AMM design directly to an IL/slippage tradeoff (see references at the end).

However, we *do* have a **Lean-proved local tradeoff** for the restricted power-family `K = x*y*(x+y)^α` (which includes
the symmetric cubic-sum curve as `α=1`). See:
- `docs/AMM_POWER_FAMILY_LOCAL_TRADEOFF_WHITEPAPER.md`
- Lean proof: `lean-mathlib/Proofs/ImpossibilityTheorem.lean`

To promote the *global* statement to “THEOREM (formal)”, the next step is to:
- Pin down **quantifiers + comparison metric** (spot-depth vs average execution, which trade sizes, which price moves).
- Extend beyond the `K = x*y*(x+y)^α` family and/or beyond local (2nd-order) balance analysis.

### Proof Intuition
Both properties are determined by **curvature**:
- Higher curvature → tighter liquidity concentration → better slippage
- Higher curvature → more aggressive rebalancing → worse IL

The tradeoff is monotonic. You can only choose WHERE on the spectrum to sit.

### Curve Family Analysis
| Curve | α Parameter | Slippage vs CPMM | IL vs CPMM |
|-------|-------------|------------------|------------|
| Constant Sum | -∞ | Much better | Much worse |
| Cubic Sum | 1 | 33% better | 2-11% worse |
| **CPMM** | **0** | **Baseline** | **Baseline** |
| Inverse blend | -0.5 | 15% worse | 25% better |

---

## 3. Impermanent Loss Comparison

### Numerical Results
| Price Move | CPMM IL | Cubic IL | Penalty |
|------------|---------|----------|---------|
| 1.5x | -2.02% | -3.00% | +0.98% |
| 2.0x | -5.72% | -8.35% | +2.63% |
| 3.0x | -13.40% | -18.95% | +5.55% |
| 5.0x | -25.46% | -34.41% | +8.95% |
| 10.0x | -42.50% | -54.14% | +11.64% |

**Initial hypothesis (lower IL at extremes) was REFUTED.** Cubic has higher IL at ALL ranges.

---

## 4. The Volume Compensation Model

### Key Insight
IL is a **terminal event** (realized at exit), but fees accumulate **continuously**.

### Breakeven Formula
```
Cubic profitable when: H × τ × f × (k - 1) > ΔIL

Where:
  H = holding period (days)
  τ = daily turnover (volume/TVL)
  f = fee rate
  k = volume multiplier from lower slippage
  ΔIL = IL penalty vs CPMM
```

### Volume Multiplier from 33% Slippage Reduction
| Demand Elasticity | Volume Multiplier |
|-------------------|-------------------|
| Inelastic (ε=0.5) | 1.22x |
| Unit elastic (ε=1.0) | 1.49x |
| Elastic (ε=1.5) | 1.82x |
| Highly elastic (ε=2.0) | 2.23x |

### Breakeven Holding Periods
At 0.3% fee rate, 50% daily turnover:

| Demand Type | 2x Price Move | 5x Price Move |
|-------------|---------------|---------------|
| Inelastic | 79 days | 269 days |
| Unit elastic | 36 days | 121 days |
| Elastic | 21 days | 72 days |
| Highly elastic | 14 days | 49 days |

Tooling:
- Breakeven calculator: `tools/cubic_lp_breakeven_analysis.py`
- Fee sweep/optimizer (isoelastic cost model): `tools/cubic_fee_optimization.py`

---

## 5. Optimal Use Cases

### RECOMMENDED: Cubic Sum Curve
| Use Case | Why |
|----------|-----|
| **Stablecoin pairs** (USDC/USDT) | Low volatility, high volume, elastic arb flow |
| **Wrapped assets** (WBTC/renBTC) | Tight peg, frequent small trades |
| **Aggregator-routed pairs** | Highly elastic demand captures volume premium |
| **Passive LPs (>90 day horizon)** | Time allows fee accumulation to overcome IL |

### NOT RECOMMENDED: Use CPMM Instead
| Use Case | Why |
|----------|-----|
| **Volatile pairs** (ETH/altcoin) | High IL penalty, unpredictable moves |
| **Short-term LPs** (<30 days) | Insufficient time to accumulate fee premium |
| **Retail-dominated pools** | Inelastic demand, low volume multiplier |
| **Active rebalancing LPs** | Frequent exits realize IL |

---

## 6. The p/q Asymmetry: Directional Pools

### Novel Primitive
Setting p ≠ q concentrates liquidity asymmetrically:
- **p > q**: More liquidity where X is scarcer (bullish X)
- **p < q**: More liquidity where Y is scarcer (bullish Y)

### Concentration Point
```
Optimal concentration at price ratio ≈ √(q/p)
```

### Example Configurations
| Configuration | Concentration | Use Case |
|---------------|---------------|----------|
| p=1, q=1 | 1:1 | Pegged assets |
| p=2, q=1 | ~0.7:1 | Expect X appreciation |
| p=1, q=4 | ~2:1 | Expect Y appreciation |

### Risk Warning
Directional pools face **adverse selection**: Informed traders will trade against the pool's bias. Requires careful fee calibration.

---

## 7. Implementation Notes

### Integer Arithmetic
The curve requires solving a quadratic for exact-in swaps:
```python
# For K = xy(px + qy), finding y' given x' = x + dx:
# Quadratic: q*x'*y'^2 + p*x'^2*y' - K >= 0
a = q * x_new
b = p * x_new * x_new
D = b * b + 4 * a * K
y_new = ceil((sqrt(D) - b) / (2 * a))
```

### Existing Implementation
- Core: `src/core/cubic_sum_amm.py`
- Tests: `tests/core/test_cubic_sum_amm.py`

---

## 7.1 Discrete (Integer) Semantics: Overdelivery + Safety Sweeps

This repo’s consensus-critical semantics are **integer**, not continuous:
- Exact-in: choose minimal `y'` such that `K(x+dx,y') >= K(x,y)` (so `K` is monotone, not exactly constant).
- Exact-out: choose minimal `dx` such that executing exact-in yields `out >= dy`.

Two practical questions for a *verified integer DEX* are:
1. **How large is the exact-out “overdelivery gap”?** (`out_exec - dy`)
2. **Can rounding create trivial 2-swap extraction?** (A→B→A with fee=0)

Deterministic sweeps (p=q=1, fee=0):
- Grid `x,y ∈ [1..200]`, `dy ∈ {1,2,5,10}`:
  - CPMM exact-out gap: `gap_max=99`, `gap_avg≈1.24`
  - Cubic-sum exact-out gap: `gap_max=58`, `gap_avg≈0.62`
- 2-swap roundtrip sweep (`exact-in → exact-in`, `dx ∈ {1,2,5,10}`, `x,y ∈ [1..200]`):
  - CPMM: `profit_max=0`
  - Cubic-sum: `profit_max=0`

Reproduce:
```bash
python3 tools/curve_comparison_sweep.py --grid-min 1 --grid-max 200 --dx 1,2,5,10 --dy 1,2,5,10 --out runs/curve_sweep.json
```

---

## 8. Research Questions

### Open Problems
1. **Optimal p/q selection**: Can historical data predict best parameters?
2. **Dynamic parameters**: Safe mechanisms to update p/q without MEV vectors?
3. **Fee optimization**: What fee rate maximizes LP returns for cubic?
4. **Multi-asset extension**: K(x,y,z) = xyz·(px + qy + rz)?

### Conjectures
1. **Conjecture 1**: Cubic + dynamic fees could achieve Pareto improvement over CPMM
2. **Conjecture 2**: The p/q ratio should track implied volatility for optimal IL/volume tradeoff
3. **Conjecture 3**: Hybrid curves (cubic near balance, CPMM at extremes) may dominate both

---

## 9. Conclusions

### The Cubic Sum Curve Is:
- **NOT** a universal improvement over CPMM
- **NOT** lower IL (it's higher at all ranges)
- **IS** a volume optimization play
- **IS** optimal for specific use cases (stables, long-horizon, elastic demand)
- **IS** a novel primitive enabling directional pools

### Decision Rule
```
Use Cubic when: Expected fee premium from volume > Expected IL penalty
               = (k - 1) × H × τ × f > ΔIL
```

### The Meta-Insight
> The cubic sum curve reveals that AMM design is not about minimizing IL; it's about **maximizing LP returns**, which is a function of volume, fees, AND IL. Different curves optimize different points in this tradeoff space.

---

## References (prior art)

- Wu & McTighe, “Constant Power Root Market Makers” (CFMM curve-family analysis; explicit IL↔slippage tradeoff).  
  `https://arxiv.org/abs/2205.07452`
- Engel & Herlihy, “Loss and Slippage in Networks of Automated Market Makers” (formal slippage/loss definitions; “costs can be shifted around but never fully eliminated”).  
  `https://arxiv.org/abs/2110.09872`
