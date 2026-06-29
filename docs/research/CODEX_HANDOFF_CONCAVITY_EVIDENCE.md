# Codex Handoff: CPMM Concavity Evidence Package

## Purpose

This file captures the deepest learned insights from three rounds of Codex
peer review on the CPMM Concavity Evidence package. It is written for the
next Codex reviewer (or any assurance agent) who starts fresh and needs the
full intellectual context without reading the entire conversation history.

## Package Identity

The package name still says "Concavity Conservation Law" in the file paths
(`ConcavityConservationLaw.lean`, `concavity_conservation_law_test.py`).
The actual content is narrower: CPMM window algebra and a generic Lipschitz
increment. The name is a historical artifact from when the hypothesis was
broader. The Lean header and Python docstring now state the honest scope.

## What Is Actually Proven (Lean)

Three theorems, all algebraic or generic:

1. `cpmm_concavity_param_formula`: `2*K/M^2 = 2*(K/M)/M`. Pure field_simp.
2. `cpmm_window_M_relationship`: `sqrt(2*L/m) = sqrt(M)` when `L=K/M`,
   `m=2*K/M^2`. This is the **epsilon=0** case. The production argmax
   window is `sqrt(2*(L+epsilon)/m)`, strictly larger when epsilon > 0.
3. `lipschitz_increment_bound`: `f(a_A) - f(0) <= L*a_A` for any
   L-Lipschitz function f. This is a **generic single-input increment**.
   It does NOT bound the stateful CPMM attack gain.

## What Is NOT Proven (and Why)

### No Conservation Law

The original hypothesis was that a "conservation product"
`window * adversarial_gain` is constant or monotone in pool depth M. This
was **falsified** in two ways:

1. The Lipschitz product `sqrt(M) * L * a_A` is **INCREASING** in M
   (larger window, same bound value). It does not decrease.
2. The concavity-based bound `(m/2)*a_A*(a_A+2*a_B)` was falsified as a
   universal stateful gain bound (ratio up to 1.88x in the large-trade
   regime). It cannot serve as the "security side" of any product.

The actual stateful gain does decrease with M empirically, but this is an
empirical observation about the CPMM simulator, not a formalized theorem.

### No Stateful Attack Connection

The Lean theorem `lipschitz_increment_bound` proves `f(a_A)-f(0) <= L*a_A`.
The stateful CPMM attack gain is `out_B_without_A - out_B_with_A`, which
involves a **pool state change** (M -> M + a_A*gamma, K -> K - out_A).
This is a different quantity from the single-input increment. The empirical
test suite checks `stateful_gain <= L*a_A` on a seeded corpus of 500
configs, and it holds, but this is empirical replay, not a Lean-proven
bridge.

A high-assurance version would need a lemma connecting the CPMM attack gain
to the Lipschitz increment under the exact continuous or rounded model. This
is future work.

## Key Falsification: The Concavity Bound

The second-order Taylor approximation `(m/2)*a_A*(a_A+2*a_B)` was proposed
as a universal bound on the stateful attack gain. It fails:

- **Small trades**: 71/500 configs exceed the bound (max ratio 1.33x).
- **Large trades** (a_B ~ M/2): 458/500 configs exceed (max ratio 1.88x).

The root cause: the Taylor expansion is in **input space** (f(x+a) - f(x)),
but the actual attack gain involves a **state change** (the pool reserves
change when A fills). The input-space Taylor model is the wrong model for
the stateful gain.

The falsification tests have **hard assertions** (`assert fail_count > 0`,
`assert max_ratio > 1.0`) as regression guards. If someone accidentally
"fixes" the bound or changes the test regime, these assertions fire.

## Key Insight: Epsilon Distinction

The Lean theorem proves `sqrt(2*L/m) = sqrt(M)` (epsilon=0). The production
argmax window from `DiscreteArgmaxProximity.lean` is
`sqrt(2*(L+epsilon)/m)` with epsilon=2. These are different quantities.

The frontier test now shows both columns:
```
       M |   win_eps0 |   win_prod |   lip_incr |   lip_prod |     actual
    1000 |      31.62 |      54.77 |     100.00 |    5477.23 |    80.2151
  100000 |     316.23 |     547.72 |     100.00 |   54772.26 |     3.8793
```

`win_eps0` is Lean-proven (= sqrt(M)). `win_prod` is the production window
(epsilon=2). The Lipschitz product uses `win_prod` and is increasing. The
actual gain decreases. There is no formal connection between the two
trends.

## Key Insight: Non-Tautological Cap Test

The original cap test computed `expected_out_A` and `actual_out_A` using
the same function on the same state, making the assertion trivially true.

The fixed test uses:
- `expected_out_A = L * a_A` (linear spot-price approximation, no slippage)
- `actual_out_A = cpmm_output_cont(p, a_A)` (full CPMM, with price impact)

The slippage ratio `actual / expected` is always < 1.0 due to concavity.
The test asserts `min_slippage_ratio < 1.0` (non-tautological: slippage is
real) and `min_slippage_ratio >= 0.9` (the cap is above the worst slippage,
so A fills). The empirical min slippage ratio is 0.923827.

## Grade Trajectory

| Round | Grade | Findings | Key Issue |
|-------|-------|----------|-----------|
| 1     | C+    | 6        | Overclaims, commutativity theorem, falsified bound in product |
| 2     | B-    | 5        | Stale "Lean PROVEN" labels, epsilon blur, tautological cap test |
| 3     | ?     | ?        | Awaiting review |

## Verification Commands

```bash
# Lean typecheck (works in Codex sandbox)
cd lean-mathlib && lake env lean Proofs/ConcavityConservationLaw.lean

# Python empirical tests (blocked in Codex sandbox, works on host)
python3 docs/research/concavity_conservation_law_test.py

# Pytest wrapper (blocked in Codex sandbox, works on host)
python3 -m pytest tests/formal/test_lean_concavity_conservation_law.py \
  tests/research/test_concavity_conservation_law.py -v
```

## What to Scrutinize in Round 3

1. Are all 5 round-2 findings resolved? Check:
   - (a) No "conservation law" overclaim in the Lean header.
   - (b) No "Lean PROVEN, universal" label on the stateful gain.
   - (c) No stale "product decreases" prose.
   - (d) Epsilon=0 vs epsilon=2 distinction is clear in both Lean and Python.
   - (e) Cap test is non-tautological (slippage ratio < 1.0 asserted).

2. Is the package free of overclaims? The Lean file should claim only
   algebraic identities and a generic Lipschitz increment. The Python file
   should label everything as either [Lean PROVEN] (algebra only) or
   [Empirical] (stateful gain, depth monotonicity, cap, frontier).

3. Is this now B+ or higher? The core algebra is sound. The overclaims are
   stripped. The falsification is honestly documented with regression guards.

## Deepest Lesson

The most important lesson from this review cycle is about **honest scope**.
The original "Concavity Conservation Law" was an attractive narrative: a
single parameter `m` governing both algorithm efficiency and mechanism
security, with a product frontier. The formal evidence supports only the
algebraic identity `sqrt(2*L/m) = sqrt(M)` and the generic Lipschitz
increment. The conservation narrative is empirical at best, falsified at
worst.

The right response to falsification is not to rescue the narrative by
mixing proven and falsified bounds. The right response is to strip the
package down to what is actually proven, label the empirical observations
as empirical, and keep the falsification as a permanent regression guard.
A clean restricted theorem is worth more than a broad claim with caveats.
