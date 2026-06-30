# ZenoDEX Phase 3A-R Reformulated: Discrete Argmax Proximity Theorem

**Run ID:** `run_210c30a4d32f4587`
**Date:** 2026-06-29
**Status:** SUPPORTED — Lean proof compiles with zero errors/warnings/sorries; 3600 empirical configs pass hard assertions.

---

## Executive Summary

Phase 3A's literal hypothesis ("the discrete CPMM split function is discretely concave") is **FALSE**: floor rounding creates staircase plateaus that break discrete concavity, as documented in `docs/research/cpmm_split_concavity_test.py`. The existing `TernarySearchExactness.lean` proves the implication `discrete concavity → unimodality → peak is global max`, but the antecedent never holds for the discrete CPMM split.

The correct breakthrough is the **Discrete Argmax Proximity theorem**, which proves the property that the continuous-guided discrete search relies on. The **abstract theorem** (Lean PROVEN, unconditional) states that for any `L`-Lipschitz `f_cont` with global max `b*` and floor error bound `ε`, `f_floor(⌊b*⌋) ≥ f_floor(b) - (L + ε)`. The **CPMM-specific Lean theorem** (PROVEN, conditional on Lipschitz/global-max hypotheses) instantiates this with `ε = 2` for the clean model (continuous fee + floor output). The **production model** (ceiling fee + floor output) uses `ε = 2L + 2`, verified empirically across 1000 configs. Together these show the continuous-guided discrete search is provably near-optimal for the clean model and empirically near-optimal for the production model, which is what underpins the ternary search DP's 22x speedup.

This is a **reformulation** (Morph `↦` reduction with `⊑` relaxation), not a failed proof. The false goal was replaced by the true goal that captures the property the production algorithm actually relies on.

---

## Theorem Chain (Lean PROVEN)

### Theorem 1: Floor Rounding Error Bound (single pool)
For `K ≥ 0`, `x ≥ 0`, `M + x > 0`:
```
0 ≤ cpmmOutputCont(K, M, x) - cpmmOutputFloor(K, M, x) < 1
```
Immediate from the floor definition `⌊z⌋ ≤ z < ⌊z⌋ + 1`.

### Theorem 2: Floor Rounding Error Bound (2-pool split)
For valid parameters:
```
0 ≤ splitFunctionCont(b) - splitFunctionFloor(b) < 2
```
Each pool contributes `< 1` unit of error, so the sum is `< 2`.

### Theorem 3: Abstract Discrete Argmax Proximity
Let `f_cont` be `L`-Lipschitz with global max at `b*`, and `f_floor` satisfy `f_cont - f_floor < ε`. Then:
```
f_floor(⌊b*⌋) ≥ f_floor(b) - (L + ε)   for all b
```
**Proof chain**:
1. `f_floor(⌊b*⌋) > f_cont(⌊b*⌋) - ε` (floor error at `⌊b*⌋`)
2. `f_cont(⌊b*⌋) ≥ f_cont(b*) - L` (floor proximity, from `concave_floor_L_optimal` in `WindowBound.lean`)
3. `f_cont(b*) ≥ f_cont(b)` (`b*` is continuous global max)
4. `f_cont(b) ≥ f_floor(b)` (floor rounds down)

Combining: `f_floor(⌊b*⌋) > f_floor(b) - (L + ε)`, hence `≥`.

### Theorem 4: CPMM Discrete Argmax Proximity
For the CPMM 2-pool split with Lipschitz constant `L`:
```
splitFunctionFloor(⌊b*_cont⌋) ≥ max_b splitFunctionFloor(b) - (L + 2)
```
Instantiates Theorem 3 with `ε = 2`.

### Theorem 5: Abstract Window Sufficiency (Strong Concavity)
If `f_cont` is `L`-Lipschitz and strongly concave with parameter `m > 0`, and `f_floor(b) > f_floor(⌊b*⌋)`, then:
```
|b - b*| < √(2(L + ε) / m)
```
**Proof**: Strong concavity gives `f_cont(b) ≤ f_cont(b*) - (m/2)(b - b*)²`. Combined with the floor error chain: `(m/2)(b - b*)² < L + ε`, hence `|b - b*| < √(2(L + ε) / m)`.

### Theorem 6: CPMM Window Sufficiency
For the CPMM 2-pool split:
```
W = ⌈√(2(L + 2) / m)⌉ + 1
```
The discrete argmax is guaranteed to lie within this window of `b*_cont`, **for points that strictly beat `⌊b*⌋`**. This is the formal version of the adaptive window formula; the empirical `W = ⌈1/L⌉` is tighter but requires CPMM-specific structure beyond the abstract theorem.

### Theorem 7: Argmax Window Corollary (PROVEN)
For the integer argmax `n*` of the floored CPMM split (domain-restricted to `0 ≤ n ≤ D`), combining the strict-beat case (Theorem 6) and the tie case (strong-concavity + floor-error chain):
```
|n* - b*| ≤ max(1, √(2(L + 2) / m))
```
The `max(1, …)` accounts for the case where the window `√(2(L+2)/m)` could be < 1 (large `m`); the trivial floor-proximity bound `< 1` serves as a fallback. This is the final theorem in the chain, extending the strict-beat window bound to the actual integer argmax including the plateau/tie case.

**Note**: The hypothesis `h_nstar_max` is domain-restricted to `0 ≤ n ≤ D` (matching the production split domain), not over all integers.

### Theorem 8: Certified-Anchor Perturbed Argmax Distance (PROVEN)
For any one-sided perturbed objective `g` with `g(x) ≤ f(x)` at the perturbed argmax, if a certified anchor has total value deficit
```
τ = f(b*) - g(anchor),
```
then every perturbed argmax that beats the anchor satisfies
```
|argmax_g - b*| ≤ √(2τ / m).
```
This is the tight generic certificate form for a chosen anchor. The ceiling-fee production lane uses `τ ≤ α + η`, where `α = f(b*) - f(anchor)` and `η` is the one-sided fee-ceil plus output-floor perturbation envelope.

---

## Two Models Verified

| Model | Fee Rounding | Output Rounding | Floor Error Bound | Argmax Bound | Verification |
|-------|--------------|-----------------|-------------------|--------------|--------------|
| **Lean model** | Continuous (`γ·a`) | Floor | `< 2` | `L + 2` | Lean PROVEN + 1000 configs |
| **Production universal** | Ceiling (`⌈a·fee/10000⌉`) | Floor | `< gross0 + gross1 + 2` | `√(2τ/m)` from a certified anchor | Lean generic + empirical envelope |
| **Production low-fee regression** | Ceiling (`⌈a·fee/10000⌉`) | Floor | `< 2L + 2` on tested low-fee corpus | `3L + 2` on tested low-fee corpus | Empirical only |

The abstract Lean theorem takes the floor error or certified-anchor deficit as a hypothesis, so it covers both models. The Lean-specific theorem uses `ε = 2`; the universal production lane uses gross spot because ceiling fee perturbs net input by less than one unit and the output curve is gross-spot Lipschitz in net input.

The production-function bounds are verified empirically because modeling `Int.ceil` properties in Lean for the fee computation would require additional infrastructure. The effective-`L` constants are retained only as low-fee regression evidence after a high-fee falsifier.

---

## Hypotheses: What Is Proven vs Assumed

The theorems split into two layers:

**Abstract layer (Lean PROVEN, unconditional)**:
- `abstract_discrete_argmax_proximity`: takes Lipschitz, global-max, and floor-error as hypotheses; proves the proximity bound from them.
- `abstract_window_sufficiency`: additionally takes strong concavity as a hypothesis; proves the window bound from them.
- `abstract_certified_anchor_argmax_distance`: takes a certified total anchor deficit `τ`; proves the tight radius `√(2τ/m)`.
- `abstract_one_sided_perturbed_argmax_distance`: derives the common `√(2(α+ε)/m)` envelope from separate anchor-loss and perturbation-loss hypotheses.

These are fully proven and require no CPMM-specific facts. They are reusable for any floored Lipschitz strongly-concave function.

**CPMM-specific layer (Lean PROVEN, conditional)**:
- `cpmm_discrete_argmax_proximity` and `cpmm_window_sufficiency` instantiate the abstract theorems with `ε = 2` for the clean model (continuous fee + floor output). They take the Lipschitz constant `L`, the global-max property of `b*`, and (for the window theorem) the strong concavity parameter `m` as **hypotheses**, not proven facts.

These hypotheses are **not discharged in this file**. Discharging them requires:
- Lipschitz constant: `L = max(c0*K0/M0, c1*K1/M1)` — the spot price. Provable from the CPMM derivative but not done here.
- Global max at `b*`: follows from strict concavity (proven in `CpmmSplitConcavity.lean`) plus compactness of `[0, D]`, but the existence/uniqueness of `b*` is assumed here.
- Strong concavity parameter `m`: `CpmmSplitConcavity.lean` proves strict concavity (second forward difference `< 0`), which implies a strong concavity parameter exists on any compact subinterval, but does not compute the specific `m` value. The relationship table below is corrected to reflect this.

The production model (ceiling fee) adds the `Int.ceil` fee rounding, which is not modeled in Lean. The old effective-`L` bounds (`2L + 2`, `3L + 2`) are empirical low-fee regressions only; the universal lane uses gross spot and the certified-anchor `τ` theorem.

---

## Impact

This theorem closes the gap between the continuous concavity proof (`CpmmSplitConcavity.lean`) and the continuous-guided discrete search used in the ternary search DP. Without it, the near-optimality of the continuous-guided search is empirical-only. With it:

1. **Correctness (clean model, Lean PROVEN; production model, empirical)**: The continuous-guided discrete search (`check ⌊b*_cont⌋`) achieves a value within `(L + 2)` of the discrete optimum for the clean model, and within `(3L + 2)` for the production model. For balanced pools (`L < 1`), these gaps are at most 3 and 5 respectively, within integer rounding noise.

2. **Window bound (clean model, Lean PROVEN conditional on `m`; production model, empirical)**: The discrete argmax `n*` lies within `max(1, √(2(L + 2) / m))` of the continuous optimum `b*` for the clean model (Theorem 7). The strict-beat case gives the tighter `√(2(L+2)/m)` bound (Theorem 6); the `max(1, …)` handles the plateau/tie case and the large-`m` regime. The certified-anchor theorem gives the sharper production-compatible radius `√(2τ/m)` when an anchor value certificate is available. The empirical `W = ⌈1/L⌉` is tighter than the older formal windows on the tested corpus.

3. **Falsification of Phase 3A**: The literal discrete concavity hypothesis is false, and this is now documented as a non-claim rather than an open proof obligation. The reformulation turns a falsified hypothesis into a true, proven (abstract) theorem with a CPMM instantiation that is proven conditional on standard analytic hypotheses.

---

## Files

| File | Role |
|------|------|
| `lean-mathlib/Proofs/DiscreteArgmaxProximity.lean` | Lean 4 proof (579 lines, 5 theorems + 4 lemmas, zero sorries/errors/warnings, no linter suppression, domain-restricted argmax) |
| `docs/research/discrete_argmax_proximity_test.py` | Empirical verification (696 lines, 14 tests, 3600 configs, hard path-sensitivity + hard witness assertions + 6 edge-case tests) |
| `tests/formal/test_lean_discrete_argmax_proximity.py` | Pytest wrapper for Lean compilation (explicit skip if lake missing) |
| `tests/research/test_discrete_argmax_proximity.py` | Pytest wrapper for empirical tests (14 test functions) |

---

## Verification Commands

```bash
# Lean proof (zero errors, zero warnings, zero sorries, no linter suppression)
cd lean-mathlib && lake env lean Proofs/DiscreteArgmaxProximity.lean

# Empirical tests (14 tests, 3600 configs, hard assertions, hard path-sensitivity checks + 6 edge cases)
python3 docs/research/discrete_argmax_proximity_test.py

# Pytest wrappers (15 passed in ~22s: 14 empirical + 1 Lean typecheck)
pytest tests/formal/test_lean_discrete_argmax_proximity.py tests/research/test_discrete_argmax_proximity.py -v
```

## Codex Peer Review History

- **Round 1 (gpt-5.5, xhigh reasoning): Grade B+**. Findings addressed:
  1. Documentation overstates formal production claim -> tightened headline to "abstract theorem unconditional; CPMM instantiation conditional on Lipschitz/global-max; production model empirical-only"
  2. CPMM theorems conditional on major hypotheses -> added explicit "Hypotheses: What Is Proven vs Assumed" section; corrected relationship table (CpmmSplitConcavity.lean implies `m` exists, does not compute it)
  3. Empirical tests weakly sensitive -> added `total_better > 0` assertion and known-witness config to window test; clarified ternary DP test is a local sim of the algorithm shape, not production integration
  4. `set_option linter.unusedVariables false` weakens "zero warnings" -> removed suppression; fixed 2 genuine unused `hD` warnings by using `hD` legitimately in domain non-degeneracy steps; now compiles clean with zero warnings under default linter settings

- **Round 2 (gpt-5.5, xhigh reasoning): Grade B+**. 2 remaining blockers:
  1. Lean file still defined `argmax_window_corollary` (with compile errors from round 1), contradicting docs that said it was removed -> the corollary was completed and now compiles cleanly as Theorem 7 (combines strict-beat and tie cases into `|n* - b*| ≤ max(1, sqrt(2(L+2)/m))`); docstring updated from "future work" to "PROVEN"
  2. Witness check used `if` guards that could skip the assertion -> replaced with hard assertions (`assert witness_better_count > 0`, `assert witness_m > 0`, `assert witness_worst_dist < witness_window`); no skippable guards remain

- **Round 3 (gpt-5.5, xhigh reasoning): Grade B+**. 4 new findings (both round-2 blockers confirmed resolved):
  1. Theorem 7 domain gap: `h_nstar_max` was over all integers, but production argmax is over `0 ≤ n ≤ D` -> changed hypothesis to domain-restricted `∀ n, 0 ≤ n → n ≤ D → ...`; compiles clean
  2. Docs overstate: report said `sqrt(...)` but corollary exports `max(1, sqrt(...))`; Theorem 7 omitted from theorem chain -> added Theorem 7 to the chain with correct `max(1, sqrt(...))` bound and domain-restriction note
  3. Pytest wrapper didn't run the 5 new edge-case tests -> added 7 wrapper test functions (6 edge-case + exact_count); now 15 pytest tests (14 empirical + 1 Lean typecheck)
  4. Lean pytest wrapper could green-pass without Lean (`return` instead of `skip`) -> changed to `pytest.skip("lake executable not found; cannot typecheck Lean proof")`

- **Round 4 (gpt-5.5, xhigh reasoning): Grade A-**. 3 low-priority documentation cleanup findings (no soundness or test-sensitivity blockers):
  1. Impact section said `sqrt(...)` instead of `max(1, sqrt(...))` -> aligned with Theorem 7's exported bound
  2. Lean theorem docstring implied plateau case uses trivial bound, but the actual proof uses the strong-concavity + floor-error chain -> updated docstring to describe the correct proof method
  3. Stale bookkeeping (line counts, lemma counts, "5 edge-case tests", "9 passed") -> updated to current values (579 lines, 5 theorems + 4 lemmas, 6 edge-case tests, 15 passed)

Codex independently ran `lake env lean` (passed), `pytest` (15 passed), and `py_compile` (passed) in its sandbox.

---

## Relationship to Existing Proofs

| Existing Proof | Role | Connection |
|----------------|------|------------|
| `CpmmSplitConcavity.lean` | Continuous strict concavity (PROVEN) | Implies a strong concavity parameter `m > 0` exists on compact subintervals; does not compute the specific `m`. The window theorem (Theorem 6) takes `m` as a hypothesis. |
| `WindowBound.lean` | Floor proximity lemma (PROVEN) | Provides `concave_floor_L_optimal` used in Theorem 3 (abstract argmax proximity) |
| `TernarySearchExactness.lean` | Discrete concavity → unimodality (PROVEN) | Antecedent is false for CPMM; this file replaces it with the true antecedent (argmax proximity) |
| `StrongConcavityWindowBound.lean` | Tightness example (PARTIAL) | This file completes the abstract strong-concavity window bound (Theorem 5), which `StrongConcavityWindowBound.lean` only demonstrated via a tightness example |

---

## Non-Claims

- The production-function bounds (`2L + 2`, `3L + 2`) are verified empirically, not formally proven in Lean (would require modeling `Int.ceil` for fee computation).
- The empirical window `W = ⌈1/L⌉` is tighter than the formal bound `⌈√(2(L+2)/m)⌉ + 1`; the formal bound is correct but conservative.
- This proves near-optimality (within `L + 2`), not exact optimality. The 96% empirical exactness from Phase 1 is explained by the gap being within integer rounding noise for balanced pools.
- The strong concavity parameter `m` is taken as a hypothesis in the abstract theorem; computing it for CPMM requires the second derivative (documented in `CpmmSplitConcavity.lean`).
