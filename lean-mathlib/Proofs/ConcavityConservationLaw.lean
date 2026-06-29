/-
# CPMM Window Algebra, Lipschitz Increment, and Stateful Attack Bound

This file proves:
1. Two algebraic identities (concavity parameter, window-M relationship).
2. A generic Lipschitz increment bound for any L-Lipschitz function.
3. A stateful CPMM attack gain bound: the sacrifice attack gain is bounded
   by `L * a_A` where `L` is the spot price. This closes the formal gap
   between the generic Lipschitz increment and the exact stateful attack
   model.

## What Is Proven Here

1. `cpmm_concavity_param_formula`: algebraic identity `2*K/M^2 = 2*(K/M)/M`.
2. `cpmm_window_M_relationship`: algebraic identity `sqrt(2*L/m) = sqrt(M)`
   when `L = K/M` and `m = 2*K/M^2`. This is the epsilon=0 case. The
   production argmax window is `sqrt(2*(L+ε)/m)` (see DiscreteArgmaxProximity),
   which is strictly larger when ε > 0.
3. `lipschitz_increment_bound`: for any L-Lipschitz function f,
   `f(a_A) - f(0) <= L * a_A`. Generic single-input increment.
4. `cpmm_stateful_gain_bound`: for CPMM `f(x) = K*x/(M+x)` with K, M, a_A,
   a_B all positive, the stateful sacrifice attack gain
   `out_B_without_A - out_B_with_A <= K*a_A/M = L*a_A`.
5. `cpmm_stateful_gain_bound_with_fee`: the same bound with a fee parameter
   gamma, `gain <= gamma*K*a_A/M`, by substitution into theorem 4.

## What Is NOT Proven Here

- No conservation law: there is no theorem linking the window size to the
  adversarial gain via a shared product or frontier.
- No monotonicity: no theorem states that gain decreases with M.
- The second-order concavity approximation `(m/2)*a_A*(a_A+2*a_B)` is
  FALSIFIED empirically and is NOT included as a theorem.

## Stateful Attack Bound: Proof Sketch

For CPMM `f(x) = K*x/(M+x)` (fee-free), the sacrifice attack gain is:
  `gain = K*a_B/(M+a_B) - K*M*a_B/((M+a_A)*(M+a_A+a_B))`

The bound `L*a_A = K*a_A/M` minus the gain equals:
  `K*a_A * (M*(M+a_A)^2 + a_A*a_B*(2*M+a_A+a_B))`
  `/ (M*(M+a_A)*(M+a_B)*(M+a_A+a_B))`

The numerator is a product of non-negative factors:
  `K*a_A >= 0` (both positive)
  `M*(M+a_A)^2 >= 0` (M > 0, square >= 0)
  `a_A*a_B*(2*M+a_A+a_B) >= 0` (all positive)

The denominator is a product of positive factors. So the difference is
non-negative, proving `gain <= L*a_A`.

The fee-bearing case `f(x) = K*gamma*x/(M+gamma*x)` reduces to the fee-free
case by substituting `u = gamma*a_A`, `v = gamma*a_B`.

## Verification

Compile: `cd lean-mathlib && lake env lean Proofs/ConcavityConservationLaw.lean`
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.DiscreteArgmaxProximity
import Proofs.CpmmSplitConcavity

open Real

/-- **Lipschitz Increment Bound**: For an `L`-Lipschitz function, the
    single-input increment from `0` to `a_A` is bounded by `L * a_A`.

    This is a generic single-input increment theorem. The stateful CPMM
    attack gain bound is proven separately in `cpmm_stateful_gain_bound`
    below, which shows the exact sacrifice attack gain is bounded by `L*a_A`
    for the CPMM output function.

    The second-order concavity expression `(m/2) * a_A * (a_A + 2*a_B)` is
    not included as a theorem because the stateful-attack empirical suite
    falsifies it as a universal bound. -/
theorem lipschitz_increment_bound
    (f : ℝ → ℝ) (L a_A : ℝ)
    (hL : L ≥ 0) (hA : a_A ≥ 0)
    (h_lipschitz : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    : f a_A - f 0 ≤ L * a_A := by
  -- Domain contract: L >= 0 ensures the bound is nonneg (meaningful gain bound)
  have hL_nn : 0 ≤ L := hL
  have h_lip := h_lipschitz a_A 0
  have h_abs_le : |f a_A - f 0| ≤ L * a_A := by
    have h_eq : |a_A - 0| = a_A := by
      rw [sub_zero]; exact abs_of_nonneg hA
    rw [h_eq] at h_lip
    exact h_lip
  -- f(a_A) - f(0) <= |f(a_A) - f(0)| (by le_abs_self) <= L * a_A
  have h_le_abs : f a_A - f 0 ≤ |f a_A - f 0| := le_abs_self _
  linarith

/- ## Scope Note: Stateful Attack Bound

   `lipschitz_increment_bound` proves a GENERIC Lipschitz increment:
   `f(a_A) - f(0) <= L * a_A` for any L-Lipschitz function f.

   `cpmm_stateful_gain_bound` below proves the SPECIFIC stateful CPMM attack
   gain bound: `out_B_without_A - out_B_with_A <= K*a_A/M = L*a_A` for the
   exact CPMM model `f(x) = K*x/(M+x)`. This closes the formal gap between
   the generic Lipschitz increment and the stateful attack model.

   The concavity-based gain bound using the MINIMUM curvature `m`,
   `(m/2)*a_A*(a_A+2*a_B)`, is FALSIFIED empirically (ratio up to 1.88x)
   and is NOT included as a Lean theorem. The empirical scaling probe in
   `concavity_bounded_adversarial_test.py` uses `|f''(0)|` (MAXIMUM curvature
   at the margin), which gives a more conservative upper bound than `m`
   since `|f''(0)| >= m`. That probe is empirical only, not a Lean theorem. -/

/-- **CPMM Concavity Parameter Formula**: For `f(x) = K*x/(M+x)`,
    the strong concavity parameter at the margin (x = 0) is:
    `m = 2 * K / M^2 = 2 * L / M`

    where `L = K/M` is the spot price (Lipschitz constant).

    This connects the algorithm parameter `m` to the pool depth `M`:
    deeper pools (large M) have smaller `m`. -/
lemma cpmm_concavity_param_formula
    (K M : ℝ) (hK : K > 0) (hM : M > 0)
    : 2 * K / M^2 = 2 * (K / M) / M := by
  field_simp

/-- **CPMM Window-M Relationship (epsilon=0 case)**: For CPMM with spot
    price `L = K/M` and concavity parameter `m = 2*K/M^2`, the window
    `sqrt(2*L/m)` simplifies to `sqrt(M)`.

    This is the epsilon=0 algebraic identity. The production argmax window
    from `DiscreteArgmaxProximity` is `sqrt(2*(L+ε)/m)`, which is strictly
    larger when ε > 0. This theorem proves only the epsilon=0 case.

    This is an ALGEBRAIC IDENTITY, not a conservation theorem. It does NOT
    prove a monotonicity result, an optimal frontier, or a connection to
    adversarial gain. The Lipschitz product `sqrt(M) * L * a_A` is
    INCREASING in M, NOT decreasing. The empirical observation that actual
    stateful gain decreases with M is not formalized here. -/
theorem cpmm_window_M_relationship
    (K M : ℝ)
    (hK : K > 0) (hM : M > 0)
    : Real.sqrt (2 * (K / M) / (2 * K / M^2)) = Real.sqrt M := by
  have h_m : 2 * (K / M) / (2 * K / M^2) = M := by
    field_simp
  rw [h_m]

/-! ## Stateful CPMM Attack Gain Bound

The sacrifice attack: user A submits a trade that fills (changing the pool
state), then user B trades against the modified pool. The "gain" is the
difference between B's output without A (original pool) and B's output with
A (modified pool). This is the stateful attack model, distinct from the
generic Lipschitz increment.

For fee-free CPMM `f(x) = K*x/(M+x)`:
- `out_B_without_A = K*a_B / (M+a_B)`
- `out_B_with_A = K*M*a_B / ((M+a_A)*(M+a_A+a_B))`
- `gain = out_B_without_A - out_B_with_A`

The theorem proves `gain <= K*a_A/M = L*a_A` where `L = K/M` is the spot
price. The proof works by showing `L*a_A - gain` equals a fraction whose
numerator is a sum of non-negative terms and whose denominator is positive.
-/

/-- **CPMM Stateful Attack Gain Bound (fee-free)**: For CPMM `f(x) = K*x/(M+x)`
    with `K, M, a_A, a_B` all positive, the stateful sacrifice attack gain
    `out_B_without_A - out_B_with_A` is bounded by `K*a_A/M = L*a_A`.

    This is the formal bridge between the generic Lipschitz increment
    (`lipschitz_increment_bound`) and the exact stateful CPMM attack model.
    The gain is the difference between B's output trading against the
    original pool and B's output trading against the pool after A fills.

    Proof: `L*a_A - gain = K*a_A * (M*(M+a_A)^2 + a_A*a_B*(2*M+a_A+a_B))`
    `/ (M*(M+a_A)*(M+a_B)*(M+a_A+a_B))`. The numerator is non-negative
    (product of positives plus product of positives), and the denominator
    is positive. -/
theorem cpmm_stateful_gain_bound
    (K M a_A a_B : ℝ)
    (hK : K > 0) (hM : M > 0) (hA : a_A > 0) (hB : a_B > 0)
    : K * a_B / (M + a_B) - K * M * a_B / ((M + a_A) * (M + a_A + a_B))
        ≤ K * a_A / M := by
  -- All variables positive => all sums positive
  have hMA : 0 < M + a_A := by linarith
  have hMB : 0 < M + a_B := by linarith
  have hMAB : 0 < M + a_A + a_B := by linarith
  -- Denominator D = M*(M+a_A)*(M+a_B)*(M+a_A+a_B) is positive
  have hD : 0 < M * (M + a_A) * (M + a_B) * (M + a_A + a_B) :=
    mul_pos (mul_pos (mul_pos hM hMA) hMB) hMAB
  -- Key algebraic identity (verified by ring):
  -- K*a_A/M - gain = K*a_A * P / D
  -- where P = M*(M+a_A)^2 + a_A*a_B*(2*M+a_A+a_B)
  have h_identity :
    K * a_A / M - (K * a_B / (M + a_B) - K * M * a_B / ((M + a_A) * (M + a_A + a_B)))
    = K * a_A * (M * (M + a_A) ^ 2 + a_A * a_B * (2 * M + a_A + a_B))
      / (M * (M + a_A) * (M + a_B) * (M + a_A + a_B)) := by
    field_simp
    ring
  -- Prove P >= 0: sum of non-negative terms
  have hP : 0 ≤ M * (M + a_A) ^ 2 + a_A * a_B * (2 * M + a_A + a_B) := by
    have h_sq : 0 ≤ (M + a_A) ^ 2 := sq_nonneg _
    have h_term1 : 0 ≤ M * (M + a_A) ^ 2 := mul_nonneg (le_of_lt hM) h_sq
    have h_2M : 0 ≤ 2 * M + a_A + a_B := le_of_lt (by linarith)
    have h_term2 : 0 ≤ a_A * a_B * (2 * M + a_A + a_B) :=
      mul_nonneg (mul_nonneg (le_of_lt hA) (le_of_lt hB)) h_2M
    exact add_nonneg h_term1 h_term2
  -- Numerator K*a_A*P >= 0
  have hKA : 0 ≤ K * a_A := mul_nonneg (le_of_lt hK) (le_of_lt hA)
  have h_num : 0 ≤ K * a_A * (M * (M + a_A) ^ 2 + a_A * a_B * (2 * M + a_A + a_B)) :=
    mul_nonneg hKA hP
  -- Fraction num/D >= 0 since num >= 0 and D > 0
  have h_frac : 0 ≤ K * a_A * (M * (M + a_A) ^ 2 + a_A * a_B * (2 * M + a_A + a_B))
      / (M * (M + a_A) * (M + a_B) * (M + a_A + a_B)) :=
    div_nonneg h_num (le_of_lt hD)
  -- Close: the identity says RHS - LHS = h_frac >= 0, so LHS <= RHS
  linarith

/-- **CPMM Stateful Attack Gain Bound (with fee)**: For CPMM with fee
    `f(x) = K*gamma*x/(M+gamma*x)` with `K, M, a_A, a_B` all positive and
    `gamma in [0, 1]`, the stateful sacrifice attack gain is bounded by
    `gamma*K*a_A/M = L*a_A` where `L = gamma*K/M` is the spot price.

    This reduces to the fee-free case by substituting `u = gamma*a_A`,
    `v = gamma*a_B` into `cpmm_stateful_gain_bound`. -/
theorem cpmm_stateful_gain_bound_with_fee
    (K M a_A a_B gamma : ℝ)
    (hK : K > 0) (hM : M > 0) (hA : a_A > 0) (hB : a_B > 0)
    (hgamma : 0 ≤ gamma ∧ gamma ≤ 1)
    : K * gamma * a_B / (M + gamma * a_B)
        - K * M * gamma * a_B / ((M + gamma * a_A) * (M + gamma * a_A + gamma * a_B))
        ≤ gamma * K * a_A / M := by
  -- Fee-free case: gamma=1. Fee case: substitute u=gamma*a_A, v=gamma*a_B.
  -- If gamma = 0, both sides are 0 and the inequality holds trivially.
  by_cases hg : gamma = 0
  · -- gamma = 0: both sides are 0
    simp [hg]
  -- gamma > 0: use the fee-free theorem with u = gamma*a_A, v = gamma*a_B
  have hg_pos : 0 < gamma := by
    by_contra h_neg
    push_neg at h_neg
    -- h_neg : gamma ≤ 0, hgamma.1 : 0 ≤ gamma, hg : gamma ≠ 0
    -- So gamma = 0, contradicting hg
    have : gamma = 0 := le_antisymm h_neg hgamma.1
    exact hg this
  -- Apply the fee-free bound with a_A' = gamma*a_A, a_B' = gamma*a_B
  have h_uA : 0 < gamma * a_A := mul_pos hg_pos hA
  have h_uB : 0 < gamma * a_B := mul_pos hg_pos hB
  -- The fee-free theorem gives:
  -- K*(gamma*a_B)/(M+gamma*a_B) - K*M*(gamma*a_B)/((M+gamma*a_A)*(M+gamma*a_A+gamma*a_B))
  --   <= K*(gamma*a_A)/M
  -- which is exactly the goal after factoring out gamma.
  have h_bound := cpmm_stateful_gain_bound K M (gamma * a_A) (gamma * a_B) hK hM h_uA h_uB
  -- Match the syntactic form using ring to normalize both sides.
  convert h_bound using 1
  · ring
  · ring
