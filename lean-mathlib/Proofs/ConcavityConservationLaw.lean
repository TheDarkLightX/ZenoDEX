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
6. `cpmm_donation_gain_argmax_bound_with_fee`: the donation/no-output exact
   optimizer with fee-scaled net inputs. The raw attacker optimum is
   `sqrt(M*(M+gammaA*a_A)) / gammaB` when `gammaB > 0`.

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

/-! ## Tight Stateful Attack Bound With Pool Depth

The bound `gain <= K*a_A/M` (Lipschitz) does not capture pool depth dependence.
The tighter bound `gain <= K*a_A/(M+a_A)` is exactly the output of the sacrificial
trade itself, and it decreases with pool depth M.

Key identity:
  `K*a_A/(M+a_A) - gain = K*M*a_A / ((M+a_B)*(M+a_A+a_B))`

The right-hand side is non-negative (all factors positive), proving the bound.
This replaces the falsified second-order approximation with an exact, tighter
bound that is decreasing in M.
-/

/-- **Tight Stateful Attack Gain Bound (fee-free)**: For CPMM `f(x) = K*x/(M+x)`
    with `K, M, a_A, a_B` all positive, the stateful sacrifice attack gain
    `out_B_without_A - out_B_with_A` is bounded by `K*a_A/(M+a_A)`.

    This is tighter than `cpmm_stateful_gain_bound` (which gives `K*a_A/M`)
    because `K*a_A/(M+a_A) < K*a_A/M` for `a_A > 0`.

    The bound `K*a_A/(M+a_A)` is exactly the output of the sacrificial trade:
    the attacker's maximum gain from the sacrifice attack is bounded by what
    the sacrificial trade itself produces. This is a depth-dependent bound:
    for fixed `a_A`, the bound decreases as `M` increases.

    Proof: `K*a_A/(M+a_A) - gain = K*M*a_A / ((M+a_B)*(M+a_A+a_B)) >= 0`. -/
theorem cpmm_stateful_gain_bound_tight
    (K M a_A a_B : ℝ)
    (hK : K > 0) (hM : M > 0) (hA : a_A > 0) (hB : a_B > 0)
    : K * a_B / (M + a_B) - K * M * a_B / ((M + a_A) * (M + a_A + a_B))
        ≤ K * a_A / (M + a_A) := by
  have hMA : 0 < M + a_A := by linarith
  have hMB : 0 < M + a_B := by linarith
  have hMAB : 0 < M + a_A + a_B := by linarith
  have hD : 0 < (M + a_B) * (M + a_A + a_B) := mul_pos hMB hMAB
  have h_identity :
    K * a_A / (M + a_A) -
    (K * a_B / (M + a_B) - K * M * a_B / ((M + a_A) * (M + a_A + a_B)))
    = K * M * a_A / ((M + a_B) * (M + a_A + a_B)) := by
    field_simp
    ring
  have hKM : 0 ≤ K * M * a_A :=
    mul_nonneg (mul_nonneg (le_of_lt hK) (le_of_lt hM)) (le_of_lt hA)
  have h_frac : 0 ≤ K * M * a_A / ((M + a_B) * (M + a_A + a_B)) :=
    div_nonneg hKM (le_of_lt hD)
  linarith

/-- **Tight Stateful Attack Gain Bound (with fee)**: The fee-bearing version
    of `cpmm_stateful_gain_bound_tight`, with bound `gamma*K*a_A/(M+gamma*a_A)`.

    This is tighter than `cpmm_stateful_gain_bound_with_fee` (which gives
    `gamma*K*a_A/M`) and decreases with pool depth M. -/
theorem cpmm_stateful_gain_bound_tight_with_fee
    (K M a_A a_B gamma : ℝ)
    (hK : K > 0) (hM : M > 0) (hA : a_A > 0) (hB : a_B > 0)
    (hgamma : 0 ≤ gamma ∧ gamma ≤ 1)
    : K * gamma * a_B / (M + gamma * a_B)
        - K * M * gamma * a_B / ((M + gamma * a_A) * (M + gamma * a_A + gamma * a_B))
        ≤ gamma * K * a_A / (M + gamma * a_A) := by
  by_cases hg : gamma = 0
  · simp [hg]
  have hg_pos : 0 < gamma := by
    by_contra h_neg
    push_neg at h_neg
    have : gamma = 0 := le_antisymm h_neg hgamma.1
    exact hg this
  have h_uA : 0 < gamma * a_A := mul_pos hg_pos hA
  have h_uB : 0 < gamma * a_B := mul_pos hg_pos hB
  have h_bound := cpmm_stateful_gain_bound_tight K M (gamma * a_A) (gamma * a_B)
    hK hM h_uA h_uB
  convert h_bound using 1
  · ring
  · ring

/-- **Pool depth monotonicity**: The tight bound `K*a_A/(M+a_A)` is strictly
    decreasing in `M` for `K, a_A > 0`.

    This formalizes the empirical observation that stateful attack gain
    decreases with pool depth. The Lipschitz bound `K*a_A/M` also decreases
    with M, but the tight bound decreases faster. -/
theorem tight_bound_decreases_with_M
    (K a_A M1 M2 : ℝ)
    (hK : K > 0) (hA : a_A > 0) (hM1 : M1 > 0) (hM2 : M2 > 0)
    (hM1_lt_M2 : M1 < M2)
    : K * a_A / (M2 + a_A) < K * a_A / (M1 + a_A) := by
  have hKA : 0 < K * a_A := mul_pos hK hA
  have hD1 : 0 < M1 + a_A := by linarith
  have hD2 : 0 < M2 + a_A := by linarith
  have hD1_lt_D2 : M1 + a_A < M2 + a_A := by linarith
  have h_cross : K * a_A * (M1 + a_A) < K * a_A * (M2 + a_A) :=
    mul_lt_mul_of_pos_left hD1_lt_D2 hKA
  have h_eq : K * a_A / (M2 + a_A) - K * a_A / (M1 + a_A) =
    -(K * a_A * (M2 + a_A - (M1 + a_A))) / ((M2 + a_A) * (M1 + a_A)) := by
    field_simp; ring
  have h_diff_pos : 0 < M2 + a_A - (M1 + a_A) := by linarith
  have h_denom_pos : 0 < (M2 + a_A) * (M1 + a_A) := mul_pos hD2 hD1
  have h_num_neg : K * a_A * (M2 + a_A - (M1 + a_A)) > 0 :=
    mul_pos hKA h_diff_pos
  have h_frac_neg : -(K * a_A * (M2 + a_A - (M1 + a_A))) /
      ((M2 + a_A) * (M1 + a_A)) < 0 := by
    rw [neg_div]
    exact neg_neg_of_pos (div_pos h_num_neg h_denom_pos)
  have h_goal : K * a_A / (M2 + a_A) - K * a_A / (M1 + a_A) < 0 := by
    rw [h_eq]; exact h_frac_neg
  linarith

/-- **Tight bound is tighter than Lipschitz**: `K*a_A/(M+a_A) < K*a_A/M`
    for `a_A > 0`.

    This shows the tight bound is strictly better than the Lipschitz bound
    whenever the sacrificial trade is non-zero. -/
theorem tight_bound_stricter_than_lipschitz
    (K M a_A : ℝ)
    (hK : K > 0) (hM : M > 0) (hA : a_A > 0)
    : K * a_A / (M + a_A) < K * a_A / M := by
  have hKA : 0 < K * a_A := mul_pos hK hA
  have hD1 : 0 < M + a_A := by linarith
  have hD2 : 0 < M := hM
  have hD2_lt_D1 : M < M + a_A := by linarith
  have h_eq : K * a_A / (M + a_A) - K * a_A / M =
    -(K * a_A * a_A) / ((M + a_A) * M) := by
    field_simp; ring
  have h_denom_pos : 0 < (M + a_A) * M := mul_pos hD1 hD2
  have h_num_pos : 0 < K * a_A * a_A := mul_pos hKA hA
  have h_frac_neg : -(K * a_A * a_A) / ((M + a_A) * M) < 0 := by
    rw [neg_div]
    exact neg_neg_of_pos (div_pos h_num_pos h_denom_pos)
  have h_goal : K * a_A / (M + a_A) - K * a_A / M < 0 := by
    rw [h_eq]; exact h_frac_neg
  linarith

/-- **Witness**: Concrete case showing the tight bound is strictly tighter
    than the Lipschitz bound. K=1000, M=1000, a_A=100, a_B=100. -/
theorem witness_tight_vs_lipschitz :
    (1000 * 100 / (1000 + 100) : ℝ) < 1000 * 100 / 1000 ∧
    (1000 * 100 / (1000 + 100) : ℝ) ≤
    1000 * 100 / (1000 + 100) - 1000 * 100 / (1000 + 100) +
    1000 * 100 / (1000 + 100) := by
  constructor
  · norm_num
  · norm_num

/-! ## Exact Donation/No-Output Attack Optimizer

There are two related stateful attack semantics:

* Filled-A state change, used by `cpmm_stateful_gain_bound_tight` above:
  A receives CPMM output and the pool output reserve changes.
* Donation/no-output perturbation, where A adds input liquidity without taking
  output. This model has gain
  `K*a_A*a_B / ((M+a_B)*(M+a_A+a_B))`.

The finite optimizer `a_B = sqrt(M*(M+a_A))` belongs to the fee-free
donation/no-output model. With fee-scaled net inputs, the optimizer is
`sqrt(M*(M+gammaA*a_A)) / gammaB` when `gammaB > 0`. It is not the optimizer
for the filled-A state-change gain, whose supremum is approached as `a_B`
grows. The theorem below proves the exact donation/no-output upper bound
without differentiating: after cross multiplication, the gap factors as
`s*(a_B-s)^2`.
-/

/-- **Donation/no-output exact attack bound**: For the fee-free CPMM donation
    perturbation gain

    `K*a_A*a_B / ((M+a_B)*(M+a_A+a_B))`,

    any positive `s` satisfying `s^2 = M*(M+a_A)` gives a global upper bound at
    `a_B = s`.

    The proof is the algebraic certificate
    `s*(M+a_B)*(M+a_A+a_B) - a_B*(M+s)*(M+a_A+s) = s*(a_B-s)^2`,
    after using `s^2 = M*(M+a_A)`. -/
theorem cpmm_donation_gain_argmax_bound
    (K M a_A a_B s : ℝ)
    (hK : K > 0) (hM : M > 0) (hA : a_A > 0) (hB : a_B > 0)
    (hs : s > 0) (hs_sq : s ^ 2 = M * (M + a_A))
    : K * a_A * a_B / ((M + a_B) * (M + a_A + a_B))
        ≤ K * a_A * s / ((M + s) * (M + a_A + s)) := by
  have hMB : 0 < M + a_B := by linarith
  have hMAB : 0 < M + a_A + a_B := by linarith
  have hMS : 0 < M + s := by linarith
  have hMAS : 0 < M + a_A + s := by linarith
  have hD_B : 0 < (M + a_B) * (M + a_A + a_B) := mul_pos hMB hMAB
  have hD_s : 0 < (M + s) * (M + a_A + s) := mul_pos hMS hMAS
  have h_gap_identity :
      s * ((M + a_B) * (M + a_A + a_B))
        - a_B * ((M + s) * (M + a_A + s))
        = s * (a_B - s) ^ 2 := by
    nlinarith [hs_sq]
  have h_gap_nonneg :
      0 ≤ s * ((M + a_B) * (M + a_A + a_B))
        - a_B * ((M + s) * (M + a_A + s)) := by
    rw [h_gap_identity]
    exact mul_nonneg (le_of_lt hs) (sq_nonneg _)
  have h_base :
      a_B / ((M + a_B) * (M + a_A + a_B))
        ≤ s / ((M + s) * (M + a_A + s)) := by
    rw [div_le_div_iff₀ hD_B hD_s]
    linarith
  have hKA_nonneg : 0 ≤ K * a_A := mul_nonneg (le_of_lt hK) (le_of_lt hA)
  have h_scaled := mul_le_mul_of_nonneg_left h_base hKA_nonneg
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_scaled

/-- **Donation/no-output optimizer witness**: For K=1000, M=1000, a_A=100,
    the symbolic optimizer can be supplied by any positive `s` with
    `s^2 = 1100000`. This witness keeps the exact theorem non-vacuous without
    requiring decimal square-root normalization. -/
theorem witness_cpmm_donation_gain_argmax_bound
    (s : ℝ) (hs : s > 0) (hs_sq : s ^ 2 = 1000 * (1000 + 100 : ℝ))
    : 1000 * 100 * 100 / ((1000 + 100) * (1000 + 100 + 100 : ℝ))
        ≤ 1000 * 100 * s / ((1000 + s) * (1000 + 100 + s)) := by
  exact cpmm_donation_gain_argmax_bound 1000 1000 100 100 s
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs hs_sq

/-- **Donation/no-output exact attack bound with fees**: fee parameters rescale
    the two raw trade sizes into net input sizes. For

    `u = gammaA*a_A` and `v = gammaB*a_B`,

    the fee-bearing donation/no-output gain

    `K*u*v / ((M+v)*(M+u+v))`

    is globally bounded by its value at any positive `s` satisfying
    `s^2 = M*(M+u)`. In raw attacker units, the optimizer is `s/gammaB` when
    `gammaB > 0`.

    The proof is a substitution into `cpmm_donation_gain_argmax_bound`; the
    upper fee-domain constraints `gammaA <= 1`, `gammaB <= 1` are economic
    assumptions for fee bps, but the algebra needs only positive net-input
    scale factors. -/
theorem cpmm_donation_gain_argmax_bound_with_fee
    (K M a_A a_B gammaA gammaB s : ℝ)
    (hK : K > 0) (hM : M > 0) (hA : a_A > 0) (hB : a_B > 0)
    (hgammaA : gammaA > 0) (hgammaB : gammaB > 0)
    (hs : s > 0) (hs_sq : s ^ 2 = M * (M + gammaA * a_A))
    : K * (gammaA * a_A) * (gammaB * a_B)
        / ((M + gammaB * a_B) * (M + gammaA * a_A + gammaB * a_B))
        ≤ K * (gammaA * a_A) * s
          / ((M + s) * (M + gammaA * a_A + s)) := by
  have huA : 0 < gammaA * a_A := mul_pos hgammaA hA
  have huB : 0 < gammaB * a_B := mul_pos hgammaB hB
  exact cpmm_donation_gain_argmax_bound K M (gammaA * a_A) (gammaB * a_B) s
    hK hM huA huB hs hs_sq

/-- **Fee-bearing donation/no-output witness**: a concrete nonzero-fee instance
    of `cpmm_donation_gain_argmax_bound_with_fee`. -/
theorem witness_cpmm_donation_gain_argmax_bound_with_fee
    (s : ℝ) (hs : s > 0)
    (hs_sq : s ^ 2 = 1000 * (1000 + (1 / 2 : ℝ) * 100))
    : 1000 * ((1 / 2 : ℝ) * 100) * ((9 / 10 : ℝ) * 100)
        / ((1000 + (9 / 10 : ℝ) * 100)
          * (1000 + (1 / 2 : ℝ) * 100 + (9 / 10 : ℝ) * 100))
        ≤ 1000 * ((1 / 2 : ℝ) * 100) * s
          / ((1000 + s) * (1000 + (1 / 2 : ℝ) * 100 + s)) := by
  exact cpmm_donation_gain_argmax_bound_with_fee
    1000 1000 100 100 (1 / 2 : ℝ) (9 / 10 : ℝ) s
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hs hs_sq
