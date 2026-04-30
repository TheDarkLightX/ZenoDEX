import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Oracle Sync Gate Soundness

Formal proof that the ZenoDex cross-module oracle synchronization gate
bounds cross-subsystem extraction.

## Two Gate Predicates

The gate admits price pairs where divergence is within D basis points:

* **Cross-multiplication** (`DivergenceBounded`): `delta * BPS ≤ D * P`
  Algebraically clean; strictly stronger than the production check.

* **Floor-division** (`DivBoundedProd`): `delta * BPS / P ≤ D`
  Matches the production code in `src/integration/zusd_api.py:171`:
    `divergence_bps = (abs(int(price_e8) - perp_price_e8) * 10_000) // perp_price_e8`
  Strictly weaker: admits states the cross-multiplication form rejects
  (see `witness_predicate_gap`).

## Predicate Bridge

`prod_implies_crossmul_succ`:
  `DivBoundedProd D → DivergenceBounded (D + 1)`

The floor absorbs at most P−1, so the gap is exactly 1 basis point.
All extraction bounds from the production predicate use `D + 1`,
giving `C * (D + 1) / BPS` — negligible overhead for typical D.

## Results

| # | Theorem | Statement |
|---|---------|-----------|
| 1 | `cross_div_le` | ad ≤ bc → a/c ≤ b/d (Nat cross-division) |
| 2 | `crossmul_implies_prod` | DivergenceBounded → DivBoundedProd |
| 3 | `prod_implies_crossmul_succ` | DivBoundedProd D → DivergenceBounded (D+1) |
| 4 | `extraction_bounded` | Cross-mul gate → C*delta/P ≤ C*D/BPS |
| 5 | `extraction_bounded_prod` | Production gate → C*delta/P ≤ C*(D+1)/BPS |
| 6 | `gate_monotone` | D ≤ D' → Gate(D) → Gate(D') |
| 7 | `prod_monotone` | D ≤ D' → ProdGate(D) → ProdGate(D') |
| 8 | `compose_move_divergence` | delta ≤ M*P/BPS → Gate(M) |
| 9 | `full_composition` | move + budget + fee → arb unprofitable |
| 10 | `extraction_additive` | Independent extractions compose additively |
| 11 | `small_div_zero_extraction` | D < BPS → per-unit extraction = 0 |
| 12 | `parameter_selection` | ∀ C ≤ C_max, extraction ≤ E (cross-mul) |
| 13 | `parameter_selection_prod` | ∀ C ≤ C_max, extraction ≤ E (production) |
| 14 | `fee_dominates_extraction` | fee_bps ≥ D → fee ≥ extraction (cross-mul) |
| 15 | `fee_dominates_extraction_prod` | fee_bps ≥ D+1 → fee ≥ extraction (production) |

## Scope

Models `cross_module_oracle_sync_gate` from `src/integration/zusd_api.py`.
Integer-only, matching e8-scaled production prices. Covers L=1 epoch lag;
L>1 involves geometric compounding (future work).
-/

section OracleSyncGate

-- ============================================================
-- Part I: Cross-Division Algebra
-- ============================================================

/-- Cross-multiplication to division inequality for natural numbers.
    Direction: ad ≤ bc → a/c ≤ b/d.
    Derived using `Nat.mul_div_mul_right` to cancel common factors. -/
theorem cross_div_le {a b c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (h : a * d ≤ b * c) : a / c ≤ b / d := by
  have rhs : b * c / (c * d) = b / d := by
    rw [show c * d = d * c from Nat.mul_comm c d]
    exact Nat.mul_div_mul_right b d hc
  calc a / c
      = a * d / (c * d) := (Nat.mul_div_mul_right a c hd).symm
    _ ≤ b * c / (c * d) := Nat.div_le_div_right h
    _ = b / d := rhs

-- ============================================================
-- Part II: Gate Predicates
-- ============================================================

/-- Cross-multiplication gate predicate (formal, stronger).
    `delta * BPS ≤ D * P` — algebraically clean for proofs. -/
@[reducible] def DivergenceBounded (delta P D BPS : ℕ) : Prop :=
  delta * BPS ≤ D * P

/-- Floor-division gate predicate (production, weaker).
    `delta * BPS / P ≤ D` — matches the production check in
    `src/integration/zusd_api.py:171`.
    Strictly weaker than `DivergenceBounded`: admits states where
    the remainder causes `delta * BPS > D * P` but
    `delta * BPS / P ≤ D` (see `witness_predicate_gap`). -/
@[reducible] def DivBoundedProd (delta P D BPS : ℕ) : Prop :=
  delta * BPS / P ≤ D

-- ============================================================
-- Part III: Predicate Bridge
-- ============================================================

/-- Cross-multiplication implies floor-division (stronger → weaker).
    Divides both sides of `delta * BPS ≤ D * P` by P. -/
theorem crossmul_implies_prod {delta P D BPS : ℕ}
    (hP : 0 < P)
    (h : DivergenceBounded delta P D BPS) :
    DivBoundedProd delta P D BPS := by
  show delta * BPS / P ≤ D
  calc delta * BPS / P
      ≤ D * P / P := Nat.div_le_div_right h
    _ = D := Nat.mul_div_cancel D hP

/-- Floor-division implies cross-multiplication with budget D+1
    (weaker → stronger+1). The floor absorbs remainder
    `(delta * BPS) % P < P`, so `delta * BPS < (D+1) * P`.
    This is the tightest bridge: the gap is exactly 1 basis point
    (see `witness_predicate_gap`). -/
theorem prod_implies_crossmul_succ {delta P D BPS : ℕ}
    (hP : 0 < P)
    (h : DivBoundedProd delta P D BPS) :
    DivergenceBounded delta P (D + 1) BPS := by
  show delta * BPS ≤ (D + 1) * P
  have h_euc := Nat.div_add_mod (delta * BPS) P
  have h_mod := Nat.mod_lt (delta * BPS) hP
  have h_succ : delta * BPS / P + 1 ≤ D + 1 := by omega
  have h_lt : delta * BPS < (delta * BPS / P + 1) * P := by
    have : (delta * BPS / P + 1) * P = P * (delta * BPS / P) + P := by ring
    linarith
  exact le_of_lt (lt_of_lt_of_le h_lt (Nat.mul_le_mul_right P h_succ))

/-- Floor-division gate is monotone in D. -/
theorem prod_monotone {delta P D D' BPS : ℕ}
    (hD : D ≤ D') (hgate : DivBoundedProd delta P D BPS) :
    DivBoundedProd delta P D' BPS :=
  Nat.le_trans hgate hD

-- ============================================================
-- Part IV: Extraction Bounds
-- ============================================================

/-- **Extraction Soundness** (cross-multiplication): If the formal gate
    admits a price pair with divergence delta, the maximum extractable
    value from C units of collateral is at most C * D / BPS. -/
theorem extraction_bounded {C delta P D BPS : ℕ}
    (hP : 0 < P) (hBPS : 0 < BPS)
    (hgate : DivergenceBounded delta P D BPS) :
    C * delta / P ≤ C * D / BPS := by
  apply cross_div_le hP hBPS
  show C * delta * BPS ≤ C * D * P
  calc C * delta * BPS
      = C * (delta * BPS) := by ring
    _ ≤ C * (D * P) := Nat.mul_le_mul_left C hgate
    _ = C * D * P := by ring

/-- **Extraction Soundness** (production): If the production gate
    admits a price pair, extraction is at most `C * (D + 1) / BPS`.
    The `D + 1` comes from the floor-division bridge. For D = 100 (1%),
    the bound is C * 101 / 10000 vs ideal C * 100 / 10000. -/
theorem extraction_bounded_prod {C delta P D BPS : ℕ}
    (hP : 0 < P) (hBPS : 0 < BPS)
    (hgate : DivBoundedProd delta P D BPS) :
    C * delta / P ≤ C * (D + 1) / BPS :=
  extraction_bounded hP hBPS (prod_implies_crossmul_succ hP hgate)

-- ============================================================
-- Part V: Gate Monotonicity
-- ============================================================

/-- Cross-multiplication gate is monotone in D. -/
theorem gate_monotone {delta P D D' BPS : ℕ}
    (hD : D ≤ D') (hgate : DivergenceBounded delta P D BPS) :
    DivergenceBounded delta P D' BPS :=
  Nat.le_trans hgate (Nat.mul_le_mul_right P hD)

-- ============================================================
-- Part VI: Epoch-Lag Composition
-- ============================================================

/-- Single-epoch oracle move bound implies divergence bounded.
    If `delta ≤ M * P / BPS`, the cross-multiplication gate holds
    with D = M. Uses floor-division safety margin:
    `(M * P / BPS) * BPS ≤ M * P`. -/
theorem compose_move_divergence {delta P M BPS : ℕ}
    (h : delta ≤ M * P / BPS) :
    DivergenceBounded delta P M BPS := by
  show delta * BPS ≤ M * P
  calc delta * BPS
      ≤ (M * P / BPS) * BPS := Nat.mul_le_mul_right BPS h
    _ ≤ M * P := Nat.div_mul_le_self (M * P) BPS

-- ============================================================
-- Part VII: Full Economic Safety
-- ============================================================

/-- **Full Economic Safety Composition**: chains oracle move bound
    through divergence gate through extraction bound to fee dominance.
    If oracle moves at most M bps/epoch, divergence budget D ≥ M,
    and protocol fees exceed C * D / BPS, then cross-module
    arbitrage is unprofitable. -/
theorem full_composition {C delta P D M BPS fee : ℕ}
    (hP : 0 < P) (hBPS : 0 < BPS)
    (h_move : delta * BPS ≤ M * P)
    (h_budget : M ≤ D)
    (h_fee : C * D / BPS < fee) :
    C * delta / P < fee :=
  Nat.lt_of_le_of_lt
    (extraction_bounded hP hBPS (gate_monotone h_budget h_move))
    h_fee

-- ============================================================
-- Part VIII: Structural Properties
-- ============================================================

/-- Two independent cross-module extractions compose additively. -/
theorem extraction_additive {C1 C2 delta1 delta2 P D BPS : ℕ}
    (hP : 0 < P) (hBPS : 0 < BPS)
    (hg1 : DivergenceBounded delta1 P D BPS)
    (hg2 : DivergenceBounded delta2 P D BPS) :
    C1 * delta1 / P + C2 * delta2 / P ≤ C1 * D / BPS + C2 * D / BPS :=
  Nat.add_le_add
    (extraction_bounded hP hBPS hg1)
    (extraction_bounded hP hBPS hg2)

/-- When D < BPS (budget under 100%), per-unit extraction is 0.
    Proved by contradiction: delta ≥ P leads to
    BPS * P ≤ delta * BPS ≤ D * P < BPS * P. -/
theorem small_div_zero_extraction {delta P D BPS : ℕ}
    (hP : 0 < P)
    (hD_small : D < BPS)
    (hgate : DivergenceBounded delta P D BPS) :
    delta / P = 0 := by
  apply Nat.div_eq_of_lt
  by_contra h_ge
  push_neg at h_ge
  have h_lower : BPS * P ≤ delta * BPS := by
    calc BPS * P ≤ BPS * delta := Nat.mul_le_mul_left BPS h_ge
      _ = delta * BPS := Nat.mul_comm BPS delta
  have h_upper : delta * BPS < BPS * P := by
    calc delta * BPS
        ≤ D * P := hgate
      _ < BPS * P := Nat.mul_lt_mul_of_pos_right hD_small hP
  linarith

-- ============================================================
-- Part IX: Operator Configuration
-- ============================================================

/-- **Parameter Selection** (cross-mul): To ensure extraction ≤ E
    for any collateral C ≤ C_max, configure `C_max * D ≤ E * BPS`. -/
theorem parameter_selection {C_max E D BPS : ℕ}
    (hBPS : 0 < BPS)
    (h_param : C_max * D ≤ E * BPS) :
    ∀ C delta P, C ≤ C_max → 0 < P →
      DivergenceBounded delta P D BPS →
      C * delta / P ≤ E := by
  intro C delta P hC_le hP hgate
  calc C * delta / P
      ≤ C * D / BPS := extraction_bounded hP hBPS hgate
    _ ≤ C_max * D / BPS := Nat.div_le_div_right (Nat.mul_le_mul_right D hC_le)
    _ ≤ E * BPS / BPS := Nat.div_le_div_right h_param
    _ = E := Nat.mul_div_cancel E hBPS

/-- **Parameter Selection** (production): To ensure extraction ≤ E
    under the production gate, configure `C_max * (D + 1) ≤ E * BPS`. -/
theorem parameter_selection_prod {C_max E D BPS : ℕ}
    (hBPS : 0 < BPS)
    (h_param : C_max * (D + 1) ≤ E * BPS) :
    ∀ C delta P, C ≤ C_max → 0 < P →
      DivBoundedProd delta P D BPS →
      C * delta / P ≤ E := by
  intro C delta P hC_le hP hgate
  calc C * delta / P
      ≤ C * (D + 1) / BPS := extraction_bounded_prod hP hBPS hgate
    _ ≤ C_max * (D + 1) / BPS :=
        Nat.div_le_div_right (Nat.mul_le_mul_right (D + 1) hC_le)
    _ ≤ E * BPS / BPS := Nat.div_le_div_right h_param
    _ = E := Nat.mul_div_cancel E hBPS

/-- **Fee Dominance** (cross-mul): If `fee_bps ≥ D`, then for any
    transaction amount A, the fee collected ≥ the extraction.
    Operators: set `fee_bps ≥ max_divergence_bps`. -/
theorem fee_dominates_extraction {A delta P D fee_bps BPS : ℕ}
    (hP : 0 < P) (hBPS : 0 < BPS)
    (hgate : DivergenceBounded delta P D BPS)
    (h_fee : D ≤ fee_bps) :
    A * delta / P ≤ A * fee_bps / BPS := by
  apply cross_div_le hP hBPS
  show A * delta * BPS ≤ A * fee_bps * P
  have h1 : delta * BPS ≤ fee_bps * P :=
    Nat.le_trans hgate (Nat.mul_le_mul_right P h_fee)
  calc A * delta * BPS
      = A * (delta * BPS) := by ring
    _ ≤ A * (fee_bps * P) := Nat.mul_le_mul_left A h1
    _ = A * fee_bps * P := by ring

/-- **Fee Dominance** (production): If `fee_bps ≥ D + 1`, then for any
    transaction amount A, the fee collected ≥ the extraction.
    Operators using the production gate: set `fee_bps ≥ max_div_bps + 1`. -/
theorem fee_dominates_extraction_prod {A delta P D fee_bps BPS : ℕ}
    (hP : 0 < P) (hBPS : 0 < BPS)
    (hgate : DivBoundedProd delta P D BPS)
    (h_fee : D + 1 ≤ fee_bps) :
    A * delta / P ≤ A * fee_bps / BPS :=
  fee_dominates_extraction hP hBPS (prod_implies_crossmul_succ hP hgate) h_fee

-- ============================================================
-- Part X: Non-Vacuity Witnesses
-- ============================================================

/-- Witness: cross-mul gate admits C=1000, delta=100, P=10000, D=100, BPS=10000.
    Extraction = bound = 10. Tight. -/
theorem witness_gate_admits_and_tight :
    let C := 1000; let delta := 100; let P := 10000; let D := 100; let BPS := 10000
    DivergenceBounded delta P D BPS
    ∧ C * delta / P = C * D / BPS
    ∧ C * delta / P = 10 := by native_decide

/-- Witness: cross-mul gate rejects divergence 200 bps against 100 bps budget. -/
theorem witness_gate_rejects :
    ¬DivergenceBounded 200 10000 100 10000 := by native_decide

/-- Witness: the two predicates genuinely differ.
    delta=101, P=10001, D=100, BPS=10000:
    Production PASSES (101*10000/10001 = 100 ≤ 100),
    cross-mul FAILS (1010000 > 1000100).
    This counterexample motivated the dual-predicate approach. -/
theorem witness_predicate_gap :
    DivBoundedProd 101 10001 100 10000
    ∧ ¬DivergenceBounded 101 10001 100 10000 := by native_decide

/-- Witness: the bridge is tight — D+1 works where D doesn't.
    delta=101, P=10001: DivergenceBounded with D+1=101 holds. -/
theorem witness_bridge_tight :
    DivBoundedProd 101 10001 100 10000
    ∧ DivergenceBounded 101 10001 101 10000 := by native_decide

/-- Witness: production extraction bound is tight.
    C=1000, delta=101, P=10001, D=100: extraction = bound = 10. -/
theorem witness_prod_extraction_tight :
    let C := 1000; let delta := 101; let P := 10001; let D := 100; let BPS := 10000
    DivBoundedProd delta P D BPS
    ∧ C * delta / P ≤ C * (D + 1) / BPS
    ∧ C * delta / P = 10
    ∧ C * (D + 1) / BPS = 10 := by native_decide

/-- Witness: full composition — move=50bps, budget=100bps, fee=51 > bound=50. -/
theorem witness_full_composition :
    let C := 5000; let delta := 50; let P := 10000
    let M := 100; let D := 100; let BPS := 10000; let fee := 51
    delta * BPS ≤ M * P
    ∧ M ≤ D
    ∧ C * D / BPS < fee
    ∧ C * delta / P < fee := by native_decide

/-- Witness: parameter_selection — C_max=10000, D=100, BPS=10000, E=100.
    Check: 10000*100 = 1000000 ≤ 100*10000 = 1000000. -/
theorem witness_parameter_selection :
    let C_max := 10000; let D := 100; let BPS := 10000; let E := 100
    C_max * D ≤ E * BPS
    ∧ 5000 * 80 / 10000 ≤ E := by native_decide

/-- Witness: fee dominance — fee_bps=100, D=100. Fee = extraction = 100. -/
theorem witness_fee_dominance :
    let A := 10000; let delta := 100; let P := 10000
    let D := 100; let fee_bps := 100; let BPS := 10000
    DivergenceBounded delta P D BPS
    ∧ D ≤ fee_bps
    ∧ A * delta / P ≤ A * fee_bps / BPS := by native_decide

/-- Witness: production fee dominance — fee_bps=101 ≥ D+1=101.
    Extraction: 10000*101/10001 = 100. Fee: 10000*101/10000 = 101. -/
theorem witness_prod_fee_dominance :
    let A := 10000; let delta := 101; let P := 10001
    let D := 100; let fee_bps := 101; let BPS := 10000
    DivBoundedProd delta P D BPS
    ∧ D + 1 ≤ fee_bps
    ∧ A * delta / P ≤ A * fee_bps / BPS := by native_decide

end OracleSyncGate
