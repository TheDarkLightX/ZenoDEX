import Mathlib.Tactic

/-!
# Route Interval Graph Certificates

This packet formalizes two small theorem targets from
`experiments/math_object_innovation_v187`:

1. Integer CPMM floor output is trapped between two adjacent rational ticks.
2. A positive potential certificate upper-bounds every certified route product.

The statements are deliberately abstract. They prove the reusable arithmetic
shape behind the Julia discovery receipt, not a production router.
-/

namespace Proofs
namespace RouteIntervalGraph

/-! ## Integer CPMM floor interval -/

/-- Integer CPMM exact-in output using post-fee net input. -/
def cpmmOutPostFee (reserveIn reserveOut netIn : Nat) : Nat :=
  (netIn * reserveOut) / (reserveIn + netIn)

/-- Numerator of the post-fee ideal rational output. -/
def cpmmIdealNum (reserveOut netIn : Nat) : Nat :=
  netIn * reserveOut

/-- Denominator of the post-fee ideal rational output. -/
def cpmmIdealDen (reserveIn netIn : Nat) : Nat :=
  reserveIn + netIn

/-- The CPMM floor output multiplied by the denominator never exceeds the
ideal rational numerator. -/
theorem cpmmOutPostFee_mul_den_le_num
    (reserveIn reserveOut netIn : Nat) :
    cpmmOutPostFee reserveIn reserveOut netIn *
        cpmmIdealDen reserveIn netIn <=
      cpmmIdealNum reserveOut netIn := by
  unfold cpmmOutPostFee cpmmIdealDen cpmmIdealNum
  exact Nat.div_mul_le_self (netIn * reserveOut) (reserveIn + netIn)

/-- The ideal rational numerator is strictly below the next integer output tick
when the denominator is positive. -/
theorem cpmm_num_lt_succ_out_mul_den
    (reserveIn reserveOut netIn : Nat)
    (hden : 0 < cpmmIdealDen reserveIn netIn) :
    cpmmIdealNum reserveOut netIn <
      (cpmmOutPostFee reserveIn reserveOut netIn + 1) *
        cpmmIdealDen reserveIn netIn := by
  unfold cpmmOutPostFee cpmmIdealDen cpmmIdealNum at *
  have hDivLt :
      (netIn * reserveOut) / (reserveIn + netIn) <
        (netIn * reserveOut) / (reserveIn + netIn) + 1 := by
    exact Nat.lt_succ_self _
  exact (Nat.div_lt_iff_lt_mul hden).mp hDivLt

/-- Integer interval form of the CPMM post-fee floor bridge.

In plain English: if the denominator is positive, `out = floor(num / den)`
is exactly the unique integer tick satisfying
`out * den <= num < (out + 1) * den`.
-/
theorem cpmm_post_fee_floor_interval
    (reserveIn reserveOut netIn : Nat)
    (hden : 0 < cpmmIdealDen reserveIn netIn) :
    cpmmOutPostFee reserveIn reserveOut netIn *
          cpmmIdealDen reserveIn netIn <=
        cpmmIdealNum reserveOut netIn ∧
      cpmmIdealNum reserveOut netIn <
        (cpmmOutPostFee reserveIn reserveOut netIn + 1) *
          cpmmIdealDen reserveIn netIn := by
  constructor
  · exact cpmmOutPostFee_mul_den_le_num reserveIn reserveOut netIn
  · exact cpmm_num_lt_succ_out_mul_den reserveIn reserveOut netIn hden

/-! ## Potential-carrying route products -/

/-- Multiplicative upper-rate product along a vertex list. -/
def pathProduct (rate : Nat -> Nat -> Rat) : List Nat -> Rat
  | [] => 1
  | [_] => 1
  | u :: v :: rest => rate u v * pathProduct rate (v :: rest)

/-- The last vertex of `u :: rest`, supplied directly so route bounds can avoid
depending on a concrete graph representation. -/
def pathLast (u : Nat) : List Nat -> Nat
  | [] => u
  | v :: rest => pathLast v rest

/-- A positive potential certificate upper-bounds every route rate product.

In plain English: if every edge satisfies
`rate(u,v) * potential(v) <= potential(u)`, then the product of rates along
any route from `first` to `last` is at most `potential(first)/potential(last)`.
-/
theorem pathProduct_potential_bound
    (rate : Nat -> Nat -> Rat) (potential : Nat -> Rat)
    (hRateNonneg : forall u v, 0 <= rate u v)
    (hEdge : forall u v, rate u v * potential v <= potential u)
    (first : Nat) (rest : List Nat) :
    pathProduct rate (first :: rest) * potential (pathLast first rest) <=
      potential first := by
  induction rest generalizing first with
  | nil =>
      simp [pathProduct, pathLast]
  | cons second tail ih =>
      cases tail with
      | nil =>
          simp [pathProduct, pathLast]
          exact hEdge first second
      | cons third more =>
          have hTail :
              pathProduct rate (second :: third :: more) *
                  potential (pathLast third more) <= potential second := by
            simpa [pathLast] using ih second
          have hMul :
              rate first second *
                  (pathProduct rate (second :: third :: more) *
                    potential (pathLast third more)) <=
                rate first second * potential second :=
            mul_le_mul_of_nonneg_left hTail (hRateNonneg first second)
          have hEdgeFirst : rate first second * potential second <= potential first :=
            hEdge first second
          calc
            pathProduct rate (first :: second :: third :: more) *
                potential (pathLast first (second :: third :: more))
                = rate first second *
                    (pathProduct rate (second :: third :: more) *
                      potential (pathLast third more)) := by
                  simp [pathProduct, pathLast, mul_assoc]
            _ <= rate first second * potential second := hMul
            _ <= potential first := hEdgeFirst

/-- Division form of `pathProduct_potential_bound`.

This is the route-pruning shape: after a prefix has reached asset `first`,
every certified continuation to `pathLast first rest` is bounded by the
potential ratio. -/
theorem pathProduct_le_potential_ratio
    (rate : Nat -> Nat -> Rat) (potential : Nat -> Rat)
    (hRateNonneg : forall u v, 0 <= rate u v)
    (hPotentialPos : forall v, 0 < potential v)
    (hEdge : forall u v, rate u v * potential v <= potential u)
    (first : Nat) (rest : List Nat) :
    pathProduct rate (first :: rest) <=
      potential first / potential (pathLast first rest) := by
  have hBound :=
    pathProduct_potential_bound rate potential hRateNonneg hEdge first rest
  have hPos : 0 < potential (pathLast first rest) :=
    hPotentialPos (pathLast first rest)
  have hDiv :=
    (le_div_iff₀ hPos).mpr hBound
  simpa [mul_comm, mul_left_comm, mul_assoc] using hDiv

/-- Non-vacuity witness for the CPMM interval theorem. -/
example :
    cpmm_post_fee_floor_interval 1000 1000 997 (by decide) =
      And.intro
        (cpmmOutPostFee_mul_den_le_num 1000 1000 997)
        (cpmm_num_lt_succ_out_mul_den 1000 1000 997 (by decide)) := by
  rfl

end RouteIntervalGraph
end Proofs
