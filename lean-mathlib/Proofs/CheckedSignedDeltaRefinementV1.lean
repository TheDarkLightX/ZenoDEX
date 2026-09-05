import Std.Tactic

/-!
Arithmetic model of `checked_signed_delta_v1`: subtract unsigned holdings in
the ordered branch, then convert the magnitude, handling i128::MIN separately.
The input type supplies the Rust u128 bound. The specification uses an exact
integer difference and a signed interval, independently of the branch recipe.
This does not prove compiler correctness, decoding, aggregation or publication.
-/
namespace Proofs.CheckedSignedDeltaRefinementV1

abbrev Holding := Fin (2 ^ 128)

def minMagnitude : Nat := 170141183460469231731687303715884105728
def signedMax : Nat := 170141183460469231731687303715884105727

inductive Reject where
  | signedStateDeltaBounds
  deriving DecidableEq, Repr

def checkedSignedDelta (post pre : Holding) : Except Reject Int :=
  if post.val ≥ pre.val then
    let magnitude := post.val - pre.val
    if magnitude ≤ signedMax then .ok (Int.ofNat magnitude)
    else .error .signedStateDeltaBounds
  else
    let magnitude := pre.val - post.val
    if magnitude = minMagnitude then .ok (-Int.ofNat minMagnitude)
    else if magnitude ≤ signedMax then .ok (-Int.ofNat magnitude)
    else .error .signedStateDeltaBounds

def exactDifference (post pre : Holding) : Int :=
  Int.ofNat post.val - Int.ofNat pre.val

def representable (delta : Int) : Prop :=
  -Int.ofNat minMagnitude ≤ delta ∧ delta ≤ Int.ofNat signedMax

instance (delta : Int) : Decidable (representable delta) :=
  inferInstanceAs (Decidable (_ ∧ _))

def specification (post pre : Holding) : Except Reject Int :=
  let delta := exactDifference post pre
  if representable delta then .ok delta else .error .signedStateDeltaBounds

theorem bounds_match_rust_widths :
    minMagnitude = 2 ^ 127 ∧ signedMax = 2 ^ 127 - 1 := by decide

theorem subtraction_magnitudes_fit_u128 (post pre : Holding) :
    post.val - pre.val < 2 ^ 128 ∧ pre.val - post.val < 2 ^ 128 := by
  have := post.isLt
  have := pre.isLt
  omega

theorem checked_signed_delta_refines_specification (post pre : Holding) :
    checkedSignedDelta post pre = specification post pre := by
  simp only [checkedSignedDelta, specification, exactDifference, representable]
  split
  · split
    · split <;> simp_all [signedMax, minMagnitude] <;> omega
    · split <;> simp_all [signedMax, minMagnitude] <;> omega
  · split
    · split <;> simp_all [signedMax, minMagnitude] <;> omega
    · split
      · split <;> simp_all [signedMax, minMagnitude] <;> omega
      · split <;> simp_all [signedMax, minMagnitude] <;> omega

theorem success_iff_exact_representable (post pre : Holding) (delta : Int) :
    checkedSignedDelta post pre = .ok delta ↔
      delta = exactDifference post pre ∧ representable delta := by
  rw [checked_signed_delta_refines_specification]
  dsimp only [specification]
  split <;> simp_all [eq_comm]

theorem rejection_iff_out_of_range (post pre : Holding) :
    checkedSignedDelta post pre = .error .signedStateDeltaBounds ↔
      ¬representable (exactDifference post pre) := by
  rw [checked_signed_delta_refines_specification]
  dsimp only [specification]
  split <;> simp_all

theorem unchanged_holdings_accept_zero (holding : Holding) :
    checkedSignedDelta holding holding = .ok 0 := by
  rw [success_iff_exact_representable]
  simp [exactDifference, representable, minMagnitude, signedMax]

theorem minimum_signed_difference_accepts :
    checkedSignedDelta ⟨0, by decide⟩ ⟨2 ^ 127, by decide⟩ =
      .ok (-170141183460469231731687303715884105728) := by rfl

theorem positive_overflow_neighbor_rejects :
    checkedSignedDelta ⟨2 ^ 127, by decide⟩ ⟨0, by decide⟩ =
      .error .signedStateDeltaBounds := by rfl

theorem negative_overflow_neighbor_rejects :
    checkedSignedDelta ⟨0, by decide⟩ ⟨2 ^ 127 + 1, by decide⟩ =
      .error .signedStateDeltaBounds := by rfl

theorem maximum_holdings_small_difference_accepts :
    checkedSignedDelta ⟨2 ^ 128 - 33, by decide⟩ ⟨2 ^ 128 - 1, by decide⟩ =
      .ok (-32) := by rfl

end Proofs.CheckedSignedDeltaRefinementV1
