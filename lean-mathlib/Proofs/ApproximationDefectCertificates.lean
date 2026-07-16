import Mathlib.Tactic

/-!
# Approximation Defect Certificates

This file formalizes the algebraic core of the research-only
`approximation_defect_receipt_v1` checker. A local reference model supplies a
certified lower margin. Defect, interaction, and reconstruction errors compose
additively. If the total error stays below the model margin, then the target is
nonnegative on that region. A finite cover lifts the local result to the whole
declared domain.

The theorem does not validate the analytic certificate identifiers carried by
the Python receipt. Those upstream certificates remain explicit external
assumptions. Overlap hashes are canonical binding checks in the executable
schema; the mathematical lifting theorem only needs every covered point to
share the same target function.
-/

namespace ApproximationDefectCertificates

/-- The three typed error components used by the executable receipt. -/
structure ErrorBudget where
  defect : ℝ
  interaction : ℝ
  reconstruction : ℝ

namespace ErrorBudget

/-- Additive composition of defect, interaction, and reconstruction errors. -/
def total (budget : ErrorBudget) : ℝ :=
  budget.defect + budget.interaction + budget.reconstruction

/-- Every typed error component is a genuine nonnegative upper bound. -/
def Nonnegative (budget : ErrorBudget) : Prop :=
  0 ≤ budget.defect ∧ 0 ≤ budget.interaction ∧ 0 ≤ budget.reconstruction

/-- One budget componentwise dominates another. -/
def ComponentwiseLE (certified allocated : ErrorBudget) : Prop :=
  certified.defect ≤ allocated.defect ∧
    certified.interaction ≤ allocated.interaction ∧
    certified.reconstruction ≤ allocated.reconstruction

/-- Componentwise allocation dominance implies dominance of the total budget. -/
theorem total_le_total_of_componentwiseLE
    {certified allocated : ErrorBudget}
    (h : ComponentwiseLE certified allocated) :
    certified.total ≤ allocated.total := by
  rcases h with ⟨hdefect, hinteraction, hreconstruction⟩
  unfold total
  linarith

/-- A nonnegative typed budget has a nonnegative composed total. -/
theorem total_nonneg {budget : ErrorBudget}
    (h : budget.Nonnegative) :
    0 ≤ budget.total := by
  rcases h with ⟨hdefect, hinteraction, hreconstruction⟩
  unfold total
  linarith

end ErrorBudget

/-- A local region with its reference model, certified margin, and error budget. -/
structure RegionCertificate (α : Type*) where
  carrier : Set α
  model : α → ℝ
  margin : ℝ
  budget : ErrorBudget

namespace RegionCertificate

/--
Validity assumptions for one local approximation receipt. The absolute error
bound already composes every typed component through `budget.total`.
-/
def Valid {α : Type*}
    (certificate : RegionCertificate α) (target : α → ℝ) : Prop :=
  certificate.budget.Nonnegative ∧
    (∀ x ∈ certificate.carrier, certificate.margin ≤ certificate.model x) ∧
    (∀ x ∈ certificate.carrier,
      |target x - certificate.model x| ≤ certificate.budget.total) ∧
    certificate.budget.total ≤ certificate.margin

end RegionCertificate

/--
Local model plus residual gluing: a model lower margin that dominates the total
absolute approximation error proves target nonnegativity on the region.
-/
theorem local_target_nonneg
    {α : Type*}
    (target model : α → ℝ)
    (region : Set α)
    (margin : ℝ)
    (budget : ErrorBudget)
    (hmodel : ∀ x ∈ region, margin ≤ model x)
    (herror : ∀ x ∈ region, |target x - model x| ≤ budget.total)
    (hbudget : budget.total ≤ margin) :
    ∀ x ∈ region, 0 ≤ target x := by
  intro x hx
  have hlower : -budget.total ≤ target x - model x :=
    (abs_le.mp (herror x hx)).1
  have htotalModel : budget.total ≤ model x :=
    le_trans hbudget (hmodel x hx)
  linarith

/-- A valid structured region certificate proves its target nonnegative locally. -/
theorem RegionCertificate.target_nonneg
    {α : Type*}
    {target : α → ℝ}
    (certificate : RegionCertificate α)
    (hvalid : certificate.Valid target) :
    ∀ x ∈ certificate.carrier, 0 ≤ target x := by
  rcases hvalid with ⟨_hnonnegative, hmodel, herror, hbudget⟩
  exact local_target_nonneg target certificate.model certificate.carrier
    certificate.margin certificate.budget hmodel herror hbudget

/-- A finite list of local regions covers every point in a declared domain. -/
def Covers {α : Type*}
    (domain : Set α) (certificates : List (RegionCertificate α)) : Prop :=
  ∀ x ∈ domain, ∃ certificate ∈ certificates, x ∈ certificate.carrier

/--
Finite-cover lifting theorem used by accepted receipts: local certificates for
one target function prove that target nonnegative throughout the covered domain.
-/
theorem finiteCover_target_nonneg
    {α : Type*}
    (target : α → ℝ)
    (domain : Set α)
    (certificates : List (RegionCertificate α))
    (hcover : Covers domain certificates)
    (hvalid : ∀ certificate ∈ certificates, certificate.Valid target) :
    ∀ x ∈ domain, 0 ≤ target x := by
  intro x hx
  rcases hcover x hx with ⟨certificate, hmember, hcarrier⟩
  exact certificate.target_nonneg (hvalid certificate hmember) x hcarrier

/--
Two local models bound to the same target have a derived mismatch bound on an
overlap. This is the analytic content behind checking adjacent overlap contracts.
-/
theorem overlap_model_mismatch_bound
    {α : Type*}
    (target leftModel rightModel : α → ℝ)
    (x : α)
    (leftError rightError : ℝ)
    (hleft : |target x - leftModel x| ≤ leftError)
    (hright : |target x - rightModel x| ≤ rightError) :
    |leftModel x - rightModel x| ≤ leftError + rightError := by
  calc
    |leftModel x - rightModel x| =
        |(leftModel x - target x) + (target x - rightModel x)| := by ring_nf
    _ ≤ |leftModel x - target x| + |target x - rightModel x| := abs_add_le _ _
    _ = |target x - leftModel x| + |target x - rightModel x| := by
      rw [abs_sub_comm (leftModel x) (target x)]
    _ ≤ leftError + rightError := add_le_add hleft hright

/-! ## Non-vacuity and side-condition witnesses -/

/-- A concrete local certificate with positive remaining margin. -/
noncomputable def witnessRegion : RegionCertificate Unit where
  carrier := Set.univ
  model := fun _ => 1
  margin := 1 / 2
  budget := {
    defect := 1 / 8
    interaction := 1 / 16
    reconstruction := 1 / 16
  }

/-- The concrete witness region certifies the constant target `3/4`. -/
theorem witnessRegion_valid :
    witnessRegion.Valid (fun _ => 3 / 4) := by
  constructor
  · norm_num [witnessRegion, ErrorBudget.Nonnegative]
  constructor
  · intro x hx
    norm_num [witnessRegion]
  constructor
  · intro x hx
    norm_num [witnessRegion, ErrorBudget.total]
  · norm_num [witnessRegion, ErrorBudget.total]

/-- The model-margin dominance condition is load-bearing. -/
theorem insufficient_margin_counterexample :
    ∃ target model margin error : ℝ,
      margin ≤ model ∧
      |target - model| ≤ error ∧
      margin < error ∧
      target < 0 := by
  exact ⟨-1, 1, 1, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

end ApproximationDefectCertificates
