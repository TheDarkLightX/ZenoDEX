import Mathlib

/-!
# Disaster Antichain Basis

This module proves a generic theorem layer for compressing
disaster-state search.

The intended ZenoDEX use:

- A disaster-search axis is a point in a preorder.
- `b ≤ x` means `x` is at least as dangerous/relaxed/general as basis axis `b`.
- If every bad axis is above some finite/minimal basis axis, and rejection is
  upward closed, then proving the basis rejected proves every covered bad axis
  rejected.

This is meant to turn large disaster inventories into small replayable
generators rather than one isolated proof per named axis.
-/

namespace Proofs
namespace DisasterAntichainBasis

universe u

variable {Axis : Type u}

/-- A unary predicate is upward closed with respect to a preorder-like relation. -/
def UpwardClosed (le : Axis → Axis → Prop) (P : Axis → Prop) : Prop :=
  ∀ ⦃a b : Axis⦄, le a b → P a → P b

/-- A set of basis axes covers every bad axis by upward closure. -/
def BasisCoversBad
    (le : Axis → Axis → Prop)
    (basis : Set Axis)
    (Bad : Axis → Prop) : Prop :=
  ∀ x : Axis, Bad x → ∃ b : Axis, basis b ∧ le b x

/-- Finite/list-shaped version, closer to replay receipts and generated audits. -/
def ListBasisCoversBad
    (le : Axis → Axis → Prop)
    (basis : List Axis)
    (Bad : Axis → Prop) : Prop :=
  ∀ x : Axis, Bad x → ∃ b : Axis, b ∈ basis ∧ le b x

/-- No two distinct basis elements dominate each other in both directions. -/
def Antichain (le : Axis → Axis → Prop) (basis : Set Axis) : Prop :=
  ∀ ⦃a b : Axis⦄, basis a → basis b → le a b → le b a → a = b

/-- A basis is exact when it covers all bad states and contains only bad states. -/
def ExactBadBasis
    (le : Axis → Axis → Prop)
    (basis : Set Axis)
    (Bad : Axis → Prop) : Prop :=
  BasisCoversBad le basis Bad ∧ ∀ b : Axis, basis b → Bad b

/-- Core lift: rejecting a covered basis and making rejection upward closed
rejects every covered bad axis. -/
theorem basis_rejection_lifts_to_all_bad
    (le : Axis → Axis → Prop)
    (basis : Set Axis)
    (Bad Rejected : Axis → Prop)
    (hcover : BasisCoversBad le basis Bad)
    (hbasisRejected : ∀ b : Axis, basis b → Rejected b)
    (hrejectUp : UpwardClosed le Rejected) :
    ∀ x : Axis, Bad x → Rejected x := by
  intro x hx
  obtain ⟨b, hb_mem, hb_le⟩ := hcover x hx
  exact hrejectUp hb_le (hbasisRejected b hb_mem)

/-- List/receipt version of the lift theorem. -/
theorem list_basis_rejection_lifts_to_all_bad
    (le : Axis → Axis → Prop)
    (basis : List Axis)
    (Bad Rejected : Axis → Prop)
    (hcover : ListBasisCoversBad le basis Bad)
    (hbasisRejected : ∀ b : Axis, b ∈ basis → Rejected b)
    (hrejectUp : UpwardClosed le Rejected) :
    ∀ x : Axis, Bad x → Rejected x := by
  intro x hx
  obtain ⟨b, hb_mem, hb_le⟩ := hcover x hx
  exact hrejectUp hb_le (hbasisRejected b hb_mem)

/-- If acceptance and rejection are disjoint, then a rejected basis excludes
accepted bad axes. This is the shape needed by fail-closed validators. -/
theorem no_accepted_bad_from_rejected_basis
    (le : Axis → Axis → Prop)
    (basis : Set Axis)
    (Bad Rejected Accepted : Axis → Prop)
    (hcover : BasisCoversBad le basis Bad)
    (hbasisRejected : ∀ b : Axis, basis b → Rejected b)
    (hrejectUp : UpwardClosed le Rejected)
    (hdisjoint : ∀ x : Axis, Accepted x → Rejected x → False) :
    ∀ x : Axis, Accepted x → Bad x → False := by
  intro x hacc hbad
  exact hdisjoint x hacc (basis_rejection_lifts_to_all_bad le basis Bad Rejected hcover hbasisRejected hrejectUp x hbad)

/-- Exact bad bases reduce proof burden: if all basis elements are rejected and
rejection is upward closed, then no bad axis can be accepted. -/
theorem exact_bad_basis_excludes_accepted_bad
    (le : Axis → Axis → Prop)
    (basis : Set Axis)
    (Bad Rejected Accepted : Axis → Prop)
    (hexact : ExactBadBasis le basis Bad)
    (hbasisRejected : ∀ b : Axis, basis b → Rejected b)
    (hrejectUp : UpwardClosed le Rejected)
    (hdisjoint : ∀ x : Axis, Accepted x → Rejected x → False) :
    ∀ x : Axis, Accepted x → Bad x → False := by
  exact no_accepted_bad_from_rejected_basis le basis Bad Rejected Accepted hexact.1 hbasisRejected hrejectUp hdisjoint

/-- Antichain property is not needed for safety, but it certifies that the basis
is not padded by mutually equivalent duplicate axes. -/
theorem antichain_exact_basis_still_lifts
    (le : Axis → Axis → Prop)
    (basis : Set Axis)
    (Bad Rejected : Axis → Prop)
    (_hantichain : Antichain le basis)
    (hexact : ExactBadBasis le basis Bad)
    (hbasisRejected : ∀ b : Axis, basis b → Rejected b)
    (hrejectUp : UpwardClosed le Rejected) :
    ∀ x : Axis, Bad x → Rejected x := by
  exact basis_rejection_lifts_to_all_bad le basis Bad Rejected hexact.1 hbasisRejected hrejectUp

section GuardMinimality

variable {Guard Obligation : Type u}

/-- A guard set covers every required obligation when each required atom has at
least one selected covering guard. -/
def GuardSetCoversRequired
    (Covers : Guard → Obligation → Prop)
    (Chosen : Guard → Prop)
    (Required : Obligation → Prop) : Prop :=
  ∀ o : Obligation, Required o → ∃ g : Guard, Chosen g ∧ Covers g o

/-- A private obligation is covered by exactly one guard. This mirrors the
private-witness rows used by the JSON disaster-obligation certificate. -/
def PrivateGuardObligation
    (Covers : Guard → Obligation → Prop)
    (g : Guard)
    (o : Obligation) : Prop :=
  Covers g o ∧ ∀ h : Guard, Covers h o → h = g

/-- If a required obligation is private to one guard, every guard set that
covers all required obligations must include that guard. -/
theorem private_obligation_forces_guard
    (Covers : Guard → Obligation → Prop)
    (Chosen : Guard → Prop)
    (Required : Obligation → Prop)
    {g : Guard}
    {o : Obligation}
    (hcover : GuardSetCoversRequired Covers Chosen Required)
    (hrequired : Required o)
    (hprivate : PrivateGuardObligation Covers g o) :
    Chosen g := by
  obtain ⟨h, hhChosen, hhCovers⟩ := hcover o hrequired
  have hEq : h = g := hprivate.right h hhCovers
  rwa [← hEq]

/-- Private witnesses for every selected guard prove that any guard set covering
the same required obligation universe contains the selected set. -/
theorem private_witnesses_force_selected_subset
    (Covers : Guard → Obligation → Prop)
    (Selected Chosen : Guard → Prop)
    (Required : Obligation → Prop)
    (hcover : GuardSetCoversRequired Covers Chosen Required)
    (hprivate :
      ∀ g : Guard, Selected g →
        ∃ o : Obligation, Required o ∧ PrivateGuardObligation Covers g o) :
    ∀ g : Guard, Selected g → Chosen g := by
  intro g hgSelected
  obtain ⟨o, hrequired, hpriv⟩ := hprivate g hgSelected
  exact private_obligation_forces_guard Covers Chosen Required hcover hrequired hpriv

/-- Finite guard-set form: private witnesses give a cardinality lower bound for
any guard set that covers the same required obligations. -/
theorem private_witnesses_cardinality_lower_bound
    [Fintype Guard]
    (Covers : Guard → Obligation → Prop)
    (Selected Chosen : Guard → Prop)
    (Required : Obligation → Prop)
    [DecidablePred Selected]
    [DecidablePred Chosen]
    (hcover : GuardSetCoversRequired Covers Chosen Required)
    (hprivate :
      ∀ g : Guard, Selected g →
        ∃ o : Obligation, Required o ∧ PrivateGuardObligation Covers g o) :
    (Finset.univ.filter Selected).card ≤ (Finset.univ.filter Chosen).card := by
  have hsubset :
      ∀ g : Guard, Selected g → Chosen g :=
    private_witnesses_force_selected_subset Covers Selected Chosen Required hcover hprivate
  exact Finset.card_le_card (by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact hsubset g hg)

end GuardMinimality

end DisasterAntichainBasis
end Proofs
