import Mathlib

/-!
# Forbidden Trace Minor Calculus

This module proves a generic theorem layer for compressing disaster traces into
small forbidden motifs.

The intended ZenoDEX use is:

- mine or define a small set of forbidden trace motifs
- prove every bad trace contains one of those motifs
- prove rejection/blocking lifts from a motif to any trace embedding it
- conclude that the whole bad trace family is rejected

This is a schema. Concrete assurance still requires instantiating `Trace`,
`Embeds`, motif coverage, and guard soundness against specific quote,
settlement, oracle, reward, signer, routing, or API-resource traces.
-/

namespace Proofs
namespace ForbiddenTraceMinor

universe u v

variable {Trace : Type u}
variable {Guard : Type v}

variable (Embeds : Trace → Trace → Prop)

/-- A predicate is embedding-upward when it survives adding irrelevant context
around the motif. -/
def EmbeddingUpwardClosed (P : Trace → Prop) : Prop :=
  ∀ ⦃m t : Trace⦄, Embeds m t → P m → P t

/-- A forbidden motif set covers bad traces when every bad trace contains one
forbidden motif. -/
def MotifCoversBad (motifs : Set Trace) (Bad : Trace → Prop) : Prop :=
  ∀ t : Trace, Bad t → ∃ m : Trace, motifs m ∧ Embeds m t

/-- List-shaped version used by generated replay receipts. -/
def ListMotifCoversBad (motifs : List Trace) (Bad : Trace → Prop) : Prop :=
  ∀ t : Trace, Bad t → ∃ m : Trace, m ∈ motifs ∧ Embeds m t

/-- The motif set is minimal up to mutual embedding. This is an audit-quality
property, not needed for safety. -/
def MotifAntichain (motifs : Set Trace) : Prop :=
  ∀ ⦃a b : Trace⦄, motifs a → motifs b → Embeds a b → Embeds b a → a = b

/-- A guard blocks a motif. -/
def GuardBlocksMotif (Blocks : Guard → Trace → Prop) (guards : Set Guard) (m : Trace) : Prop :=
  ∃ g : Guard, guards g ∧ Blocks g m

/-- Every forbidden motif has at least one guard hitting it. -/
def GuardsHitAllMotifs (Blocks : Guard → Trace → Prop) (guards : Set Guard) (motifs : Set Trace) : Prop :=
  ∀ m : Trace, motifs m → GuardBlocksMotif Blocks guards m

/-- Rejecting forbidden motifs rejects every bad trace when rejection lifts
through embedding. -/
theorem motif_rejection_lifts_to_all_bad
    (motifs : Set Trace)
    (Bad Rejected : Trace → Prop)
    (hcover : MotifCoversBad Embeds motifs Bad)
    (hmotifsRejected : ∀ m : Trace, motifs m → Rejected m)
    (hrejectUp : EmbeddingUpwardClosed Embeds Rejected) :
    ∀ t : Trace, Bad t → Rejected t := by
  intro t hbad
  obtain ⟨m, hm, hemb⟩ := hcover t hbad
  exact hrejectUp hemb (hmotifsRejected m hm)

/-- List-shaped receipt theorem. -/
theorem list_motif_rejection_lifts_to_all_bad
    (motifs : List Trace)
    (Bad Rejected : Trace → Prop)
    (hcover : ListMotifCoversBad Embeds motifs Bad)
    (hmotifsRejected : ∀ m : Trace, m ∈ motifs → Rejected m)
    (hrejectUp : EmbeddingUpwardClosed Embeds Rejected) :
    ∀ t : Trace, Bad t → Rejected t := by
  intro t hbad
  obtain ⟨m, hm, hemb⟩ := hcover t hbad
  exact hrejectUp hemb (hmotifsRejected m hm)

/-- If accepted and rejected traces are disjoint, forbidden motif rejection
excludes accepted bad traces. -/
theorem forbidden_motifs_exclude_accepted_bad
    (motifs : Set Trace)
    (Bad Rejected Accepted : Trace → Prop)
    (hcover : MotifCoversBad Embeds motifs Bad)
    (hmotifsRejected : ∀ m : Trace, motifs m → Rejected m)
    (hrejectUp : EmbeddingUpwardClosed Embeds Rejected)
    (hdisjoint : ∀ t : Trace, Accepted t → Rejected t → False) :
    ∀ t : Trace, Accepted t → Bad t → False := by
  intro t hacc hbad
  exact hdisjoint t hacc
    (motif_rejection_lifts_to_all_bad Embeds motifs Bad Rejected hcover hmotifsRejected hrejectUp t hbad)

/-- Guard hitting theorem: if every forbidden motif is hit by a guard, and a
guard hit on an embedded motif rejects the containing trace, then all bad traces
are rejected. -/
theorem guard_hitting_set_rejects_all_bad
    (motifs : Set Trace)
    (Bad Rejected : Trace → Prop)
    (Blocks : Guard → Trace → Prop)
    (guards : Set Guard)
    (hcover : MotifCoversBad Embeds motifs Bad)
    (hhit : GuardsHitAllMotifs Blocks guards motifs)
    (hguardSound :
      ∀ (g : Guard) (m t : Trace),
        guards g → Blocks g m → Embeds m t → Rejected t) :
    ∀ t : Trace, Bad t → Rejected t := by
  intro t hbad
  obtain ⟨m, hm, hemb⟩ := hcover t hbad
  obtain ⟨g, hg, hblocks⟩ := hhit m hm
  exact hguardSound g m t hg hblocks hemb

/-- If the motif basis is an antichain, the same safety lift holds while also
recording that the basis is minimal/non-duplicative up to embedding equivalence. -/
theorem antichain_motif_basis_rejection_lifts
    (motifs : Set Trace)
    (Bad Rejected : Trace → Prop)
    (_hantichain : MotifAntichain Embeds motifs)
    (hcover : MotifCoversBad Embeds motifs Bad)
    (hmotifsRejected : ∀ m : Trace, motifs m → Rejected m)
    (hrejectUp : EmbeddingUpwardClosed Embeds Rejected) :
    ∀ t : Trace, Bad t → Rejected t := by
  exact motif_rejection_lifts_to_all_bad Embeds motifs Bad Rejected hcover hmotifsRejected hrejectUp

end ForbiddenTraceMinor
end Proofs
