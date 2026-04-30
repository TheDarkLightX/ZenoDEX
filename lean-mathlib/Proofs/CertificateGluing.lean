import Mathlib

/-!
# Certificate Gluing

This module proves a generic theorem layer for eliminating
cross-surface disaster states.

The intended ZenoDEX use:

- Quote, route, settlement, oracle, app-hash, and signer-registry certificates
  are local views of one intended global protocol state.
- A local bundle is safe only if the views glue into at least one global state.
- If local views glue uniquely, then there is no ambiguity drift between
  surfaces.
- If the accepted path is sound with respect to gluing, an inconsistent bundle
  cannot be accepted.

This turns cross-surface validation into a small algebra of global sections.
-/

namespace Proofs
namespace CertificateGluing

universe u v w

variable {Ix : Type u}
variable {Global : Type v}
variable {View : Ix → Type w}

/-- A bundle stores one local certificate/view for each surface. -/
structure Bundle (View : Ix → Type w) where
  view : (i : Ix) → View i

variable (restrict : (i : Ix) → Global → View i)

/-- A global state realizes a local bundle when every local view is the
restriction/projection of that global state. -/
def RealizedBy (b : Bundle View) (g : Global) : Prop :=
  ∀ i : Ix, b.view i = restrict i g

/-- The bundle has a global section. -/
def HasGlobalSection (b : Bundle View) : Prop :=
  ∃ g : Global, RealizedBy restrict b g

/-- A bundle is inconsistent when no global state realizes all local views. -/
def InconsistentBundle (b : Bundle View) : Prop :=
  ¬ HasGlobalSection restrict b

/-- A restriction family separates global states when equal local views force
equal global states. -/
def SeparatesPoints : Prop :=
  ∀ g h : Global, (∀ i : Ix, restrict i g = restrict i h) → g = h

/-- A local compatibility checker is complete if compatibility implies gluing. -/
def CompatibilityComplete (Compatible : Bundle View → Prop) : Prop :=
  ∀ b : Bundle View, Compatible b → HasGlobalSection restrict b

/-- Accepted bundles are gluing-sound when every accepted bundle has a global
section. -/
def AcceptedSound (Accepted : Bundle View → Prop) : Prop :=
  ∀ b : Bundle View, Accepted b → HasGlobalSection restrict b

/-- If acceptance is gluing-sound, no inconsistent bundle can be accepted. -/
theorem accepted_sound_excludes_inconsistent
    (Accepted : Bundle View → Prop)
    (hsound : AcceptedSound restrict Accepted) :
    ∀ b : Bundle View, Accepted b → InconsistentBundle restrict b → False := by
  intro b hacc hinc
  exact hinc (hsound b hacc)

/-- Complete compatibility plus an acceptance rule guarded by compatibility
excludes inconsistent accepted bundles. -/
theorem compatible_acceptance_excludes_inconsistent
    (Compatible Accepted : Bundle View → Prop)
    (hcomplete : CompatibilityComplete restrict Compatible)
    (hacceptedCompatible : ∀ b : Bundle View, Accepted b → Compatible b) :
    ∀ b : Bundle View, Accepted b → InconsistentBundle restrict b → False := by
  intro b hacc hinc
  exact hinc (hcomplete b (hacceptedCompatible b hacc))

/-- If restrictions separate points, a bundle has at most one global section. -/
theorem global_section_unique_of_separates
    (hsep : SeparatesPoints restrict) :
    ∀ (b : Bundle View) (g h : Global),
      RealizedBy restrict b g → RealizedBy restrict b h → g = h := by
  intro b g h hg hh
  apply hsep
  intro i
  have := hg i
  have := hh i
  rw [← this, ← hg i]

/-- Unique gluing gives a canonical global state from any chosen witness. -/
theorem canonical_global_state_of_unique_gluing
    (hsep : SeparatesPoints restrict)
    (b : Bundle View)
    (g h : Global)
    (hg : RealizedBy restrict b g)
    (hh : RealizedBy restrict b h) :
    g = h := by
  exact global_section_unique_of_separates restrict hsep b g h hg hh

/-- A global-safe predicate can be transported through a realized bundle. -/
def BundleForcesGlobalSafe
    (Safe : Global → Prop)
    (b : Bundle View) : Prop :=
  ∀ g : Global, RealizedBy restrict b g → Safe g

/-- If accepted bundles always glue and force global safety, then accepted
bundles cannot realize a globally bad state. -/
theorem accepted_glued_bundle_excludes_global_bad
    (Accepted : Bundle View → Prop)
    (Safe Bad : Global → Prop)
    (_hsound : AcceptedSound restrict Accepted)
    (hforces : ∀ b : Bundle View, Accepted b → BundleForcesGlobalSafe restrict Safe b)
    (hdisjoint : ∀ g : Global, Safe g → Bad g → False) :
    ∀ (b : Bundle View) (g : Global),
      Accepted b → RealizedBy restrict b g → Bad g → False := by
  intro b g hacc hreal hbad
  exact hdisjoint g (hforces b hacc g hreal) hbad

/-- Full cross-surface disaster exclusion: accepted bundles are compatible,
compatibility is complete, compatibility forces global safety, and safe states
are disjoint from globally bad states. -/
theorem compatible_gluing_excludes_cross_surface_disaster
    (Compatible Accepted : Bundle View → Prop)
    (Safe Bad : Global → Prop)
    (_hcomplete : CompatibilityComplete restrict Compatible)
    (_hacceptedCompatible : ∀ b : Bundle View, Accepted b → Compatible b)
    (hforces : ∀ b : Bundle View, Accepted b → BundleForcesGlobalSafe restrict Safe b)
    (hdisjoint : ∀ g : Global, Safe g → Bad g → False) :
    ∀ (b : Bundle View) (g : Global),
      Accepted b → RealizedBy restrict b g → Bad g → False := by
  intro b g hacc hreal hbad
  exact hdisjoint g (hforces b hacc g hreal) hbad

/-! ## Reusable Helper Lemmas

Additional sheaf/global-section lemmas that support downstream
quote-settlement and oracle-apphash-signer consistency validators. -/

/-- A bundle constructed by restricting a global state always has a global section. -/
theorem hasGlobalSection_of_restrict (g : Global) :
    HasGlobalSection restrict ⟨fun i => restrict i g⟩ :=
  ⟨g, fun _ => rfl⟩

/-- Soundness composes: if `Accepted₁` implies `Accepted₂` and `Accepted₂` is sound,
then `Accepted₁` is sound. -/
theorem acceptedSound_of_implies
    (Accepted₁ Accepted₂ : Bundle View → Prop)
    (h : ∀ b, Accepted₁ b → Accepted₂ b)
    (hsound : AcceptedSound restrict Accepted₂) :
    AcceptedSound restrict Accepted₁ :=
  fun b ha => hsound b (h b ha)

/-- Conjunction of two sound acceptance predicates is sound. -/
theorem acceptedSound_and
    (A₁ A₂ : Bundle View → Prop)
    (h₁ : AcceptedSound restrict A₁) :
    AcceptedSound restrict (fun b => A₁ b ∧ A₂ b) :=
  fun b ⟨ha, _⟩ => h₁ b ha

/-- An inconsistent bundle stays inconsistent under any restriction family. -/
theorem inconsistent_no_witness
    (b : Bundle View)
    (hinc : InconsistentBundle restrict b) :
    ∀ g : Global, ¬ RealizedBy restrict b g :=
  fun g hg => hinc ⟨g, hg⟩

/-- If the restriction family separates points, `HasGlobalSection` implies
a unique witness, i.e., the global section is a partial function. -/
theorem unique_witness_of_separates
    (hsep : SeparatesPoints restrict)
    (b : Bundle View)
    (hsec : HasGlobalSection restrict b) :
    ∃! g : Global, RealizedBy restrict b g := by
  obtain ⟨g, hg⟩ := hsec
  exact ⟨g, hg, fun h hh => global_section_unique_of_separates restrict hsep b h g hh hg⟩

end CertificateGluing
end Proofs
