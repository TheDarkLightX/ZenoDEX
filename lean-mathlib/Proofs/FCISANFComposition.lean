import Proofs.FCISDurableRetraction
import Proofs.FCISTreeChordGateAuthority

namespace FCISANFComposition

universe uLineage uPayload uA uD

/-- The lineage coordinates that must remain aligned through the ANF path. -/
structure ANFLineagePath (Lineage : Type uLineage) where
  sourceLineage : Lineage
  semanticLineage : Lineage
  receiptLineage : Lineage
  bundleLineage : Lineage
  effectLineage : Lineage

/-- A durable effect together with the lineage coordinates it claims. -/
structure AcceptedDurableEffect
    (Lineage : Type uLineage)
    (Payload : Type uPayload) where
  path : ANFLineagePath Lineage
  payload : Payload

/-- Horizontal semantic and artifact roots must have one source lineage. -/
structure HorizontalArtifactCoherence
    {Lineage : Type uLineage}
    {Payload : Type uPayload}
    (candidate : AcceptedDurableEffect Lineage Payload) : Prop where
  semantic_matches_source :
    candidate.path.semanticLineage = candidate.path.sourceLineage

/-- Global path and gate evidence must preserve the semantic lineage. -/
structure GlobalPathGateCoherence
    {Lineage : Type uLineage}
    {Payload : Type uPayload}
    (stage : Nat)
    (crossed : Finset Nat)
    (candidate : AcceptedDurableEffect Lineage Payload) : Prop where
  receipt_matches_semantic :
    candidate.path.receiptLineage = candidate.path.semanticLineage
  gate_receipt_complete :
    FCISTreeChordGateAuthority.GateComplete stage crossed

/--
Vertical durable retraction is explicit about the partial reopen result.  The
lineage equality is the projection needed by the ANF composition theorem; the
reopen field keeps the value-or-reject boundary visible in the same witness.
-/
structure VerticalDurableRetraction
    {A : Type uA}
    {D : Type uD}
    {Lineage : Type uLineage}
    {Payload : Type uPayload}
    (retraction : FCISDurableRetraction.DurableRetraction A D)
    (candidate : AcceptedDurableEffect Lineage Payload) : Prop where
  bundle_matches_receipt :
    candidate.path.bundleLineage = candidate.path.receiptLineage
  partial_reopen_preserves_encoded_history :
    ∀ authorized,
      retraction.reopen (retraction.encode authorized) = Except.ok authorized

/-- A committed external effect retains the bundle lineage as its ancestry. -/
structure ExternalEffectAncestry
    {Lineage : Type uLineage}
    {Payload : Type uPayload}
    (candidate : AcceptedDurableEffect Lineage Payload) : Prop where
  effect_matches_bundle :
    candidate.path.effectLineage = candidate.path.bundleLineage

/--
All premises for the abstract ANF composition theorem.  Authentication and
inventory completeness are parameters and proof fields, so the theorem cannot
silently manufacture either property from an artifact root.
-/
structure ANFCompositionPremises
    {A : Type uA}
    {D : Type uD}
    {Lineage : Type uLineage}
    {Payload : Type uPayload}
    (authenticated inventoryComplete :
      AcceptedDurableEffect Lineage Payload → Prop)
    (stage : Nat)
    (crossed : Finset Nat)
    (retraction : FCISDurableRetraction.DurableRetraction A D)
    (candidate : AcceptedDurableEffect Lineage Payload) : Prop where
  authenticated_input : authenticated candidate
  inventory_complete : inventoryComplete candidate
  horizontal : HorizontalArtifactCoherence candidate
  global : GlobalPathGateCoherence stage crossed candidate
  vertical : VerticalDurableRetraction retraction candidate
  effect_ancestry : ExternalEffectAncestry candidate

/--
Abstract ANF composition: once authentication, complete inventory, horizontal
coherence, global path/gate coherence, vertical durable retraction, and effect
ancestry are all supplied, the durable effect has one source lineage.

The conclusion retains the authentication and inventory witnesses.  This keeps
the theorem's authority premises visible to downstream refinements instead of
allowing a caller-constructed candidate to promote itself.
-/
theorem accepted_durable_effect_has_one_source_lineage
    {A : Type uA}
    {D : Type uD}
    {Lineage : Type uLineage}
    {Payload : Type uPayload}
    {authenticated inventoryComplete :
      AcceptedDurableEffect Lineage Payload → Prop}
    (stage : Nat)
    (crossed : Finset Nat)
    (retraction : FCISDurableRetraction.DurableRetraction A D)
    (candidate : AcceptedDurableEffect Lineage Payload)
    (premises :
      ANFCompositionPremises authenticated inventoryComplete stage crossed
        retraction candidate) :
    ∃ source : Lineage,
      source = candidate.path.sourceLineage ∧
      candidate.path.effectLineage = source ∧
      authenticated candidate ∧ inventoryComplete candidate := by
  have effect_matches_source :
      candidate.path.effectLineage = candidate.path.sourceLineage := by
    calc
      candidate.path.effectLineage = candidate.path.bundleLineage :=
        premises.effect_ancestry.effect_matches_bundle
      _ = candidate.path.receiptLineage :=
        premises.vertical.bundle_matches_receipt
      _ = candidate.path.semanticLineage :=
        premises.global.receipt_matches_semantic
      _ = candidate.path.sourceLineage :=
        premises.horizontal.semantic_matches_source
  exact ⟨candidate.path.sourceLineage, rfl, effect_matches_source,
    ⟨premises.authenticated_input, premises.inventory_complete⟩⟩

/-- The lineage equality projection used by downstream acceptance adapters. -/
theorem accepted_effect_lineage_eq_source_lineage
    {A : Type uA}
    {D : Type uD}
    {Lineage : Type uLineage}
    {Payload : Type uPayload}
    {authenticated inventoryComplete :
      AcceptedDurableEffect Lineage Payload → Prop}
    (stage : Nat)
    (crossed : Finset Nat)
    (retraction : FCISDurableRetraction.DurableRetraction A D)
    (candidate : AcceptedDurableEffect Lineage Payload)
    (premises :
      ANFCompositionPremises authenticated inventoryComplete stage crossed
        retraction candidate) :
    candidate.path.effectLineage = candidate.path.sourceLineage := by
  obtain ⟨source, source_is_original, effect_is_source, _, _⟩ :=
    accepted_durable_effect_has_one_source_lineage stage crossed retraction
      candidate premises
  exact effect_is_source.trans source_is_original

/-- A partial reopen has exactly one of the two typed result shapes. -/
theorem partial_reopen_has_value_or_reject
    {A : Type uA}
    {D : Type uD}
    (retraction : FCISDurableRetraction.DurableRetraction A D)
    (layout : D) :
    (∃ reason : FCISDurableRetraction.Reject,
        retraction.reopen layout = Except.error reason) ∨
      (∃ history : A, retraction.reopen layout = Except.ok history) := by
  cases result : retraction.reopen layout with
  | error reason =>
      exact Or.inl ⟨reason, rfl⟩
  | ok history =>
      exact Or.inr ⟨history, rfl⟩

/-- A finite witness demonstrates the theorem without hiding its premises. -/
def exampleRetraction :
    FCISDurableRetraction.DurableRetraction Nat Nat where
  encode := id
  reopen := fun layout => Except.ok layout
  reopen_encode := by
    intro authorized
    rfl

def exampleCandidate : AcceptedDurableEffect Nat Unit where
  path :=
    { sourceLineage := 7
      semanticLineage := 7
      receiptLineage := 7
      bundleLineage := 7
      effectLineage := 7 }
  payload := ()

def exampleAuthenticated :
    AcceptedDurableEffect Nat Unit → Prop := fun _ => True

def exampleInventoryComplete :
    AcceptedDurableEffect Nat Unit → Prop := fun _ => True

def examplePremises :
    ANFCompositionPremises exampleAuthenticated exampleInventoryComplete 0 ∅
      exampleRetraction exampleCandidate where
  authenticated_input := True.intro
  inventory_complete := True.intro
  horizontal := { semantic_matches_source := rfl }
  global :=
    { receipt_matches_semantic := rfl
      gate_receipt_complete :=
        FCISTreeChordGateAuthority.gateComplete_zero }
  vertical :=
    { bundle_matches_receipt := rfl
      partial_reopen_preserves_encoded_history :=
        exampleRetraction.reopen_encode }
  effect_ancestry := { effect_matches_bundle := rfl }

example :
    ∃ source : Nat,
      source = exampleCandidate.path.sourceLineage ∧
      exampleCandidate.path.effectLineage = source ∧
      exampleAuthenticated exampleCandidate ∧
      exampleInventoryComplete exampleCandidate := by
  exact accepted_durable_effect_has_one_source_lineage 0 ∅ exampleRetraction
    exampleCandidate examplePremises

#print axioms accepted_durable_effect_has_one_source_lineage
#print axioms accepted_effect_lineage_eq_source_lineage
#print axioms partial_reopen_has_value_or_reject

end FCISANFComposition
