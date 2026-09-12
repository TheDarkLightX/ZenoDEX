import Proofs.AssetLaneCustodyCoordinatorOutcomeV2

/-!
Complete coordinator admission through actual ordered outcomes and histories.

The imported model derives its leaf verdict, complete successor and every guard
internally. The task must establish preservation from initial admission and
typed command shape, including rejected attempts and arbitrary observed source
packets. It must not assume that each transition succeeds or that its successor
is admitted. All imported definitions and the three theorem statements are fixed.

Scope: the finite Lean model's constructor and policy-origin relation. Arbitrary
source effects do not become authorized by these state-preservation theorems.
Exact finite-source refinement, runtime decoding/hashing, cryptographic receipt
validity and publication remain separate obligations.
-/

namespace Proofs.AssetLaneCustodyCoordinatorTraceV2

open Proofs.AssetLaneCustodyCoordinatorOutcomeV2

/-- Recover the actual acceptance guards from a returned accepted outcome.
No accepted guard or externally supplied successor is a hypothesis. -/
theorem accepted_exposes_checked_frame
    {roots : Roots} {commits : Commitments} {pre : D.FullState}
    {action : Input} {source : SourceCandidate} {result : Accepted}
    (accepted : transition roots commits pre action source = .accepted result) :
    A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre ∧
      leafVerdict roots.digest pre action.leaf = none ∧
      ∃ occurrence,
        occurrenceId action.leaf = some occurrence ∧
        SourceBindings roots commits pre action occurrence source ∧
        Projection roots pre action source ∧
        D.Resources (D.step roots.digest pre action.leaf) ∧
        Reprojection roots.digest pre action.leaf ∧
        result = completed roots commits pre action source := by
  -- Stage 1 must have passed, else the coordinator returns REGISTRY_BINDING_MISMATCH.
  have bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre := by
    by_contra mismatch
    rw [registry_binding_mismatch_precedes_leaf roots commits pre action source mismatch]
      at accepted
    simp at accepted
  -- Stage 2 must have accepted the leaf, else its exact code is returned.
  have verdict : leafVerdict roots.digest pre action.leaf = none := by
    cases route : leafVerdict roots.digest pre action.leaf with
    | none => rfl
    | some code =>
        rw [(leaf_rejection_preserves_route_and_code roots commits pre action source code
          bindings route).1] at accepted
        simp at accepted
  obtain ⟨occurrence, present⟩ :=
    accepted_leaf_has_occurrence roots.digest pre action.leaf verdict
  have staged : transition roots commits pre action source =
      stages roots commits pre action source occurrence := by
    unfold transition
    rw [if_pos bindings]
    simp only [verdict, present]
  rw [staged] at accepted
  unfold stages at accepted
  -- Each remaining stage must have passed, else a coordinator code is returned.
  have sourceOk : SourceBindings roots commits pre action occurrence source := by
    by_contra mismatch
    rw [if_neg mismatch] at accepted
    simp at accepted
  rw [if_pos sourceOk] at accepted
  have projected : Projection roots pre action source := by
    by_contra mismatch
    rw [if_neg mismatch] at accepted
    simp at accepted
  rw [if_pos projected] at accepted
  have fits : D.Resources (D.step roots.digest pre action.leaf) := by
    by_contra mismatch
    rw [if_neg mismatch] at accepted
    simp at accepted
  rw [if_pos fits] at accepted
  have reprojected : Reprojection roots.digest pre action.leaf := by
    by_contra mismatch
    rw [if_neg mismatch] at accepted
    simp at accepted
  rw [if_pos reprojected] at accepted
  exact ⟨bindings, verdict, occurrence, present, sourceOk, projected, fits, reprojected,
    by simpa using accepted.symm⟩

/-- Every actual returned outcome preserves the complete modeled constructor
and policy bindings. Resource-failing and all other rejected attempts retain
the original state; successful attempts obtain resource admission from the
actual coordinator guard, never a separate post-fit hypothesis. -/
theorem transition_preserves_complete_admission
    {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop}
    (roots : Roots) (commits : Commitments)
    (pre : D.FullState) (action : Input) (source : SourceCandidate)
    (initial : A.ConstructorAdmission rootSyntax namespaceSyntax pre)
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (input : X.ActionAdmission action.leaf) :
    A.ConstructorAdmission rootSyntax namespaceSyntax
        (transition roots commits pre action source).postState ∧
      A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy
        (transition roots commits pre action source).postState := by
  cases outcome : transition roots commits pre action source with
  | accepted result =>
      obtain ⟨-, -, occurrence, -, -, -, fits, -, shape⟩ :=
        accepted_exposes_checked_frame outcome
      have post : (Outcome.accepted result : Outcome pre).postState =
          D.step roots.digest pre action.leaf := by
        rw [shape]; rfl
      rw [post]
      exact ⟨A.step_preserves_constructor_admission roots.digest initial input fits,
        A.policy_origin_bindings_preserved roots.digest pre action.leaf bindings⟩
  | rejected code =>
      have post : (Outcome.rejected code : Outcome pre).postState = pre := rfl
      rw [post]
      exact ⟨initial, bindings⟩

/-- Fold the actual coordinator outcomes; rejected attempts are included. -/
def execute (roots : Roots) (commits : Commitments) (initial : D.FullState)
    (attempts : List (Input × SourceCandidate)) : D.FullState :=
  attempts.foldl
    (fun state attempt => (transition roots commits state attempt.1 attempt.2).postState)
    initial

/-- Certified initialization and per-command shape suffice at every prefix.
This does not assume a state invariant, successful acceptance, resource fit,
source validity or restored admission separately at each history position. -/
theorem every_prefix_preserves_complete_admission
    {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop}
    (roots : Roots) (commits : Commitments) (initial : D.FullState)
    (attempts : List (Input × SourceCandidate))
    (admitted : A.ConstructorAdmission rootSyntax namespaceSyntax initial)
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy initial)
    (inputs : ∀ attempt ∈ attempts, X.ActionAdmission attempt.1.leaf) :
    ∀ front rest, attempts = front ++ rest →
      A.ConstructorAdmission rootSyntax namespaceSyntax
          (execute roots commits initial front) ∧
        A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy
          (execute roots commits initial front) := by
  have general : ∀ (front : List (Input × SourceCandidate)) (state : D.FullState),
      A.ConstructorAdmission rootSyntax namespaceSyntax state →
      A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy state →
      (∀ attempt ∈ front, X.ActionAdmission attempt.1.leaf) →
      A.ConstructorAdmission rootSyntax namespaceSyntax (execute roots commits state front) ∧
        A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy
          (execute roots commits state front) := by
    intro front
    induction front with
    | nil => intro state admittedState bindingsState _; exact ⟨admittedState, bindingsState⟩
    | cons attempt tail ih =>
        intro state admittedState bindingsState shapes
        have stepped := transition_preserves_complete_admission roots commits state
          attempt.1 attempt.2 admittedState bindingsState (shapes attempt (by simp))
        have unfold_execute : execute roots commits state (attempt :: tail) =
            execute roots commits (transition roots commits state attempt.1 attempt.2).postState
              tail := rfl
        rw [unfold_execute]
        exact ih _ stepped.1 stepped.2 (fun other mem => shapes other (by simp [mem]))
  intro front rest split
  exact general front initial admitted bindings
    (fun attempt mem => inputs attempt (by rw [split]; exact List.mem_append_left _ mem))

end Proofs.AssetLaneCustodyCoordinatorTraceV2
