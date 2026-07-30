import Mathlib

namespace FCISTreeChordGateAuthority

universe uNode uValue

/-- A directed path whose constructors are locally checked edge witnesses. -/
inductive DPath {Node : Type uNode} (Edge : Node → Node → Prop) : Node → Node → Type uNode
  | nil (node : Node) : DPath Edge node node
  | cons {source middle target : Node} :
      Edge source middle → DPath Edge middle target → DPath Edge source target

namespace DPath

/-- Execute edge transports along a directed path. -/
def run
    {Node : Type uNode}
    {Value : Type uValue}
    {Edge : Node → Node → Prop}
    (transport : {source target : Node} → Edge source target → Value → Value) :
    {source target : Node} → DPath Edge source target → Value → Value
  | _, _, .nil _, value => value
  | _, _, .cons edge rest, value =>
      run transport rest (transport edge value)

/--
If every declared edge transports its source canonical value to the exact target
canonical value, every declared path reaches that target value.  This theorem
requires no inverse: decoding, authentication, authorization, commit, reopen,
and delivery maps may all be non-injective.
-/
theorem run_eq_canonical
    {Node : Type uNode}
    {Value : Type uValue}
    {Edge : Node → Node → Prop}
    (canonical : Node → Value)
    (transport : {source target : Node} → Edge source target → Value → Value)
    (edgeCoherent : ∀ {source target : Node} (edge : Edge source target),
      transport edge (canonical source) = canonical target)
    {source target : Node}
    (path : DPath Edge source target) :
    run transport path (canonical source) = canonical target := by
  induction path with
  | nil node => rfl
  | @cons source middle target edge rest inductionHypothesis =>
      simp only [run]
      rw [edgeCoherent edge]
      exact inductionHypothesis

/-- Local edge coherence makes any two declared paths with common endpoints agree. -/
theorem two_paths_agree
    {Node : Type uNode}
    {Value : Type uValue}
    {Edge : Node → Node → Prop}
    (canonical : Node → Value)
    (transport : {source target : Node} → Edge source target → Value → Value)
    (edgeCoherent : ∀ {source target : Node} (edge : Edge source target),
      transport edge (canonical source) = canonical target)
    {source target : Node}
    (left right : DPath Edge source target) :
    run transport left (canonical source) = run transport right (canonical source) := by
  rw [run_eq_canonical canonical transport edgeCoherent left]
  rw [run_eq_canonical canonical transport edgeCoherent right]

/-- Any edge-local invariant composes along every declared path. -/
theorem invariant_of_edges
    {Node : Type uNode}
    {Edge : Node → Node → Prop}
    (Invariant : Node → Prop)
    (edgePreserves : ∀ {source target : Node},
      Edge source target → Invariant source → Invariant target)
    {source target : Node}
    (path : DPath Edge source target)
    (sourceInvariant : Invariant source) :
    Invariant target := by
  induction path with
  | nil node => exact sourceInvariant
  | @cons source middle target edge rest inductionHypothesis =>
      exact inductionHypothesis (edgePreserves edge sourceInvariant)

end DPath

/-- Every gate strictly below `stage` has a recorded crossing receipt. -/
def GateComplete (stage : Nat) (crossed : Finset Nat) : Prop :=
  ∀ gate, gate < stage → gate ∈ crossed

/-- The source stage requires no gate receipt. -/
theorem gateComplete_zero : GateComplete 0 ∅ := by
  intro gate impossible
  omega

/-- Same-stage edges preserve a complete gate prefix. -/
theorem gateComplete_stay
    (stage : Nat)
    (crossed : Finset Nat)
    (complete : GateComplete stage crossed) :
    GateComplete stage crossed :=
  complete

/-- Crossing exactly one stage and recording that stage preserves completeness. -/
theorem gateComplete_cross
    (stage : Nat)
    (crossed : Finset Nat)
    (complete : GateComplete stage crossed) :
    GateComplete (stage + 1) (insert stage crossed) := by
  intro gate gateBeforeTarget
  by_cases gate = stage
  · simp [gate, Finset.mem_insert]
  · have gateBeforeSource : gate < stage := by omega
    exact Finset.mem_insert_of_mem (complete gate gateBeforeSource)

/--
A monotone unit edge that crosses a level is exactly that level's gate edge.
This is the local arithmetic core of the filtration argument.
-/
theorem unit_stage_edge_crosses_unique_gate
    (sourceStage targetStage gate : Nat)
    (monotone : sourceStage ≤ targetStage)
    (unitStep : targetStage ≤ sourceStage + 1)
    (beforeGate : sourceStage ≤ gate)
    (afterGate : gate < targetStage) :
    sourceStage = gate ∧ targetStage = gate + 1 := by
  omega

/-- A unit authority edge cannot skip two or more theorem-bearing stages. -/
theorem unit_stage_edge_cannot_skip
    (sourceStage targetStage : Nat)
    (unitStep : targetStage ≤ sourceStage + 1) :
    ¬ sourceStage + 1 < targetStage := by
  omega

/-- Equal lineage environments remain equal after the same deterministic binding. -/
theorem equal_lineage_extension
    {Role Digest : Type}
    [DecidableEq Role]
    (left right : Role → Option Digest)
    (role : Role)
    (digest : Digest)
    (same : left = right) :
    Function.update left role (some digest) =
      Function.update right role (some digest) := by
  simpa [same]

#print axioms DPath.run_eq_canonical
#print axioms DPath.two_paths_agree
#print axioms DPath.invariant_of_edges
#print axioms gateComplete_zero
#print axioms gateComplete_stay
#print axioms gateComplete_cross
#print axioms unit_stage_edge_crosses_unique_gate
#print axioms unit_stage_edge_cannot_skip
#print axioms equal_lineage_extension

end FCISTreeChordGateAuthority
