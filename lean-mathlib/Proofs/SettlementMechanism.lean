import Proofs.SettlementCanonicalExecution

/-!
# Global Settlement Mechanism Interface

This file packages the canonical settlement bridge as a reusable global theorem
schema for any DEX mechanism that implements the settlement interface.

The theorem is intentionally conditional: arbitrary code called a "DEX
mechanism" is not safe by name.  A mechanism becomes covered by the global
settlement algebra only after it supplies the explicit obligations below:

* exact runtime generator coverage,
* a winner certificate over the emitted keys,
* winner feasibility in the projected feasible domain, and
* runtime trace realization of the selected candidate.

Once those obligations are checked, the mechanism inherits canonical safe
settlement without reproving the batch objective theorem.
-/

namespace TauSwap
namespace SettlementMechanism

open BatchCPMMUnification
open SettlementCanonicalExecution

abbrev Key := _root_.TauSwap.Batch.Key

/-- Abstract interface exposed by any mechanism that wants to reuse the global
settlement theorem.  The concrete mechanism may be CPMM, routing, batch auction,
orderbook, perps settlement, or another certified executor; this interface only
records the finite feasible domain, the emitted runtime key list, the selected
candidate, and the trace that was actually executed. -/
structure Mechanism where
  Candidate : Type
  domain : Finset Candidate
  emitted : List Key
  keyOf : Candidate → Key
  selected : SettlementCandidate
  trace : BatchSettlement

/-- The feasible domain as canonical settlement keys. -/
def feasibleKeys (M : Mechanism) : Finset Key :=
  M.domain.image M.keyOf

/-- Exact generator coverage: after forgetting order and duplicates, the
runtime-emitted key list is exactly the feasible key image. -/
def GeneratorExact (M : Mechanism) : Prop :=
  M.emitted.toFinset = feasibleKeys M

/-- Runtime winner certificate over the emitted list. -/
def WinnerCertified (M : Mechanism) : Prop :=
  ListCertificateOK M.emitted M.selected.key

/-- The selected candidate's key is feasible for this mechanism. -/
def WinnerFeasible (M : Mechanism) : Prop :=
  M.selected.key ∈ feasibleKeys M

/-- The executed runtime trace realizes the selected candidate. -/
def TraceRealizesWinner (M : Mechanism) : Prop :=
  Realizes M.trace M.selected

/-- Complete obligation bundle needed to instantiate the global settlement
algebra for a concrete mechanism. -/
structure SettlementObligations (M : Mechanism) : Prop where
  generator_exact : GeneratorExact M
  winner_certified : WinnerCertified M
  winner_feasible : WinnerFeasible M
  trace_realizes_winner : TraceRealizesWinner M

/-- The canonical safe-settlement property exported by the global theorem. -/
def CanonicalSafeSettlement (M : Mechanism) : Prop :=
  batchToSettlement M.trace = batchToSettlement M.selected.batch ∧
    M.selected.key ∈ feasibleKeys M ∧
    (∀ x ∈ feasibleKeys M,
      (batchAB M.trace).1 ≥ _root_.TauSwap.Batch.vol x) ∧
    (∀ x ∈ feasibleKeys M,
      (batchAB M.trace).1 = _root_.TauSwap.Batch.vol x →
        (batchAB M.trace).2 ≥ _root_.TauSwap.Batch.sur x) ∧
    (∀ x ∈ feasibleKeys M,
      (batchAB M.trace).1 = _root_.TauSwap.Batch.vol x →
        (batchAB M.trace).2 = _root_.TauSwap.Batch.sur x →
          M.selected.order ≤ _root_.TauSwap.Batch.ord x)

/-- Exact generator coverage supplies the list-coverage obligation expected by
the lower-level canonical execution theorem. -/
theorem generatorExact_coversKeyList
    (M : Mechanism)
    (hgen : GeneratorExact M) :
    CoversKeyList M.emitted M.domain M.keyOf := by
  exact coversKeyList_of_toFinset_eq_image hgen

/-- The global settlement algebra theorem: every mechanism satisfying the
settlement obligations executes a canonical safe settlement over its feasible
key image. -/
theorem obligations_imply_canonical_safe
    (M : Mechanism)
    (h : SettlementObligations M) :
    CanonicalSafeSettlement M := by
  exact realized_runtime_list_certificate_executes_canonical_of_toFinset_eq_image
    h.winner_certified h.generator_exact h.winner_feasible
    h.trace_realizes_winner

/-- A certified mechanism family is any predicate over mechanisms together with
a proof that accepted mechanisms satisfy the settlement obligations. -/
structure CertifiedMechanismFamily where
  accepts : Mechanism → Prop
  obligations : ∀ M, accepts M → SettlementObligations M

/-- Any mechanism accepted by a certified family inherits canonical safe
settlement.  This is the reusable family-level form for CPMM, orderbook, routing,
perps settlement, and future mechanism families. -/
theorem accepted_mechanism_canonical_safe
    (F : CertifiedMechanismFamily)
    (M : Mechanism)
    (haccepts : F.accepts M) :
    CanonicalSafeSettlement M :=
  obligations_imply_canonical_safe M (F.obligations M haccepts)

/-- Direct component form used by concrete adapters and certificate checkers. -/
theorem global_settlement_algebra
    (M : Mechanism)
    (hgen : GeneratorExact M)
    (hcert : WinnerCertified M)
    (hfeasible : WinnerFeasible M)
    (hreal : TraceRealizesWinner M) :
    CanonicalSafeSettlement M := by
  exact obligations_imply_canonical_safe M
    ⟨hgen, hcert, hfeasible, hreal⟩

end SettlementMechanism
end TauSwap
