import Proofs.ZenoDEXExactOutManyPoolConcreteKeyCoverWitness
import Proofs.ZenoDEXExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge

open scoped Classical

/-!
# Exact-Out Many-Pool Repaired Key-Cover Witness Extraction

This file promotes the Aristotle-discovered witness-extraction bridge from the
proof packet into the repo proof surface.

It closes the small runtime-style gap between:

- selected-winner candidate rows, and
- the abstract `SelectedKeyMinimumWitness` consumed by the repaired key-cover
  semantic bridge.

The concrete domination-row to `KeyCover` bridge is supplied by
`ZenoDEXExactOutManyPoolConcreteKeyCoverWitness`.
-/

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolRepairedKeyCoverWitnessExtraction

open ExactOutCanonicalMinimizer
open ExactOutManyPoolConcreteKeyCoverWitness
open ExactOutManyPoolKeyCoverBridge
open TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket
open TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverSemanticBridge
open TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge

noncomputable section

/-- Runtime-style selected-winner evidence after the index/match/minimality
checks pass. `candidateKeys` is the concrete candidate-key stream emitted by the
runtime certificate; `coversSelectedKeys` links that stream to the abstract
`selectedKeys` finset. -/
structure ConcreteSelectedWinnerWitness
    (PoolId : Type) [LinearOrder PoolId]
    (selectedKeys : Finset (Key PoolId)) where
  kStar : Key PoolId
  candidateKeys : List (Key PoolId)
  coversSelectedKeys : ∀ k, k ∈ selectedKeys ↔ k ∈ candidateKeys
  winnerInCandidates : kStar ∈ candidateKeys
  winnerMinimalInCandidates :
    ∀ k, k ∈ candidateKeys → kStar ≤ k

/-- Concrete selected-winner rows construct the abstract selected-minimum witness
expected by the repaired key-cover semantic bridge. -/
def concreteSelectedWinner_implies_selectedMinimumWitness
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys : Finset (Key PoolId)}
    (w : ConcreteSelectedWinnerWitness PoolId selectedKeys) :
    SelectedKeyMinimumWitness selectedKeys :=
  { kStar := w.kStar
    selectedMem := (w.coversSelectedKeys w.kStar).mpr w.winnerInCandidates
    minimalSelected := fun k hk =>
      w.winnerMinimalInCandidates k ((w.coversSelectedKeys k).mp hk) }

/-- Concrete runtime witness rows discharge the existing interpretation bridge.

This theorem composes:

- verified interpretation-packet booleans,
- concrete selected-winner extraction, and
- concrete domination rows proving key cover.

It intentionally keeps `hSubset` explicit because the runtime packet's
`selectedKeysSubsetFullKeys` boolean still needs a separate selected/full key
membership interpretation.
-/
theorem concreteRuntimeWitnesses_discharge_interpretation_bridge
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys fullKeys : Finset (Key PoolId)}
    (keyCoverInputs : KeyCoverInputs)
    (interpInputs : InterpretationInputs)
    (hInterpOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket interpInputs).packetOk = true)
    (hKeyCoverAligned :
      interpInputs.keyCoverPacketOk =
        (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket.buildPacket keyCoverInputs).packetOk)
    (selectedWitness : ConcreteSelectedWinnerWitness PoolId selectedKeys)
    (coverWitness : ConcreteKeyCoverWitness PoolId selectedKeys fullKeys)
    (hSubset : ∀ k, k ∈ selectedKeys → k ∈ fullKeys) :
    ∃! k, k ∈ fullKeys ∧ ∀ y, y ∈ fullKeys → k ≤ y := by
  exact TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge.packetOk_and_interpretation_implies_full_canonical_exists
    keyCoverInputs interpInputs hInterpOk hKeyCoverAligned
    (fun _ _ _ => concreteSelectedWinner_implies_selectedMinimumWitness selectedWitness)
    (fun _ _ hk => hSubset _ hk)
    (fun _ _ _ _ _ => concreteWitness_implies_keyCover coverWitness)

end
end ExactOutManyPoolRepairedKeyCoverWitnessExtraction
end ZenoDEX
end TauSwap

