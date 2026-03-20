import Proofs.ZenoDEXExactOutManyPoolRepairedKeyCoverInterpretationPacket
import Proofs.ZenoDEXExactOutManyPoolRepairedKeyCoverSemanticBridge

open scoped Classical

/-!
# ZenoDEX Exact-Out Many-Pool Repaired Key-Cover Interpretation Semantic Bridge

This file closes the current proof seam between:

- the repaired key-cover interpretation packet shell, and
- the existing finite-key repaired key-cover semantic bridge.

What it proves:

- if the repaired interpretation packet verifies and `packetOk = true`,
- if its `keyCoverPacketOk` field is aligned with the repaired key-cover packet,
- and if the interpretation booleans are given their intended witness meanings,

then the selected-domain winner already lifts to the unique canonical minimum of
the full bounded key set.

What it does **not** prove:

- that the runtime booleans automatically have those witness meanings without an
  external interpretation,
- or that the unbounded/global exact-out blocker is closed.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge

open TauSwap.ZenoDEX.ExactOutCanonicalMinimizer
open TauSwap.ZenoDEX.ExactOutManyPoolKeyCoverBridge
open TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverSemanticBridge

noncomputable section

abbrev KeyCoverInputs := TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket.Inputs
abbrev KeyCoverPacketData := TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket.Packet
abbrev InterpretationInputs := TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.Inputs
abbrev InterpretationPacketData := TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.Packet

theorem packetOk_implies_keyCoverPacketOk
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.keyCoverPacketOk = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨hKeyCoverOk, _hIndex, _hMatches, _hMinimal, _hWitnessIndex, _hWitnessCover, _hWitnessKeys, _hWitnessDominate⟩
  exact hKeyCoverOk

theorem packetOk_implies_selectedWinnerIndexInRange
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.selectedWinnerIndexInRange = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨_hKeyCoverOk, hIndex, _hMatches, _hMinimal, _hWitnessIndex, _hWitnessCover, _hWitnessKeys, _hWitnessDominate⟩
  exact hIndex

theorem packetOk_implies_selectedWinnerMatchesCertificate
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.selectedWinnerMatchesCertificate = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨_hKeyCoverOk, _hIndex, hMatches, _hMinimal, _hWitnessIndex, _hWitnessCover, _hWitnessKeys, _hWitnessDominate⟩
  exact hMatches

theorem packetOk_implies_selectedWinnerKeyMinimal
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.selectedWinnerKeyMinimal = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨_hKeyCoverOk, _hIndex, _hMatches, hMinimal, _hWitnessIndex, _hWitnessCover, _hWitnessKeys, _hWitnessDominate⟩
  exact hMinimal

theorem packetOk_implies_dominationWitnessIndicesInRange
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.dominationWitnessIndicesInRange = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨_hKeyCoverOk, _hIndex, _hMatches, _hMinimal, hWitnessIndex, _hWitnessCover, _hWitnessKeys, _hWitnessDominate⟩
  exact hWitnessIndex

theorem packetOk_implies_dominationWitnessesCoverFullCandidates
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.dominationWitnessesCoverFullCandidates = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨_hKeyCoverOk, _hIndex, _hMatches, _hMinimal, _hWitnessIndex, hWitnessCover, _hWitnessKeys, _hWitnessDominate⟩
  exact hWitnessCover

theorem packetOk_implies_dominationWitnessKeysMatchCandidates
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.dominationWitnessKeysMatchCandidates = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨_hKeyCoverOk, _hIndex, _hMatches, _hMinimal, _hWitnessIndex, _hWitnessCover, hWitnessKeys, _hWitnessDominate⟩
  exact hWitnessKeys

theorem packetOk_implies_dominationWitnessesDominate
    (inputs : InterpretationInputs)
    (hOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket inputs).packetOk = true) :
    inputs.dominationWitnessesDominate = true := by
  rcases (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.packetOk_iff inputs).1 hOk with
    ⟨_hKeyCoverOk, _hIndex, _hMatches, _hMinimal, _hWitnessIndex, _hWitnessCover, _hWitnessKeys, hWitnessDominate⟩
  exact hWitnessDominate

/-- Main composition theorem: a verified interpretation packet plus aligned
packet booleans and their intended witness meanings imply full bounded
canonicality. -/
theorem packetOk_and_interpretation_implies_full_canonical_exists
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys fullKeys : Finset (Key PoolId)}
    (keyCoverInputs : KeyCoverInputs)
    (interpInputs : InterpretationInputs)
    (hInterpOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.buildPacket interpInputs).packetOk = true)
    (hKeyCoverAligned :
      interpInputs.keyCoverPacketOk =
        (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket.buildPacket keyCoverInputs).packetOk)
    (hSelectedMin :
      interpInputs.selectedWinnerIndexInRange = true →
        interpInputs.selectedWinnerMatchesCertificate = true →
          interpInputs.selectedWinnerKeyMinimal = true →
            SelectedKeyMinimumWitness selectedKeys)
    (hSubset :
      keyCoverInputs.selectedKeysSubsetFullKeys = true →
        ∀ k, k ∈ selectedKeys → k ∈ fullKeys)
    (hCover :
      interpInputs.dominationWitnessIndicesInRange = true →
        interpInputs.dominationWitnessesCoverFullCandidates = true →
          interpInputs.dominationWitnessKeysMatchCandidates = true →
            interpInputs.dominationWitnessesDominate = true →
              keyCoverInputs.keyCoverHolds = true →
                KeyCover selectedKeys fullKeys) :
    ∃! k, k ∈ fullKeys ∧ ∀ y, y ∈ fullKeys → k ≤ y := by
  have hKeyCoverOkInput : interpInputs.keyCoverPacketOk = true :=
    packetOk_implies_keyCoverPacketOk interpInputs hInterpOk
  have hKeyCoverOk :
      (TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket.buildPacket keyCoverInputs).packetOk = true := by
    rw [← hKeyCoverAligned]
    exact hKeyCoverOkInput
  exact
    TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverSemanticBridge.packetOk_and_interpretation_implies_full_canonical_exists
        (inputs := keyCoverInputs)
        hKeyCoverOk
        (hSelectedMin
          (packetOk_implies_selectedWinnerIndexInRange interpInputs hInterpOk)
          (packetOk_implies_selectedWinnerMatchesCertificate interpInputs hInterpOk)
          (packetOk_implies_selectedWinnerKeyMinimal interpInputs hInterpOk))
        hSubset
        (fun hKeyCoverHolds =>
          hCover
            (packetOk_implies_dominationWitnessIndicesInRange interpInputs hInterpOk)
            (packetOk_implies_dominationWitnessesCoverFullCandidates interpInputs hInterpOk)
            (packetOk_implies_dominationWitnessKeysMatchCandidates interpInputs hInterpOk)
            (packetOk_implies_dominationWitnessesDominate interpInputs hInterpOk)
            hKeyCoverHolds)

/-- Verified-packet wrapper so replayable verification composes directly with the
interpreted repaired key-cover bridge. -/
theorem verifyPackets_and_interpretation_implies_full_canonical_exists
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys fullKeys : Finset (Key PoolId)}
    (keyCoverInputs : KeyCoverInputs)
    (interpInputs : InterpretationInputs)
    {keyCoverPacket : KeyCoverPacketData}
    {interpPacket : InterpretationPacketData}
    (hKeyCoverVerify :
      TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket.verifyPacket keyCoverInputs keyCoverPacket)
    (hInterpVerify :
      TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.verifyPacket interpInputs interpPacket)
    (hInterpOk : interpPacket.packetOk = true)
    (hKeyCoverAligned :
      interpInputs.keyCoverPacketOk = keyCoverPacket.packetOk)
    (hSelectedMin :
      interpInputs.selectedWinnerIndexInRange = true →
        interpInputs.selectedWinnerMatchesCertificate = true →
          interpInputs.selectedWinnerKeyMinimal = true →
            SelectedKeyMinimumWitness selectedKeys)
    (hSubset :
      keyCoverInputs.selectedKeysSubsetFullKeys = true →
        ∀ k, k ∈ selectedKeys → k ∈ fullKeys)
    (hCover :
      interpInputs.dominationWitnessIndicesInRange = true →
        interpInputs.dominationWitnessesCoverFullCandidates = true →
          interpInputs.dominationWitnessKeysMatchCandidates = true →
            interpInputs.dominationWitnessesDominate = true →
              keyCoverInputs.keyCoverHolds = true →
                KeyCover selectedKeys fullKeys) :
    ∃! k, k ∈ fullKeys ∧ ∀ y, y ∈ fullKeys → k ≤ y := by
  unfold TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverPacket.verifyPacket at hKeyCoverVerify
  unfold TauSwap.Routing.ExactOutManyPoolRepairedKeyCoverInterpretationPacket.verifyPacket at hInterpVerify
  subst keyCoverPacket
  subst interpPacket
  exact packetOk_and_interpretation_implies_full_canonical_exists
    (keyCoverInputs := keyCoverInputs)
    (interpInputs := interpInputs)
    hInterpOk
    hKeyCoverAligned
    hSelectedMin
    hSubset
    hCover

end
end ExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge
end Routing
end TauSwap
