import Proofs.ZenoDEXExactOutManyPoolRepairedKeyCoverPacket
import Proofs.ZenoDEXExactOutManyPoolKeyCoverBridge

open scoped Classical

/-!
# ZenoDEX Exact-Out Many-Pool Repaired Key-Cover Semantic Bridge

This file packages the strongest honest bridge currently derivable from the
repaired many-pool exact-out key-cover packet.

What it proves:

- if the repaired key-cover packet verifies and `packetOk = true`,
- and the packet's boolean fields are interpreted as the semantic hypotheses
  required by the existing finite-key `KeyCover` bridge,

then unique canonical minimality over the full bounded key set already follows.

What it does **not** prove:

- that the runtime witness payloads already carry those semantics automatically,
- or that the exact-out world-model blocker is closed by the packet shell alone.

That interpretation layer remains the real blocker.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedKeyCoverSemanticBridge

open TauSwap.ZenoDEX.ExactOutCanonicalMinimizer
open TauSwap.ZenoDEX.ExactOutManyPoolKeyCoverBridge
open ExactOutManyPoolRepairedKeyCoverPacket

noncomputable section

abbrev PacketInputs := ExactOutManyPoolRepairedKeyCoverPacket.Inputs
abbrev Packet := ExactOutManyPoolRepairedKeyCoverPacket.Packet

/-- Selected-domain minimum witness expected by the repaired key-cover bridge.
It packages the exact witness needed to feed the finite-key `KeyCover` theorem.
-/
structure SelectedKeyMinimumWitness
    {PoolId : Type} [LinearOrder PoolId]
    (selectedKeys : Finset (Key PoolId)) where
  kStar : Key PoolId
  selectedMem : kStar ∈ selectedKeys
  minimalSelected : ∀ k, k ∈ selectedKeys → kStar ≤ k

theorem packetOk_implies_selectedDomainContractOk
    (inputs : PacketInputs)
    (hOk : (buildPacket inputs).packetOk = true) :
    inputs.selectedDomainContractOk = true := by
  rcases (packetOk_iff inputs).1 hOk with
    ⟨hSelected, _hFull, _hSubset, _hCover, _hCanonical⟩
  exact hSelected

theorem packetOk_implies_repairedFullDomainPacketOk
    (inputs : PacketInputs)
    (hOk : (buildPacket inputs).packetOk = true) :
    inputs.repairedFullDomainPacketOk = true := by
  rcases (packetOk_iff inputs).1 hOk with
    ⟨_hSelected, hFull, _hSubset, _hCover, _hCanonical⟩
  exact hFull

theorem packetOk_implies_selectedKeysSubsetFullKeys
    (inputs : PacketInputs)
    (hOk : (buildPacket inputs).packetOk = true) :
    inputs.selectedKeysSubsetFullKeys = true := by
  rcases (packetOk_iff inputs).1 hOk with
    ⟨_hSelected, _hFull, hSubset, _hCover, _hCanonical⟩
  exact hSubset

theorem packetOk_implies_keyCoverHolds
    (inputs : PacketInputs)
    (hOk : (buildPacket inputs).packetOk = true) :
    inputs.keyCoverHolds = true := by
  rcases (packetOk_iff inputs).1 hOk with
    ⟨_hSelected, _hFull, _hSubset, hCover, _hCanonical⟩
  exact hCover

theorem packetOk_implies_selectedDomainCanonicalMatchesFullDomainCanonical
    (inputs : PacketInputs)
    (hOk : (buildPacket inputs).packetOk = true) :
    inputs.selectedDomainCanonicalMatchesFullDomainCanonical = true := by
  rcases (packetOk_iff inputs).1 hOk with
    ⟨_hSelected, _hFull, _hSubset, _hCover, hCanonical⟩
  exact hCanonical

/-- Honest packaging theorem for the current repaired key-cover boundary.

If `packetOk = true` and the repaired packet booleans are interpreted as the
semantic subset and key-cover hypotheses required by the finite-key bridge,
then any selected-domain minimum already lifts to the unique canonical minimum
of the full bounded key set.
-/
theorem packetOk_and_interpretation_implies_full_canonical_exists
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys fullKeys : Finset (Key PoolId)}
    (inputs : PacketInputs)
    (hOk : (buildPacket inputs).packetOk = true)
    (hSelectedMin : SelectedKeyMinimumWitness selectedKeys)
    (hSubset :
      inputs.selectedKeysSubsetFullKeys = true →
        ∀ k, k ∈ selectedKeys → k ∈ fullKeys)
    (hCover :
      inputs.keyCoverHolds = true →
        KeyCover selectedKeys fullKeys) :
    ∃! k, k ∈ fullKeys ∧ ∀ y, y ∈ fullKeys → k ≤ y := by
  exact keyCover_implies_exists_unique_full_canonical
    hSelectedMin.selectedMem
    hSelectedMin.minimalSelected
    (hSubset (packetOk_implies_selectedKeysSubsetFullKeys inputs hOk))
    (hCover (packetOk_implies_keyCoverHolds inputs hOk))

/-- Verified-packet wrapper for the same bridge, so replayable packet
verification composes directly with the semantic interpretation hypotheses. -/
theorem verifyPacket_and_packetOk_and_interpretation_implies_full_canonical_exists
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys fullKeys : Finset (Key PoolId)}
    (inputs : PacketInputs)
    {packet : Packet}
    (hVerify : verifyPacket inputs packet)
    (hOk : packet.packetOk = true)
    (hSelectedMin : SelectedKeyMinimumWitness selectedKeys)
    (hSubset :
      inputs.selectedKeysSubsetFullKeys = true →
        ∀ k, k ∈ selectedKeys → k ∈ fullKeys)
    (hCover :
      inputs.keyCoverHolds = true →
        KeyCover selectedKeys fullKeys) :
    ∃! k, k ∈ fullKeys ∧ ∀ y, y ∈ fullKeys → k ≤ y := by
  unfold verifyPacket at hVerify
  subst packet
  exact packetOk_and_interpretation_implies_full_canonical_exists
    (inputs := inputs)
    hOk
    hSelectedMin
    hSubset
    hCover

end
end ExactOutManyPoolRepairedKeyCoverSemanticBridge
end Routing
end TauSwap
