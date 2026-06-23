import Proofs.ZenoDEXSettlementEndToEndCertificatePacket
import Proofs.ZenoDEXSettlementFeatureExtensionPacket
import Proofs.ZenoDEXSettlementValuePacket

/-!
# ZenoDEX Settlement Gate Blockers

This packet promotes the useful "blocker witness" pattern from the external
MathLib workbench into the concrete ZenoDEX settlement packets.

The existing packet files prove when `packetOk = true`. This file adds the
dual operational fact used by replay/debug tooling: a settlement packet fails
exactly when its deterministic list of named blockers is nonempty.
-/

namespace TauSwap

namespace SettlementValuePacket

inductive BlockingFlag
  | priceProvenanceOk
  | assetConservationOk
  | valueConservationOk
  | lpLiabilityBalancedOk
  | attestationOk
  deriving DecidableEq, Repr

def blockingFlags (inputs : Inputs) : List BlockingFlag :=
  (if inputs.priceProvenanceOk then [] else [.priceProvenanceOk]) ++
  (if inputs.assetConservationOk then [] else [.assetConservationOk]) ++
  (if inputs.valueConservationOk then [] else [.valueConservationOk]) ++
  (if inputs.lpMode && !inputs.lpLiabilityBalancedOk then [.lpLiabilityBalancedOk] else []) ++
  (if inputs.attestationMode && !inputs.attestationOk then [.attestationOk] else [])

theorem packetOk_eq_true_iff_no_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔ blockingFlags inputs = [] := by
  cases inputs with
  | mk lpMode attestationMode priceProvenanceOk attestationOk assetConservationOk lpLiabilityBalancedOk valueConservationOk =>
      cases lpMode <;>
        cases attestationMode <;>
        cases priceProvenanceOk <;>
        cases attestationOk <;>
        cases assetConservationOk <;>
        cases lpLiabilityBalancedOk <;>
        cases valueConservationOk <;>
        decide

theorem packetOk_eq_false_iff_nonempty_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔ blockingFlags inputs ≠ [] := by
  cases inputs with
  | mk lpMode attestationMode priceProvenanceOk attestationOk assetConservationOk lpLiabilityBalancedOk valueConservationOk =>
      cases lpMode <;>
        cases attestationMode <;>
        cases priceProvenanceOk <;>
        cases attestationOk <;>
        cases assetConservationOk <;>
        cases lpLiabilityBalancedOk <;>
        cases valueConservationOk <;>
        decide

end SettlementValuePacket

namespace SettlementFeatureExtensionPacket

inductive BlockingFlag
  | buybackFloorOk
  | buybackFloorFixedpointOk
  | rebateOk
  | lockWeightOk
  deriving DecidableEq, Repr

def blockingFlags (inputs : Inputs) : List BlockingFlag :=
  (if inputs.buybackFloorOk then [] else [.buybackFloorOk]) ++
  (if inputs.buybackFloorFixedpointOk then [] else [.buybackFloorFixedpointOk]) ++
  (if inputs.rebateOk then [] else [.rebateOk]) ++
  (if inputs.lockWeightOk then [] else [.lockWeightOk])

theorem featureExtensionOk_eq_packetOk (inputs : Inputs) :
    (buildPacket inputs).featureExtensionOk = (buildPacket inputs).packetOk := by
  rfl

theorem packetOk_eq_true_iff_no_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔ blockingFlags inputs = [] := by
  cases inputs with
  | mk buybackFloorOk buybackFloorFixedpointOk rebateOk lockWeightOk =>
      cases buybackFloorOk <;>
        cases buybackFloorFixedpointOk <;>
        cases rebateOk <;>
        cases lockWeightOk <;>
        decide

theorem packetOk_eq_false_iff_nonempty_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔ blockingFlags inputs ≠ [] := by
  cases inputs with
  | mk buybackFloorOk buybackFloorFixedpointOk rebateOk lockWeightOk =>
      cases buybackFloorOk <;>
        cases buybackFloorFixedpointOk <;>
        cases rebateOk <;>
        cases lockWeightOk <;>
        decide

end SettlementFeatureExtensionPacket

namespace SettlementEndToEndCertificatePacket

inductive BlockingFlag
  | strongCertificateOk
  | featureExtensionPacketOk
  | moduleBundleOk
  | fullPriceRailsOk
  | priceProvenanceOk
  | assetConservationOk
  | valueConservationOk
  | lpLiabilityBalancedOk
  | attestationOk
  deriving DecidableEq, Repr

def blockingFlags (inputs : Inputs) : List BlockingFlag :=
  (if inputs.strongCertificateOk then [] else [.strongCertificateOk]) ++
  (if inputs.featureExtensionPacketOk then [] else [.featureExtensionPacketOk]) ++
  (if inputs.moduleBundleOk then [] else [.moduleBundleOk]) ++
  (if inputs.fullPriceRailsOk then [] else [.fullPriceRailsOk]) ++
  (if inputs.priceProvenanceOk then [] else [.priceProvenanceOk]) ++
  (if inputs.assetConservationOk then [] else [.assetConservationOk]) ++
  (if inputs.valueConservationOk then [] else [.valueConservationOk]) ++
  (if inputs.lpLiabilityBalancedOk then [] else [.lpLiabilityBalancedOk]) ++
  (if inputs.attestationMode && !inputs.attestationOk then [.attestationOk] else [])

theorem blockingFlags_endogenousLpMode_irrelevant
    (inputs : Inputs) (flag : Bool) :
    blockingFlags { inputs with endogenousLpMode := flag } =
      blockingFlags inputs := by
  rfl

theorem packetOk_endogenousLpMode_irrelevant
    (inputs : Inputs) (flag : Bool) :
    (buildPacket { inputs with endogenousLpMode := flag }).packetOk =
      (buildPacket inputs).packetOk := by
  rfl

theorem packetOk_eq_true_iff_no_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔ blockingFlags inputs = [] := by
  cases inputs with
  | mk attestationMode endogenousLpMode strongCertificateOk featureExtensionPacketOk moduleBundleOk fullPriceRailsOk priceProvenanceOk attestationOk assetConservationOk lpLiabilityBalancedOk valueConservationOk =>
      cases attestationMode <;>
        cases endogenousLpMode <;>
        cases strongCertificateOk <;>
        cases featureExtensionPacketOk <;>
        cases moduleBundleOk <;>
        cases fullPriceRailsOk <;>
        cases priceProvenanceOk <;>
        cases attestationOk <;>
        cases assetConservationOk <;>
        cases lpLiabilityBalancedOk <;>
        cases valueConservationOk <;>
        decide

theorem packetOk_eq_false_iff_nonempty_blockers (inputs : Inputs) :
    (buildPacket inputs).packetOk = false ↔ blockingFlags inputs ≠ [] := by
  cases inputs with
  | mk attestationMode endogenousLpMode strongCertificateOk featureExtensionPacketOk moduleBundleOk fullPriceRailsOk priceProvenanceOk attestationOk assetConservationOk lpLiabilityBalancedOk valueConservationOk =>
      cases attestationMode <;>
        cases endogenousLpMode <;>
        cases strongCertificateOk <;>
        cases featureExtensionPacketOk <;>
        cases moduleBundleOk <;>
        cases fullPriceRailsOk <;>
        cases priceProvenanceOk <;>
        cases attestationOk <;>
        cases assetConservationOk <;>
        cases lpLiabilityBalancedOk <;>
        cases valueConservationOk <;>
        decide

end SettlementEndToEndCertificatePacket

end TauSwap
