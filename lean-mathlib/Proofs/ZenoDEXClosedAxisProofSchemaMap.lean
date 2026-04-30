import Proofs.ZenoDEXDisasterSchemaInstantiations
import Mathlib

/-!
# ZenoDEX Closed-Axis Proof Schema Map

This file mirrors the Python disaster proof-schema map at the Lean level. It is
not a runtime refinement proof. It proves that the current closed disaster-axis
set is total over the declared proof-schema lanes: every closed axis has at
least one reusable theorem schema assigned to it.
-/

namespace Proofs
namespace ZenoDEXClosedAxisProofSchemaMap

inductive ProofSchema
  | ammIntegerRuntimeBridge
  | certificateGluing
  | disasterAntichainBasis
  | disasterTraceLifting
  | forbiddenTraceMinor
  | noFreeResourceTraceLedger
  | zenodexDisasterSchemaInstantiations
  deriving DecidableEq, Repr

inductive ClosedDisasterAxis
  | epochSplitBrain
  | identityRegistryDrift
  | canonicalizationEquivocation
  | serializationWidthAliasing
  | resourceBudgetAbort
  | repairAfterTamper
  | externalStateDrift
  | atomicityPartialSideEffect
  | restartReplayPersistence
  | dependencyOutageFailClosed
  | reciprocalNettingPairForgery
  | boundedAdvisorySearchEnvelope
  | exactOutCandidateDomainExplosion
  | tauGatePolicyAliasing
  | confidentialReceiptAttestationDrift
  | batchClearingFragmentationOrdering
  | perpFundingLiquidationOracleWindow
  | proofMiningPacketEnvelopeReplay
  | tauNetClientTransportBoundary
  | settlementProofRecomputeGate
  | operationsParserCanonicalEnvelope
  | dexEngineSequenceAnomalySurface
  | dexCoreRefParityDrift
  | boundaryConcolicWrapperConsistency
  | exactOutPrefilterWinnerRepairBoundary
  | perpEngineIntegrationOracleBootstrapBoundary
  | quoteReceiptTransportIntentBoundary
  | tauRunnerSubprocessTransportBoundary
  | dexSettlementRecoveryProofUnitBoundary
  deriving DecidableEq, Repr

def closedAxes : List ClosedDisasterAxis :=
  [
    .epochSplitBrain,
    .identityRegistryDrift,
    .canonicalizationEquivocation,
    .serializationWidthAliasing,
    .resourceBudgetAbort,
    .repairAfterTamper,
    .externalStateDrift,
    .atomicityPartialSideEffect,
    .restartReplayPersistence,
    .dependencyOutageFailClosed,
    .reciprocalNettingPairForgery,
    .boundedAdvisorySearchEnvelope,
    .exactOutCandidateDomainExplosion,
    .tauGatePolicyAliasing,
    .confidentialReceiptAttestationDrift,
    .batchClearingFragmentationOrdering,
    .perpFundingLiquidationOracleWindow,
    .proofMiningPacketEnvelopeReplay,
    .tauNetClientTransportBoundary,
    .settlementProofRecomputeGate,
    .operationsParserCanonicalEnvelope,
    .dexEngineSequenceAnomalySurface,
    .dexCoreRefParityDrift,
    .boundaryConcolicWrapperConsistency,
    .exactOutPrefilterWinnerRepairBoundary,
    .perpEngineIntegrationOracleBootstrapBoundary,
    .quoteReceiptTransportIntentBoundary,
    .tauRunnerSubprocessTransportBoundary,
    .dexSettlementRecoveryProofUnitBoundary
  ]

def schemasForAxis : ClosedDisasterAxis → List ProofSchema
  | .epochSplitBrain =>
      [.disasterTraceLifting, .certificateGluing, .forbiddenTraceMinor]
  | .identityRegistryDrift =>
      [.disasterTraceLifting, .certificateGluing]
  | .canonicalizationEquivocation =>
      [.certificateGluing, .disasterAntichainBasis]
  | .serializationWidthAliasing =>
      [.forbiddenTraceMinor, .disasterAntichainBasis]
  | .resourceBudgetAbort =>
      [.noFreeResourceTraceLedger, .zenodexDisasterSchemaInstantiations]
  | .repairAfterTamper =>
      [.forbiddenTraceMinor, .certificateGluing]
  | .externalStateDrift =>
      [.disasterTraceLifting, .certificateGluing]
  | .atomicityPartialSideEffect =>
      [.noFreeResourceTraceLedger, .certificateGluing]
  | .restartReplayPersistence =>
      [.disasterTraceLifting, .forbiddenTraceMinor]
  | .dependencyOutageFailClosed =>
      [.forbiddenTraceMinor, .disasterTraceLifting]
  | .reciprocalNettingPairForgery =>
      [.forbiddenTraceMinor, .zenodexDisasterSchemaInstantiations]
  | .boundedAdvisorySearchEnvelope =>
      [.noFreeResourceTraceLedger, .zenodexDisasterSchemaInstantiations]
  | .exactOutCandidateDomainExplosion =>
      [.noFreeResourceTraceLedger, .disasterAntichainBasis]
  | .tauGatePolicyAliasing =>
      [.forbiddenTraceMinor, .disasterAntichainBasis]
  | .confidentialReceiptAttestationDrift =>
      [.certificateGluing, .disasterTraceLifting]
  | .batchClearingFragmentationOrdering =>
      [.disasterAntichainBasis, .certificateGluing]
  | .perpFundingLiquidationOracleWindow =>
      [.forbiddenTraceMinor, .zenodexDisasterSchemaInstantiations]
  | .proofMiningPacketEnvelopeReplay =>
      [.noFreeResourceTraceLedger, .zenodexDisasterSchemaInstantiations, .certificateGluing]
  | .tauNetClientTransportBoundary =>
      [.forbiddenTraceMinor, .disasterTraceLifting]
  | .settlementProofRecomputeGate =>
      [.certificateGluing, .disasterTraceLifting]
  | .operationsParserCanonicalEnvelope =>
      [.forbiddenTraceMinor, .disasterAntichainBasis]
  | .dexEngineSequenceAnomalySurface =>
      [.disasterTraceLifting, .forbiddenTraceMinor]
  | .dexCoreRefParityDrift =>
      [.ammIntegerRuntimeBridge, .disasterTraceLifting]
  | .boundaryConcolicWrapperConsistency =>
      [.forbiddenTraceMinor, .disasterAntichainBasis]
  | .exactOutPrefilterWinnerRepairBoundary =>
      [.disasterAntichainBasis, .certificateGluing]
  | .perpEngineIntegrationOracleBootstrapBoundary =>
      [.forbiddenTraceMinor, .zenodexDisasterSchemaInstantiations]
  | .quoteReceiptTransportIntentBoundary =>
      [.certificateGluing, .forbiddenTraceMinor]
  | .tauRunnerSubprocessTransportBoundary =>
      [.forbiddenTraceMinor, .noFreeResourceTraceLedger]
  | .dexSettlementRecoveryProofUnitBoundary =>
      [.certificateGluing, .disasterTraceLifting]

theorem closed_axes_count : closedAxes.length = 29 := by
  rfl

theorem schemasForAxis_nonempty (axis : ClosedDisasterAxis) :
    schemasForAxis axis ≠ [] := by
  cases axis <;> decide

theorem schemasForAxis_length_pos (axis : ClosedDisasterAxis) :
    0 < (schemasForAxis axis).length := by
  cases axis <;> decide

theorem closed_axis_members_have_schema
    (axis : ClosedDisasterAxis)
    (_hmem : axis ∈ closedAxes) :
    schemasForAxis axis ≠ [] :=
  schemasForAxis_nonempty axis

theorem resource_budget_abort_uses_resource_ledger :
    .noFreeResourceTraceLedger ∈ schemasForAxis .resourceBudgetAbort := by
  decide

theorem proof_mining_packet_uses_resource_and_instantiation :
    .noFreeResourceTraceLedger ∈ schemasForAxis .proofMiningPacketEnvelopeReplay ∧
      .zenodexDisasterSchemaInstantiations ∈
        schemasForAxis .proofMiningPacketEnvelopeReplay := by
  decide

theorem reciprocal_netting_uses_forbidden_minor :
    .forbiddenTraceMinor ∈ schemasForAxis .reciprocalNettingPairForgery := by
  decide

theorem dex_core_ref_parity_uses_integer_bridge :
    .ammIntegerRuntimeBridge ∈ schemasForAxis .dexCoreRefParityDrift := by
  decide

end ZenoDEXClosedAxisProofSchemaMap
end Proofs
