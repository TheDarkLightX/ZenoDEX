import Proofs.GlobalSettlementCoreV2

/-!
# GlobalSettlementABI V2 bounded refinement outcomes

This file gives a source-shaped Lean model of the closed Python/Rust outcome
surface in `global_economic_refinement_outcome_v2.py` and `outcome.rs`.  It
fixes the exact 46 reject-code wire values and their order.  Rejection exposes
the submitted pre-state root as its post-state root, an empty six-field effect
plan, empty terminal and Oracle plans, no consumed occurrences, no outbox
entries, and authority `NONE`.

The validation model records two deliberately narrow rules from the executable
outcome surface: an external outbox failure has precedence over a non-static
zero-occurrence failure, and an unknown validation lookup fails closed as
`INTERNAL_CONTRACT_DRIFT`.

## Claim boundary

Roots and validation messages remain abstract.  Source hashes are checked by
the companion Python test and are not internalized by Lean.  These theorems
establish no Python/Rust runtime refinement, exception equivalence, verifier or
publisher authority, settlement or value-moving authority, migration result,
release status, or production readiness.  They do not mount a runtime route or
prove that either executable classifier reaches a particular rejection.
-/

namespace Proofs
namespace GlobalEconomicRefinementOutcomeV2

open GlobalSettlementCoreV2

def outcomeAuthority : String := "NONE"

theorem production_authority_is_none : outcomeAuthority = "NONE" := rfl

/-! ## Closed reject registry -/

inductive RejectCode where
  | malformedCandidate
  | externalOutboxRequiresPublisher
  | zeroOccurrenceNotStatic
  | fixedContextChanged
  | laneOwnershipChanged
  | disabledLaneWrite
  | laneWriteCoverageMismatch
  | laneWriteRootMismatch
  | signedStateDeltaOverflow
  | balancesStateEffectMismatch
  | custodyStateEffectMismatch
  | liabilitiesStateEffectMismatch
  | reservesStateEffectMismatch
  | supplyEffectTotalOverflow
  | supplyIssueBurnMismatch
  | ownedAccountingTotalOverflow
  | ownedTotalNotSupply
  | conservationAssetCoverageMismatch
  | conservationStateMismatch
  | annotationMirrorOverflow
  | feeAllocationNotMirrored
  | rewardOrSlashNotMirrored
  | zeroFeeConservationRow
  | feeResidueOverflow
  | feeResidueStateMismatch
  | custodyBackingTotalOverflow
  | liabilityTotalOverflow
  | liabilitiesExceedBacking
  | openTerminalTotalOverflow
  | openTerminalExceedsLiability
  | terminalLiabilityDeltaOverflow
  | terminalPreStateMismatch
  | terminalOwningLaneWriteMissing
  | terminalPlanMismatch
  | terminalLiabilityMismatch
  | oracleLaneWriteMissing
  | oraclePreStateMismatch
  | oraclePlanMismatch
  | occurrencesNotOrderedUnique
  | replayConsumptionMismatch
  | occurrenceContextMismatch
  | replayAlreadyConsumed
  | replayPostStateMismatch
  | heightProgressionMismatch
  | occurrenceHeightMismatch
  | internalContractDrift
  deriving DecidableEq, Repr

def RejectCode.wire : RejectCode → String
  | .malformedCandidate => "MALFORMED_CANDIDATE"
  | .externalOutboxRequiresPublisher => "EXTERNAL_OUTBOX_REQUIRES_PUBLISHER"
  | .zeroOccurrenceNotStatic => "ZERO_OCCURRENCE_NOT_STATIC"
  | .fixedContextChanged => "FIXED_CONTEXT_CHANGED"
  | .laneOwnershipChanged => "LANE_OWNERSHIP_CHANGED"
  | .disabledLaneWrite => "DISABLED_LANE_WRITE"
  | .laneWriteCoverageMismatch => "LANE_WRITE_COVERAGE_MISMATCH"
  | .laneWriteRootMismatch => "LANE_WRITE_ROOT_MISMATCH"
  | .signedStateDeltaOverflow => "SIGNED_STATE_DELTA_OVERFLOW"
  | .balancesStateEffectMismatch => "BALANCES_STATE_EFFECT_MISMATCH"
  | .custodyStateEffectMismatch => "CUSTODY_STATE_EFFECT_MISMATCH"
  | .liabilitiesStateEffectMismatch => "LIABILITIES_STATE_EFFECT_MISMATCH"
  | .reservesStateEffectMismatch => "RESERVES_STATE_EFFECT_MISMATCH"
  | .supplyEffectTotalOverflow => "SUPPLY_EFFECT_TOTAL_OVERFLOW"
  | .supplyIssueBurnMismatch => "SUPPLY_ISSUE_BURN_MISMATCH"
  | .ownedAccountingTotalOverflow => "OWNED_ACCOUNTING_TOTAL_OVERFLOW"
  | .ownedTotalNotSupply => "OWNED_TOTAL_NOT_SUPPLY"
  | .conservationAssetCoverageMismatch => "CONSERVATION_ASSET_COVERAGE_MISMATCH"
  | .conservationStateMismatch => "CONSERVATION_STATE_MISMATCH"
  | .annotationMirrorOverflow => "ANNOTATION_MIRROR_OVERFLOW"
  | .feeAllocationNotMirrored => "FEE_ALLOCATION_NOT_MIRRORED"
  | .rewardOrSlashNotMirrored => "REWARD_OR_SLASH_NOT_MIRRORED"
  | .zeroFeeConservationRow => "ZERO_FEE_CONSERVATION_ROW"
  | .feeResidueOverflow => "FEE_RESIDUE_OVERFLOW"
  | .feeResidueStateMismatch => "FEE_RESIDUE_STATE_MISMATCH"
  | .custodyBackingTotalOverflow => "CUSTODY_BACKING_TOTAL_OVERFLOW"
  | .liabilityTotalOverflow => "LIABILITY_TOTAL_OVERFLOW"
  | .liabilitiesExceedBacking => "LIABILITIES_EXCEED_BACKING"
  | .openTerminalTotalOverflow => "OPEN_TERMINAL_TOTAL_OVERFLOW"
  | .openTerminalExceedsLiability => "OPEN_TERMINAL_EXCEEDS_LIABILITY"
  | .terminalLiabilityDeltaOverflow => "TERMINAL_LIABILITY_DELTA_OVERFLOW"
  | .terminalPreStateMismatch => "TERMINAL_PRE_STATE_MISMATCH"
  | .terminalOwningLaneWriteMissing => "TERMINAL_OWNING_LANE_WRITE_MISSING"
  | .terminalPlanMismatch => "TERMINAL_PLAN_MISMATCH"
  | .terminalLiabilityMismatch => "TERMINAL_LIABILITY_MISMATCH"
  | .oracleLaneWriteMissing => "ORACLE_LANE_WRITE_MISSING"
  | .oraclePreStateMismatch => "ORACLE_PRE_STATE_MISMATCH"
  | .oraclePlanMismatch => "ORACLE_PLAN_MISMATCH"
  | .occurrencesNotOrderedUnique => "OCCURRENCES_NOT_ORDERED_UNIQUE"
  | .replayConsumptionMismatch => "REPLAY_CONSUMPTION_MISMATCH"
  | .occurrenceContextMismatch => "OCCURRENCE_CONTEXT_MISMATCH"
  | .replayAlreadyConsumed => "REPLAY_ALREADY_CONSUMED"
  | .replayPostStateMismatch => "REPLAY_POST_STATE_MISMATCH"
  | .heightProgressionMismatch => "HEIGHT_PROGRESSION_MISMATCH"
  | .occurrenceHeightMismatch => "OCCURRENCE_HEIGHT_MISMATCH"
  | .internalContractDrift => "INTERNAL_CONTRACT_DRIFT"

def allRejectCodes : List RejectCode :=
  [ .malformedCandidate,
    .externalOutboxRequiresPublisher,
    .zeroOccurrenceNotStatic,
    .fixedContextChanged,
    .laneOwnershipChanged,
    .disabledLaneWrite,
    .laneWriteCoverageMismatch,
    .laneWriteRootMismatch,
    .signedStateDeltaOverflow,
    .balancesStateEffectMismatch,
    .custodyStateEffectMismatch,
    .liabilitiesStateEffectMismatch,
    .reservesStateEffectMismatch,
    .supplyEffectTotalOverflow,
    .supplyIssueBurnMismatch,
    .ownedAccountingTotalOverflow,
    .ownedTotalNotSupply,
    .conservationAssetCoverageMismatch,
    .conservationStateMismatch,
    .annotationMirrorOverflow,
    .feeAllocationNotMirrored,
    .rewardOrSlashNotMirrored,
    .zeroFeeConservationRow,
    .feeResidueOverflow,
    .feeResidueStateMismatch,
    .custodyBackingTotalOverflow,
    .liabilityTotalOverflow,
    .liabilitiesExceedBacking,
    .openTerminalTotalOverflow,
    .openTerminalExceedsLiability,
    .terminalLiabilityDeltaOverflow,
    .terminalPreStateMismatch,
    .terminalOwningLaneWriteMissing,
    .terminalPlanMismatch,
    .terminalLiabilityMismatch,
    .oracleLaneWriteMissing,
    .oraclePreStateMismatch,
    .oraclePlanMismatch,
    .occurrencesNotOrderedUnique,
    .replayConsumptionMismatch,
    .occurrenceContextMismatch,
    .replayAlreadyConsumed,
    .replayPostStateMismatch,
    .heightProgressionMismatch,
    .occurrenceHeightMismatch,
    .internalContractDrift ]

theorem all_reject_codes_length : allRejectCodes.length = 46 := rfl

theorem all_reject_codes_wire_order :
    allRejectCodes.map RejectCode.wire =
      [ "MALFORMED_CANDIDATE",
        "EXTERNAL_OUTBOX_REQUIRES_PUBLISHER",
        "ZERO_OCCURRENCE_NOT_STATIC",
        "FIXED_CONTEXT_CHANGED",
        "LANE_OWNERSHIP_CHANGED",
        "DISABLED_LANE_WRITE",
        "LANE_WRITE_COVERAGE_MISMATCH",
        "LANE_WRITE_ROOT_MISMATCH",
        "SIGNED_STATE_DELTA_OVERFLOW",
        "BALANCES_STATE_EFFECT_MISMATCH",
        "CUSTODY_STATE_EFFECT_MISMATCH",
        "LIABILITIES_STATE_EFFECT_MISMATCH",
        "RESERVES_STATE_EFFECT_MISMATCH",
        "SUPPLY_EFFECT_TOTAL_OVERFLOW",
        "SUPPLY_ISSUE_BURN_MISMATCH",
        "OWNED_ACCOUNTING_TOTAL_OVERFLOW",
        "OWNED_TOTAL_NOT_SUPPLY",
        "CONSERVATION_ASSET_COVERAGE_MISMATCH",
        "CONSERVATION_STATE_MISMATCH",
        "ANNOTATION_MIRROR_OVERFLOW",
        "FEE_ALLOCATION_NOT_MIRRORED",
        "REWARD_OR_SLASH_NOT_MIRRORED",
        "ZERO_FEE_CONSERVATION_ROW",
        "FEE_RESIDUE_OVERFLOW",
        "FEE_RESIDUE_STATE_MISMATCH",
        "CUSTODY_BACKING_TOTAL_OVERFLOW",
        "LIABILITY_TOTAL_OVERFLOW",
        "LIABILITIES_EXCEED_BACKING",
        "OPEN_TERMINAL_TOTAL_OVERFLOW",
        "OPEN_TERMINAL_EXCEEDS_LIABILITY",
        "TERMINAL_LIABILITY_DELTA_OVERFLOW",
        "TERMINAL_PRE_STATE_MISMATCH",
        "TERMINAL_OWNING_LANE_WRITE_MISSING",
        "TERMINAL_PLAN_MISMATCH",
        "TERMINAL_LIABILITY_MISMATCH",
        "ORACLE_LANE_WRITE_MISSING",
        "ORACLE_PRE_STATE_MISMATCH",
        "ORACLE_PLAN_MISMATCH",
        "OCCURRENCES_NOT_ORDERED_UNIQUE",
        "REPLAY_CONSUMPTION_MISMATCH",
        "OCCURRENCE_CONTEXT_MISMATCH",
        "REPLAY_ALREADY_CONSUMED",
        "REPLAY_POST_STATE_MISMATCH",
        "HEIGHT_PROGRESSION_MISMATCH",
        "OCCURRENCE_HEIGHT_MISMATCH",
        "INTERNAL_CONTRACT_DRIFT" ] := rfl

theorem all_reject_codes_complete (code : RejectCode) : code ∈ allRejectCodes := by
  cases code <;> decide

theorem all_reject_codes_no_duplicates : allRejectCodes.Nodup := by
  decide

theorem all_reject_code_wires_no_duplicates :
    (allRejectCodes.map RejectCode.wire).Nodup := by
  decide

theorem RejectCode.wire_injective {left right : RejectCode}
    (sameWire : left.wire = right.wire) : left = right := by
  cases left <;> cases right <;> simp_all [RejectCode.wire]

/-! ## Validation classification and precedence -/

inductive ValidationLookup where
  | mapped (code : RejectCode)
  | unknown
  deriving DecidableEq, Repr

def classifyValidation : ValidationLookup → RejectCode
  | .mapped code => code
  | .unknown => .internalContractDrift

theorem known_validation_preserves_code (code : RejectCode) :
    classifyValidation (.mapped code) = code := rfl

theorem unknown_validation_maps_to_internal_contract_drift :
    classifyValidation .unknown = .internalContractDrift := rfl

structure ValidationSignals where
  externalOutboxPresent : Bool
  zeroOccurrenceNonStatic : Bool
  deriving DecidableEq, Repr

def firstValidationFailure (signals : ValidationSignals) : Option RejectCode :=
  if signals.externalOutboxPresent then
    some .externalOutboxRequiresPublisher
  else if signals.zeroOccurrenceNonStatic then
    some .zeroOccurrenceNotStatic
  else
    none

def outboxAndZeroOccurrenceFailures : ValidationSignals := ⟨true, true⟩

theorem external_outbox_precedes_zero_occurrence :
    firstValidationFailure outboxAndZeroOccurrenceFailures =
      some .externalOutboxRequiresPublisher := rfl

theorem zero_occurrence_selected_when_outbox_absent :
    firstValidationFailure ⟨false, true⟩ = some .zeroOccurrenceNotStatic := rfl

/-! ## Exact reject-is-no-op projection -/

structure RejectedOutcome where
  rejectCode : RejectCode
  preStateRoot : RootId
  deriving DecidableEq, Repr

def reject (code : RejectCode) (preStateRoot : RootId) : RejectedOutcome :=
  ⟨code, preStateRoot⟩

def RejectedOutcome.postStateRoot (rejected : RejectedOutcome) : RootId :=
  rejected.preStateRoot

def RejectedOutcome.effectPlan (_ : RejectedOutcome) : EffectPlan :=
  EffectPlan.empty

def RejectedOutcome.terminalPlanDeltas (_ : RejectedOutcome) : List RootId := []

def RejectedOutcome.oraclePlanDeltas (_ : RejectedOutcome) : List RootId := []

def RejectedOutcome.consumedOccurrences (_ : RejectedOutcome) : List RootId := []

def RejectedOutcome.outbox (_ : RejectedOutcome) : List ExternalOutboxEnqueue := []

def RejectedOutcome.productionAuthority (_ : RejectedOutcome) : String :=
  outcomeAuthority

def CompleteNoOp (rejected : RejectedOutcome) : Prop :=
  rejected.postStateRoot = rejected.preStateRoot ∧
    rejected.effectPlan.IsEmpty ∧
    rejected.terminalPlanDeltas = [] ∧
    rejected.oraclePlanDeltas = [] ∧
    rejected.consumedOccurrences = [] ∧
    rejected.outbox = [] ∧
    rejected.productionAuthority = "NONE"

theorem rejected_post_state_root_is_pre_state_root (rejected : RejectedOutcome) :
    rejected.postStateRoot = rejected.preStateRoot := rfl

theorem rejected_effect_plan_is_empty (rejected : RejectedOutcome) :
    rejected.effectPlan.IsEmpty := effectPlan_empty_has_six_empty_fields

theorem rejected_terminal_and_oracle_plans_are_empty (rejected : RejectedOutcome) :
    rejected.terminalPlanDeltas = [] ∧ rejected.oraclePlanDeltas = [] := ⟨rfl, rfl⟩

theorem rejected_consumes_no_occurrences (rejected : RejectedOutcome) :
    rejected.consumedOccurrences = [] := rfl

theorem rejected_outbox_is_empty (rejected : RejectedOutcome) :
    rejected.outbox = [] := rfl

theorem rejected_authority_is_none (rejected : RejectedOutcome) :
    rejected.productionAuthority = "NONE" := rfl

theorem rejected_outcome_is_complete_no_op (rejected : RejectedOutcome) :
    CompleteNoOp rejected := by
  exact ⟨rfl, effectPlan_empty_has_six_empty_fields, rfl, rfl, rfl, rfl, rfl⟩

theorem every_reject_code_is_complete_no_op :
    ∀ code preStateRoot, CompleteNoOp (reject code preStateRoot) := by
  intro code preStateRoot
  exact rejected_outcome_is_complete_no_op (reject code preStateRoot)

end GlobalEconomicRefinementOutcomeV2
end Proofs
