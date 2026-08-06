use super::{
    EconomicLaneIdV1, GlobalAccountMovementInputV1, GlobalCustodyEffectInputV1,
    GlobalEconomicEffectPlanErrorV1, GlobalEconomicEffectRowV1, GlobalExternalOutboxInputV1,
    GlobalFeeEffectInputV1, GlobalIssueBurnInputV1, GlobalLiabilityEffectInputV1,
    GlobalOccurrenceConsumptionKindV1, GlobalReserveEffectInputV1, GlobalRewardSlashInputV1,
};
use crate::CommitmentV3;

use super::global_economic_effect_plan_types::GlobalEconomicEffectContentV1;

impl GlobalEconomicEffectRowV1 {
    pub fn account_movement(
        input: GlobalAccountMovementInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::AccountMovement {
            lane_id: input.lane_id,
            asset_id: input.asset_id,
            source_id: input.source_id,
            destination_id: input.destination_id,
            amount_atoms: input.amount_atoms,
        })
    }

    pub fn issue_burn(
        input: GlobalIssueBurnInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::IssueBurn {
            lane_id: input.lane_id,
            asset_id: input.asset_id,
            kind: input.kind,
            bucket_id: input.bucket_id,
            amount_atoms: input.amount_atoms,
            authority_scope_id: input.authority_scope_id,
            action_authorization_binding: input.action_authorization_binding,
        })
    }

    pub fn custody(
        input: GlobalCustodyEffectInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::Custody {
            lane_id: input.lane_id,
            asset_id: input.asset_id,
            custody_id: input.custody_id,
            custody_pre_atoms: input.custody_pre_atoms,
            custody_post_atoms: input.custody_post_atoms,
            claimant_entitlements_pre_atoms: input.claimant_entitlements_pre_atoms,
            claimant_entitlements_post_atoms: input.claimant_entitlements_post_atoms,
            unencumbered_reserves_pre_atoms: input.unencumbered_reserves_pre_atoms,
            unencumbered_reserves_post_atoms: input.unencumbered_reserves_post_atoms,
        })
    }

    pub fn liability(
        input: GlobalLiabilityEffectInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::Liability {
            lane_id: input.lane_id,
            asset_id: input.asset_id,
            liability_id: input.liability_id,
            pre_atoms: input.pre_atoms,
            post_atoms: input.post_atoms,
        })
    }

    pub fn reserve(
        input: GlobalReserveEffectInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::Reserve {
            lane_id: input.lane_id,
            asset_id: input.asset_id,
            reserve_id: input.reserve_id,
            pre_atoms: input.pre_atoms,
            post_atoms: input.post_atoms,
        })
    }

    pub fn fee(input: GlobalFeeEffectInputV1) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::Fee {
            lane_id: input.lane_id,
            asset_id: input.asset_id,
            fee_id: input.fee_id,
            charged_atoms: input.charged_atoms,
            allocated_atoms: input.allocated_atoms,
            carried_residue_atoms: input.carried_residue_atoms,
        })
    }

    pub fn reward_slash(
        input: GlobalRewardSlashInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::RewardSlash {
            lane_id: input.lane_id,
            asset_id: input.asset_id,
            kind: input.kind,
            source_id: input.source_id,
            destination_id: input.destination_id,
            amount_atoms: input.amount_atoms,
            authority_scope_id: input.authority_scope_id,
            action_authorization_binding: input.action_authorization_binding,
        })
    }

    pub fn lane_write(
        lane_id: EconomicLaneIdV1,
        object_id: CommitmentV3,
        pre_value_hash: CommitmentV3,
        post_value_hash: CommitmentV3,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::LaneWrite {
            lane_id,
            object_id,
            pre_value_hash,
            post_value_hash,
        })
    }

    pub fn occurrence_consumption(
        kind: GlobalOccurrenceConsumptionKindV1,
        consumption_id: CommitmentV3,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::OccurrenceConsumption {
            kind,
            consumption_id,
        })
    }

    pub fn terminal_obligation(
        lane_id: EconomicLaneIdV1,
        obligation_id: CommitmentV3,
        pre_status_hash: CommitmentV3,
        post_status_hash: CommitmentV3,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::TerminalObligation {
            lane_id,
            obligation_id,
            pre_status_hash,
            post_status_hash,
        })
    }

    pub fn external_outbox_enqueue(
        input: GlobalExternalOutboxInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_content(GlobalEconomicEffectContentV1::ExternalOutboxEnqueue {
            lane_id: EconomicLaneIdV1::ExternalCustody,
            outbox_id: input.outbox_id,
            destination_domain_id: input.destination_domain_id,
            asset_id: input.asset_id,
            amount_atoms: input.amount_atoms,
            value_effect_id: input.value_effect_id,
            payload_commitment: input.payload_commitment,
        })
    }
}
