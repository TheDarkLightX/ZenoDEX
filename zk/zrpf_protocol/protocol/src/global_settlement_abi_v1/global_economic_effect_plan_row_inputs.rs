use super::{EconomicLaneIdV1, GlobalIssueBurnKindV1, GlobalRewardSlashKindV1};
use crate::{ActionAuthorizationBindingIdV1, AuthorizationScopeIdV1, CommitmentV3, DomainIdV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalAccountMovementInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub asset_id: CommitmentV3,
    pub source_id: CommitmentV3,
    pub destination_id: CommitmentV3,
    pub amount_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalIssueBurnInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub asset_id: CommitmentV3,
    pub kind: GlobalIssueBurnKindV1,
    pub bucket_id: CommitmentV3,
    pub amount_atoms: u128,
    pub authority_scope_id: AuthorizationScopeIdV1,
    pub action_authorization_binding: ActionAuthorizationBindingIdV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalCustodyEffectInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub asset_id: CommitmentV3,
    pub custody_id: CommitmentV3,
    pub custody_pre_atoms: u128,
    pub custody_post_atoms: u128,
    pub claimant_entitlements_pre_atoms: u128,
    pub claimant_entitlements_post_atoms: u128,
    pub unencumbered_reserves_pre_atoms: u128,
    pub unencumbered_reserves_post_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalLiabilityEffectInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub asset_id: CommitmentV3,
    pub liability_id: CommitmentV3,
    pub pre_atoms: u128,
    pub post_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalReserveEffectInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub asset_id: CommitmentV3,
    pub reserve_id: CommitmentV3,
    pub pre_atoms: u128,
    pub post_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalFeeEffectInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub asset_id: CommitmentV3,
    pub fee_id: CommitmentV3,
    pub charged_atoms: u128,
    pub allocated_atoms: u128,
    pub carried_residue_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalRewardSlashInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub asset_id: CommitmentV3,
    pub kind: GlobalRewardSlashKindV1,
    pub source_id: CommitmentV3,
    pub destination_id: CommitmentV3,
    pub amount_atoms: u128,
    pub authority_scope_id: AuthorizationScopeIdV1,
    pub action_authorization_binding: ActionAuthorizationBindingIdV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalExternalOutboxInputV1 {
    pub outbox_id: CommitmentV3,
    pub destination_domain_id: DomainIdV3,
    pub asset_id: CommitmentV3,
    pub amount_atoms: u128,
    pub value_effect_id: CommitmentV3,
    pub payload_commitment: CommitmentV3,
}
