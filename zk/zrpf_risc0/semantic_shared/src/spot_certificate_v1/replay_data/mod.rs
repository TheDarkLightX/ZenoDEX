use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_effect_plan_v2, decode_exact_value_aggregate_proposal_v5,
    encode_settlement_effect_plan_v2, encode_value_aggregate_proposal_v5, CommitmentV3,
    ProposedValueAggregateV5, SettlementEffectPlanV2, MAX_FULL_BLOB_DA_BYTES_V1,
};

mod codec;
mod error;

pub use codec::{
    decode_exact_ordinary_spot_settlement_replay_data_v1,
    encode_ordinary_spot_settlement_replay_data_v1,
};
pub use error::OrdinarySpotSettlementReplayDataErrorV1;

use codec::require_part_lengths;

use crate::{derive_spot_settlement_projection_v1, SpotSettlementAuthorizationInputV1};

pub const ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V1: u16 = 1;
pub const MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1: usize = MAX_FULL_BLOB_DA_BYTES_V1;

const REPLAY_DATA_SCHEMA_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.ordinary_spot_settlement_replay_data.schema.v1";

/// Canonical V5 proposal and deterministic ordinary Spot V1 plan bytes.
///
/// This replay object contains no transaction payload or source proof artifact.
/// Construction supplies no persistence, state-transition, or settlement authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrdinarySpotSettlementReplayDataV1 {
    proposal_bytes: Vec<u8>,
    settlement_effect_plan_bytes: Vec<u8>,
}

impl OrdinarySpotSettlementReplayDataV1 {
    pub fn recompose(
        proposal: &ProposedValueAggregateV5,
        authorization: SpotSettlementAuthorizationInputV1,
    ) -> Result<Self, OrdinarySpotSettlementReplayDataErrorV1> {
        let projection = derive_spot_settlement_projection_v1(proposal, authorization)?;
        Self::from_recomposed(proposal, projection.settlement_plan())
    }

    pub fn validate_self_consistency(&self) -> Result<(), OrdinarySpotSettlementReplayDataErrorV1> {
        require_part_lengths(
            self.proposal_bytes.len(),
            self.settlement_effect_plan_bytes.len(),
        )?;
        let proposal = decode_exact_value_aggregate_proposal_v5(&self.proposal_bytes)?;
        let plan = decode_exact_settlement_effect_plan_v2(&self.settlement_effect_plan_bytes)?;
        require_recomposed_plan(&proposal, &plan)
    }

    pub fn proposal_bytes(&self) -> &[u8] {
        &self.proposal_bytes
    }

    pub fn settlement_effect_plan_bytes(&self) -> &[u8] {
        &self.settlement_effect_plan_bytes
    }

    pub(super) fn from_recomposed(
        proposal: &ProposedValueAggregateV5,
        plan: &SettlementEffectPlanV2,
    ) -> Result<Self, OrdinarySpotSettlementReplayDataErrorV1> {
        let proposal_bytes = encode_value_aggregate_proposal_v5(proposal)?;
        let settlement_effect_plan_bytes = encode_settlement_effect_plan_v2(plan)?;
        require_part_lengths(proposal_bytes.len(), settlement_effect_plan_bytes.len())?;
        Ok(Self {
            proposal_bytes,
            settlement_effect_plan_bytes,
        })
    }

    pub(super) fn from_encoded_parts(
        proposal_bytes: Vec<u8>,
        settlement_effect_plan_bytes: Vec<u8>,
    ) -> Result<Self, OrdinarySpotSettlementReplayDataErrorV1> {
        let replay_data = Self {
            proposal_bytes,
            settlement_effect_plan_bytes,
        };
        replay_data.validate_self_consistency()?;
        Ok(replay_data)
    }
}

pub fn ordinary_spot_settlement_replay_data_schema_id_v1(
) -> Result<CommitmentV3, OrdinarySpotSettlementReplayDataErrorV1> {
    let length = u16::try_from(REPLAY_DATA_SCHEMA_DOMAIN_V1.len()).map_err(|_| {
        OrdinarySpotSettlementReplayDataErrorV1::ArithmeticOverflow("schema_domain")
    })?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(REPLAY_DATA_SCHEMA_DOMAIN_V1);
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| OrdinarySpotSettlementReplayDataErrorV1::InvalidDerivedCommitment("schema_id"))
}

fn require_recomposed_plan(
    proposal: &ProposedValueAggregateV5,
    plan: &SettlementEffectPlanV2,
) -> Result<(), OrdinarySpotSettlementReplayDataErrorV1> {
    let actions = plan.economic_action_batch().actions();
    if actions.len() != 1 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::PlanActionCount {
            actual: actions.len(),
            expected: 1,
        });
    }
    let action = &actions[0];
    let record = action.record();
    let authorization = SpotSettlementAuthorizationInputV1 {
        authorization_subject_id: record.authorization_subject_id(),
        authorization_scope_id: record.authorization_scope_id(),
        authorization_nonce: record.authorization_nonce(),
        authorization_grant_id: action.authorization_grant_id(),
    };
    let expected = derive_spot_settlement_projection_v1(proposal, authorization)?;
    if expected.settlement_plan() != plan {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::RecomposedPlanMismatch);
    }
    Ok(())
}
