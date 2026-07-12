use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_effect_plan_v2, decode_exact_value_aggregate_proposal_v5,
    encode_settlement_effect_plan_v2, encode_value_aggregate_proposal_v5, CommitmentV3,
    ProposedValueAggregateV5, SparseMerkleCellTransitionWitnessV1, MAX_FULL_BLOB_DA_BYTES_V1,
};

mod codec;
mod error;

pub use codec::{
    decode_exact_ordinary_spot_settlement_replay_data_v2,
    encode_ordinary_spot_settlement_replay_data_v2,
};
pub use error::OrdinarySpotSettlementReplayDataErrorV2;

use super::wire_v2::validate_authorization_v2;
use codec::require_part_lengths;

use crate::{
    derive_spot_settlement_state_projection_v2, SpotSettlementAuthorizationInputV1,
    SpotSettlementStateProjectionV2,
};

pub const ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V2: u16 = 2;
pub const MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2: usize = MAX_FULL_BLOB_DA_BYTES_V1;

const REPLAY_DATA_SCHEMA_DOMAIN_V2: &[u8] =
    b"zenodex.zrpf.ordinary_spot_settlement_replay_data.schema.v2";

/// Independently replayable state-bound ordinary Spot settlement data.
///
/// The private fields carry exact canonical proposal and plan bytes plus the
/// exact authorization and sparse witness needed to rederive that plan. This
/// value remains proof-neutral and supplies no receipt or ledger authority.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::OrdinarySpotSettlementReplayDataV2;
/// let _ = OrdinarySpotSettlementReplayDataV2 {
///     proposal_bytes: vec![],
///     authorization: unimplemented!(),
///     witness: unimplemented!(),
///     settlement_effect_plan_bytes: vec![],
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrdinarySpotSettlementReplayDataV2 {
    proposal_bytes: Vec<u8>,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
    settlement_effect_plan_bytes: Vec<u8>,
}

impl OrdinarySpotSettlementReplayDataV2 {
    pub fn recompose(
        proposal: &ProposedValueAggregateV5,
        authorization: SpotSettlementAuthorizationInputV1,
        witness: &SparseMerkleCellTransitionWitnessV1,
    ) -> Result<Self, OrdinarySpotSettlementReplayDataErrorV2> {
        let projection =
            derive_spot_settlement_state_projection_v2(proposal, authorization, witness.clone())?;
        Self::from_validated(proposal, authorization, witness.clone(), &projection)
    }

    pub fn validate_self_consistency(&self) -> Result<(), OrdinarySpotSettlementReplayDataErrorV2> {
        validate_authorization_v2(self.authorization)?;
        let witness_bytes =
            zenodex_zrpf_protocol_v3::encode_sparse_merkle_cell_transition_witness_v1(
                &self.witness,
            )?;
        require_part_lengths(
            self.proposal_bytes.len(),
            witness_bytes.len(),
            self.settlement_effect_plan_bytes.len(),
        )?;
        let proposal = decode_exact_value_aggregate_proposal_v5(&self.proposal_bytes)?;
        let plan = decode_exact_settlement_effect_plan_v2(&self.settlement_effect_plan_bytes)?;
        let expected = derive_spot_settlement_state_projection_v2(
            &proposal,
            self.authorization,
            self.witness.clone(),
        )?;
        if expected.settlement_plan() != &plan {
            return Err(OrdinarySpotSettlementReplayDataErrorV2::RecomposedPlanMismatch);
        }
        Ok(())
    }

    pub fn proposal_bytes(&self) -> &[u8] {
        &self.proposal_bytes
    }

    pub const fn authorization(&self) -> SpotSettlementAuthorizationInputV1 {
        self.authorization
    }

    pub const fn witness(&self) -> &SparseMerkleCellTransitionWitnessV1 {
        &self.witness
    }

    pub fn settlement_effect_plan_bytes(&self) -> &[u8] {
        &self.settlement_effect_plan_bytes
    }

    pub(super) fn from_validated(
        proposal: &ProposedValueAggregateV5,
        authorization: SpotSettlementAuthorizationInputV1,
        witness: SparseMerkleCellTransitionWitnessV1,
        projection: &SpotSettlementStateProjectionV2,
    ) -> Result<Self, OrdinarySpotSettlementReplayDataErrorV2> {
        let replay = Self {
            proposal_bytes: encode_value_aggregate_proposal_v5(proposal)?,
            authorization,
            witness,
            settlement_effect_plan_bytes: encode_settlement_effect_plan_v2(
                projection.settlement_plan(),
            )?,
        };
        replay.validate_self_consistency()?;
        Ok(replay)
    }

    pub(super) fn from_encoded_parts(
        proposal_bytes: Vec<u8>,
        authorization: SpotSettlementAuthorizationInputV1,
        witness: SparseMerkleCellTransitionWitnessV1,
        settlement_effect_plan_bytes: Vec<u8>,
    ) -> Result<Self, OrdinarySpotSettlementReplayDataErrorV2> {
        let replay = Self {
            proposal_bytes,
            authorization,
            witness,
            settlement_effect_plan_bytes,
        };
        replay.validate_self_consistency()?;
        Ok(replay)
    }
}

pub fn ordinary_spot_settlement_replay_data_schema_id_v2(
) -> Result<CommitmentV3, OrdinarySpotSettlementReplayDataErrorV2> {
    let length = u16::try_from(REPLAY_DATA_SCHEMA_DOMAIN_V2.len()).map_err(|_| {
        OrdinarySpotSettlementReplayDataErrorV2::ArithmeticOverflow("schema_domain")
    })?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(REPLAY_DATA_SCHEMA_DOMAIN_V2);
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| OrdinarySpotSettlementReplayDataErrorV2::InvalidDerivedCommitment("schema_id"))
}
