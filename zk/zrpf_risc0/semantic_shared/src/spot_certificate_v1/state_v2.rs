use zenodex_zrpf_protocol_v3::{
    CommitmentV3, FullBlobDataAvailabilityCertificateV1, ProposedValueAggregateV5,
    SettlementEpochCertificateV1, SparseMerkleCellTransitionWitnessV1,
};

use super::{
    compose_checked_certificate, derive_certificate_fields_after_empty_policy,
    encode_ordinary_spot_settlement_replay_data_v2,
    ordinary_spot_settlement_replay_data_schema_id_v2, require_empty_ordinary_rows,
    require_full_blob_data_availability, CheckedSpotCertificateInputsV1,
    OrdinarySpotSettlementCertificateErrorV1, OrdinarySpotSettlementReplayDataV2,
};
use crate::{derive_spot_settlement_state_projection_v2, SpotSettlementAuthorizationInputV1};

/// Recomposes state-bound ordinary Spot compatibility data with exact full-blob DA.
///
/// `semantic_claim_binding` must be derived only after verifying the exact L2
/// proposal receipt under its governed image. This proof-neutral function does
/// not authenticate that binding, verify a receipt, or grant settlement authority.
/// Its five explicit inputs preserve the separate proposal, authorization,
/// ledger-witness, claim-binding, and data-availability trust boundaries.
pub fn compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: SparseMerkleCellTransitionWitnessV1,
    semantic_claim_binding: CommitmentV3,
    data_availability_certificate: &FullBlobDataAvailabilityCertificateV1,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    let replay_witness = witness.clone();
    let projection = derive_spot_settlement_state_projection_v2(proposal, authorization, witness)?;
    let plan = projection.settlement_plan();
    plan.validate_self_consistency()?;
    require_empty_ordinary_rows(
        plan.message_effects().len(),
        plan.carry_effects().len(),
        plan.reward_effects().len(),
    )?;
    let replay = OrdinarySpotSettlementReplayDataV2::from_validated(
        proposal,
        authorization,
        replay_witness,
        &projection,
    )?;
    let replay_bytes = encode_ordinary_spot_settlement_replay_data_v2(&replay)?;
    require_full_blob_data_availability(
        proposal,
        data_availability_certificate,
        ordinary_spot_settlement_replay_data_schema_id_v2()?,
        &replay_bytes,
    )?;
    let fields = derive_certificate_fields_after_empty_policy(proposal, plan)?;
    compose_checked_certificate(
        proposal,
        CheckedSpotCertificateInputsV1::new(plan, &fields),
        semantic_claim_binding,
        data_availability_certificate.certificate_root(),
    )
}
