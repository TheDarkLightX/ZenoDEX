use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_effect_plan_v2, decode_exact_value_aggregate_proposal_v5,
    encode_settlement_admission_journal_v1, SettlementAdmissionJournalV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    compose_ordinary_spot_settlement_certificate_with_operational_carry_v3,
    OrdinarySpotSettlementReplayDataV2,
};

use crate::{
    encode_source_opened_spot_settlement_replay_v3,
    source_opened_spot_settlement_replay_schema_id_v3, SourceOpenedSpotSettlementErrorV6,
    SourceOpenedSpotSettlementGuestInputV3,
};

pub fn compose_source_opened_spot_settlement_output_after_l2_verification_v3(
    input: &SourceOpenedSpotSettlementGuestInputV3,
    semantic_claim_binding: zenodex_zrpf_protocol_v3::CommitmentV3,
) -> Result<Vec<u8>, SourceOpenedSpotSettlementErrorV6> {
    input.validate_self_consistency()?;
    let base = input.base();
    let proposal = decode_exact_value_aggregate_proposal_v5(base.proposal_bytes())?;
    let replay = OrdinarySpotSettlementReplayDataV2::recompose(
        &proposal,
        base.authorization(),
        base.witness(),
    )?;
    let replay_bytes = encode_source_opened_spot_settlement_replay_v3(&replay, input.source())?;
    let certificate = compose_ordinary_spot_settlement_certificate_with_operational_carry_v3(
        &proposal,
        base.authorization(),
        base.witness().clone(),
        semantic_claim_binding,
        base.data_availability_certificate(),
        source_opened_spot_settlement_replay_schema_id_v3()?,
        &replay_bytes,
    )?;
    let plan = decode_exact_settlement_effect_plan_v2(replay.settlement_effect_plan_bytes())?;
    let admission = SettlementAdmissionJournalV1::derive(&certificate, &plan)?;
    encode_settlement_admission_journal_v1(&admission).map_err(Into::into)
}
