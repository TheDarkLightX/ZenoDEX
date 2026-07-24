use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::CommitmentV3;

use crate::{
    encode_spot_settlement_v7_journal_v1,
    open_spot_settlement_v7_after_source_receipt_verification_v1,
    ProposedSpotSettlementV7EnvelopeV1, SourceOpenedSpotSettlementV7OpeningV1,
    SpotSettlementV7ErrorV1, SpotSettlementV7JournalV1,
};

/// Proof-neutral result after exact source opening and V7 recomposition.
///
/// The opening retains complete pre/post snapshots and the internally derived
/// Plan B. The journal is the bounded public receipt surface. Only a
/// receipt-bearing guest or sealed host verifier may elevate this relation.
pub struct ComposedSpotSettlementV7V1 {
    opening: SourceOpenedSpotSettlementV7OpeningV1,
    journal: SpotSettlementV7JournalV1,
    journal_bytes: Vec<u8>,
}

impl ComposedSpotSettlementV7V1 {
    pub const fn opening(&self) -> &SourceOpenedSpotSettlementV7OpeningV1 {
        &self.opening
    }
    pub const fn journal(&self) -> &SpotSettlementV7JournalV1 {
        &self.journal
    }
    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }
    pub fn into_parts(
        self,
    ) -> (
        SourceOpenedSpotSettlementV7OpeningV1,
        SpotSettlementV7JournalV1,
        Vec<u8>,
    ) {
        (self.opening, self.journal, self.journal_bytes)
    }
}

pub fn compose_spot_settlement_v7_after_source_receipt_verification_v1(
    envelope: ProposedSpotSettlementV7EnvelopeV1,
    verified_child_image_id: [u32; 8],
    verified_child_claim_binding: CommitmentV3,
) -> Result<ComposedSpotSettlementV7V1, SpotSettlementV7ErrorV1> {
    let opening = open_spot_settlement_v7_after_source_receipt_verification_v1(
        envelope,
        verified_child_image_id,
        verified_child_claim_binding,
    )?;
    let journal = SpotSettlementV7JournalV1::from_opening(&opening)?;
    let journal_bytes = encode_spot_settlement_v7_journal_v1(&journal)?;
    Ok(ComposedSpotSettlementV7V1 {
        opening,
        journal,
        journal_bytes,
    })
}
