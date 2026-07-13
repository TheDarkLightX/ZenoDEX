#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1;
use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
    decode_exact_source_opened_spot_settlement_guest_envelope_v3,
    MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3,
};

use receipt_verified::ReceiptVerifiedSourceOpenedSpotSettlementV6;

risc0_zkvm::guest::entry!(main);

mod receipt_verified {
    use alloc::vec::Vec;
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_protocol_v3::CommitmentV3;
    use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;
    use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
        bind_source_opened_spot_settlement_guest_input_after_l2_receipt_verification_v3,
        compose_source_opened_spot_settlement_output_after_l2_verification_v3,
        SourceOpenedSpotSettlementErrorV6, SourceOpenedSpotSettlementGuestEnvelopeV3,
        SourceOpenedSpotSettlementGuestInputV3,
    };
    use zenodex_zrpf_risc0_spot_value_aggregate_root_policy_v6::PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6;

    pub(super) struct ReceiptVerifiedSourceOpenedSpotSettlementV6 {
        input: SourceOpenedSpotSettlementGuestInputV3,
        l2_claim_binding: CommitmentV3,
    }

    impl ReceiptVerifiedSourceOpenedSpotSettlementV6 {
        pub(super) fn authenticate(
            envelope: SourceOpenedSpotSettlementGuestEnvelopeV3,
        ) -> Result<Self, SourceOpenedSpotSettlementErrorV6> {
            match env::verify(
                PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6,
                envelope.proposal_bytes(),
            ) {
                Ok(()) => {}
                Err(never) => match never {},
            }
            let l2_claim_binding = derive_risc0_verified_claim_binding_v1(
                PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6,
                envelope.proposal_bytes(),
            )
            .map_err(|_| SourceOpenedSpotSettlementErrorV6::InvalidDerivedCommitment("L2 claim"))?;
            let input =
                bind_source_opened_spot_settlement_guest_input_after_l2_receipt_verification_v3(
                    envelope,
                )?;
            Ok(Self {
                input,
                l2_claim_binding,
            })
        }

        pub(super) fn compose(&self) -> Result<Vec<u8>, SourceOpenedSpotSettlementErrorV6> {
            compose_source_opened_spot_settlement_output_after_l2_verification_v3(
                &self.input,
                self.l2_claim_binding,
            )
        }
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    let envelope = match decode_exact_source_opened_spot_settlement_guest_envelope_v3(&input_bytes)
    {
        Ok(value) => value,
        Err(_) => abort("ZRPF source-opened Spot V6 settlement envelope rejected"),
    };
    let verified = match ReceiptVerifiedSourceOpenedSpotSettlementV6::authenticate(envelope) {
        Ok(value) => value,
        Err(_) => abort("ZRPF source-opened Spot V6 settlement L2 binding rejected"),
    };
    let admission_journal_bytes = match verified.compose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF source-opened Spot V6 settlement composition rejected"),
    };
    if admission_journal_bytes.len() > MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1 {
        abort("ZRPF source-opened Spot V6 admission journal exceeds bound");
    }
    env::commit_slice(&admission_journal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value)
            if value > 0 && value <= MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3 =>
        {
            value
        }
        _ => abort("ZRPF source-opened Spot V6 settlement input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
