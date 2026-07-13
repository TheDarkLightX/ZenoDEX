#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_risc0_spot_settlement_v7_shared::{
    decode_exact_spot_settlement_v7_guest_envelope_v1,
    MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1,
    MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1,
};

use receipt_verified::ReceiptVerifiedSpotSettlementV7;

risc0_zkvm::guest::entry!(main);

mod receipt_verified {
    use alloc::vec::Vec;

    use risc0_zkvm::guest::env;
    use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;
    use zenodex_zrpf_risc0_spot_settlement_v7_child_policy::final_source_opened_spot_settlement_v6_image_id_v1;
    use zenodex_zrpf_risc0_spot_settlement_v7_shared::{
        compose_spot_settlement_v7_after_source_receipt_verification_v1,
        ProposedSpotSettlementV7EnvelopeV1, SpotSettlementV7ErrorV1,
    };

    /// Guest-local typestate proving `env::verify` happened before any child
    /// journal, replay, certificate, or state-opening interpretation.
    pub(super) struct ReceiptVerifiedSpotSettlementV7 {
        journal_bytes: Vec<u8>,
    }

    impl ReceiptVerifiedSpotSettlementV7 {
        pub(super) fn authenticate_and_compose(
            envelope: ProposedSpotSettlementV7EnvelopeV1,
        ) -> Result<Self, SpotSettlementV7ErrorV1> {
            let child_image = final_source_opened_spot_settlement_v6_image_id_v1()
                .map_err(|_| SpotSettlementV7ErrorV1::FinalV6ImageIdUnmaterialized)?;
            match env::verify(child_image, envelope.source_child_journal_bytes()) {
                Ok(()) => {}
                Err(never) => match never {},
            }
            let claim = derive_risc0_verified_claim_binding_v1(
                child_image,
                envelope.source_child_journal_bytes(),
            )
            .map_err(|_| SpotSettlementV7ErrorV1::ChildJournalHash)?;
            let composed = compose_spot_settlement_v7_after_source_receipt_verification_v1(
                envelope,
                child_image,
                claim,
            )?;
            Ok(Self {
                journal_bytes: composed.journal_bytes().to_vec(),
            })
        }

        pub(super) fn journal_bytes(&self) -> &[u8] {
            &self.journal_bytes
        }
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    let envelope = match decode_exact_spot_settlement_v7_guest_envelope_v1(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("Spot settlement V7 envelope rejected"),
    };
    let verified = match ReceiptVerifiedSpotSettlementV7::authenticate_and_compose(envelope) {
        Ok(value) => value,
        Err(_) => abort("Spot settlement V7 source verification or composition rejected"),
    };
    if verified.journal_bytes().len() > MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1 {
        abort("Spot settlement V7 journal exceeds Firecracker payload bound");
    }
    env::commit_slice(verified.journal_bytes());
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0_u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1 => value,
        _ => abort("Spot settlement V7 input length unsupported"),
    };
    let mut input = vec![0_u8; input_len];
    env::read_slice(&mut input);
    input
}
