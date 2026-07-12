#![no_std]
#![no_main]

extern crate alloc;

// This method authenticates one exact Value Aggregate V5 L2 proposal and
// derives a state-bound ordinary Spot settlement certificate. It establishes
// no DA persistence, source finality, ledger admission, release, or production
// authority. A future sealed verifier must authenticate this guest image and
// exact certificate bytes before any admission decision.

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1;
use zenodex_zrpf_risc0_semantic_shared::{
    decode_exact_ordinary_spot_settlement_guest_envelope_v2,
    MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
};

use receipt_verified::ReceiptVerifiedSpotSettlementInputV2;

risc0_zkvm::guest::entry!(main);

const _: () = assert!(MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2 == 74_678);
const _: () = assert!(MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 == 1_024);

mod receipt_verified {
    use alloc::vec::Vec;
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_protocol_v3::CommitmentV3;
    use zenodex_zrpf_risc0_semantic_shared::{
        bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2,
        compose_ordinary_spot_settlement_guest_output_after_l2_verification_v2,
        OrdinarySpotSettlementGuestCompositionErrorV2, OrdinarySpotSettlementGuestEnvelopeV2,
        OrdinarySpotSettlementGuestInputV2,
    };
    use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;
    use zenodex_zrpf_risc0_value_aggregate_root_policy::PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(super) enum ReceiptVerifiedSpotSettlementInputErrorV2 {
        ClaimBinding,
        InputBinding,
    }

    /// Guest-local capability created only after the exact L2 proposal bytes
    /// have passed RISC0 assumption verification under the root policy.
    pub(super) struct ReceiptVerifiedSpotSettlementInputV2 {
        input: OrdinarySpotSettlementGuestInputV2,
        semantic_claim_binding: CommitmentV3,
    }

    impl ReceiptVerifiedSpotSettlementInputV2 {
        pub(super) fn authenticate(
            envelope: OrdinarySpotSettlementGuestEnvelopeV2,
        ) -> Result<Self, ReceiptVerifiedSpotSettlementInputErrorV2> {
            match env::verify(
                PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
                envelope.proposal_bytes(),
            ) {
                Ok(()) => {}
                Err(never) => match never {},
            }
            let semantic_claim_binding = derive_risc0_verified_claim_binding_v1(
                PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
                envelope.proposal_bytes(),
            )
            .map_err(|_| ReceiptVerifiedSpotSettlementInputErrorV2::ClaimBinding)?;
            let input = bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2(
                envelope,
            )
            .map_err(|_| ReceiptVerifiedSpotSettlementInputErrorV2::InputBinding)?;
            Ok(Self {
                input,
                semantic_claim_binding,
            })
        }

        pub(super) fn compose(
            &self,
        ) -> Result<Vec<u8>, OrdinarySpotSettlementGuestCompositionErrorV2> {
            compose_ordinary_spot_settlement_guest_output_after_l2_verification_v2(
                &self.input,
                self.semantic_claim_binding,
            )
        }
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    // The envelope decoder validates bounded framing and non-proposal
    // components while preserving the V5 proposal as uninterpreted bytes.
    let envelope = match decode_exact_ordinary_spot_settlement_guest_envelope_v2(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF ordinary Spot settlement envelope rejected"),
    };
    let verified = match ReceiptVerifiedSpotSettlementInputV2::authenticate(envelope) {
        Ok(value) => value,
        Err(_) => abort("ZRPF ordinary Spot settlement L2 binding rejected"),
    };
    let certificate_bytes = match verified.compose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF ordinary Spot settlement composition rejected"),
    };
    if certificate_bytes.len() > MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 {
        abort("ZRPF ordinary Spot settlement certificate exceeds bound");
    }
    env::commit_slice(&certificate_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2 => {
            value
        }
        _ => abort("ZRPF ordinary Spot settlement input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
