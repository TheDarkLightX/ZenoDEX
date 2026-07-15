//! Fail-closed evidence harness for Spot settlement V7.

use risc0_zkvm::{compute_image_id, default_prover, Digest, InnerReceipt, ProverOpts};

use zenodex_zrpf_risc0_execution_profile::{
    build_exact_framed_executor_env_v1, execute_exact_stage_v1, ExactAssumptionV1,
    ExactStageExecutionRequestV1, StageExecutionProfileV1,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, program_id_from_risc0_words_v3,
};
use zenodex_zrpf_risc0_spot_settlement_v7_child_policy::final_source_opened_spot_settlement_v6_image_id_v1;
use zenodex_zrpf_risc0_spot_settlement_v7_methods::{
    ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ELF, ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID,
};
use zenodex_zrpf_risc0_spot_settlement_v7_shared::{
    compose_spot_settlement_v7_after_source_receipt_verification_v1,
    decode_exact_spot_settlement_v7_guest_envelope_v1,
    required_source_child_receipt_security_profile_id_v1,
};
use zenodex_zrpf_risc0_spot_settlement_v7_verifier::{
    verify_spot_settlement_v7_canonical_succinct_bytes, VerifiedSpotSettlementV7ReceiptV1,
};
use zenodex_zrpf_risc0_verifier::{
    VerifiedSourceOpenedSpotSettlementReceiptV6, ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
};

const SPOT_SETTLEMENT_V7_STAGE_ID_V1: &str = "spot_settlement_v7";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotSettlementV7HarnessErrorV1 {
    FinalV6ImageIdUnmaterialized,
    V7MethodUnmaterialized,
}

pub fn require_materialized_spot_settlement_v7_method_v1(
) -> Result<(), SpotSettlementV7HarnessErrorV1> {
    final_source_opened_spot_settlement_v6_image_id_v1()
        .map_err(|_| SpotSettlementV7HarnessErrorV1::FinalV6ImageIdUnmaterialized)?;
    if ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ELF.is_empty()
        || ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID
            .iter()
            .all(|word| *word == 0)
    {
        return Err(SpotSettlementV7HarnessErrorV1::V7MethodUnmaterialized);
    }
    Ok(())
}

/// Prove one exact V7 envelope with one authenticated V6 child assumption and
/// immediately cross the sealed host-verification boundary.
///
/// This harness grants no release or production authority. It exists to
/// generate bounded local evidence after C1 materializes the final V6 image.
pub fn prove_and_verify_spot_settlement_v7_v1(
    exact_guest_input_bytes: &[u8],
    canonical_source_v6_receipt_bytes: &[u8],
) -> Result<VerifiedSpotSettlementV7ReceiptV1, String> {
    let prepared =
        prepare_spot_settlement_v7_v1(exact_guest_input_bytes, canonical_source_v6_receipt_bytes)?;
    let env = build_exact_framed_executor_env_v1(
        exact_guest_input_bytes,
        std::slice::from_ref(prepared.verified_child.receipt()),
    )
    .map_err(|error| format!("V7 executor environment rejected: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            env,
            ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V7 proving failed: {error}"))?
        .receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("V7 prover returned a non-Succinct receipt".to_owned());
    }
    let receipt_bytes =
        serde_json::to_vec(&receipt).map_err(|error| format!("encode V7 receipt: {error}"))?;
    verify_spot_settlement_v7_canonical_succinct_bytes(
        &receipt_bytes,
        exact_guest_input_bytes,
        canonical_source_v6_receipt_bytes,
    )
    .map_err(|error| format!("sealed V7 verification failed: {error}"))
}

/// Execute the exact V7 workload without generating a proof.
///
/// The resulting profile binds the observed workload and exact recomposed
/// journal. Every proof, release, settlement, accelerator, and production
/// authority field remains false.
pub fn profile_spot_settlement_v7_execution_v1(
    exact_guest_input_bytes: &[u8],
    canonical_source_v6_receipt_bytes: &[u8],
) -> Result<StageExecutionProfileV1, String> {
    let prepared =
        prepare_spot_settlement_v7_v1(exact_guest_input_bytes, canonical_source_v6_receipt_bytes)?;
    let assumptions = [ExactAssumptionV1::new(
        prepared.verified_child.receipt(),
        prepared.child_image,
    )];
    let request = ExactStageExecutionRequestV1::new(
        SPOT_SETTLEMENT_V7_STAGE_ID_V1,
        ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
        ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ELF,
        ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID,
        exact_guest_input_bytes,
        &assumptions,
        &prepared.expected_journal_bytes,
    )
    .map_err(|error| format!("V7 execution-profile request rejected: {error}"))?;
    execute_exact_stage_v1(&request)
        .map_err(|error| format!("V7 execution profiling failed: {error}"))
}

struct PreparedSpotSettlementV7V1 {
    child_image: [u32; 8],
    verified_child: VerifiedSourceOpenedSpotSettlementReceiptV6,
    expected_journal_bytes: Vec<u8>,
}

fn prepare_spot_settlement_v7_v1(
    exact_guest_input_bytes: &[u8],
    canonical_source_v6_receipt_bytes: &[u8],
) -> Result<PreparedSpotSettlementV7V1, String> {
    require_materialized_spot_settlement_v7_method_v1()
        .map_err(|error| format!("V7 method policy rejected: {error:?}"))?;
    if std::env::var_os("RISC0_DEV_MODE").is_some() {
        return Err("ambient RISC0_DEV_MODE is forbidden".to_owned());
    }
    let computed = compute_image_id(ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ELF)
        .map_err(|error| format!("compute V7 image ID: {error}"))?;
    if computed != Digest::from(ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID) {
        return Err("freshly built V7 ELF differs from its generated image ID".to_owned());
    }
    let envelope = decode_exact_spot_settlement_v7_guest_envelope_v1(exact_guest_input_bytes)
        .map_err(|error| format!("V7 guest input rejected: {error}"))?;
    let child_image = final_source_opened_spot_settlement_v6_image_id_v1()
        .map_err(|_| "final V6 child image remains unmaterialized".to_owned())?;
    let expected_child_program = program_id_from_risc0_words_v3(child_image)
        .map_err(|_| "final V6 child program identity is invalid".to_owned())?;
    let verified_child =
        VerifiedSourceOpenedSpotSettlementReceiptV6::verify_canonical_succinct_bytes(
            canonical_source_v6_receipt_bytes,
        )
        .map_err(|error| format!("governed V6 child receipt rejected: {error}"))?;
    if verified_child.verified_program_id() != expected_child_program {
        return Err("sealed V6 verifier identity differs from the V7 child policy".to_owned());
    }
    if verified_child.receipt_profile().profile_id() != ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1 {
        return Err("sealed V6 receipt profile differs from the V7 child policy".to_owned());
    }
    let _required_child_receipt_profile = required_source_child_receipt_security_profile_id_v1()
        .map_err(|error| format!("derive governed V6 child receipt profile: {error}"))?;
    if verified_child.receipt().journal.bytes.as_slice() != envelope.source_child_journal_bytes() {
        return Err("V6 assumption journal differs from the exact V7 envelope child".to_owned());
    }
    let child_claim =
        derive_risc0_verified_claim_binding_v1(child_image, envelope.source_child_journal_bytes())
            .map_err(|error| format!("derive V7 child claim binding: {error}"))?;
    let composed = compose_spot_settlement_v7_after_source_receipt_verification_v1(
        envelope,
        child_image,
        child_claim,
    )
    .map_err(|error| format!("recompose exact V7 journal: {error:?}"))?;
    Ok(PreparedSpotSettlementV7V1 {
        child_image,
        verified_child,
        expected_journal_bytes: composed.journal_bytes().to_vec(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const HARNESS_SOURCE: &str = include_str!("lib.rs");

    #[test]
    fn harness_cannot_prove_against_placeholder_child_identity() {
        assert_eq!(
            require_materialized_spot_settlement_v7_method_v1(),
            Err(SpotSettlementV7HarnessErrorV1::FinalV6ImageIdUnmaterialized)
        );
    }

    #[test]
    fn sealed_v6_profile_verification_precedes_journal_recomposition() {
        let verify = HARNESS_SOURCE
            .find("VerifiedSourceOpenedSpotSettlementReceiptV6::verify_canonical_succinct_bytes")
            .unwrap();
        let recompose = HARNESS_SOURCE
            .rfind("compose_spot_settlement_v7_after_source_receipt_verification_v1(")
            .unwrap();
        assert!(verify < recompose);
        let raw_verify = ["source_v6_receipt", ".verify(child_image)"].concat();
        assert!(!HARNESS_SOURCE.contains(&raw_verify));
    }

    #[test]
    fn proof_and_profile_share_one_exact_preparation_path() {
        let proof_start = HARNESS_SOURCE
            .find("pub fn prove_and_verify_spot_settlement_v7_v1(")
            .unwrap();
        let profile_start = HARNESS_SOURCE
            .find("pub fn profile_spot_settlement_v7_execution_v1(")
            .unwrap();
        let preparation_start = HARNESS_SOURCE
            .find("fn prepare_spot_settlement_v7_v1(")
            .unwrap();
        let proof_source = &HARNESS_SOURCE[proof_start..profile_start];
        let profile_source = &HARNESS_SOURCE[profile_start..preparation_start];
        assert!(proof_source.contains("prepare_spot_settlement_v7_v1("));
        assert!(profile_source.contains("prepare_spot_settlement_v7_v1("));
        assert!(profile_source.contains("execute_exact_stage_v1(&request)"));
        assert!(profile_source.contains("&prepared.expected_journal_bytes"));
    }
}
