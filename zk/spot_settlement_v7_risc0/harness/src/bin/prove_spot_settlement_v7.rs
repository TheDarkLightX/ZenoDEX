//! Authority-neutral artifact generator for one bounded Spot V7 receipt.

use std::env;

use risc0_zkvm::{InnerReceipt, Receipt};
use serde_json::json;
use zenodex_zrpf_risc0_spot_settlement_v7_harness::prove_and_verify_spot_settlement_v7_v1;
use zenodex_zrpf_risc0_spot_settlement_v7_shared::MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1;
use zenodex_zrpf_risc0_spot_settlement_v7_verifier::{
    encode_spot_settlement_v7_verifier_output_v1,
    verify_spot_settlement_v7_canonical_succinct_bytes, VerifiedSpotSettlementV7ErrorV1,
    MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1,
};

#[path = "prove_spot_settlement_v7/artifact_io.rs"]
mod artifact_io;
#[path = "prove_spot_settlement_v7/cli.rs"]
mod cli;

use artifact_io::{
    canonical_receipt_bytes, persist_verified_artifacts, read_bounded_regular_file, sha256_hex,
    CandidateArtifactsV1,
};
use cli::parse_options;

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    if env::var_os("RISC0_DEV_MODE").is_some() {
        return Err("ambient RISC0_DEV_MODE is forbidden".to_owned());
    }
    let options = parse_options(env::args().skip(1))?;
    let guest_input = read_bounded_regular_file(
        &options.v7_guest_input,
        "V7 guest input",
        MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1,
    )?;
    let child_receipt = read_bounded_regular_file(
        &options.v6_child_receipt,
        "V6 child receipt",
        MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1,
    )?;

    let verified = prove_and_verify_spot_settlement_v7_v1(&guest_input, &child_receipt)?;
    let receipt_bytes = canonical_receipt_bytes(verified.receipt())?;
    let journal_bytes = verified.receipt().journal.bytes.clone();
    let verifier_output = verified
        .firecracker_output()
        .map_err(|error| format!("derive verified V7 output: {error}"))?;
    let verifier_output_bytes = encode_spot_settlement_v7_verifier_output_v1(&verifier_output)
        .map_err(|error| format!("encode verified V7 output: {error}"))?;
    let plan_b_bytes = verifier_output
        .exact_plan_b_bytes()
        .map_err(|error| format!("extract exact V7 Plan B: {error}"))?;
    let mutation_bytes =
        exact_seal_mutation_reject(verified.receipt(), &guest_input, &child_receipt)?;
    let artifacts = CandidateArtifactsV1 {
        receipt: &receipt_bytes,
        receipt_seal_mutation: &mutation_bytes,
        journal: &journal_bytes,
        verifier_output: &verifier_output_bytes,
        plan_b: &plan_b_bytes,
    };
    persist_verified_artifacts(&options, artifacts)?;
    emit_report(&verified, &guest_input, &child_receipt, artifacts)
}

fn exact_seal_mutation_reject(
    receipt: &Receipt,
    exact_guest_input: &[u8],
    canonical_child_receipt: &[u8],
) -> Result<Vec<u8>, String> {
    let mut candidate = receipt.clone();
    let InnerReceipt::Succinct(inner) = &mut candidate.inner else {
        return Err("verified V7 receipt is not Succinct".to_owned());
    };
    let word = inner
        .seal
        .get_mut(1)
        .ok_or_else(|| "V7 Succinct seal lacks governed word 1".to_owned())?;
    *word ^= 1;
    let mutation_bytes = canonical_receipt_bytes(&candidate)?;
    match verify_spot_settlement_v7_canonical_succinct_bytes(
        &mutation_bytes,
        exact_guest_input,
        canonical_child_receipt,
    ) {
        Err(VerifiedSpotSettlementV7ErrorV1::ReceiptVerificationFailed) => Ok(mutation_bytes),
        Err(error) => Err(format!(
            "V7 exact seal mutation rejected at unexpected boundary: {}",
            error.code()
        )),
        Ok(_) => Err("V7 exact seal mutation was accepted".to_owned()),
    }
}

fn emit_report(
    verified: &zenodex_zrpf_risc0_spot_settlement_v7_verifier::VerifiedSpotSettlementV7ReceiptV1,
    guest_input: &[u8],
    child_receipt: &[u8],
    artifacts: CandidateArtifactsV1<'_>,
) -> Result<(), String> {
    let report = json!({
        "schema": "zenodex/zrpf_spot_settlement_v7_proof_report/v1",
        "status": "spot_settlement_v7_succinct_receipt_verified_before_persistence",
        "v7_program_id": hex32(verified.verified_program_id().as_bytes()),
        "v7_profile_id": hex32(verified.verified_profile_id().as_bytes()),
        "v7_program_manifest_root": hex32(
            verified.verified_program_manifest_root().as_bytes(),
        ),
        "v7_journal_sha256": sha256_hex(artifacts.journal),
        "v7_receipt_sha256": sha256_hex(artifacts.receipt),
        "v7_receipt_seal_mutation_sha256": sha256_hex(
            artifacts.receipt_seal_mutation,
        ),
        "v7_verifier_output_sha256": sha256_hex(artifacts.verifier_output),
        "v7_plan_b_sha256": sha256_hex(artifacts.plan_b),
        "v7_guest_input_sha256": sha256_hex(guest_input),
        "v6_child_receipt_sha256": sha256_hex(child_receipt),
        "receipt_kind": "succinct",
        "exact_seal_mutation_rejected": true,
        "release_authority": false,
        "settlement_authority": false,
        "production_authority": false,
        "zero_knowledge_privacy": false,
        "nonclaims": [
            "candidate generation does not establish source or build provenance",
            "candidate generation does not establish Firecracker execution",
            "candidate generation does not establish data retrievability or finality",
            "candidate generation grants no release settlement or production authority"
        ]
    });
    println!(
        "{}",
        serde_json::to_string(&report)
            .map_err(|error| format!("encode V7 proof report: {error}"))?
    );
    Ok(())
}

fn hex32(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(64);
    for byte in bytes {
        result.push(char::from(HEX[usize::from(byte >> 4)]));
        result.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex32_is_fixed_lowercase() {
        let mut bytes = [0_u8; 32];
        bytes[0] = 0xab;
        bytes[31] = 0xcd;
        let encoded = hex32(&bytes);
        assert_eq!(encoded.len(), 64);
        assert!(encoded.starts_with("ab00"));
        assert!(encoded.ends_with("00cd"));
    }
}
