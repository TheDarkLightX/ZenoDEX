//! Independent retained-receipt replay for the bounded Spot V6 proof chain.
//!
//! The verifier authenticates and exactly recomposes leaf, L1, L2, and
//! settlement statements. It also requires one exact Succinct seal-word
//! mutation per layer to fail cryptographic verification and constructs a fake
//! leaf receipt that must remain rejected even when ambient dev-mode variables
//! are present. The output grants no ledger, release, or production authority.

use std::io::{self, Read, Write};

use risc0_zkvm::{FakeReceipt, InnerReceipt, Receipt, ReceiptClaim};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use zenodex_zrpf_protocol_v3::NodeLevelV3;
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::{
    pinned_source_opened_spot_value_leaf_identity_v6,
    source_opened_spot_value_aggregate_l1_manifest_root_v6,
    source_opened_spot_value_aggregate_l1_profile_id_v6,
    PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6,
};
use zenodex_zrpf_risc0_spot_value_aggregate_l2_policy_v6::{
    pinned_source_opened_spot_value_aggregate_l1_identity_v6,
    PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
};
use zenodex_zrpf_risc0_spot_value_aggregate_root_policy_v6::pinned_source_opened_spot_value_aggregate_l2_root_identity_v6;
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    decode_exact_source_opened_spot_value_leaf_input_v6,
    recompose_source_opened_spot_value_leaf_statement_v6,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    recompose_expected_source_opened_spot_value_aggregate_level_one_v6,
    recompose_expected_value_aggregate_level_two_v5, ValueAggregateLevelOneInputV5,
    ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionPolicyV5,
};
use zenodex_zrpf_risc0_verifier::{
    ExpectedValueAggregateReceiptIdentityV5, VerifiedSourceOpenedSpotSettlementAdmissionV6,
    VerifiedSourceOpenedSpotValueLeafReceiptV6, VerifiedValueAggregateReceiptV5,
    MAX_CANONICAL_RECEIPT_BYTES_V3,
};

const REQUEST_SCHEMA: &str = "zenodex.source_opened_spot_v6_chain_verifier.request.v1";
const RESPONSE_SCHEMA: &str = "zenodex.source_opened_spot_v6_chain_verifier.response.v1";
const ERROR_SCHEMA: &str = "zenodex.source_opened_spot_v6_chain_verifier.error.v1";
const MAX_REQUEST_BYTES: usize = 48 * 1_024 * 1_024;
const MAX_AUXILIARY_BYTES: usize = 16 * 1_024 * 1_024;
const MUTATION_WORD_INDEX: usize = 1;

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct VerifyRequestV1 {
    schema: String,
    leaf_source_envelope_hex: String,
    leaf_receipt_hex: String,
    leaf_mutation_receipt_hex: String,
    level_one_receipt_hex: String,
    level_one_mutation_receipt_hex: String,
    level_two_receipt_hex: String,
    level_two_mutation_receipt_hex: String,
    settlement_receipt_hex: String,
    settlement_mutation_receipt_hex: String,
    settlement_guest_input_hex: String,
}

#[derive(Debug, Serialize)]
struct VerifyResponseV1 {
    ok: bool,
    schema: &'static str,
    positive_receipts_verified: u8,
    exact_seal_mutations_rejected: u8,
    fake_receipt_rejected: bool,
    receipt_profile_id: String,
    leaf_receipt_sha256: String,
    level_one_receipt_sha256: String,
    level_two_receipt_sha256: String,
    settlement_receipt_sha256: String,
    settlement_claim_binding: String,
    settlement_admission_journal_sha256: String,
    release_authority: bool,
    settlement_authority: bool,
    production_authority: bool,
}

#[derive(Debug, Serialize)]
struct ErrorResponseV1 {
    ok: bool,
    schema: &'static str,
    error_code: &'static str,
}

#[derive(Clone, Copy, Debug)]
struct CliError(&'static str);

fn main() {
    match run() {
        Ok(response) => {
            if write_json(&response, io::stdout().lock()).is_err() {
                emit_error(CliError("response_write_failed"));
            }
        }
        Err(error) => emit_error(error),
    }
}

fn run() -> Result<VerifyResponseV1, CliError> {
    let request_bytes = read_bounded_stdin()?;
    let request = decode_exact_request(&request_bytes)?;
    let leaf_source_envelope = decode_lower_hex(
        &request.leaf_source_envelope_hex,
        MAX_AUXILIARY_BYTES,
        "leaf_source_envelope_rejected",
    )?;
    let leaf_bytes = receipt_bytes(&request.leaf_receipt_hex, "leaf_receipt_rejected")?;
    let leaf_mutation = receipt_bytes(
        &request.leaf_mutation_receipt_hex,
        "leaf_mutation_receipt_rejected",
    )?;
    let l1_bytes = receipt_bytes(&request.level_one_receipt_hex, "level_one_receipt_rejected")?;
    let l1_mutation = receipt_bytes(
        &request.level_one_mutation_receipt_hex,
        "level_one_mutation_receipt_rejected",
    )?;
    let l2_bytes = receipt_bytes(&request.level_two_receipt_hex, "level_two_receipt_rejected")?;
    let l2_mutation = receipt_bytes(
        &request.level_two_mutation_receipt_hex,
        "level_two_mutation_receipt_rejected",
    )?;
    let settlement_bytes = receipt_bytes(
        &request.settlement_receipt_hex,
        "settlement_receipt_rejected",
    )?;
    let settlement_mutation = receipt_bytes(
        &request.settlement_mutation_receipt_hex,
        "settlement_mutation_receipt_rejected",
    )?;
    let settlement_guest_input = decode_lower_hex(
        &request.settlement_guest_input_hex,
        MAX_AUXILIARY_BYTES,
        "settlement_guest_input_rejected",
    )?;

    require_exact_seal_mutation(&leaf_bytes, &leaf_mutation)?;
    require_exact_seal_mutation(&l1_bytes, &l1_mutation)?;
    require_exact_seal_mutation(&l2_bytes, &l2_mutation)?;
    require_exact_seal_mutation(&settlement_bytes, &settlement_mutation)?;

    let leaf_envelope = decode_exact_source_opened_spot_value_leaf_input_v6(&leaf_source_envelope)
        .map_err(|_| CliError("leaf_source_envelope_rejected"))?;
    let expected_leaf = recompose_source_opened_spot_value_leaf_statement_v6(&leaf_envelope)
        .map_err(|_| CliError("leaf_recomposition_rejected"))?;
    let leaf = VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_exact_succinct_bytes(
        &leaf_bytes,
        &expected_leaf,
    )
    .map_err(|_| CliError("leaf_receipt_rejected"))?;
    if VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_exact_succinct_bytes(
        &leaf_mutation,
        &expected_leaf,
    )
    .is_ok()
    {
        return Err(CliError("leaf_mutation_accepted"));
    }

    let l1_input = ValueAggregateLevelOneInputV5::new(vec![leaf.receipt().journal.bytes.clone()])
        .map_err(|_| CliError("level_one_input_rejected"))?;
    let l1_policy = ValueAggregateRecompositionPolicyV5::new(
        leaf.statement()
            .structural_adapter_journal()
            .scope()
            .clone(),
        vec![pinned_source_opened_spot_value_leaf_identity_v6()
            .map_err(|_| CliError("level_one_policy_rejected"))?],
    )
    .map_err(|_| CliError("level_one_policy_rejected"))?;
    let expected_l1 =
        recompose_expected_source_opened_spot_value_aggregate_level_one_v6(&l1_input, &l1_policy)
            .map_err(|_| CliError("level_one_recomposition_rejected"))?;
    let l1_identity = expected_l1_identity()?;
    let l1 = VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &l1_bytes,
        PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
        l1_identity,
        &expected_l1,
    )
    .map_err(|_| CliError("level_one_receipt_rejected"))?;
    if VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &l1_mutation,
        PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
        l1_identity,
        &expected_l1,
    )
    .is_ok()
    {
        return Err(CliError("level_one_mutation_accepted"));
    }

    let l2_input = ValueAggregateLevelTwoInputV5::new(vec![l1.receipt().journal.bytes.clone()])
        .map_err(|_| CliError("level_two_input_rejected"))?;
    let l2_policy = ValueAggregateRecompositionPolicyV5::new(
        l1.proposal().scope().clone(),
        vec![pinned_source_opened_spot_value_aggregate_l1_identity_v6()
            .map_err(|_| CliError("level_two_policy_rejected"))?],
    )
    .map_err(|_| CliError("level_two_policy_rejected"))?;
    let expected_l2 = recompose_expected_value_aggregate_level_two_v5(&l2_input, &l2_policy)
        .map_err(|_| CliError("level_two_recomposition_rejected"))?;
    let l2_root = pinned_source_opened_spot_value_aggregate_l2_root_identity_v6()
        .map_err(|_| CliError("level_two_identity_rejected"))?;
    let l2_identity = ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(2).map_err(|_| CliError("level_two_identity_rejected"))?,
        l2_root.expected_profile_id(),
        l2_root.expected_manifest_root(),
    )
    .map_err(|_| CliError("level_two_identity_rejected"))?;
    let _l2 = VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &l2_bytes,
        l2_root.expected_image_id(),
        l2_identity,
        &expected_l2,
    )
    .map_err(|_| CliError("level_two_receipt_rejected"))?;
    if VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &l2_mutation,
        l2_root.expected_image_id(),
        l2_identity,
        &expected_l2,
    )
    .is_ok()
    {
        return Err(CliError("level_two_mutation_accepted"));
    }

    let settlement = VerifiedSourceOpenedSpotSettlementAdmissionV6::verify(
        &settlement_bytes,
        &settlement_guest_input,
    )
    .map_err(|_| CliError("settlement_receipt_rejected"))?;
    if VerifiedSourceOpenedSpotSettlementAdmissionV6::verify(
        &settlement_mutation,
        &settlement_guest_input,
    )
    .is_ok()
    {
        return Err(CliError("settlement_mutation_accepted"));
    }
    require_fake_leaf_rejected(&leaf)?;

    let settlement_journal = &settlement.verified_receipt().receipt().journal.bytes;
    Ok(VerifyResponseV1 {
        ok: true,
        schema: RESPONSE_SCHEMA,
        positive_receipts_verified: 4,
        exact_seal_mutations_rejected: 4,
        fake_receipt_rejected: true,
        receipt_profile_id: settlement
            .verified_receipt()
            .receipt_profile()
            .profile_id()
            .to_owned(),
        leaf_receipt_sha256: sha256_hex(&leaf_bytes),
        level_one_receipt_sha256: sha256_hex(&l1_bytes),
        level_two_receipt_sha256: sha256_hex(&l2_bytes),
        settlement_receipt_sha256: sha256_hex(&settlement_bytes),
        settlement_claim_binding: hex32(
            settlement
                .verified_receipt()
                .settlement_claim_binding()
                .as_bytes(),
        ),
        settlement_admission_journal_sha256: sha256_hex(settlement_journal),
        release_authority: false,
        settlement_authority: false,
        production_authority: false,
    })
}

fn expected_l1_identity() -> Result<ExpectedValueAggregateReceiptIdentityV5, CliError> {
    let program_id =
        program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6)
            .map_err(|_| CliError("level_one_identity_rejected"))?;
    ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(1).map_err(|_| CliError("level_one_identity_rejected"))?,
        source_opened_spot_value_aggregate_l1_profile_id_v6()
            .map_err(|_| CliError("level_one_identity_rejected"))?,
        source_opened_spot_value_aggregate_l1_manifest_root_v6(program_id)
            .map_err(|_| CliError("level_one_identity_rejected"))?,
    )
    .map_err(|_| CliError("level_one_identity_rejected"))
}

fn require_fake_leaf_rejected(
    leaf: &VerifiedSourceOpenedSpotValueLeafReceiptV6,
) -> Result<(), CliError> {
    let fake = Receipt::try_from(FakeReceipt::new(ReceiptClaim::ok(
        PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6,
        leaf.receipt().journal.bytes.clone(),
    )))
    .map_err(|_| CliError("fake_receipt_construction_failed"))?;
    let fake_bytes =
        serde_json::to_vec(&fake).map_err(|_| CliError("fake_receipt_construction_failed"))?;
    if VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_canonical_succinct_bytes(
        &fake_bytes,
    )
    .is_ok()
    {
        return Err(CliError("fake_receipt_accepted"));
    }
    Ok(())
}

fn require_exact_seal_mutation(source: &[u8], candidate: &[u8]) -> Result<(), CliError> {
    let source_receipt = decode_exact_receipt(source)?;
    let mut candidate_receipt = decode_exact_receipt(candidate)?;
    let (source_seal, candidate_seal) = match (&source_receipt.inner, &candidate_receipt.inner) {
        (InnerReceipt::Succinct(source), InnerReceipt::Succinct(candidate)) => {
            (&source.seal, &candidate.seal)
        }
        _ => return Err(CliError("mutation_relation_rejected")),
    };
    if source_seal.len() <= MUTATION_WORD_INDEX || source_seal.len() != candidate_seal.len() {
        return Err(CliError("mutation_relation_rejected"));
    }
    let mut difference = None;
    for (index, (original, mutated)) in source_seal.iter().zip(candidate_seal).enumerate() {
        if original != mutated {
            if difference.replace((index, *original, *mutated)).is_some() {
                return Err(CliError("mutation_relation_rejected"));
            }
        }
    }
    if difference
        != Some((
            MUTATION_WORD_INDEX,
            source_seal[MUTATION_WORD_INDEX],
            source_seal[MUTATION_WORD_INDEX] ^ 1,
        ))
    {
        return Err(CliError("mutation_relation_rejected"));
    }
    match &mut candidate_receipt.inner {
        InnerReceipt::Succinct(candidate_inner) => {
            candidate_inner.seal[MUTATION_WORD_INDEX] = source_seal[MUTATION_WORD_INDEX];
        }
        _ => return Err(CliError("mutation_relation_rejected")),
    }
    let restored = serde_json::to_vec(&candidate_receipt)
        .map_err(|_| CliError("mutation_relation_rejected"))?;
    if restored != source {
        return Err(CliError("mutation_relation_rejected"));
    }
    Ok(())
}

fn decode_exact_receipt(bytes: &[u8]) -> Result<Receipt, CliError> {
    let receipt: Receipt =
        serde_json::from_slice(bytes).map_err(|_| CliError("mutation_relation_rejected"))?;
    let canonical =
        serde_json::to_vec(&receipt).map_err(|_| CliError("mutation_relation_rejected"))?;
    if canonical != bytes {
        return Err(CliError("mutation_relation_rejected"));
    }
    Ok(receipt)
}

fn receipt_bytes(value: &str, code: &'static str) -> Result<Vec<u8>, CliError> {
    decode_lower_hex(value, MAX_CANONICAL_RECEIPT_BYTES_V3, code)
}

fn read_bounded_stdin() -> Result<Vec<u8>, CliError> {
    let limit = u64::try_from(MAX_REQUEST_BYTES + 1).map_err(|_| CliError("request_too_large"))?;
    let mut bytes = Vec::new();
    io::stdin()
        .lock()
        .take(limit)
        .read_to_end(&mut bytes)
        .map_err(|_| CliError("request_read_failed"))?;
    if bytes.is_empty() || bytes.len() > MAX_REQUEST_BYTES {
        return Err(CliError("request_too_large"));
    }
    Ok(bytes)
}

fn decode_exact_request(bytes: &[u8]) -> Result<VerifyRequestV1, CliError> {
    let request: VerifyRequestV1 =
        serde_json::from_slice(bytes).map_err(|_| CliError("request_json_rejected"))?;
    if request.schema != REQUEST_SCHEMA {
        return Err(CliError("request_schema_rejected"));
    }
    if serde_json::to_vec(&request).map_err(|_| CliError("request_json_rejected"))? != bytes {
        return Err(CliError("request_json_noncanonical"));
    }
    Ok(request)
}

fn decode_lower_hex(
    value: &str,
    maximum_bytes: usize,
    code: &'static str,
) -> Result<Vec<u8>, CliError> {
    if value.is_empty() || value.len() > maximum_bytes.saturating_mul(2) || value.len() % 2 != 0 {
        return Err(CliError(code));
    }
    let mut decoded = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let high = lower_nibble(pair[0]).ok_or(CliError(code))?;
        let low = lower_nibble(pair[1]).ok_or(CliError(code))?;
        decoded.push((high << 4) | low);
    }
    Ok(decoded)
}

const fn lower_nibble(value: u8) -> Option<u8> {
    match value {
        b'0'..=b'9' => Some(value - b'0'),
        b'a'..=b'f' => Some(value - b'a' + 10),
        _ => None,
    }
}

fn write_json(value: &impl Serialize, mut writer: impl Write) -> Result<(), CliError> {
    let bytes = serde_json::to_vec(value).map_err(|_| CliError("response_encode_failed"))?;
    writer
        .write_all(&bytes)
        .map_err(|_| CliError("response_write_failed"))?;
    writer
        .write_all(b"\n")
        .map_err(|_| CliError("response_write_failed"))
}

fn emit_error(error: CliError) -> ! {
    let response = ErrorResponseV1 {
        ok: false,
        schema: ERROR_SCHEMA,
        error_code: error.0,
    };
    let _ = write_json(&response, io::stderr().lock());
    std::process::exit(1)
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex32(&Sha256::digest(bytes))
}

fn hex32(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(bytes.len() * 2);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

#[cfg(test)]
mod tests {
    use super::{decode_exact_request, lower_nibble, REQUEST_SCHEMA};

    #[test]
    fn lowercase_hex_decoder_is_exact() {
        assert_eq!(lower_nibble(b'0'), Some(0));
        assert_eq!(lower_nibble(b'f'), Some(15));
        assert_eq!(lower_nibble(b'F'), None);
    }

    #[test]
    fn request_rejects_unknown_and_duplicate_fields() {
        let unknown = format!(
            "{{\"schema\":\"{REQUEST_SCHEMA}\",\"leaf_source_envelope_hex\":\"00\",\"extra\":true}}"
        );
        assert!(decode_exact_request(unknown.as_bytes()).is_err());
        let duplicate =
            format!("{{\"schema\":\"{REQUEST_SCHEMA}\",\"schema\":\"{REQUEST_SCHEMA}\"}}");
        assert!(decode_exact_request(duplicate.as_bytes()).is_err());
    }
}
