use std::path::PathBuf;

use risc0_zkvm::{compute_image_id, default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts};
use zenodex_zrpf_protocol_v3::ProposedValueAggregateV5;
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF, ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID,
    ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ELF, ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_value_aggregate_shared::{
    encode_value_aggregate_guest_input_v5, recompose_expected_value_aggregate_level_one_v5,
    GovernedValueChildIdentityV5, ValueAggregateGuestInputErrorV5, ValueAggregateGuestInputV5,
    ValueAggregateLevelOneInputV5, ValueAggregateRecompositionErrorV5,
    ValueAggregateRecompositionPolicyV5,
};
use zenodex_zrpf_risc0_value_node_shared::{
    spot_value_leaf_manifest_root_v4, spot_value_leaf_profile_id_v4, PINNED_V1_ADAPTER_IMAGE_ID_A,
};
use zenodex_zrpf_risc0_verifier::{
    historical_spot_value_leaf_v4::AuthenticatedSpotValueLeafReceiptV4,
    VerifiedValueAggregateReceiptV5,
};

#[path = "prove_value_aggregate_l1_v5/artifact_io.rs"]
mod artifact_io;
#[path = "prove_value_aggregate_l1_v5/cli.rs"]
mod cli;
#[path = "prove_value_aggregate_l1_v5/report.rs"]
mod report;

use artifact_io::{canonical_receipt_bytes, persist_new_receipt, read_bounded_receipt_file};
use cli::{Mode, Options};

struct LevelOneMaterial {
    guest_input_bytes: Vec<u8>,
    expected_proposal: ProposedValueAggregateV5,
}

#[derive(Debug, PartialEq, Eq)]
enum LevelOneMaterialError {
    Recomposition(ValueAggregateRecompositionErrorV5),
    GuestInput(ValueAggregateGuestInputErrorV5),
}

impl core::fmt::Display for LevelOneMaterialError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Recomposition(error) => write!(formatter, "V5 recomposition rejected: {error}"),
            Self::GuestInput(error) => write!(formatter, "V5 guest input rejected: {error}"),
        }
    }
}

impl From<ValueAggregateRecompositionErrorV5> for LevelOneMaterialError {
    fn from(error: ValueAggregateRecompositionErrorV5) -> Self {
        Self::Recomposition(error)
    }
}

impl From<ValueAggregateGuestInputErrorV5> for LevelOneMaterialError {
    fn from(error: ValueAggregateGuestInputErrorV5) -> Self {
        Self::GuestInput(error)
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let options = cli::process_options()?;
    validate_methods()?;
    let children = load_authenticated_children(&options.child_paths)?;
    let policy = governed_child_policy(&children)?;
    let child_journal_bytes = children
        .iter()
        .map(|child| child.receipt().journal.bytes.clone())
        .collect();
    let material = recompose_exact_level_one(child_journal_bytes, &policy)
        .map_err(|error| error.to_string())?;
    match options.mode {
        Mode::Prove => prove_and_persist(options, children, material),
        Mode::VerifyExisting => verify_existing(options, children.len(), material),
    }
}

fn prove_and_persist(
    options: Options,
    children: Vec<AuthenticatedSpotValueLeafReceiptV4>,
    material: LevelOneMaterial,
) -> Result<(), String> {
    let verified = prove_and_verify(&children, &material, options.expected_identity)?;
    let receipt_bytes = canonical_receipt_bytes(verified.receipt())?;
    persist_new_receipt(&options.receipt_path, &receipt_bytes)?;
    report::write_report(
        options.mode,
        &verified,
        children.len(),
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID,
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
        &receipt_bytes,
        true,
    )
}

fn verify_existing(
    options: Options,
    child_count: usize,
    material: LevelOneMaterial,
) -> Result<(), String> {
    let receipt_bytes = read_bounded_receipt_file(&options.receipt_path)?;
    let verified = VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &receipt_bytes,
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
        options.expected_identity,
        &material.expected_proposal,
    )
    .map_err(|error| format!("sealed V5 aggregate verification failed: {error}"))?;
    report::write_report(
        options.mode,
        &verified,
        child_count,
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID,
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
        &receipt_bytes,
        false,
    )
}

fn load_authenticated_children(
    paths: &[PathBuf],
) -> Result<Vec<AuthenticatedSpotValueLeafReceiptV4>, String> {
    paths
        .iter()
        .enumerate()
        .map(|(index, path)| {
            let bytes = read_bounded_receipt_file(path)
                .map_err(|error| format!("child receipt {index}: {error}"))?;
            AuthenticatedSpotValueLeafReceiptV4::verify_canonical_succinct_bytes(
                &bytes,
                ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID,
            )
            .map_err(|error| format!("child receipt {index} authentication failed: {error}"))
        })
        .collect()
}

fn governed_child_policy(
    children: &[AuthenticatedSpotValueLeafReceiptV4],
) -> Result<ValueAggregateRecompositionPolicyV5, String> {
    let first = children
        .first()
        .ok_or_else(|| "V5 aggregate requires at least one authenticated child".to_owned())?;
    let child_program_id = program_id_from_risc0_words_v3(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID)
        .map_err(|error| format!("derive governed child program: {error}"))?;
    let adapter_program_id = program_id_from_risc0_words_v3(PINNED_V1_ADAPTER_IMAGE_ID_A)
        .map_err(|error| format!("derive governed adapter program: {error}"))?;
    let child_profile_id = spot_value_leaf_profile_id_v4()
        .map_err(|error| format!("derive governed child profile: {error}"))?;
    let child_manifest_root =
        spot_value_leaf_manifest_root_v4(child_program_id, adapter_program_id)
            .map_err(|error| format!("derive governed child manifest: {error}"))?;
    let identity = GovernedValueChildIdentityV5::new(
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID,
        child_program_id,
        child_profile_id,
        child_manifest_root,
    )
    .map_err(|error| format!("construct governed child identity: {error}"))?;
    ValueAggregateRecompositionPolicyV5::new(
        first.journal().structural().scope().clone(),
        vec![identity; children.len()],
    )
    .map_err(|error| format!("construct governed child policy: {error}"))
}

fn recompose_exact_level_one(
    child_journal_bytes: Vec<Vec<u8>>,
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<LevelOneMaterial, LevelOneMaterialError> {
    let input = ValueAggregateLevelOneInputV5::new(child_journal_bytes)?;
    let expected_proposal = recompose_expected_value_aggregate_level_one_v5(&input, policy)?;
    let guest_input_bytes =
        encode_value_aggregate_guest_input_v5(&ValueAggregateGuestInputV5::LevelOne(input))?;
    Ok(LevelOneMaterial {
        guest_input_bytes,
        expected_proposal,
    })
}

fn prove_and_verify(
    children: &[AuthenticatedSpotValueLeafReceiptV4],
    material: &LevelOneMaterial,
    expected_identity: zenodex_zrpf_risc0_verifier::ExpectedValueAggregateReceiptIdentityV5,
) -> Result<VerifiedValueAggregateReceiptV5, String> {
    let input_length = u32::try_from(material.guest_input_bytes.len())
        .map_err(|_| "V5 guest input length exceeds u32".to_owned())?;
    let mut builder = ExecutorEnv::builder();
    builder
        .write_slice(&[input_length])
        .write_slice(&material.guest_input_bytes);
    for child in children {
        builder.add_assumption(child.receipt().clone());
    }
    let executor_env = builder
        .build()
        .map_err(|error| format!("V5 aggregate executor environment: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V5 aggregate proving failed: {error}"))?
        .receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("V5 aggregate prover returned a non-Succinct receipt".to_owned());
    }
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &receipt_bytes,
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
        expected_identity,
        &material.expected_proposal,
    )
    .map_err(|error| format!("sealed V5 aggregate verification failed: {error}"))
}

fn validate_methods() -> Result<(), String> {
    validate_method(
        "Spot value V4 child",
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF,
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID,
    )?;
    validate_method(
        "value aggregate L1 V5",
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ELF,
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
    )?;
    if ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID == ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID {
        return Err("child and parent image IDs must differ".to_owned());
    }
    Ok(())
}

fn validate_method(name: &str, elf: &[u8], image_id: [u32; 8]) -> Result<(), String> {
    if elf.is_empty() || image_id.iter().all(|word| *word == 0) {
        return Err(format!("{name} method is a placeholder"));
    }
    let computed =
        compute_image_id(elf).map_err(|error| format!("compute {name} image ID: {error}"))?;
    if computed != Digest::from(image_id) {
        return Err(format!("{name} image ID mismatch"));
    }
    Ok(())
}

#[cfg(test)]
#[path = "prove_value_aggregate_l1_v5/tests.rs"]
mod tests;
