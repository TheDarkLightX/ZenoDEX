use std::path::PathBuf;

use risc0_zkvm::{compute_image_id, default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts};
use zenodex_zrpf_protocol_v3::{NodeLevelV3, ProposedValueAggregateV5};
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ELF, ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
    ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L2_ELF, ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L2_ID,
};
use zenodex_zrpf_risc0_value_aggregate_l2_policy::{
    pinned_value_aggregate_level_one_identity_v5, PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
};
use zenodex_zrpf_risc0_value_aggregate_root_policy::{
    pinned_value_aggregate_level_two_root_identity_v5, PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    encode_value_aggregate_guest_input_v5, recompose_expected_value_aggregate_level_two_v5,
    ValueAggregateGuestInputErrorV5, ValueAggregateGuestInputV5, ValueAggregateLevelTwoInputV5,
    ValueAggregateRecompositionErrorV5, ValueAggregateRecompositionPolicyV5,
};
use zenodex_zrpf_risc0_verifier::{
    ExpectedValueAggregateReceiptIdentityV5, VerifiedValueAggregateReceiptV5,
};

#[path = "prove_value_aggregate_l2_v5/artifact_io.rs"]
mod artifact_io;
#[path = "prove_value_aggregate_l2_v5/cli.rs"]
mod cli;
#[path = "prove_value_aggregate_l2_v5/report.rs"]
mod report;

use artifact_io::{canonical_receipt_bytes, persist_new_receipt, read_bounded_receipt_file};
use cli::{Mode, Options};

struct LevelTwoMaterial {
    guest_input_bytes: Vec<u8>,
    expected_proposal: ProposedValueAggregateV5,
}

#[derive(Debug, PartialEq, Eq)]
enum LevelTwoMaterialError {
    Recomposition(ValueAggregateRecompositionErrorV5),
    GuestInput(ValueAggregateGuestInputErrorV5),
}

impl core::fmt::Display for LevelTwoMaterialError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Recomposition(error) => {
                write!(formatter, "V5 L2 recomposition rejected: {error}")
            }
            Self::GuestInput(error) => write!(formatter, "V5 L2 guest input rejected: {error}"),
        }
    }
}

impl From<ValueAggregateRecompositionErrorV5> for LevelTwoMaterialError {
    fn from(error: ValueAggregateRecompositionErrorV5) -> Self {
        Self::Recomposition(error)
    }
}

impl From<ValueAggregateGuestInputErrorV5> for LevelTwoMaterialError {
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
    let children = load_authenticated_level_one_children(&options.child_paths)?;
    let policy = governed_level_one_policy(&children)?;
    let child_proposal_bytes = children
        .iter()
        .map(|child| child.receipt().journal.bytes.clone())
        .collect();
    let material = recompose_exact_level_two(child_proposal_bytes, &policy)
        .map_err(|error| error.to_string())?;
    match options.mode {
        Mode::Prove => prove_and_persist(options, children, material),
        Mode::VerifyExisting => verify_existing(options, children.len(), material),
    }
}

fn prove_and_persist(
    options: Options,
    children: Vec<VerifiedValueAggregateReceiptV5>,
    material: LevelTwoMaterial,
) -> Result<(), String> {
    let verified = prove_and_verify(&children, &material)?;
    let receipt_bytes = canonical_receipt_bytes(verified.receipt())?;
    persist_new_receipt(&options.receipt_path, &receipt_bytes)?;
    report::write_report(
        options.mode,
        &verified,
        children.len(),
        &receipt_bytes,
        true,
    )
}

fn verify_existing(
    options: Options,
    child_count: usize,
    material: LevelTwoMaterial,
) -> Result<(), String> {
    let receipt_bytes = read_bounded_receipt_file(&options.receipt_path)?;
    let verified = verify_exact_root_receipt(&receipt_bytes, &material.expected_proposal)?;
    report::write_report(options.mode, &verified, child_count, &receipt_bytes, false)
}

fn load_authenticated_level_one_children(
    paths: &[PathBuf],
) -> Result<Vec<VerifiedValueAggregateReceiptV5>, String> {
    let expected_identity = expected_level_one_receipt_identity()?;
    paths
        .iter()
        .enumerate()
        .map(|(index, path)| {
            let bytes = read_bounded_receipt_file(path)
                .map_err(|error| format!("L1 child receipt {index}: {error}"))?;
            VerifiedValueAggregateReceiptV5::verify_canonical_succinct_bytes(
                &bytes,
                PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
                expected_identity,
            )
            .map_err(|error| format!("L1 child receipt {index} authentication failed: {error}"))
        })
        .collect()
}

fn expected_level_one_receipt_identity() -> Result<ExpectedValueAggregateReceiptIdentityV5, String>
{
    let identity = pinned_value_aggregate_level_one_identity_v5()
        .map_err(|error| format!("derive governed L1 identity: {error}"))?;
    ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(1).map_err(|error| format!("derive L1 level: {error}"))?,
        identity.expected_profile_id(),
        identity.expected_manifest_root(),
    )
    .map_err(|error| format!("construct governed L1 receipt identity: {error}"))
}

fn expected_level_two_root_receipt_identity(
) -> Result<ExpectedValueAggregateReceiptIdentityV5, String> {
    let identity = pinned_value_aggregate_level_two_root_identity_v5()
        .map_err(|error| format!("derive governed L2 root identity: {error}"))?;
    ExpectedValueAggregateReceiptIdentityV5::new(
        identity.aggregate_level(),
        identity.expected_profile_id(),
        identity.expected_manifest_root(),
    )
    .map_err(|error| format!("construct governed L2 root receipt identity: {error}"))
}

fn governed_level_one_policy(
    children: &[VerifiedValueAggregateReceiptV5],
) -> Result<ValueAggregateRecompositionPolicyV5, String> {
    let first = children
        .first()
        .ok_or_else(|| "V5 L2 aggregate requires at least one authenticated L1 child".to_owned())?;
    let identity = pinned_value_aggregate_level_one_identity_v5()
        .map_err(|error| format!("derive governed L1 identity: {error}"))?;
    ValueAggregateRecompositionPolicyV5::new(
        first.proposal().scope().clone(),
        vec![identity; children.len()],
    )
    .map_err(|error| format!("construct governed L1 child policy: {error}"))
}

fn recompose_exact_level_two(
    child_proposal_bytes: Vec<Vec<u8>>,
    policy: &ValueAggregateRecompositionPolicyV5,
) -> Result<LevelTwoMaterial, LevelTwoMaterialError> {
    let input = ValueAggregateLevelTwoInputV5::new(child_proposal_bytes)?;
    let expected_proposal = recompose_expected_value_aggregate_level_two_v5(&input, policy)?;
    let guest_input_bytes =
        encode_value_aggregate_guest_input_v5(&ValueAggregateGuestInputV5::LevelTwo(input))?;
    Ok(LevelTwoMaterial {
        guest_input_bytes,
        expected_proposal,
    })
}

fn prove_and_verify(
    children: &[VerifiedValueAggregateReceiptV5],
    material: &LevelTwoMaterial,
) -> Result<VerifiedValueAggregateReceiptV5, String> {
    let input_length = u32::try_from(material.guest_input_bytes.len())
        .map_err(|_| "V5 L2 guest input length exceeds u32".to_owned())?;
    let mut builder = ExecutorEnv::builder();
    builder
        .write_slice(&[input_length])
        .write_slice(&material.guest_input_bytes);
    for child in children {
        builder.add_assumption(child.receipt().clone());
    }
    let executor_env = builder
        .build()
        .map_err(|error| format!("V5 L2 executor environment: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L2_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V5 L2 proving failed: {error}"))?
        .receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("V5 L2 prover returned a non-Succinct receipt".to_owned());
    }
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    verify_exact_root_receipt(&receipt_bytes, &material.expected_proposal)
}

fn verify_exact_root_receipt(
    receipt_bytes: &[u8],
    expected_proposal: &ProposedValueAggregateV5,
) -> Result<VerifiedValueAggregateReceiptV5, String> {
    VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        receipt_bytes,
        PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
        expected_level_two_root_receipt_identity()?,
        expected_proposal,
    )
    .map_err(|error| format!("sealed V5 L2 root verification failed: {error}"))
}

fn validate_methods() -> Result<(), String> {
    validate_method(
        "value aggregate L1 V5 child",
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ELF,
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID,
        PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
    )?;
    validate_method(
        "value aggregate L2 V5 root",
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L2_ELF,
        ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L2_ID,
        PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
    )?;
    if PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5 == PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5 {
        return Err("governed L1 and L2 image IDs must differ".to_owned());
    }
    Ok(())
}

fn validate_method(
    name: &str,
    elf: &[u8],
    generated_image_id: [u32; 8],
    governed_image_id: [u32; 8],
) -> Result<(), String> {
    if elf.is_empty() || generated_image_id.iter().all(|word| *word == 0) {
        return Err(format!("{name} method is a placeholder"));
    }
    if generated_image_id != governed_image_id {
        return Err(format!(
            "{name} generated image ID differs from governed policy"
        ));
    }
    let computed =
        compute_image_id(elf).map_err(|error| format!("compute {name} image ID: {error}"))?;
    if computed != Digest::from(generated_image_id) {
        return Err(format!("{name} image ID mismatch"));
    }
    Ok(())
}

#[cfg(test)]
#[path = "prove_value_aggregate_l2_v5/tests.rs"]
mod tests;
