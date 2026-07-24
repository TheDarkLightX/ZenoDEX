use std::{env, path::PathBuf};

use risc0_zkvm::{compute_image_id, default_prover, Digest, ProverOpts};
use zenodex_zrpf_protocol_v3::NodeLevelV3;
use zenodex_zrpf_risc0_execution_profile::build_exact_framed_executor_env_v1;
use zenodex_zrpf_risc0_spot_v6_methods::{
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ELF,
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID, ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF,
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID,
};
use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::{
    pinned_source_opened_spot_value_leaf_identity_v6,
    source_opened_spot_value_aggregate_l1_manifest_root_v6,
    source_opened_spot_value_aggregate_l1_profile_id_v6,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    encode_value_aggregate_guest_input_v5,
    recompose_expected_source_opened_spot_value_aggregate_level_one_v6, ValueAggregateGuestInputV5,
    ValueAggregateLevelOneInputV5, ValueAggregateRecompositionPolicyV5,
};
use zenodex_zrpf_risc0_verifier::{
    ExpectedValueAggregateReceiptIdentityV5, VerifiedSourceOpenedSpotValueLeafReceiptV6,
    VerifiedValueAggregateReceiptV5,
};

#[path = "prove_spot_value_leaf_v4/artifact_io.rs"]
mod artifact_io;

use artifact_io::{
    canonical_receipt_bytes, persist_receipt, read_bounded_regular_file, require_succinct,
    sha256_hex,
};

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
    let (receipt_out, child_path) = parse_options(env::args().skip(1))?;
    validate_method(
        "V6 leaf",
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF,
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID,
    )?;
    validate_method(
        "V6 L1",
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ELF,
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID,
    )?;
    let child_bytes = read_bounded_regular_file(&child_path, "V6 leaf receipt")?;
    let child =
        VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_canonical_succinct_bytes(
            &child_bytes,
        )
        .map_err(|error| format!("V6 leaf verification failed: {error}"))?;
    let input = ValueAggregateLevelOneInputV5::new(vec![child.receipt().journal.bytes.clone()])
        .map_err(|error| format!("V6 L1 input rejected: {error}"))?;
    let policy = ValueAggregateRecompositionPolicyV5::new(
        child
            .statement()
            .structural_adapter_journal()
            .scope()
            .clone(),
        vec![pinned_source_opened_spot_value_leaf_identity_v6()
            .map_err(|error| format!("V6 leaf policy rejected: {error}"))?],
    )
    .map_err(|error| format!("V6 L1 policy rejected: {error}"))?;
    let expected =
        recompose_expected_source_opened_spot_value_aggregate_level_one_v6(&input, &policy)
            .map_err(|error| format!("V6 L1 recomposition rejected: {error}"))?;
    let guest_input = encode_value_aggregate_guest_input_v5(
        &ValueAggregateGuestInputV5::LevelOneSourceOpenedSpotV6(input),
    )
    .map_err(|error| format!("V6 L1 input encoding failed: {error}"))?;
    let executor_env =
        build_exact_framed_executor_env_v1(&guest_input, std::slice::from_ref(child.receipt()))
            .map_err(|error| format!("V6 L1 executor environment rejected: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V6 L1 proving failed: {error}"))?
        .receipt;
    require_succinct(&receipt, "V6 L1")?;
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    let program_id = zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3(
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID,
    )
    .map_err(|error| format!("derive V6 L1 program ID: {error}"))?;
    let expected_identity = ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(1).map_err(|error| format!("derive V6 L1 level: {error}"))?,
        source_opened_spot_value_aggregate_l1_profile_id_v6()
            .map_err(|error| format!("derive V6 L1 profile: {error}"))?,
        source_opened_spot_value_aggregate_l1_manifest_root_v6(program_id)
            .map_err(|error| format!("derive V6 L1 manifest: {error}"))?,
    )
    .map_err(|error| format!("construct V6 L1 identity: {error}"))?;
    let verified = VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &receipt_bytes,
        ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID,
        expected_identity,
        &expected,
    )
    .map_err(|error| format!("sealed V6 L1 verification failed: {error}"))?;
    persist_receipt(&receipt_out, &receipt_bytes)?;
    println!(
        "{}",
        serde_json::to_string(&serde_json::json!({
            "child_receipt_sha256": sha256_hex(&child_bytes),
            "image_id": Digest::from(ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID).to_string(),
            "ok": true,
            "receipt_bytes": receipt_bytes.len(),
            "receipt_sha256": sha256_hex(&receipt_bytes),
            "schema": "zenodex/zrpf_source_opened_spot_value_aggregate_l1_v6_proof_report/v1",
            "status": "source_opened_spot_value_aggregate_l1_v6_succinct_receipt_verified",
            "verified_child_count": verified.proposal().children().len(),
        }))
        .map_err(|error| format!("V6 L1 report encode: {error}"))?
    );
    Ok(())
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<(PathBuf, PathBuf), String> {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.len() != 4
        || args[0] != "--receipt-out"
        || args[2] != "--child"
        || args[1].is_empty()
        || args[3].is_empty()
    {
        return Err(
            "usage: prove_spot_value_aggregate_l1_v6 --receipt-out <l1.receipt.json> --child <v6-leaf.receipt.json>"
                .to_owned(),
        );
    }
    Ok((PathBuf::from(&args[1]), PathBuf::from(&args[3])))
}

fn validate_method(name: &str, elf: &[u8], image_id: [u32; 8]) -> Result<(), String> {
    if elf.is_empty() || image_id.iter().all(|word| *word == 0) {
        return Err(format!("{name} method is a placeholder"));
    }
    let computed = compute_image_id(elf).map_err(|error| format!("compute {name}: {error}"))?;
    if computed != Digest::from(image_id) {
        return Err(format!("{name} image ID mismatch"));
    }
    Ok(())
}
