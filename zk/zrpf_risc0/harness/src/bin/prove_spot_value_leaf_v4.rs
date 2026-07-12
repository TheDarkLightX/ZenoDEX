use std::{env, ffi::OsStr, path::Path, path::PathBuf};

use risc0_zkvm::{compute_image_id, default_prover, Digest, ExecutorEnv, ProverOpts};
use zenodex_zrpf_protocol_v3::NodeJournalV4;
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF, ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID,
};
use zenodex_zrpf_risc0_semantic_shared::{SpotRepresentedValuePolicyV1, SpotValueLeafOpeningV1};
use zenodex_zrpf_risc0_shared::{project_policy_bound_v1_journal, SourceKindV1};
use zenodex_zrpf_risc0_value_node_shared::{
    encode_raw_spot_value_leaf_input_v4, encode_spot_value_leaf_witness_v4,
    propose_spot_value_leaf_v4, RawSpotValueLeafInputV4, SpotValueLeafWitnessV4,
    PINNED_V1_ADAPTER_IMAGE_ID_A,
};
use zenodex_zrpf_risc0_verifier::historical_spot_value_leaf_v4::{
    ExactSpotValueLeafReceiptV4, VerifiedSpotValueLeafReceiptErrorV4,
};
use zenodex_zrpf_risc0_verifier::VerifiedNodeReceiptV3;

#[path = "prove_spot_value_leaf_v4/artifact_io.rs"]
mod artifact_io;
#[path = "prove_spot_value_leaf_v4/report.rs"]
mod report;
#[path = "prove_spot_value_leaf_v4/source.rs"]
mod source;
#[cfg(test)]
#[path = "prove_spot_value_leaf_v4/tests.rs"]
mod tests;

use artifact_io::{
    canonical_receipt_bytes, persist_receipt, read_bounded_regular_file, require_succinct,
    sha256_hex,
};
use report::{print_report, ReportInput};
use source::{load_verified_source, VerifiedSource};

const ASSIGNED_LEAF_ORDINAL: u64 = 0;
const RETAINED_ADAPTER_RECEIPT_BYTES: usize = 593_192;
const RETAINED_ADAPTER_RECEIPT_SHA256: &str =
    "67d792e018f94c354dc55184d562edb490e7c4262795ea69f9a747ce231b8ae9";
const RETAINED_ADAPTER_JOURNAL_BYTES: usize = 1_547;
const RETAINED_ADAPTER_JOURNAL_SHA256: &str =
    "0b145b1bee53123458a3eab3568a11ebf01910e76034e5001ec8b27a247c6d5a";
const RETAINED_SEMANTIC_OPENING: [u8; 32] = [
    0x07, 0x7b, 0x98, 0xb1, 0x01, 0xcc, 0xaa, 0xa2, 0x6b, 0xc6, 0x0c, 0x55, 0xf4, 0x04, 0xeb, 0x45,
    0x52, 0x9c, 0xf8, 0xe3, 0x3f, 0x88, 0x1e, 0xe3, 0x40, 0xc8, 0x93, 0x1e, 0x9c, 0x66, 0xb0, 0xc0,
];
const EXPECTED_V4_GUEST_ELF_BYTES: usize = 467_680;
const EXPECTED_V4_GUEST_ELF_SHA256: &str =
    "6b0452db9c8f2adf6d82dc37884830f289ff3811e083c276e2ad0bda45d6babd";
const EXPECTED_V4_IMAGE_ID: [u32; 8] = [
    3_473_282_264,
    1_999_634_215,
    547_286_378,
    2_333_271_038,
    3_834_090_373,
    2_085_707_079,
    2_388_587_125,
    1_886_015_318,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Prove,
    Verify,
}

struct Options {
    mode: Mode,
    receipt_path: PathBuf,
    source_path: PathBuf,
    adapter_path: PathBuf,
}

struct VerifiedAdapter {
    receipt: VerifiedNodeReceiptV3,
    semantic_opening: [u8; 32],
    receipt_sha256: String,
}

struct PreparedLeaf {
    input_bytes: Vec<u8>,
    expected_journal: NodeJournalV4,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    reject_ambient_dev_mode()?;
    let options = parse_options(env::args().skip(1))?;
    let guest_artifact_loaded_and_matched = match options.mode {
        Mode::Prove => {
            validate_value_leaf_method()?;
            true
        }
        Mode::Verify => false,
    };
    let source = load_verified_source(&options.source_path)?;
    let adapter = load_exact_adapter(&options.adapter_path, &source)?;
    let prepared = prepare_leaf(&source, &adapter)?;

    let (verified, receipt_bytes, receipt_written, status) = match options.mode {
        Mode::Prove => {
            let verified = prove_exact_leaf(&prepared, &adapter)?;
            let receipt_bytes = canonical_receipt_bytes(verified.authenticated().receipt())?;
            persist_receipt(&options.receipt_path, &receipt_bytes)?;
            (
                verified,
                receipt_bytes,
                true,
                "temporary_path_v4_spot_value_leaf_succinct_receipt_verified",
            )
        }
        Mode::Verify => {
            let receipt_bytes = read_bounded_regular_file(&options.receipt_path, "V4 receipt")?;
            let receipt_sha256 = sha256_hex(&receipt_bytes);
            let verified = ExactSpotValueLeafReceiptV4::verify_exact_succinct_bytes(
                &receipt_bytes,
                EXPECTED_V4_IMAGE_ID,
                &prepared.expected_journal,
            )
            .map_err(|error| receipt_reject_json(&receipt_sha256, error))?;
            (
                verified,
                receipt_bytes,
                false,
                "persisted_v4_spot_value_leaf_succinct_receipt_verified",
            )
        }
    };

    print_report(ReportInput {
        source: &source,
        adapter: &adapter,
        prepared: &prepared,
        verified: &verified,
        receipt_bytes: &receipt_bytes,
        receipt_written,
        guest_artifact_loaded_and_matched,
        status,
    })
}

fn reject_ambient_dev_mode() -> Result<(), String> {
    let value = env::var_os("RISC0_DEV_MODE");
    if !ambient_dev_mode_is_forbidden(value.as_deref()) {
        return Ok(());
    }
    Err(ambient_dev_mode_reject_json())
}

fn ambient_dev_mode_is_forbidden(value: Option<&OsStr>) -> bool {
    value.is_some()
}

fn ambient_dev_mode_reject_json() -> String {
    serde_json::json!({
        "candidate_accepted": false,
        "ok": false,
        "reject": {
            "boundary": "prove_spot_value_leaf_v4_process_start",
            "code": "ambient_risc0_dev_mode_forbidden",
            "variable": "RISC0_DEV_MODE",
        },
        "schema": "zenodex/zrpf_spot_value_leaf_v4_environment_reject/v1",
        "status": "ambient_dev_mode_environment_rejected",
    })
    .to_string()
}

fn receipt_reject_json(receipt_sha256: &str, error: VerifiedSpotValueLeafReceiptErrorV4) -> String {
    let code = match error {
        VerifiedSpotValueLeafReceiptErrorV4::ReceiptArtifact(inner) => inner.code(),
        _ => error.code(),
    };
    serde_json::json!({
        "candidate_accepted": false,
        "ok": false,
        "receipt_sha256": receipt_sha256,
        "reject": {
            "boundary": "ExactSpotValueLeafReceiptV4::verify_exact_succinct_bytes",
            "code": code,
            "outer_code": error.code(),
            "variant": format!("{error:?}"),
        },
        "schema": "zenodex/zrpf_spot_value_leaf_v4_receipt_reject/v1",
        "status": "persisted_v4_spot_value_leaf_receipt_rejected",
    })
    .to_string()
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args: Vec<String> = args.into_iter().collect();
    if args.len() != 6 {
        return Err(usage().to_owned());
    }
    let mode = match args[0].as_str() {
        "--receipt-out" => Mode::Prove,
        "--verify-receipt" => Mode::Verify,
        _ => return Err(usage().to_owned()),
    };
    if !valid_path_token(&args[1])
        || args[2] != "--source-proof"
        || !valid_path_token(&args[3])
        || args[4] != "--adapter-receipt"
        || !valid_path_token(&args[5])
    {
        return Err(usage().to_owned());
    }
    Ok(Options {
        mode,
        receipt_path: PathBuf::from(&args[1]),
        source_path: PathBuf::from(&args[3]),
        adapter_path: PathBuf::from(&args[5]),
    })
}

fn valid_path_token(value: &str) -> bool {
    !value.is_empty() && !value.starts_with("--")
}

fn usage() -> &'static str {
    "usage: prove_spot_value_leaf_v4 (--receipt-out <v4.receipt.json>|--verify-receipt <v4.receipt.json>) --source-proof <retained-ordinal-0-spot-v1-proof.json> --adapter-receipt <retained-ordinal-0-adapter.receipt.json>"
}

fn validate_value_leaf_method() -> Result<(), String> {
    if ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF.is_empty()
        || ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID
            .iter()
            .all(|word| *word == 0)
    {
        return Err("V4 Spot value-leaf method is a placeholder".to_owned());
    }
    if ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF.len() != EXPECTED_V4_GUEST_ELF_BYTES
        || sha256_hex(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF) != EXPECTED_V4_GUEST_ELF_SHA256
        || ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID != EXPECTED_V4_IMAGE_ID
    {
        return Err("V4 Spot value-leaf method differs from the reviewed local image".to_owned());
    }
    let computed = compute_image_id(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF)
        .map_err(|error| format!("compute V4 Spot value-leaf image ID: {error}"))?;
    if computed != Digest::from(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID) {
        return Err("V4 Spot value-leaf method image ID mismatch".to_owned());
    }
    Ok(())
}

fn load_exact_adapter(path: &Path, source: &VerifiedSource) -> Result<VerifiedAdapter, String> {
    let expected = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        &source.receipt.journal.bytes,
        ASSIGNED_LEAF_ORDINAL,
        PINNED_V1_ADAPTER_IMAGE_ID_A,
    )
    .map_err(|error| format!("adapter host projection rejected: {error}"))?;
    let receipt_bytes = read_bounded_regular_file(path, "adapter receipt")?;
    if receipt_bytes.len() != RETAINED_ADAPTER_RECEIPT_BYTES
        || sha256_hex(&receipt_bytes) != RETAINED_ADAPTER_RECEIPT_SHA256
    {
        return Err("adapter receipt differs from retained ordinal-zero receipt".to_owned());
    }
    let receipt = VerifiedNodeReceiptV3::verify_exact_succinct_bytes(
        &receipt_bytes,
        PINNED_V1_ADAPTER_IMAGE_ID_A,
        &expected.journal,
    )
    .map_err(|error| format!("exact adapter receipt verification failed: {error}"))?;
    let semantic_opening = expected
        .source_binding
        .canonical_hash()
        .map_err(|error| format!("semantic source opening derivation failed: {error}"))?
        .into_bytes();
    if semantic_opening != RETAINED_SEMANTIC_OPENING
        || receipt.receipt().journal.bytes.len() != RETAINED_ADAPTER_JOURNAL_BYTES
        || sha256_hex(&receipt.receipt().journal.bytes) != RETAINED_ADAPTER_JOURNAL_SHA256
    {
        return Err("adapter receipt differs from the reviewed semantic opening".to_owned());
    }
    Ok(VerifiedAdapter {
        receipt,
        semantic_opening,
        receipt_sha256: sha256_hex(&receipt_bytes),
    })
}

fn prepare_leaf(
    source: &VerifiedSource,
    adapter: &VerifiedAdapter,
) -> Result<PreparedLeaf, String> {
    let opening = SpotValueLeafOpeningV1::new(
        source.summary.lane_id.clone(),
        source.summary.pre_state_root,
        source.summary.post_state_root,
        source.asset_rows.clone(),
    )
    .map_err(|error| format!("Spot value opening rejected: {error}"))?;
    let policy = SpotRepresentedValuePolicyV1::new(source.summary.public_policy_hash, vec![])
        .map_err(|error| format!("Spot value policy rejected: {error}"))?;
    let witness = SpotValueLeafWitnessV4::new(adapter.semantic_opening, opening, policy)
        .map_err(|error| format!("V4 witness rejected: {error}"))?;
    let witness_bytes = encode_spot_value_leaf_witness_v4(&witness)
        .map_err(|error| format!("V4 witness encode failed: {error}"))?;
    let input = RawSpotValueLeafInputV4::new(
        EXPECTED_V4_IMAGE_ID,
        adapter.receipt.receipt().journal.bytes.clone(),
        witness_bytes,
    )
    .map_err(|error| format!("V4 raw input rejected: {error}"))?;
    let expected_journal = propose_spot_value_leaf_v4(&input)
        .map_err(|error| format!("V4 host proposal rejected: {error}"))?;
    let input_bytes = encode_raw_spot_value_leaf_input_v4(&input)
        .map_err(|error| format!("V4 input encode failed: {error}"))?;
    Ok(PreparedLeaf {
        input_bytes,
        expected_journal,
    })
}

fn prove_exact_leaf(
    prepared: &PreparedLeaf,
    adapter: &VerifiedAdapter,
) -> Result<ExactSpotValueLeafReceiptV4, String> {
    let input_length =
        u32::try_from(prepared.input_bytes.len()).map_err(|_| "V4 input length exceeds u32")?;
    let executor_env = ExecutorEnv::builder()
        .write_slice(&[input_length])
        .write_slice(&prepared.input_bytes)
        .add_assumption(adapter.receipt.receipt().clone())
        .build()
        .map_err(|error| format!("V4 executor environment rejected: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V4 Spot value-leaf proving failed: {error}"))?
        .receipt;
    require_succinct(&receipt, "V4 Spot value leaf")?;
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    ExactSpotValueLeafReceiptV4::verify_exact_succinct_bytes(
        &receipt_bytes,
        EXPECTED_V4_IMAGE_ID,
        &prepared.expected_journal,
    )
    .map_err(|error| format!("fresh V4 receipt verification failed: {error}"))
}
