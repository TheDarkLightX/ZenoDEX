use std::path::Path;

use risc0_zkvm::{default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};
use serde_json::Value;
use sha2::{Digest as _, Sha256};
use zenodex_zrpf_protocol_v3::{NodeLevelV3, ProposedValueAggregateV5};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_value_aggregate_l2_policy::{
    pinned_value_aggregate_level_one_identity_v5, PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
};
use zenodex_zrpf_risc0_value_aggregate_root_policy::{
    pinned_value_aggregate_level_two_root_identity_v5, PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    encode_value_aggregate_guest_input_v5, recompose_expected_value_aggregate_level_one_v5,
    recompose_expected_value_aggregate_level_two_v5, GovernedValueChildIdentityV5,
    ValueAggregateGuestInputV5, ValueAggregateLevelOneInputV5, ValueAggregateLevelTwoInputV5,
    ValueAggregateRecompositionPolicyV5,
};
use zenodex_zrpf_risc0_value_node_shared::{
    spot_value_leaf_manifest_root_v4, spot_value_leaf_profile_id_v4, PINNED_V1_ADAPTER_IMAGE_ID_A,
};
use zenodex_zrpf_risc0_verifier::{
    historical_spot_value_leaf_v4::AuthenticatedSpotValueLeafReceiptV4,
    ExpectedValueAggregateReceiptIdentityV5, VerifiedValueAggregateReceiptV5,
};

#[path = "prove_retained_value_aggregate_v5/artifact_io.rs"]
mod artifact_io;
#[path = "prove_retained_value_aggregate_v5/cli.rs"]
mod cli;
#[path = "prove_retained_value_aggregate_v5/report.rs"]
mod report;

use artifact_io::{
    canonical_receipt_bytes, persist_bundle, read_receipt_once, BoundProgram, PersistedBundle,
};
use cli::{Mode, Options};

const GOVERNED_BUILD_RECORD_BYTES: &[u8] = include_bytes!(
    "../../../../../docs/research/ZRPF_VALUE_AGGREGATE_V5_PROGRAM_BUILD_RECORD_20260712.json"
);
const GOVERNED_BUILD_RECORD_SHA256: &str =
    "8f406f81ab6ee9c9db8ed324fd4b7c5c4532d0b6a3db407800e44665cd3725fc";
const BUILD_RECORD_SCHEMA: &str = "zenodex/zrpf_value_aggregate_v5_program_build_record/v2";
const BUILD_RECORD_PROFILE: &str = "experimental_bounded_value_aggregate_v5";

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProgramSpec {
    label: &'static str,
    size_bytes: usize,
    sha256: [u8; 32],
    image_id: [u32; 8],
}

struct GovernedPrograms {
    child: ProgramSpec,
    level_one: ProgramSpec,
    level_two: ProgramSpec,
}

struct LevelMaterial {
    guest_input_bytes: Vec<u8>,
    expected_proposal: ProposedValueAggregateV5,
}

struct ProvedReceipts {
    level_one: VerifiedValueAggregateReceiptV5,
    level_two: VerifiedValueAggregateReceiptV5,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    require_retained_host_feature_closure()?;
    reject_ambient_prover_authority()?;
    let options = cli::process_options()?;
    let governed = governed_programs_from_record(GOVERNED_BUILD_RECORD_BYTES)?;
    let level_one_program =
        BoundProgram::load_once(&options.level_one_program, &governed.level_one)?;
    let level_two_program =
        BoundProgram::load_once(&options.level_two_program, &governed.level_two)?;
    require_distinct_programs(&level_one_program, &level_two_program)?;
    let child = load_authenticated_child(&options.child_receipt, &governed.child)?;

    match options.mode {
        Mode::Preflight => report::write_report(report_input(options.mode, &governed, None, None)),
        Mode::Prove => prove_persist_and_report(
            options,
            governed,
            child,
            level_one_program,
            level_two_program,
        ),
    }
}

fn prove_persist_and_report(
    options: Options,
    governed: GovernedPrograms,
    child: AuthenticatedSpotValueLeafReceiptV4,
    level_one_program: BoundProgram,
    level_two_program: BoundProgram,
) -> Result<(), String> {
    let proved = prove_receipt_pair(&governed, &child, &level_one_program, &level_two_program)?;
    let bundle = report::encode_receipt_bundle(&proved)?;
    let persisted = persist_bundle(
        options
            .bundle_out
            .as_deref()
            .ok_or_else(|| "prove mode requires a bundle output".to_owned())?,
        bundle.bytes(),
    )?;
    report::write_report(report_input(
        options.mode,
        &governed,
        Some(&bundle),
        Some(&persisted),
    ))
}

fn prove_receipt_pair(
    governed: &GovernedPrograms,
    child: &AuthenticatedSpotValueLeafReceiptV4,
    level_one_program: &BoundProgram,
    level_two_program: &BoundProgram,
) -> Result<ProvedReceipts, String> {
    let level_one_material = level_one_material(child, &governed.child)?;
    let level_one = prove_level_one(level_one_program, child, &level_one_material)?;
    let level_two_material = level_two_material(&level_one)?;
    let level_two = prove_level_two(level_two_program, &level_one, &level_two_material)?;
    Ok(ProvedReceipts {
        level_one,
        level_two,
    })
}

fn load_authenticated_child(
    path: &Path,
    spec: &ProgramSpec,
) -> Result<AuthenticatedSpotValueLeafReceiptV4, String> {
    let bytes = read_receipt_once(path, "V4 child receipt")?;
    AuthenticatedSpotValueLeafReceiptV4::verify_canonical_succinct_bytes(&bytes, spec.image_id)
        .map_err(|error| format!("V4 child receipt authentication failed: {error}"))
}

fn level_one_material(
    child: &AuthenticatedSpotValueLeafReceiptV4,
    child_spec: &ProgramSpec,
) -> Result<LevelMaterial, String> {
    let child_program_id = program_id_from_risc0_words_v3(child_spec.image_id)
        .map_err(|error| format!("derive V4 child program: {error}"))?;
    let adapter_program_id = program_id_from_risc0_words_v3(PINNED_V1_ADAPTER_IMAGE_ID_A)
        .map_err(|error| format!("derive V1 adapter program: {error}"))?;
    let child_identity = GovernedValueChildIdentityV5::new(
        child_spec.image_id,
        child_program_id,
        spot_value_leaf_profile_id_v4()
            .map_err(|error| format!("derive V4 child profile: {error}"))?,
        spot_value_leaf_manifest_root_v4(child_program_id, adapter_program_id)
            .map_err(|error| format!("derive V4 child manifest: {error}"))?,
    )
    .map_err(|error| format!("construct governed V4 child identity: {error}"))?;
    let input = ValueAggregateLevelOneInputV5::new(vec![child.receipt().journal.bytes.clone()])
        .map_err(|error| format!("construct V5 L1 input: {error}"))?;
    let policy = ValueAggregateRecompositionPolicyV5::new(
        child.journal().structural().scope().clone(),
        vec![child_identity],
    )
    .map_err(|error| format!("construct V5 L1 policy: {error}"))?;
    let expected_proposal = recompose_expected_value_aggregate_level_one_v5(&input, &policy)
        .map_err(|error| format!("recompose V5 L1 proposal: {error}"))?;
    let guest_input_bytes =
        encode_value_aggregate_guest_input_v5(&ValueAggregateGuestInputV5::LevelOne(input))
            .map_err(|error| format!("encode V5 L1 guest input: {error}"))?;
    Ok(LevelMaterial {
        guest_input_bytes,
        expected_proposal,
    })
}

fn level_two_material(child: &VerifiedValueAggregateReceiptV5) -> Result<LevelMaterial, String> {
    let input = ValueAggregateLevelTwoInputV5::new(vec![child.receipt().journal.bytes.clone()])
        .map_err(|error| format!("construct V5 L2 input: {error}"))?;
    let identity = pinned_value_aggregate_level_one_identity_v5()
        .map_err(|error| format!("derive governed V5 L1 identity: {error}"))?;
    let policy =
        ValueAggregateRecompositionPolicyV5::new(child.proposal().scope().clone(), vec![identity])
            .map_err(|error| format!("construct V5 L2 policy: {error}"))?;
    let expected_proposal = recompose_expected_value_aggregate_level_two_v5(&input, &policy)
        .map_err(|error| format!("recompose V5 L2 proposal: {error}"))?;
    let guest_input_bytes =
        encode_value_aggregate_guest_input_v5(&ValueAggregateGuestInputV5::LevelTwo(input))
            .map_err(|error| format!("encode V5 L2 guest input: {error}"))?;
    Ok(LevelMaterial {
        guest_input_bytes,
        expected_proposal,
    })
}

fn prove_level_one(
    program: &BoundProgram,
    child: &AuthenticatedSpotValueLeafReceiptV4,
    material: &LevelMaterial,
) -> Result<VerifiedValueAggregateReceiptV5, String> {
    let receipt = prove_succinct(
        program,
        material,
        [child.receipt().clone()].into_iter(),
        "V5 L1",
    )?;
    let bytes = canonical_receipt_bytes(&receipt)?;
    VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &bytes,
        PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
        expected_level_one_identity()?,
        &material.expected_proposal,
    )
    .map_err(|error| format!("sealed V5 L1 verification failed: {error}"))
}

fn prove_level_two(
    program: &BoundProgram,
    child: &VerifiedValueAggregateReceiptV5,
    material: &LevelMaterial,
) -> Result<VerifiedValueAggregateReceiptV5, String> {
    let receipt = prove_succinct(
        program,
        material,
        [child.receipt().clone()].into_iter(),
        "V5 L2",
    )?;
    let bytes = canonical_receipt_bytes(&receipt)?;
    VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes(
        &bytes,
        PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
        expected_level_two_identity()?,
        &material.expected_proposal,
    )
    .map_err(|error| format!("sealed V5 L2 verification failed: {error}"))
}

fn prove_succinct(
    program: &BoundProgram,
    material: &LevelMaterial,
    assumptions: impl Iterator<Item = Receipt>,
    label: &str,
) -> Result<Receipt, String> {
    let input_length = u32::try_from(material.guest_input_bytes.len())
        .map_err(|_| format!("{label} guest input length exceeds u32"))?;
    let mut builder = ExecutorEnv::builder();
    builder
        .write_slice(&[input_length])
        .write_slice(&material.guest_input_bytes);
    for assumption in assumptions {
        builder.add_assumption(assumption);
    }
    let environment = builder
        .build()
        .map_err(|error| format!("{label} executor environment: {error}"))?;
    let prover = default_prover();
    require_sdk_ipc_prover(&prover.get_name(), label)?;
    let receipt = prover
        .prove_with_opts(environment, program.bytes(), &ProverOpts::succinct())
        .map_err(|error| format!("{label} proving failed: {error}"))?
        .receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(format!("{label} prover returned a non-Succinct receipt"));
    }
    Ok(receipt)
}

fn require_sdk_ipc_prover(name: &str, label: &str) -> Result<(), String> {
    if name != "ipc" {
        return Err(format!("{label} requires the SDK-selected IPC prover"));
    }
    Ok(())
}

fn expected_level_one_identity() -> Result<ExpectedValueAggregateReceiptIdentityV5, String> {
    let identity = pinned_value_aggregate_level_one_identity_v5()
        .map_err(|error| format!("derive V5 L1 identity: {error}"))?;
    ExpectedValueAggregateReceiptIdentityV5::new(
        NodeLevelV3::new(1).map_err(|error| format!("derive V5 L1 level: {error}"))?,
        identity.expected_profile_id(),
        identity.expected_manifest_root(),
    )
    .map_err(|error| format!("construct V5 L1 receipt identity: {error}"))
}

fn expected_level_two_identity() -> Result<ExpectedValueAggregateReceiptIdentityV5, String> {
    let identity = pinned_value_aggregate_level_two_root_identity_v5()
        .map_err(|error| format!("derive V5 L2 identity: {error}"))?;
    ExpectedValueAggregateReceiptIdentityV5::new(
        identity.aggregate_level(),
        identity.expected_profile_id(),
        identity.expected_manifest_root(),
    )
    .map_err(|error| format!("construct V5 L2 receipt identity: {error}"))
}

fn governed_programs_from_record(raw: &[u8]) -> Result<GovernedPrograms, String> {
    if hex::encode(Sha256::digest(raw)) != GOVERNED_BUILD_RECORD_SHA256 {
        return Err("embedded V5 build record differs from governed SHA-256".to_owned());
    }
    let record: Value = serde_json::from_slice(raw)
        .map_err(|error| format!("decode governed V5 build record: {error}"))?;
    require_string(&record, "schema", BUILD_RECORD_SCHEMA)?;
    require_string(&record, "profile", BUILD_RECORD_PROFILE)?;
    let child = program_spec(&record, "spot_value_leaf_v4", "Spot value leaf V4 child")?;
    let level_one = program_spec(&record, "level_one", "value aggregate L1 V5")?;
    let level_two = program_spec(&record, "level_two", "value aggregate L2 V5")?;
    if level_one.image_id != PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5 {
        return Err("V5 build record L1 image differs from governed policy".to_owned());
    }
    if level_two.image_id != PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5 {
        return Err("V5 build record L2 image differs from governed policy".to_owned());
    }
    if string_field(section(&record, "level_two")?, "pinned_level_one_image_id")?
        != digest_hex(level_one.image_id)
    {
        return Err("V5 build record L2 child pin differs from governed L1".to_owned());
    }
    require_false_authority_claims(&record)?;
    Ok(GovernedPrograms {
        child,
        level_one,
        level_two,
    })
}

fn program_spec(record: &Value, field: &str, label: &'static str) -> Result<ProgramSpec, String> {
    let value = section(record, field)?;
    let size_bytes = usize::try_from(
        value
            .get("combined_program_binary_bytes")
            .and_then(Value::as_u64)
            .ok_or_else(|| format!("V5 build record {field} byte length missing"))?,
    )
    .map_err(|_| format!("V5 build record {field} byte length unsupported"))?;
    let sha256 = parse_hex_32(string_field(value, "combined_program_binary_sha256")?)?;
    let image_id = parse_image_words(value.get("image_id_words_le"), field)?;
    if string_field(value, "image_id_hex")? != digest_hex(image_id) {
        return Err(format!("V5 build record {field} image encoding mismatch"));
    }
    Ok(ProgramSpec {
        label,
        size_bytes,
        sha256,
        image_id,
    })
}

fn section<'a>(record: &'a Value, field: &str) -> Result<&'a Value, String> {
    record
        .get(field)
        .filter(|value| value.is_object())
        .ok_or_else(|| format!("V5 build record {field} section missing"))
}

fn string_field<'a>(value: &'a Value, field: &str) -> Result<&'a str, String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("V5 build record {field} missing"))
}

fn require_string(record: &Value, field: &str, expected: &str) -> Result<(), String> {
    if string_field(record, field)? != expected {
        return Err(format!("V5 build record {field} mismatch"));
    }
    Ok(())
}

fn parse_image_words(value: Option<&Value>, field: &str) -> Result<[u32; 8], String> {
    let words = value
        .and_then(Value::as_array)
        .filter(|words| words.len() == 8)
        .ok_or_else(|| format!("V5 build record {field} image words missing"))?;
    let parsed = words
        .iter()
        .map(|word| {
            word.as_u64()
                .and_then(|value| u32::try_from(value).ok())
                .ok_or_else(|| format!("V5 build record {field} image word unsupported"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    parsed
        .try_into()
        .map_err(|_| format!("V5 build record {field} image word count mismatch"))
}

fn parse_hex_32(value: &str) -> Result<[u8; 32], String> {
    let bytes = hex::decode(value).map_err(|_| "V5 build record digest is not hex".to_owned())?;
    bytes
        .try_into()
        .map_err(|_| "V5 build record digest length mismatch".to_owned())
}

fn digest_hex(words: [u32; 8]) -> String {
    Digest::from(words).to_string()
}

fn require_false_authority_claims(record: &Value) -> Result<(), String> {
    let claims = section(record, "claims")?;
    for field in [
        "cross_host_reproducible_build",
        "level_one_receipt_generated",
        "level_two_receipt_generated",
        "settlement_semantics_verified",
        "durable_atomic_admission_verified",
        "release_authority",
        "settlement_authority",
        "production_authority",
    ] {
        if claims.get(field) != Some(&Value::Bool(false)) {
            return Err(format!("V5 build record {field} must remain false"));
        }
    }
    Ok(())
}

fn require_distinct_programs(
    level_one: &BoundProgram,
    level_two: &BoundProgram,
) -> Result<(), String> {
    if level_one.image_id() == level_two.image_id() || level_one.sha256() == level_two.sha256() {
        return Err("governed V5 L1 and L2 programs must differ".to_owned());
    }
    Ok(())
}

fn reject_ambient_prover_authority() -> Result<(), String> {
    for field in [
        "RISC0_DEV_MODE",
        "RISC0_PROVER",
        "BONSAI_API_URL",
        "BONSAI_API_KEY",
    ] {
        if std::env::var_os(field).is_some() {
            return Err(format!(
                "{field} must be absent for retained V5 SDK IPC proving"
            ));
        }
    }
    Ok(())
}

fn require_retained_host_feature_closure() -> Result<(), String> {
    if cfg!(feature = "legacy-methods") || cfg!(feature = "spot-v6-methods") {
        return Err(
            "retained V5 proving requires both method-build features to be disabled".to_owned(),
        );
    }
    Ok(())
}

fn report_input<'a>(
    mode: Mode,
    governed: &'a GovernedPrograms,
    bundle: Option<&'a report::EncodedReceiptBundle>,
    persisted: Option<&'a PersistedBundle>,
) -> report::ReportInput<'a> {
    report::ReportInput {
        mode,
        build_record_sha256: GOVERNED_BUILD_RECORD_SHA256,
        child: &governed.child,
        level_one: &governed.level_one,
        level_two: &governed.level_two,
        bundle,
        persisted,
    }
}

#[cfg(test)]
#[path = "prove_retained_value_aggregate_v5/tests.rs"]
mod tests;
