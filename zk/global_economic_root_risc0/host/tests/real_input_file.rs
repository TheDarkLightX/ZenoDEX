//! File-driven isolated qualification of the unchanged ROOT guest and journal.
//! Input files and successful receipts supply no signer or publication authority.

#[path = "../../test_support/mod.rs"]
mod support;

use std::{io::Read, path::Path};

use risc0_zkvm::Receipt;
use zenodex_global_economic_epoch_risc0_shared::{
    canonical_json_bytes_v1, GlobalEconomicRecursiveGuestInputV1,
};
use zenodex_global_economic_root_risc0_host::{
    economic_root_image_root_v1, prove_economic_root_succinct_v1, verify_economic_root_receipt_v1,
};
use zenodex_global_economic_root_risc0_methods::{
    ZENODEX_ECONOMIC_ROOT_GUEST_ELF, ZENODEX_ECONOMIC_ROOT_GUEST_ID,
};
use zenodex_global_economic_root_risc0_shared::{
    canonical_root_input_bytes_v1, prepare_root_input_v1, RootGuestInputV1,
};

const MAX_QUALIFICATION_FILE_BYTES: u64 = 32 * 1024 * 1024;

fn bounded_read(path: impl AsRef<Path>) -> Vec<u8> {
    let mut bytes = Vec::new();
    std::fs::File::open(path)
        .unwrap()
        .take(MAX_QUALIFICATION_FILE_BYTES + 1)
        .read_to_end(&mut bytes)
        .unwrap();
    assert!(bytes.len() as u64 <= MAX_QUALIFICATION_FILE_BYTES);
    bytes
}

fn decode_input(format: &str, bytes: &[u8]) -> Result<RootGuestInputV1, String> {
    let input = match format {
        "initial-json" => RootGuestInputV1::InitialStateV1(bytes.to_vec()),
        "recursive-epoch-json" => {
            let value: GlobalEconomicRecursiveGuestInputV1 =
                serde_json::from_slice(bytes).map_err(|e| format!("{e:?}"))?;
            let canonical = canonical_json_bytes_v1(&value, "qualification input")
                .map_err(|e| format!("{e:?}"))?;
            if canonical != bytes {
                return Err("noncanonical qualification input".to_owned());
            }
            RootGuestInputV1::RecursiveEpochV1(value)
        }
        _ => return Err("unknown qualification input format".to_owned()),
    };
    canonical_root_input_bytes_v1(&input).map_err(|e| format!("{e:?}"))?;
    Ok(input)
}

#[test]
fn input_format_is_explicit_and_canonical_before_proving() {
    let initial = support::initial_root_input(support::root(1).as_str());
    let RootGuestInputV1::InitialStateV1(bytes) = initial else {
        panic!("initial fixture");
    };
    assert!(decode_input("initial-json", &bytes).is_ok());
    assert!(decode_input("recursive-epoch-json", &bytes).is_err());
    assert!(decode_input("unknown", &bytes).is_err());
    let mut padded = bytes;
    padded.push(b' ');
    assert!(decode_input("initial-json", &padded).is_err());
}

#[test]
#[ignore = "genuine proof from exact supplied files on an authorized isolated prover"]
fn real_root_from_exact_input_files() {
    let input = decode_input(
        &std::env::var("ZENODEX_ROOT_INPUT_FORMAT").unwrap(),
        &bounded_read(std::env::var_os("ZENODEX_ROOT_INPUT_FILE").unwrap()),
    )
    .unwrap();
    let encoded = canonical_root_input_bytes_v1(&input).unwrap();
    let prepared = prepare_root_input_v1(&encoded).unwrap();
    let paths: Vec<String> = serde_json::from_slice(&bounded_read(
        std::env::var_os("ZENODEX_ROOT_NATIVE_RECEIPT_PATHS_FILE").unwrap(),
    ))
    .unwrap();
    assert_eq!(paths.len(), prepared.child_claims().len());
    let children = paths
        .iter()
        .map(|path| {
            let bytes = bounded_read(path);
            let receipt: Receipt = serde_json::from_slice(&bytes).unwrap();
            assert_eq!(serde_json::to_vec(&receipt).unwrap(), bytes);
            receipt
        })
        .collect();
    let receipt = prove_economic_root_succinct_v1(&input, children).unwrap();
    verify_economic_root_receipt_v1(&receipt, &prepared).unwrap();
    let directory =
        std::path::PathBuf::from(std::env::var_os("ZENODEX_ROOT_FILE_EVIDENCE_DIR").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    for (name, bytes) in [
        ("root.input", encoded),
        ("root.journal", receipt.journal.bytes.clone()),
        ("root.receipt", postcard::to_allocvec(&receipt).unwrap()),
        ("root.elf", ZENODEX_ECONOMIC_ROOT_GUEST_ELF.to_vec()),
    ] {
        std::fs::write(directory.join(name), bytes).unwrap();
    }
    std::fs::write(
        directory.join("subject.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "root_image_id": economic_root_image_root_v1().unwrap(),
            "root_image_words": ZENODEX_ECONOMIC_ROOT_GUEST_ID,
            "statement_kind": format!("{:?}", prepared.kind()),
            "child_receipt_count": paths.len(),
            "signature_authority_verified": false,
            "publication_qualified": false,
            "production_authority": false,
        }))
        .unwrap(),
    )
    .unwrap();
}
