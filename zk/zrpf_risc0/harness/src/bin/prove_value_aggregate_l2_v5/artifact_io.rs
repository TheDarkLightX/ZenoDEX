use std::{
    fs,
    io::{Read, Write},
    path::Path,
};

#[cfg(unix)]
use std::os::unix::fs::MetadataExt;

use risc0_zkvm::Receipt;
use sha2::{Digest as _, Sha256};
use zenodex_zrpf_risc0_verifier::MAX_CANONICAL_RECEIPT_BYTES_V3;

const MAX_RECEIPT_BYTES_U64: u64 = 16_777_216;
const MAX_RECEIPT_READ_BYTES_U64: u64 = MAX_RECEIPT_BYTES_U64 + 1;
const _: () = assert!(MAX_CANONICAL_RECEIPT_BYTES_V3 == 16_777_216);

pub(super) fn read_bounded_receipt_file(path: &Path) -> Result<Vec<u8>, String> {
    let path_metadata =
        fs::symlink_metadata(path).map_err(|error| format!("receipt metadata: {error}"))?;
    if !path_metadata.is_file()
        || path_metadata.file_type().is_symlink()
        || path_metadata.len() > MAX_RECEIPT_BYTES_U64
    {
        return Err("receipt must be a bounded non-symlink regular file".to_owned());
    }
    let mut input = fs::File::open(path).map_err(|error| format!("open receipt: {error}"))?;
    let opened_metadata = input
        .metadata()
        .map_err(|error| format!("opened receipt metadata: {error}"))?;
    if !same_file_version(&path_metadata, &opened_metadata) {
        return Err("receipt path changed while opened".to_owned());
    }
    let mut bytes = Vec::new();
    (&mut input)
        .take(MAX_RECEIPT_READ_BYTES_U64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read receipt: {error}"))?;
    let final_metadata = input
        .metadata()
        .map_err(|error| format!("final receipt metadata: {error}"))?;
    if !same_file_version(&opened_metadata, &final_metadata) {
        return Err("receipt changed while read".to_owned());
    }
    if bytes.is_empty() || bytes.len() > MAX_CANONICAL_RECEIPT_BYTES_V3 {
        return Err("receipt byte length unsupported".to_owned());
    }
    Ok(bytes)
}

pub(super) fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_CANONICAL_RECEIPT_BYTES_V3 {
        return Err("canonical receipt bytes exceed bound".to_owned());
    }
    Ok(bytes)
}

pub(super) fn persist_new_receipt(path: &Path, bytes: &[u8]) -> Result<(), String> {
    if bytes.is_empty() || bytes.len() > MAX_CANONICAL_RECEIPT_BYTES_V3 {
        return Err("persisted receipt bytes exceed bound".to_owned());
    }
    let mut output = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("create L2 root receipt: {error}"))?;
    output
        .write_all(bytes)
        .map_err(|error| format!("write L2 root receipt: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync L2 root receipt: {error}"))
}

pub(super) fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

#[cfg(unix)]
pub(super) fn same_file_version(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.mode() == right.mode()
        && left.size() == right.size()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(not(unix))]
pub(super) fn same_file_version(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() == right.is_file()
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}
