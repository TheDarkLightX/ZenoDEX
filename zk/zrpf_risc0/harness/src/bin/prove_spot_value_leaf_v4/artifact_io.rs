use std::{
    fs,
    io::{Read, Seek, SeekFrom, Write},
    path::Path,
};

#[cfg(unix)]
use std::os::unix::fs::MetadataExt;

use risc0_zkvm::{InnerReceipt, Receipt};
use sha2::{Digest as ShaDigest, Sha256};

pub(super) const MAX_ARTIFACT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_ARTIFACT_BYTES_U64: u64 = 16 * 1_024 * 1_024;
const MAX_ARTIFACT_READ_BYTES_U64: u64 = MAX_ARTIFACT_BYTES_U64 + 1;

pub(super) fn require_succinct(receipt: &Receipt, label: &str) -> Result<(), String> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(format!("{label} receipt is not Succinct"));
    }
    Ok(())
}

pub(super) fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_ARTIFACT_BYTES {
        return Err("canonical receipt bytes exceed evidence bound".to_owned());
    }
    Ok(bytes)
}

pub(super) fn persist_receipt(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut output = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("create V4 receipt output: {error}"))?;
    output
        .write_all(bytes)
        .map_err(|error| format!("write V4 receipt output: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync V4 receipt output: {error}"))?;
    output
        .seek(SeekFrom::Start(0))
        .map_err(|error| format!("rewind V4 receipt output: {error}"))?;
    let mut reread = Vec::new();
    (&mut output)
        .take(MAX_ARTIFACT_READ_BYTES_U64)
        .read_to_end(&mut reread)
        .map_err(|error| format!("reread V4 receipt output: {error}"))?;
    if reread != bytes {
        return Err("persisted V4 receipt differs from verified bytes".to_owned());
    }
    Ok(())
}

pub(super) fn read_bounded_regular_file(path: &Path, label: &str) -> Result<Vec<u8>, String> {
    let path_metadata =
        fs::symlink_metadata(path).map_err(|error| format!("{label} metadata: {error}"))?;
    if !path_metadata.is_file()
        || path_metadata.file_type().is_symlink()
        || path_metadata.len() > MAX_ARTIFACT_BYTES_U64
    {
        return Err(format!(
            "{label} must be a bounded non-symlink regular file"
        ));
    }
    let mut input = fs::File::open(path).map_err(|error| format!("open {label}: {error}"))?;
    let opened_metadata = input
        .metadata()
        .map_err(|error| format!("opened {label} metadata: {error}"))?;
    if !same_file_version(&path_metadata, &opened_metadata) {
        return Err(format!("{label} path changed while it was opened"));
    }
    let mut bytes = Vec::new();
    (&mut input)
        .take(MAX_ARTIFACT_READ_BYTES_U64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read {label}: {error}"))?;
    let final_metadata = input
        .metadata()
        .map_err(|error| format!("final {label} metadata: {error}"))?;
    if !same_file_version(&opened_metadata, &final_metadata) {
        return Err(format!("{label} changed while it was read"));
    }
    if bytes.is_empty() || bytes.len() > MAX_ARTIFACT_BYTES {
        return Err(format!("{label} byte length unsupported"));
    }
    Ok(bytes)
}

#[cfg(unix)]
fn same_file_version(left: &fs::Metadata, right: &fs::Metadata) -> bool {
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
fn same_file_version(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() == right.is_file()
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}

pub(super) fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
