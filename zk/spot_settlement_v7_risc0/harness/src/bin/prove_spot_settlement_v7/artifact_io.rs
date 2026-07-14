use std::{
    fs,
    io::{Read, Seek, SeekFrom, Write},
    path::Path,
};

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};

use risc0_zkvm::{InnerReceipt, Receipt};
use sha2::{Digest as ShaDigest, Sha256};

use super::cli::Options;

const MAX_BOUNDED_READ_EXTRA_BYTES: u64 = 1;

#[derive(Clone, Copy)]
pub(super) struct CandidateArtifactsV1<'a> {
    pub(super) receipt: &'a [u8],
    pub(super) receipt_seal_mutation: &'a [u8],
    pub(super) journal: &'a [u8],
    pub(super) verifier_output: &'a [u8],
    pub(super) plan_b: &'a [u8],
}

pub(super) fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("V7 receipt is not Succinct".to_owned());
    }
    let bytes = serde_json::to_vec(receipt)
        .map_err(|error| format!("encode canonical V7 receipt: {error}"))?;
    if bytes.is_empty()
        || bytes.len()
            > zenodex_zrpf_risc0_spot_settlement_v7_verifier::MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1
    {
        return Err("canonical V7 receipt bytes exceed evidence bound".to_owned());
    }
    Ok(bytes)
}

pub(super) fn read_bounded_regular_file(
    path: &Path,
    label: &str,
    maximum_bytes: usize,
) -> Result<Vec<u8>, String> {
    let maximum_u64 = u64::try_from(maximum_bytes)
        .map_err(|_| format!("{label} maximum byte length unsupported"))?;
    let path_metadata =
        fs::symlink_metadata(path).map_err(|error| format!("{label} metadata: {error}"))?;
    if !path_metadata.is_file()
        || path_metadata.file_type().is_symlink()
        || path_metadata.len() == 0
        || path_metadata.len() > maximum_u64
    {
        return Err(format!(
            "{label} must be a nonempty bounded non-symlink regular file"
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
        .take(maximum_u64.saturating_add(MAX_BOUNDED_READ_EXTRA_BYTES))
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read {label}: {error}"))?;
    let final_metadata = input
        .metadata()
        .map_err(|error| format!("final {label} metadata: {error}"))?;
    if !same_file_version(&opened_metadata, &final_metadata) {
        return Err(format!("{label} changed while it was read"));
    }
    if bytes.is_empty() || bytes.len() > maximum_bytes {
        return Err(format!("{label} byte length unsupported"));
    }
    Ok(bytes)
}

pub(super) fn persist_verified_artifacts(
    options: &Options,
    artifacts: CandidateArtifactsV1<'_>,
) -> Result<(), String> {
    write_new_verified(&options.v7_receipt_out, artifacts.receipt, "V7 receipt")?;
    write_new_verified(
        &options.v7_receipt_seal_mutation_out,
        artifacts.receipt_seal_mutation,
        "V7 receipt seal mutation",
    )?;
    write_new_verified(&options.v7_journal_out, artifacts.journal, "V7 journal")?;
    write_new_verified(
        &options.v7_verifier_output_out,
        artifacts.verifier_output,
        "V7 verifier output",
    )?;
    write_new_verified(&options.v7_plan_b_out, artifacts.plan_b, "V7 Plan B")
}

fn write_new_verified(path: &Path, bytes: &[u8], label: &str) -> Result<(), String> {
    if bytes.is_empty() {
        return Err(format!("{label} output is empty"));
    }
    let mut options = fs::OpenOptions::new();
    options.read(true).write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o600);
    let mut output = options
        .open(path)
        .map_err(|error| format!("create {label} output: {error}"))?;
    output
        .write_all(bytes)
        .map_err(|error| format!("write {label} output: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync {label} output: {error}"))?;
    output
        .seek(SeekFrom::Start(0))
        .map_err(|error| format!("rewind {label} output: {error}"))?;
    let read_limit = u64::try_from(bytes.len())
        .map_err(|_| format!("{label} output length unsupported"))?
        .saturating_add(MAX_BOUNDED_READ_EXTRA_BYTES);
    let mut reread = Vec::new();
    (&mut output)
        .take(read_limit)
        .read_to_end(&mut reread)
        .map_err(|error| format!("reread {label} output: {error}"))?;
    if reread != bytes {
        return Err(format!("persisted {label} differs from verified bytes"));
    }
    Ok(())
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
    format!("{:x}", Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn isolated_path(label: &str) -> std::path::PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must follow Unix epoch")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "zenodex-v7-proof-runner-{label}-{}-{nonce}",
            std::process::id()
        ))
    }

    #[test]
    fn write_is_create_new_and_reread_checked() {
        let path = isolated_path("write");
        write_new_verified(&path, b"verified", "test").expect("first write must succeed");
        assert_eq!(fs::read(&path).expect("read output"), b"verified");
        assert!(write_new_verified(&path, b"replacement", "test").is_err());
        fs::remove_file(path).expect("remove test output");
    }

    #[test]
    fn bounded_reader_rejects_empty_and_symlink_inputs() {
        let root = isolated_path("read");
        fs::create_dir(&root).expect("create test directory");
        let empty = root.join("empty");
        fs::write(&empty, []).expect("write empty file");
        assert!(read_bounded_regular_file(&empty, "empty", 8).is_err());

        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;
            let target = root.join("target");
            let link = root.join("link");
            fs::write(&target, b"value").expect("write target");
            symlink(&target, &link).expect("create symlink");
            assert!(read_bounded_regular_file(&link, "link", 8).is_err());
        }
        fs::remove_dir_all(root).expect("remove test directory");
    }
}
