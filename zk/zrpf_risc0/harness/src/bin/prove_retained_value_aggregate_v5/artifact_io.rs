use std::{
    fs::{File, Metadata},
    io::{Read, Seek, SeekFrom, Write},
    os::unix::fs::MetadataExt,
    path::Path,
};

use std::fs;

use risc0_zkvm::{compute_image_id, Digest, Receipt};
use rustix::fs::{Mode, OFlags};
use sha2::{Digest as _, Sha256};

use super::ProgramSpec;

pub(super) const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_BUNDLE_BYTES: usize = 32 * 1_024 * 1_024;

pub(super) struct PersistedBundle {
    byte_length: usize,
    sha256: [u8; 32],
}

impl PersistedBundle {
    pub(super) const fn byte_length(&self) -> usize {
        self.byte_length
    }

    pub(super) const fn sha256(&self) -> [u8; 32] {
        self.sha256
    }
}

pub(super) struct BoundProgram {
    bytes: Vec<u8>,
    sha256: [u8; 32],
    image_id: [u32; 8],
}

impl BoundProgram {
    pub(super) fn load_once(path: &Path, spec: &ProgramSpec) -> Result<Self, String> {
        let bytes = read_regular_once(path, spec.size_bytes, spec.label)?;
        if bytes.len() != spec.size_bytes {
            return Err(format!(
                "{} byte length differs from governed record",
                spec.label
            ));
        }
        let sha256: [u8; 32] = Sha256::digest(&bytes).into();
        if sha256 != spec.sha256 {
            return Err(format!(
                "{} SHA-256 differs from governed record",
                spec.label
            ));
        }
        let computed = compute_image_id(&bytes)
            .map_err(|error| format!("compute {} image ID: {error}", spec.label))?;
        if computed != Digest::from(spec.image_id) {
            return Err(format!(
                "{} image ID differs from governed record",
                spec.label
            ));
        }
        Ok(Self {
            bytes,
            sha256,
            image_id: spec.image_id,
        })
    }

    pub(super) fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub(super) const fn sha256(&self) -> [u8; 32] {
        self.sha256
    }

    pub(super) const fn image_id(&self) -> [u32; 8] {
        self.image_id
    }
}

pub(super) fn read_receipt_once(path: &Path, label: &str) -> Result<Vec<u8>, String> {
    read_regular_once(path, MAX_RECEIPT_BYTES, label)
}

pub(super) fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_RECEIPT_BYTES {
        return Err("canonical receipt bytes exceed governed bound".to_owned());
    }
    Ok(bytes)
}

pub(super) fn persist_bundle(path: &Path, bytes: &[u8]) -> Result<PersistedBundle, String> {
    if bytes.is_empty() || bytes.len() > MAX_BUNDLE_BYTES {
        return Err("V5 receipt bundle byte length unsupported".to_owned());
    }
    let descriptor = rustix::fs::open(
        path,
        OFlags::RDWR
            | OFlags::CREATE
            | OFlags::EXCL
            | OFlags::NOFOLLOW
            | OFlags::NONBLOCK
            | OFlags::CLOEXEC,
        Mode::RUSR | Mode::WUSR,
    )
    .map_err(|error| format!("create V5 receipt bundle: {error}"))?;
    let mut output = File::from(descriptor);
    output
        .write_all(bytes)
        .map_err(|error| format!("write V5 receipt bundle: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync V5 receipt bundle: {error}"))?;
    output
        .seek(SeekFrom::Start(0))
        .map_err(|error| format!("rewind V5 receipt bundle: {error}"))?;
    let maximum_read = u64::try_from(MAX_BUNDLE_BYTES)
        .ok()
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| "V5 receipt bundle read bound unsupported".to_owned())?;
    let mut observed = Vec::new();
    (&mut output)
        .take(maximum_read)
        .read_to_end(&mut observed)
        .map_err(|error| format!("reread V5 receipt bundle: {error}"))?;
    if observed != bytes {
        return Err("persisted V5 receipt bundle differs from verified bytes".to_owned());
    }
    let opened_metadata = output
        .metadata()
        .map_err(|error| format!("persisted V5 receipt bundle metadata: {error}"))?;
    let path_metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("persisted V5 receipt bundle path metadata: {error}"))?;
    if !same_file_version(&opened_metadata, &path_metadata) {
        return Err("persisted V5 receipt bundle path identity changed".to_owned());
    }
    Ok(PersistedBundle {
        byte_length: observed.len(),
        sha256: Sha256::digest(&observed).into(),
    })
}

pub(super) fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn read_regular_once(path: &Path, maximum: usize, label: &str) -> Result<Vec<u8>, String> {
    let descriptor = rustix::fs::open(
        path,
        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|error| format!("open {label}: {error}"))?;
    let mut input = File::from(descriptor);
    let before = input
        .metadata()
        .map_err(|error| format!("opened {label} metadata: {error}"))?;
    require_bounded_regular(&before, maximum, label)?;
    let maximum_read = u64::try_from(maximum)
        .ok()
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| format!("{label} bound overflow"))?;
    let mut bytes = Vec::new();
    (&mut input)
        .take(maximum_read)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read {label}: {error}"))?;
    let after = input
        .metadata()
        .map_err(|error| format!("final {label} metadata: {error}"))?;
    if !same_file_version(&before, &after) {
        return Err(format!("{label} changed while read"));
    }
    let observed_length =
        u64::try_from(bytes.len()).map_err(|_| format!("{label} byte length unsupported"))?;
    if bytes.is_empty() || bytes.len() > maximum || observed_length != after.len() {
        return Err(format!("{label} byte length unsupported"));
    }
    Ok(bytes)
}

fn require_bounded_regular(metadata: &Metadata, maximum: usize, label: &str) -> Result<(), String> {
    let maximum = u64::try_from(maximum).map_err(|_| format!("{label} byte bound unsupported"))?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.len() == 0
        || metadata.len() > maximum
    {
        return Err(format!("{label} must be a bounded regular file"));
    }
    Ok(())
}

fn same_file_version(left: &Metadata, right: &Metadata) -> bool {
    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.mode() == right.mode()
        && left.size() == right.size()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(test)]
pub(super) fn read_fixture_once(path: &Path, maximum: usize) -> Result<Vec<u8>, String> {
    read_regular_once(path, maximum, "test fixture")
}

#[cfg(test)]
pub(super) fn remove_fixture(path: &Path) {
    let _ = fs::remove_file(path);
}
