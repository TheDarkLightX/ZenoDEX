use std::collections::BTreeSet;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

use sha2::{Digest as ShaDigest, Sha256};
use zenodex_zrpf_risc0_verifier::MAX_CANONICAL_RECEIPT_BYTES_V3;

use crate::error::ReplayError;
use crate::profile::{MAX_RECEIPT_READ_BYTES_U64, RETAINED_ARTIFACTS};

#[derive(Debug)]
pub(crate) struct BundlePaths {
    #[cfg(unix)]
    pub(crate) directory: rustix::fd::OwnedFd,
}

pub(crate) fn parse_bundle_directory(
    args: impl IntoIterator<Item = String>,
) -> Result<BundlePaths, ReplayError> {
    let args: Vec<String> = args.into_iter().collect();
    let [root] = args.as_slice() else {
        return Err(ReplayError::Usage);
    };
    if root.is_empty() {
        return Err(ReplayError::Usage);
    }

    #[cfg(not(unix))]
    {
        return Err(ReplayError::UnsupportedPlatform);
    }

    #[cfg(unix)]
    let root = PathBuf::from(root);
    #[cfg(unix)]
    let directory = open_bundle_directory(&root)?;
    #[cfg(unix)]
    let entries =
        rustix::fs::Dir::read_from(&directory).map_err(|_| ReplayError::BundleDirectory)?;
    #[cfg(unix)]
    let mut actual = BTreeSet::new();
    #[cfg(unix)]
    for entry in entries {
        let entry = entry.map_err(|_| ReplayError::BundleDirectory)?;
        let name = std::str::from_utf8(entry.file_name().to_bytes())
            .map_err(|_| ReplayError::BundleInventory)?;
        if name == "." || name == ".." {
            continue;
        }
        actual.insert(name.to_owned());
    }
    #[cfg(unix)]
    let expected: BTreeSet<String> = RETAINED_ARTIFACTS
        .iter()
        .map(|artifact| artifact.name.to_owned())
        .collect();
    #[cfg(unix)]
    if actual != expected {
        return Err(ReplayError::BundleInventory);
    }
    #[cfg(unix)]
    Ok(BundlePaths { directory })
}

#[cfg(unix)]
pub(crate) fn open_bundle_directory(path: &Path) -> Result<rustix::fd::OwnedFd, ReplayError> {
    use rustix::fs::{Mode, OFlags};

    let directory = rustix::fs::open(
        path,
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| ReplayError::BundleDirectory)?;
    let metadata = rustix::fs::fstat(&directory).map_err(|_| ReplayError::BundleDirectory)?;
    if !rustix::fs::FileType::from_raw_mode(metadata.st_mode).is_dir() {
        return Err(ReplayError::BundleDirectory);
    }
    Ok(directory)
}

pub(crate) fn read_bounded_regular_file(
    paths: &BundlePaths,
    name: &'static str,
) -> Result<Vec<u8>, ReplayError> {
    #[cfg(not(unix))]
    {
        let _ = paths;
        let _ = name;
        return Err(ReplayError::UnsupportedPlatform);
    }

    #[cfg(unix)]
    let descriptor = rustix::fs::openat(
        &paths.directory,
        name,
        rustix::fs::OFlags::RDONLY
            | rustix::fs::OFlags::NOFOLLOW
            | rustix::fs::OFlags::NONBLOCK
            | rustix::fs::OFlags::CLOEXEC,
        rustix::fs::Mode::empty(),
    )
    .map_err(|_| ReplayError::ReceiptArtifact(name))?;
    #[cfg(unix)]
    let metadata =
        rustix::fs::fstat(&descriptor).map_err(|_| ReplayError::ReceiptArtifact(name))?;
    #[cfg(unix)]
    let size_bytes =
        usize::try_from(metadata.st_size).map_err(|_| ReplayError::ReceiptArtifact(name))?;
    #[cfg(unix)]
    if !rustix::fs::FileType::from_raw_mode(metadata.st_mode).is_file()
        || size_bytes == 0
        || size_bytes > MAX_CANONICAL_RECEIPT_BYTES_V3
    {
        return Err(ReplayError::ReceiptArtifact(name));
    }
    #[cfg(unix)]
    let input = fs::File::from(descriptor);
    #[cfg(unix)]
    let mut bytes = Vec::new();
    #[cfg(unix)]
    input
        .take(MAX_RECEIPT_READ_BYTES_U64)
        .read_to_end(&mut bytes)
        .map_err(|_| ReplayError::ReceiptArtifact(name))?;
    #[cfg(unix)]
    if bytes.len() != size_bytes || bytes.len() > MAX_CANONICAL_RECEIPT_BYTES_V3 {
        return Err(ReplayError::ReceiptArtifact(name));
    }
    #[cfg(unix)]
    Ok(bytes)
}

pub(crate) fn require_retained_artifact_binding(
    name: &'static str,
    bytes: &[u8],
) -> Result<(), ReplayError> {
    let artifact = RETAINED_ARTIFACTS
        .iter()
        .find(|artifact| artifact.name == name)
        .ok_or(ReplayError::ReceiptArtifactBinding(name))?;
    if bytes.len() != artifact.size_bytes || hex::encode(Sha256::digest(bytes)) != artifact.sha256 {
        return Err(ReplayError::ReceiptArtifactBinding(name));
    }
    Ok(())
}
