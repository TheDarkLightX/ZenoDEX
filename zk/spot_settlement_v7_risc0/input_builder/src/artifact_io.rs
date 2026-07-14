use std::fs::{self, Metadata, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};

use crate::SpotSettlementV7InputBuilderErrorV1;

pub(crate) fn read_stable_bounded_input_v1(
    path: &Path,
    maximum_bytes: usize,
    label: &'static str,
) -> Result<Vec<u8>, SpotSettlementV7InputBuilderErrorV1> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    let mut input = options
        .open(path)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::InputOpen(label))?;
    let before = input
        .metadata()
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::InputMetadata(label))?;
    require_single_link_regular(&before, maximum_bytes, label)?;
    let read_bound = maximum_bytes
        .checked_add(1)
        .ok_or(SpotSettlementV7InputBuilderErrorV1::InputLength(label))?;
    let read_bound_u64 = u64::try_from(read_bound)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::InputLength(label))?;
    let mut bytes = Vec::new();
    (&mut input)
        .take(read_bound_u64)
        .read_to_end(&mut bytes)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::InputRead(label))?;
    let after = input
        .metadata()
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::InputMetadata(label))?;
    let path_after = fs::symlink_metadata(path)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::InputChanged(label))?;
    if !same_file_version(&before, &after) || !same_file_version(&after, &path_after) {
        return Err(SpotSettlementV7InputBuilderErrorV1::InputChanged(label));
    }
    if bytes.is_empty() || bytes.len() > maximum_bytes {
        return Err(SpotSettlementV7InputBuilderErrorV1::InputLength(label));
    }
    Ok(bytes)
}

pub(crate) fn persist_create_new_exact_v1(
    path: &Path,
    bytes: &[u8],
) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    let mut options = OpenOptions::new();
    options.read(true).write(true).create_new(true);
    #[cfg(unix)]
    {
        options
            .mode(0o600)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    }
    let mut output = options
        .open(path)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputCreate)?;
    #[cfg(unix)]
    output
        .set_permissions(fs::Permissions::from_mode(0o600))
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputPermissions)?;
    let opened = output
        .metadata()
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputMetadata)?;
    require_new_output_file(&opened)?;
    output
        .write_all(bytes)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputWrite)?;
    output
        .sync_all()
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputSync)?;
    output
        .seek(SeekFrom::Start(0))
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputSeek)?;
    let read_bound = bytes
        .len()
        .checked_add(1)
        .and_then(|value| u64::try_from(value).ok())
        .ok_or(SpotSettlementV7InputBuilderErrorV1::OutputRead)?;
    let mut reread = Vec::new();
    (&mut output)
        .take(read_bound)
        .read_to_end(&mut reread)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputRead)?;
    let final_metadata = output
        .metadata()
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputMetadata)?;
    let path_metadata = fs::symlink_metadata(path)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputChanged)?;
    let expected_length = u64::try_from(bytes.len())
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::OutputChanged)?;
    if !same_file_identity(&opened, &final_metadata)
        || !same_file_version(&final_metadata, &path_metadata)
        || !has_one_link(&final_metadata)
        || final_metadata.len() != expected_length
        || reread != bytes
    {
        return Err(SpotSettlementV7InputBuilderErrorV1::OutputChanged);
    }
    Ok(())
}

fn require_single_link_regular(
    metadata: &Metadata,
    maximum_bytes: usize,
    label: &'static str,
) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    let maximum = u64::try_from(maximum_bytes)
        .map_err(|_| SpotSettlementV7InputBuilderErrorV1::InputLength(label))?;
    if !metadata.is_file() || !has_one_link(metadata) {
        return Err(SpotSettlementV7InputBuilderErrorV1::InputNotSingleLinkRegular(label));
    }
    if metadata.len() == 0 || metadata.len() > maximum {
        return Err(SpotSettlementV7InputBuilderErrorV1::InputLength(label));
    }
    Ok(())
}

fn require_new_output_file(metadata: &Metadata) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    if !metadata.is_file()
        || !has_one_link(metadata)
        || !has_private_output_mode(metadata)
        || metadata.len() != 0
    {
        return Err(SpotSettlementV7InputBuilderErrorV1::OutputMetadata);
    }
    Ok(())
}

#[cfg(unix)]
fn has_one_link(metadata: &Metadata) -> bool {
    metadata.nlink() == 1
}

#[cfg(not(unix))]
const fn has_one_link(_metadata: &Metadata) -> bool {
    true
}

#[cfg(unix)]
fn has_private_output_mode(metadata: &Metadata) -> bool {
    metadata.mode() & 0o777 == 0o600
}

#[cfg(not(unix))]
const fn has_private_output_mode(_metadata: &Metadata) -> bool {
    true
}

#[cfg(unix)]
fn same_file_identity(left: &Metadata, right: &Metadata) -> bool {
    left.dev() == right.dev() && left.ino() == right.ino() && left.mode() == right.mode()
}

#[cfg(not(unix))]
fn same_file_identity(left: &Metadata, right: &Metadata) -> bool {
    left.is_file() == right.is_file()
}

#[cfg(unix)]
fn same_file_version(left: &Metadata, right: &Metadata) -> bool {
    same_file_identity(left, right)
        && left.size() == right.size()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(not(unix))]
fn same_file_version(left: &Metadata, right: &Metadata) -> bool {
    same_file_identity(left, right)
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}
