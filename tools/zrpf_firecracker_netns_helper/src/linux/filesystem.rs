use std::ffi::CString;
use std::io;
use std::mem::zeroed;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::path::{Path, PathBuf};

use crate::{DecodedNetnsRequestV1, NetnsHelperErrorV1};

pub(super) const NSFS_MAGIC: libc::c_long = 0x6e736673;

pub(super) fn open_trusted_root(path: &str) -> Result<OwnedFd, NetnsHelperErrorV1> {
    let slash = CString::new("/").map_err(|_| NetnsHelperErrorV1::RootDirectoryRejected)?;
    let descriptor = unsafe {
        libc::open(
            slash.as_ptr(),
            libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC,
        )
    };
    if descriptor < 0 {
        return Err(NetnsHelperErrorV1::RootDirectoryRejected);
    }
    let mut current = unsafe { OwnedFd::from_raw_fd(descriptor) };
    let components = path[1..].split('/').collect::<Vec<_>>();
    for (index, component) in components.iter().enumerate() {
        let name =
            CString::new(*component).map_err(|_| NetnsHelperErrorV1::RootDirectoryRejected)?;
        let next = unsafe {
            libc::openat(
                current.as_raw_fd(),
                name.as_ptr(),
                libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
            )
        };
        if next < 0 {
            return Err(NetnsHelperErrorV1::RootDirectoryRejected);
        }
        let opened = unsafe { OwnedFd::from_raw_fd(next) };
        require_root_owned_directory(&fstat(opened.as_raw_fd())?, index + 1 == components.len())?;
        current = opened;
    }
    Ok(current)
}

fn require_root_owned_directory(
    metadata: &libc::stat,
    is_namespace_root: bool,
) -> Result<(), NetnsHelperErrorV1> {
    if metadata.st_uid != 0
        || metadata.st_mode & libc::S_IFMT != libc::S_IFDIR
        || metadata.st_mode & 0o022 != 0
        || (is_namespace_root && metadata.st_mode & 0o077 != 0)
    {
        return Err(NetnsHelperErrorV1::RootDirectoryRejected);
    }
    Ok(())
}

pub(super) fn require_root_owned_namespace_mount(
    metadata: &libc::stat,
) -> Result<(), NetnsHelperErrorV1> {
    if metadata.st_uid != 0
        || metadata.st_nlink != 1
        || metadata.st_mode & libc::S_IFMT != libc::S_IFREG
        || metadata.st_mode & 0o222 != 0
    {
        return Err(NetnsHelperErrorV1::NamespaceOwnershipRejected);
    }
    Ok(())
}

pub(super) fn require_root_owned_partial_file(
    metadata: &libc::stat,
) -> Result<(), NetnsHelperErrorV1> {
    if metadata.st_uid != 0
        || metadata.st_nlink != 1
        || metadata.st_mode & libc::S_IFMT != libc::S_IFREG
        || metadata.st_mode & 0o777 != 0o600
    {
        return Err(NetnsHelperErrorV1::NamespaceCleanupRejected);
    }
    Ok(())
}

pub(super) fn create_empty_target(root_fd: RawFd, name: &str) -> Result<(), NetnsHelperErrorV1> {
    let name = CString::new(name).map_err(|_| NetnsHelperErrorV1::NamespaceCreateRejected)?;
    let descriptor = unsafe {
        libc::openat(
            root_fd,
            name.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_CREAT | libc::O_EXCL,
            0o600,
        )
    };
    if descriptor < 0 {
        return Err(match io::Error::last_os_error().raw_os_error() {
            Some(libc::EEXIST) => NetnsHelperErrorV1::NamespaceAlreadyExists,
            _ => NetnsHelperErrorV1::NamespaceCreateRejected,
        });
    }
    drop(unsafe { OwnedFd::from_raw_fd(descriptor) });
    Ok(())
}

pub(super) fn open_optional_target(
    root_fd: RawFd,
    name: &str,
) -> Result<Option<OwnedFd>, NetnsHelperErrorV1> {
    let name = CString::new(name).map_err(|_| NetnsHelperErrorV1::NamespaceOpenRejected)?;
    let descriptor = unsafe {
        libc::openat(
            root_fd,
            name.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
        )
    };
    if descriptor >= 0 {
        return Ok(Some(unsafe { OwnedFd::from_raw_fd(descriptor) }));
    }
    if io::Error::last_os_error().raw_os_error() == Some(libc::ENOENT) {
        return Ok(None);
    }
    Err(NetnsHelperErrorV1::NamespaceOpenRejected)
}

pub(super) fn open_namespace(root_fd: RawFd, name: &str) -> Result<OwnedFd, NetnsHelperErrorV1> {
    open_optional_target(root_fd, name)?.ok_or(NetnsHelperErrorV1::NamespaceOpenRejected)
}

pub(super) fn require_namespace_identity(
    namespace: &OwnedFd,
    expected: Option<(u64, u64)>,
) -> Result<(u64, u64), NetnsHelperErrorV1> {
    let metadata = fstat(namespace.as_raw_fd())?;
    require_root_owned_namespace_mount(&metadata)?;
    if fstatfs_type(namespace.as_raw_fd())? != NSFS_MAGIC {
        return Err(NetnsHelperErrorV1::NamespaceTypeRejected);
    }
    let identity = (metadata.st_dev, metadata.st_ino);
    if expected.is_some_and(|expected_identity| identity != expected_identity) {
        return Err(NetnsHelperErrorV1::NamespaceIdentityMismatch);
    }
    Ok(identity)
}

pub(super) fn require_target_absent(root_fd: RawFd, name: &str) -> Result<(), NetnsHelperErrorV1> {
    let name = CString::new(name).map_err(|_| NetnsHelperErrorV1::NamespaceAbsenceRejected)?;
    let mut metadata: libc::stat = unsafe { zeroed() };
    let result = unsafe {
        libc::fstatat(
            root_fd,
            name.as_ptr(),
            &mut metadata,
            libc::AT_SYMLINK_NOFOLLOW,
        )
    };
    if result != 0 && io::Error::last_os_error().raw_os_error() == Some(libc::ENOENT) {
        return Ok(());
    }
    Err(NetnsHelperErrorV1::NamespaceAbsenceRejected)
}

pub(super) fn enter_namespace(namespace: &OwnedFd) -> Result<(), NetnsHelperErrorV1> {
    if unsafe { libc::setns(namespace.as_raw_fd(), libc::CLONE_NEWNET) } != 0 {
        return Err(NetnsHelperErrorV1::NamespaceSetnsRejected);
    }
    Ok(())
}

pub(super) fn fstat(descriptor: RawFd) -> Result<libc::stat, NetnsHelperErrorV1> {
    let mut metadata: libc::stat = unsafe { zeroed() };
    if unsafe { libc::fstat(descriptor, &mut metadata) } != 0 {
        return Err(NetnsHelperErrorV1::IoRejected);
    }
    Ok(metadata)
}

pub(super) fn fstatfs_type(descriptor: RawFd) -> Result<libc::c_long, NetnsHelperErrorV1> {
    let mut value: libc::statfs = unsafe { zeroed() };
    if unsafe { libc::fstatfs(descriptor, &mut value) } != 0 {
        return Err(NetnsHelperErrorV1::IoRejected);
    }
    Ok(value.f_type)
}

pub(super) fn unlink_target(root_fd: RawFd, name: &str) -> Result<(), NetnsHelperErrorV1> {
    let name = CString::new(name).map_err(|_| NetnsHelperErrorV1::NamespaceCleanupRejected)?;
    if unsafe { libc::unlinkat(root_fd, name.as_ptr(), 0) } != 0 {
        return Err(NetnsHelperErrorV1::NamespaceCleanupRejected);
    }
    Ok(())
}

pub(super) fn unmount_path(path: &Path) -> Result<(), NetnsHelperErrorV1> {
    let path = path_cstring(path)?;
    if unsafe { libc::umount2(path.as_ptr(), 0) } != 0 {
        return Err(NetnsHelperErrorV1::NamespaceDestroyRejected);
    }
    Ok(())
}

pub(super) fn joined_path(request: &DecodedNetnsRequestV1) -> Result<PathBuf, NetnsHelperErrorV1> {
    let mut path = PathBuf::from(request.namespace_root());
    path.push(request.namespace_name());
    let maximum_path =
        usize::try_from(libc::PATH_MAX).map_err(|_| NetnsHelperErrorV1::NamespaceRootCanonical)?;
    if path.as_os_str().as_encoded_bytes().len() > maximum_path {
        return Err(NetnsHelperErrorV1::NamespaceRootCanonical);
    }
    Ok(path)
}

pub(super) fn path_cstring(path: &Path) -> Result<CString, NetnsHelperErrorV1> {
    CString::new(path.as_os_str().as_encoded_bytes())
        .map_err(|_| NetnsHelperErrorV1::NamespaceRootCanonical)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn root_and_mount_object_modes_are_distinct_and_fail_closed() {
        let ancestor = metadata(libc::S_IFDIR | 0o755, 0, 2);
        let private_root = metadata(libc::S_IFDIR | 0o700, 0, 2);
        let open_root = metadata(libc::S_IFDIR | 0o755, 0, 2);
        let namespace = metadata(libc::S_IFREG | 0o444, 0, 1);
        let partial = metadata(libc::S_IFREG | 0o600, 0, 1);

        assert_eq!(require_root_owned_directory(&ancestor, false), Ok(()));
        assert_eq!(require_root_owned_directory(&private_root, true), Ok(()));
        assert_eq!(
            require_root_owned_directory(&open_root, true),
            Err(NetnsHelperErrorV1::RootDirectoryRejected)
        );
        assert_eq!(require_root_owned_namespace_mount(&namespace), Ok(()));
        assert_eq!(require_root_owned_partial_file(&partial), Ok(()));
        assert_eq!(
            require_root_owned_namespace_mount(&partial),
            Err(NetnsHelperErrorV1::NamespaceOwnershipRejected)
        );
        assert_eq!(
            require_root_owned_partial_file(&namespace),
            Err(NetnsHelperErrorV1::NamespaceCleanupRejected)
        );
    }

    fn metadata(mode: libc::mode_t, uid: libc::uid_t, links: libc::nlink_t) -> libc::stat {
        let mut value: libc::stat = unsafe { zeroed() };
        value.st_mode = mode;
        value.st_uid = uid;
        value.st_nlink = links;
        value
    }
}
