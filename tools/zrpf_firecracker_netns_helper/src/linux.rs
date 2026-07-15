use std::ffi::CString;
use std::fs;
use std::io;
use std::os::fd::{AsRawFd, RawFd};

use crate::{
    DecodedNetnsRequestV1, NetnsHelperErrorV1, NetnsKernelObservationV1, NetnsKernelV1,
    NetnsOperationV1,
};

mod filesystem;
mod netlink;
mod process;
mod seccomp;

use filesystem::{
    create_empty_target, enter_namespace, fstat, fstatfs_type, joined_path, open_namespace,
    open_optional_target, open_trusted_root, path_cstring, require_namespace_identity,
    require_root_owned_namespace_mount, require_root_owned_partial_file, require_target_absent,
    unlink_target, unmount_path, NSFS_MAGIC,
};
use netlink::require_empty_network_inventory;
use process::{current_tid, require_empty_process_membership};
use seccomp::install_netlink_only as install_netlink_only_seccomp_v1;

pub struct LinuxNetnsKernelV1;

impl LinuxNetnsKernelV1 {
    pub fn new() -> Result<Self, NetnsHelperErrorV1> {
        // The helper must begin and remain root; callers cannot delegate this
        // boundary to a setuid transition or ambient capability gain.
        if unsafe { libc::geteuid() } != 0 {
            return Err(NetnsHelperErrorV1::TrustedUid);
        }
        install_netlink_only_seccomp_v1()?;
        Ok(Self)
    }
}

impl NetnsKernelV1 for LinuxNetnsKernelV1 {
    fn execute(
        &mut self,
        request: &DecodedNetnsRequestV1,
    ) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
        match request.operation() {
            NetnsOperationV1::Create => create_namespace(request),
            NetnsOperationV1::Inspect => inspect_namespace(request),
            NetnsOperationV1::Destroy => destroy_namespace(request),
            NetnsOperationV1::Cleanup => cleanup_namespace(request),
            NetnsOperationV1::Absence => require_namespace_absent(request),
        }
    }
}

pub fn close_unexpected_descriptors_v1() -> Result<(), NetnsHelperErrorV1> {
    // close_range is atomic with respect to descriptor-number reuse and leaves
    // only stdin, stdout, and stderr available to the privileged helper.
    let result = unsafe { libc::syscall(libc::SYS_close_range, 3_u32, u32::MAX, 0_u32) };
    if result == 0 {
        return Ok(());
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() != Some(libc::ENOSYS) {
        return Err(NetnsHelperErrorV1::IoRejected);
    }
    let descriptors = fs::read_dir("/proc/self/fd")
        .map_err(|_| NetnsHelperErrorV1::IoRejected)?
        .filter_map(Result::ok)
        .filter_map(|entry| entry.file_name().to_string_lossy().parse::<RawFd>().ok())
        .filter(|descriptor| *descriptor >= 3)
        .collect::<Vec<_>>();
    for descriptor in descriptors {
        let result = unsafe { libc::close(descriptor) };
        if result != 0 && io::Error::last_os_error().raw_os_error() != Some(libc::EBADF) {
            return Err(NetnsHelperErrorV1::IoRejected);
        }
    }
    Ok(())
}

fn create_namespace(
    request: &DecodedNetnsRequestV1,
) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
    let root = open_trusted_root(request.namespace_root())?;
    require_target_absent(root.as_raw_fd(), request.namespace_name())?;
    create_empty_target(root.as_raw_fd(), request.namespace_name())?;
    let target = joined_path(request)?;
    let mut mounted = false;
    let result = (|| {
        if unsafe { libc::unshare(libc::CLONE_NEWNET) } != 0 {
            return Err(NetnsHelperErrorV1::NamespaceCreateRejected);
        }
        let source = CString::new("/proc/self/ns/net")
            .map_err(|_| NetnsHelperErrorV1::NamespaceMountRejected)?;
        let target_c = path_cstring(&target)?;
        if unsafe {
            libc::mount(
                source.as_ptr(),
                target_c.as_ptr(),
                core::ptr::null(),
                libc::MS_BIND,
                core::ptr::null(),
            )
        } != 0
        {
            return Err(NetnsHelperErrorV1::NamespaceMountRejected);
        }
        mounted = true;
        let namespace = open_namespace(root.as_raw_fd(), request.namespace_name())?;
        let (device, inode) = require_namespace_identity(&namespace, None)?;
        require_empty_process_membership(device, inode, Some(current_tid()?))?;
        require_empty_network_inventory()?;
        Ok(NetnsKernelObservationV1::for_operation(
            NetnsOperationV1::Create,
            device,
            inode,
        ))
    })();
    if result.is_err() {
        if mounted {
            let _ = unmount_path(&target);
        }
        let _ = unlink_target(root.as_raw_fd(), request.namespace_name());
    }
    result
}

fn inspect_namespace(
    request: &DecodedNetnsRequestV1,
) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
    let root = open_trusted_root(request.namespace_root())?;
    let namespace = open_namespace(root.as_raw_fd(), request.namespace_name())?;
    let identity = (request.expected_device(), request.expected_inode());
    let (device, inode) = require_namespace_identity(&namespace, Some(identity))?;
    require_empty_process_membership(device, inode, None)?;
    enter_namespace(&namespace)?;
    require_empty_process_membership(device, inode, Some(current_tid()?))?;
    require_empty_network_inventory()?;
    Ok(NetnsKernelObservationV1::for_operation(
        NetnsOperationV1::Inspect,
        device,
        inode,
    ))
}

fn destroy_namespace(
    request: &DecodedNetnsRequestV1,
) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
    let root = open_trusted_root(request.namespace_root())?;
    let namespace = open_namespace(root.as_raw_fd(), request.namespace_name())?;
    let identity = (request.expected_device(), request.expected_inode());
    let (device, inode) = require_namespace_identity(&namespace, Some(identity))?;
    require_empty_process_membership(device, inode, None)?;
    enter_namespace(&namespace)?;
    require_empty_process_membership(device, inode, Some(current_tid()?))?;
    require_empty_network_inventory()?;
    let target = joined_path(request)?;
    unmount_path(&target)?;
    unlink_target(root.as_raw_fd(), request.namespace_name())?;
    require_target_absent(root.as_raw_fd(), request.namespace_name())?;
    Ok(NetnsKernelObservationV1::for_operation(
        NetnsOperationV1::Destroy,
        device,
        inode,
    ))
}

fn cleanup_namespace(
    request: &DecodedNetnsRequestV1,
) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
    let root = open_trusted_root(request.namespace_root())?;
    let Some(target) = open_optional_target(root.as_raw_fd(), request.namespace_name())? else {
        return Ok(NetnsKernelObservationV1::for_operation(
            NetnsOperationV1::Cleanup,
            0,
            0,
        ));
    };
    let metadata = fstat(target.as_raw_fd())?;
    let namespace_type = fstatfs_type(target.as_raw_fd())?;
    let device = metadata.st_dev;
    let inode = metadata.st_ino;
    if namespace_type == NSFS_MAGIC {
        require_root_owned_namespace_mount(&metadata)?;
        require_empty_process_membership(device, inode, None)?;
        enter_namespace(&target)?;
        require_empty_process_membership(device, inode, Some(current_tid()?))?;
        require_empty_network_inventory()?;
        unmount_path(&joined_path(request)?)?;
    } else {
        require_root_owned_partial_file(&metadata)?;
    }
    unlink_target(root.as_raw_fd(), request.namespace_name())?;
    require_target_absent(root.as_raw_fd(), request.namespace_name())?;
    Ok(NetnsKernelObservationV1::for_operation(
        NetnsOperationV1::Cleanup,
        device,
        inode,
    ))
}

fn require_namespace_absent(
    request: &DecodedNetnsRequestV1,
) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
    let root = open_trusted_root(request.namespace_root())?;
    require_target_absent(root.as_raw_fd(), request.namespace_name())?;
    Ok(NetnsKernelObservationV1::for_operation(
        NetnsOperationV1::Absence,
        request.expected_device(),
        request.expected_inode(),
    ))
}
