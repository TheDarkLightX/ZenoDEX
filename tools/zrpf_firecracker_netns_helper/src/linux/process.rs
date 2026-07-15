use std::ffi::CString;
use std::fs;
use std::io;
use std::mem::zeroed;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::path::PathBuf;

use crate::NetnsHelperErrorV1;

const MAX_SCANNED_TASKS: u32 = 1_048_576;

pub(super) fn require_empty_process_membership(
    device: u64,
    inode: u64,
    excluded_tid: Option<i32>,
) -> Result<(), NetnsHelperErrorV1> {
    let mut scanned = 0_u32;
    for process in fs::read_dir("/proc").map_err(|_| NetnsHelperErrorV1::IoRejected)? {
        let process = process.map_err(|_| NetnsHelperErrorV1::IoRejected)?;
        let Some(pid) = process.file_name().to_string_lossy().parse::<u32>().ok() else {
            continue;
        };
        let task_root = PathBuf::from(format!("/proc/{pid}/task"));
        let tasks = match fs::read_dir(task_root) {
            Ok(value) => value,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(_) => return Err(NetnsHelperErrorV1::IoRejected),
        };
        for task in tasks {
            let task = task.map_err(|_| NetnsHelperErrorV1::IoRejected)?;
            let Some(tid) = task.file_name().to_string_lossy().parse::<i32>().ok() else {
                continue;
            };
            if excluded_tid == Some(tid) {
                continue;
            }
            scanned = scanned
                .checked_add(1)
                .ok_or(NetnsHelperErrorV1::IoRejected)?;
            if scanned > MAX_SCANNED_TASKS {
                return Err(NetnsHelperErrorV1::IoRejected);
            }
            let path = CString::new(format!("/proc/{pid}/task/{tid}/ns/net"))
                .map_err(|_| NetnsHelperErrorV1::IoRejected)?;
            let descriptor = unsafe { libc::open(path.as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC) };
            if descriptor < 0 {
                if io::Error::last_os_error().raw_os_error() == Some(libc::ENOENT) {
                    continue;
                }
                return Err(NetnsHelperErrorV1::IoRejected);
            }
            let descriptor = unsafe { OwnedFd::from_raw_fd(descriptor) };
            let metadata = fstat(descriptor.as_raw_fd())?;
            if metadata.st_dev == device && metadata.st_ino == inode {
                return Err(NetnsHelperErrorV1::ProcessMembershipNotEmpty);
            }
        }
    }
    Ok(())
}

pub(super) fn current_tid() -> Result<i32, NetnsHelperErrorV1> {
    i32::try_from(unsafe { libc::syscall(libc::SYS_gettid) })
        .map_err(|_| NetnsHelperErrorV1::IoRejected)
}

fn fstat(descriptor: i32) -> Result<libc::stat, NetnsHelperErrorV1> {
    let mut metadata: libc::stat = unsafe { zeroed() };
    if unsafe { libc::fstat(descriptor, &mut metadata) } != 0 {
        return Err(NetnsHelperErrorV1::IoRejected);
    }
    Ok(metadata)
}
