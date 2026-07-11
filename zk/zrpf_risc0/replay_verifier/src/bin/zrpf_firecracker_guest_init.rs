//! PID 1 for the bounded ZRPF retained-receipt Firecracker replay guest.

use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

use rustix::fs::{FileType, Mode, OFlags};
use rustix::mount::MountFlags;
use rustix::system::RebootCommand;
use sha2::{Digest as _, Sha256};
use zenodex_zrpf_risc0_replay_verifier::firecracker_protocol::{
    commit_accepted_output, read_request_from_output, FirecrackerProtocolError,
};
use zenodex_zrpf_risc0_replay_verifier::{run_cli, ReplayError};

const INPUT_DEVICE: &str = "/dev/vdb";
const OUTPUT_DEVICE: &str = "/dev/vdc";
const INPUT_MOUNT: &str = "/input";
const RECEIPT_DIRECTORY: &str = "/input/receipts";
const MAX_INPUT_DRIVE_BYTES: u64 = 16_777_216;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GuestInitError {
    OutputDevice,
    Request(FirecrackerProtocolError),
    InputDevice,
    InputBinding,
    InputMount,
    Replay(ReplayError),
    OutputCommit(FirecrackerProtocolError),
}

fn main() {
    if !is_expected_pid1(std::process::id()) {
        std::process::exit(125);
    }
    let _ = run_guest();
    terminate_guest()
}

const fn is_expected_pid1(process_id: u32) -> bool {
    process_id == 1
}

fn run_guest() -> Result<(), GuestInitError> {
    let mut output =
        open_block_device(OUTPUT_DEVICE, true).map_err(|_| GuestInitError::OutputDevice)?;
    let request = read_request_from_output(&mut output).map_err(GuestInitError::Request)?;
    let mut input =
        open_block_device(INPUT_DEVICE, false).map_err(|_| GuestInitError::InputDevice)?;
    let input_sha256 = hash_bounded_input_drive(&mut input)?;
    if &input_sha256 != request.input_drive_sha256() {
        return Err(GuestInitError::InputBinding);
    }
    mount_input_drive()?;
    let report = run_cli([RECEIPT_DIRECTORY.to_owned()]).map_err(GuestInitError::Replay)?;
    if hash_bounded_input_drive(&mut input)? != input_sha256 {
        return Err(GuestInitError::InputBinding);
    }
    commit_accepted_output(&mut output, &request, input_sha256, &report)
        .map_err(GuestInitError::OutputCommit)
}

fn open_block_device(path: &str, writable: bool) -> Result<File, GuestInitError> {
    let access = if writable {
        OFlags::RDWR
    } else {
        OFlags::RDONLY
    };
    let descriptor = rustix::fs::open(
        path,
        access | OFlags::CLOEXEC | OFlags::NOFOLLOW | OFlags::NONBLOCK,
        Mode::empty(),
    )
    .map_err(|_| GuestInitError::InputDevice)?;
    let metadata = rustix::fs::fstat(&descriptor).map_err(|_| GuestInitError::InputDevice)?;
    if !FileType::from_raw_mode(metadata.st_mode).is_block_device() {
        return Err(GuestInitError::InputDevice);
    }
    Ok(File::from(descriptor))
}

fn hash_bounded_input_drive(input: &mut File) -> Result<[u8; 32], GuestInitError> {
    let size = input
        .seek(SeekFrom::End(0))
        .map_err(|_| GuestInitError::InputDevice)?;
    if size == 0 || size > MAX_INPUT_DRIVE_BYTES {
        return Err(GuestInitError::InputDevice);
    }
    input
        .seek(SeekFrom::Start(0))
        .map_err(|_| GuestInitError::InputDevice)?;
    let mut remaining = size;
    let mut buffer = [0_u8; 65_536];
    let mut hasher = Sha256::new();
    while remaining > 0 {
        let limit = usize::try_from(remaining.min(buffer.len() as u64))
            .map_err(|_| GuestInitError::InputDevice)?;
        input
            .read_exact(&mut buffer[..limit])
            .map_err(|_| GuestInitError::InputDevice)?;
        hasher.update(&buffer[..limit]);
        remaining -= limit as u64;
    }
    Ok(hasher.finalize().into())
}

fn mount_input_drive() -> Result<(), GuestInitError> {
    let flags = MountFlags::RDONLY
        | MountFlags::NOSUID
        | MountFlags::NODEV
        | MountFlags::NOEXEC
        | MountFlags::NOATIME;
    rustix::mount::mount(INPUT_DEVICE, INPUT_MOUNT, "squashfs", flags, None)
        .map_err(|_| GuestInitError::InputMount)
}

fn terminate_guest() -> ! {
    let _ = rustix::system::reboot(RebootCommand::Restart);
    loop {
        std::thread::park();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn guest_paths_and_input_bound_are_fixed() {
        assert_eq!(INPUT_DEVICE, "/dev/vdb");
        assert_eq!(OUTPUT_DEVICE, "/dev/vdc");
        assert_eq!(RECEIPT_DIRECTORY, "/input/receipts");
        assert_eq!(MAX_INPUT_DRIVE_BYTES, 16_777_216);
        assert!(is_expected_pid1(1));
        assert!(!is_expected_pid1(2));
    }
}
