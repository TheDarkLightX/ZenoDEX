//! PID 1 for the authority-neutral Spot V7 Firecracker protocol lane.
//!
//! This binary consumes a precomputed, structurally valid V7 verifier-output
//! payload. It does not verify a RISC0 receipt and cannot create execution,
//! settlement, release, or production authority.
//!
//! The pre/post drive hashes do not defend against a host that transiently
//! swaps mutable backing bytes and restores them before the second hash. A
//! future authority profile must require root-owned immutable backing for the
//! complete VM lifetime and test that launcher invariant independently.

#[cfg(target_os = "linux")]
mod linux {
    use std::fs::File;
    use std::io::{Read, Seek, SeekFrom};

    use rustix::fs::{FileType, Mode, OFlags};
    use rustix::mount::MountFlags;
    use rustix::system::RebootCommand;
    use sha2::{Digest as _, Sha256};
    use zenodex_zrpf_spot_v7_firecracker_runtime::{
        commit_data_only_output_v1, decode_structural_spot_v7_payload_v1,
        read_request_from_output_v1, SpotV7FirecrackerProtocolErrorV1,
        SPOT_V7_FIRECRACKER_EXECUTION_AUTHORITY_V1,
        SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1, SPOT_V7_FIRECRACKER_PRODUCTION_READY_V1,
        SPOT_V7_FIRECRACKER_RELEASE_AUTHORITY_V1, SPOT_V7_FIRECRACKER_SETTLEMENT_AUTHORITY_V1,
    };

    const INPUT_DEVICE: &str = "/dev/vdb";
    const OUTPUT_DEVICE: &str = "/dev/vdc";
    const INPUT_MOUNT: &str = "/input";
    const PRECOMPUTED_V7_PAYLOAD: &str = "/input/spot-v7-verifier-output.bin";
    const MAX_INPUT_DRIVE_BYTES: u64 = 16_777_216;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum GuestInitError {
        AuthorityInvariant,
        OutputDevice,
        Request(SpotV7FirecrackerProtocolErrorV1),
        InputDevice,
        InputBinding,
        InputMount,
        PayloadFile,
        Payload(SpotV7FirecrackerProtocolErrorV1),
        OutputCommit(SpotV7FirecrackerProtocolErrorV1),
    }

    pub(super) fn main() {
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
        require_authority_neutral_profile()?;
        let mut output = open_block_device(OUTPUT_DEVICE, true, GuestInitError::OutputDevice)?;
        let request = read_request_from_output_v1(&mut output).map_err(GuestInitError::Request)?;
        let mut input = open_block_device(INPUT_DEVICE, false, GuestInitError::InputDevice)?;
        let input_sha256 = hash_bounded_input_drive(&mut input)?;
        if &input_sha256 != request.input_drive_sha256() {
            return Err(GuestInitError::InputBinding);
        }
        mount_input_drive()?;
        let payload_bytes = read_precomputed_payload()?;
        let payload = decode_structural_spot_v7_payload_v1(&payload_bytes)
            .map_err(GuestInitError::Payload)?;
        if hash_bounded_input_drive(&mut input)? != input_sha256 {
            return Err(GuestInitError::InputBinding);
        }
        commit_data_only_output_v1(&mut output, &request, input_sha256, &payload)
            .map_err(GuestInitError::OutputCommit)
    }

    fn require_authority_neutral_profile() -> Result<(), GuestInitError> {
        if SPOT_V7_FIRECRACKER_EXECUTION_AUTHORITY_V1
            || SPOT_V7_FIRECRACKER_SETTLEMENT_AUTHORITY_V1
            || SPOT_V7_FIRECRACKER_RELEASE_AUTHORITY_V1
            || SPOT_V7_FIRECRACKER_PRODUCTION_READY_V1
        {
            return Err(GuestInitError::AuthorityInvariant);
        }
        Ok(())
    }

    fn open_block_device(
        path: &str,
        writable: bool,
        error: GuestInitError,
    ) -> Result<File, GuestInitError> {
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
        .map_err(|_| error)?;
        let metadata = rustix::fs::fstat(&descriptor).map_err(|_| error)?;
        if !FileType::from_raw_mode(metadata.st_mode).is_block_device() {
            return Err(error);
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
            let read_limit = remaining.min(65_536);
            let limit = usize::try_from(read_limit).map_err(|_| GuestInitError::InputDevice)?;
            input
                .read_exact(&mut buffer[..limit])
                .map_err(|_| GuestInitError::InputDevice)?;
            hasher.update(&buffer[..limit]);
            remaining = remaining
                .checked_sub(read_limit)
                .ok_or(GuestInitError::InputDevice)?;
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

    fn read_precomputed_payload() -> Result<Vec<u8>, GuestInitError> {
        let descriptor = rustix::fs::open(
            PRECOMPUTED_V7_PAYLOAD,
            OFlags::RDONLY | OFlags::CLOEXEC | OFlags::NOFOLLOW | OFlags::NONBLOCK,
            Mode::empty(),
        )
        .map_err(|_| GuestInitError::PayloadFile)?;
        let metadata = rustix::fs::fstat(&descriptor).map_err(|_| GuestInitError::PayloadFile)?;
        if !FileType::from_raw_mode(metadata.st_mode).is_file() {
            return Err(GuestInitError::PayloadFile);
        }
        let length = usize::try_from(metadata.st_size).map_err(|_| GuestInitError::PayloadFile)?;
        if length == 0 || length > SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1 {
            return Err(GuestInitError::PayloadFile);
        }
        let file = File::from(descriptor);
        let mut payload = Vec::with_capacity(length);
        file.take(
            u64::try_from(SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1)
                .map_err(|_| GuestInitError::PayloadFile)?
                + 1,
        )
        .read_to_end(&mut payload)
        .map_err(|_| GuestInitError::PayloadFile)?;
        if payload.len() != length {
            return Err(GuestInitError::PayloadFile);
        }
        Ok(payload)
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
        fn protocol_only_guest_paths_bounds_and_authority_are_fixed() {
            assert_eq!(INPUT_DEVICE, "/dev/vdb");
            assert_eq!(OUTPUT_DEVICE, "/dev/vdc");
            assert_eq!(INPUT_MOUNT, "/input");
            assert_eq!(PRECOMPUTED_V7_PAYLOAD, "/input/spot-v7-verifier-output.bin");
            assert_eq!(MAX_INPUT_DRIVE_BYTES, 16_777_216);
            assert_eq!(SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1, 65_536);
            assert!(is_expected_pid1(1));
            assert!(!is_expected_pid1(2));
            assert_eq!(require_authority_neutral_profile(), Ok(()));
        }
    }
}

#[cfg(target_os = "linux")]
fn main() {
    linux::main()
}

#[cfg(not(target_os = "linux"))]
fn main() {
    std::process::exit(125);
}
