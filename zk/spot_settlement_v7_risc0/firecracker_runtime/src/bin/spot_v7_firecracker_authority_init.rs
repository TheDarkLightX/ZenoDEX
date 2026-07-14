//! PID 1 for the receipt-verifying Spot V7 Firecracker candidate lane.
//!
//! The binary reads an exact four-file input image, authenticates the V6 and
//! V7 receipts through the sealed governed verifier exactly once, derives the
//! verifier payload itself, rechecks the complete input drive, and only then
//! writes a committed output. Every failure returns before the sole commit
//! call. Final images, live jailed-runner evidence, release admission, the
//! atomic authority store, and all production claims remain unavailable.

#[cfg(target_os = "linux")]
mod linux {
    use std::fs::File;
    use std::io::{Read, Seek, SeekFrom};

    use rustix::fs::{FileType, Mode, OFlags};
    use rustix::mount::MountFlags;
    use rustix::system::RebootCommand;
    use sha2::{Digest as _, Sha256};
    use zenodex_zrpf_spot_v7_firecracker_runtime::{
        commit_data_only_output_v1, derive_governed_spot_v7_authority_payload_v1,
        read_request_from_output_v1, SpotV7FirecrackerAuthorityVerificationErrorV1,
        SpotV7FirecrackerProtocolErrorV1, SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1,
        SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1,
        SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1,
        SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1,
        SPOT_V7_FIRECRACKER_AUTHORITY_PID1_LIVE_RUNNER_AUTHORITY_V1,
        SPOT_V7_FIRECRACKER_AUTHORITY_PID1_PRODUCTION_READY_V1,
        SPOT_V7_FIRECRACKER_AUTHORITY_PID1_RELEASE_AUTHORITY_V1,
        SPOT_V7_FIRECRACKER_AUTHORITY_PID1_SETTLEMENT_AUTHORITY_V1,
        SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1, SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1,
    };

    const INPUT_DEVICE: &str = "/dev/vdb";
    const OUTPUT_DEVICE: &str = "/dev/vdc";
    const INPUT_MOUNT: &str = "/input";
    const AUTHORITY_MANIFEST: &str = "/input/spot-v7-authority-input.bin";
    const V7_RECEIPT: &str = "/input/spot-v7.receipt.json";
    const V7_GUEST_INPUT: &str = "/input/spot-v7.guest-input.bin";
    const V6_RECEIPT: &str = "/input/spot-v6.receipt.json";
    const EXPECTED_INPUT_NAMES: [&str; 4] = [
        "spot-v6.receipt.json",
        "spot-v7-authority-input.bin",
        "spot-v7.guest-input.bin",
        "spot-v7.receipt.json",
    ];
    const MAX_AUTHORITY_INPUT_DRIVE_BYTES_V1: u64 = 64 * 1_024 * 1_024;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum GuestInitError {
        AuthorityInvariant,
        OutputDevice,
        OutputNotPristine,
        Request(SpotV7FirecrackerProtocolErrorV1),
        InputDevice,
        InputBinding,
        InputMount,
        InputInventory,
        AuthorityManifest,
        V7Receipt,
        V7GuestInput,
        V6Receipt,
        Verification(SpotV7FirecrackerAuthorityVerificationErrorV1),
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
        require_nonpromoted_authority_profile()?;
        let mut output = open_block_device(OUTPUT_DEVICE, true, GuestInitError::OutputDevice)?;
        let request = read_request_from_output_v1(&mut output).map_err(GuestInitError::Request)?;
        require_pristine_output_after_request(&mut output)?;

        let mut input = open_block_device(INPUT_DEVICE, false, GuestInitError::InputDevice)?;
        let input_sha256 = hash_bounded_input_drive(&mut input)?;
        if &input_sha256 != request.input_drive_sha256() {
            return Err(GuestInitError::InputBinding);
        }
        mount_input_drive()?;
        require_exact_input_inventory()?;

        let manifest_bytes = read_regular_file(
            AUTHORITY_MANIFEST,
            SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1,
            Some(SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1),
            GuestInitError::AuthorityManifest,
        )?;
        let v7_receipt_bytes = read_regular_file(
            V7_RECEIPT,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1,
            None,
            GuestInitError::V7Receipt,
        )?;
        let guest_input_bytes = read_regular_file(
            V7_GUEST_INPUT,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1,
            None,
            GuestInitError::V7GuestInput,
        )?;
        let v6_receipt_bytes = read_regular_file(
            V6_RECEIPT,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1,
            None,
            GuestInitError::V6Receipt,
        )?;

        let payload = derive_governed_spot_v7_authority_payload_v1(
            &request,
            &manifest_bytes,
            &v7_receipt_bytes,
            &guest_input_bytes,
            &v6_receipt_bytes,
        )
        .map_err(GuestInitError::Verification)?;
        if hash_bounded_input_drive(&mut input)? != input_sha256 {
            return Err(GuestInitError::InputBinding);
        }
        commit_data_only_output_v1(&mut output, &request, input_sha256, &payload)
            .map_err(GuestInitError::OutputCommit)
    }

    fn require_nonpromoted_authority_profile() -> Result<(), GuestInitError> {
        if SPOT_V7_FIRECRACKER_AUTHORITY_PID1_LIVE_RUNNER_AUTHORITY_V1
            || SPOT_V7_FIRECRACKER_AUTHORITY_PID1_RELEASE_AUTHORITY_V1
            || SPOT_V7_FIRECRACKER_AUTHORITY_PID1_SETTLEMENT_AUTHORITY_V1
            || SPOT_V7_FIRECRACKER_AUTHORITY_PID1_PRODUCTION_READY_V1
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

    fn require_pristine_output_after_request(output: &mut File) -> Result<(), GuestInitError> {
        let size = output
            .seek(SeekFrom::End(0))
            .map_err(|_| GuestInitError::OutputDevice)?;
        if size != SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1 as u64 {
            return Err(GuestInitError::OutputDevice);
        }
        output
            .seek(SeekFrom::Start(SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1 as u64))
            .map_err(|_| GuestInitError::OutputDevice)?;
        let mut buffer = [0_u8; 65_536];
        let mut remaining = size
            .checked_sub(SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1 as u64)
            .ok_or(GuestInitError::OutputDevice)?;
        while remaining > 0 {
            let limit = usize::try_from(remaining.min(buffer.len() as u64))
                .map_err(|_| GuestInitError::OutputDevice)?;
            output
                .read_exact(&mut buffer[..limit])
                .map_err(|_| GuestInitError::OutputDevice)?;
            if buffer[..limit].iter().any(|byte| *byte != 0) {
                return Err(GuestInitError::OutputNotPristine);
            }
            remaining = remaining
                .checked_sub(limit as u64)
                .ok_or(GuestInitError::OutputDevice)?;
        }
        Ok(())
    }

    fn hash_bounded_input_drive(input: &mut File) -> Result<[u8; 32], GuestInitError> {
        let size = input
            .seek(SeekFrom::End(0))
            .map_err(|_| GuestInitError::InputDevice)?;
        if size == 0 || size > MAX_AUTHORITY_INPUT_DRIVE_BYTES_V1 {
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
            remaining = remaining
                .checked_sub(limit as u64)
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

    fn require_exact_input_inventory() -> Result<(), GuestInitError> {
        let entries = std::fs::read_dir(INPUT_MOUNT).map_err(|_| GuestInitError::InputInventory)?;
        let mut names = Vec::with_capacity(EXPECTED_INPUT_NAMES.len());
        for entry in entries {
            let entry = entry.map_err(|_| GuestInitError::InputInventory)?;
            let name = entry
                .file_name()
                .into_string()
                .map_err(|_| GuestInitError::InputInventory)?;
            names.push(name);
        }
        names.sort_unstable();
        if names.len() != EXPECTED_INPUT_NAMES.len()
            || names
                .iter()
                .map(String::as_str)
                .ne(EXPECTED_INPUT_NAMES.iter().copied())
        {
            return Err(GuestInitError::InputInventory);
        }
        Ok(())
    }

    fn read_regular_file(
        path: &str,
        maximum: usize,
        exact: Option<usize>,
        error: GuestInitError,
    ) -> Result<Vec<u8>, GuestInitError> {
        let descriptor = rustix::fs::open(
            path,
            OFlags::RDONLY | OFlags::CLOEXEC | OFlags::NOFOLLOW | OFlags::NONBLOCK,
            Mode::empty(),
        )
        .map_err(|_| error)?;
        let before = rustix::fs::fstat(&descriptor).map_err(|_| error)?;
        if !FileType::from_raw_mode(before.st_mode).is_file() {
            return Err(error);
        }
        let length = usize::try_from(before.st_size).map_err(|_| error)?;
        if length == 0 || length > maximum || exact.is_some_and(|value| value != length) {
            return Err(error);
        }
        let mut file = File::from(descriptor);
        let mut bytes = Vec::with_capacity(length);
        (&mut file)
            .take(u64::try_from(maximum).map_err(|_| error)? + 1)
            .read_to_end(&mut bytes)
            .map_err(|_| error)?;
        let after = rustix::fs::fstat(&file).map_err(|_| error)?;
        if bytes.len() != length || !same_file_observation(&before, &after) {
            return Err(error);
        }
        Ok(bytes)
    }

    fn same_file_observation(before: &rustix::fs::Stat, after: &rustix::fs::Stat) -> bool {
        before.st_dev == after.st_dev
            && before.st_ino == after.st_ino
            && before.st_mode == after.st_mode
            && before.st_size == after.st_size
            && before.st_mtime == after.st_mtime
            && before.st_mtime_nsec == after.st_mtime_nsec
            && before.st_ctime == after.st_ctime
            && before.st_ctime_nsec == after.st_ctime_nsec
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

        const AUTHORITY_INIT_SOURCE: &str = include_str!("spot_v7_firecracker_authority_init.rs");

        #[test]
        fn authority_pid1_paths_bounds_and_nonclaims_are_fixed() {
            assert_eq!(INPUT_DEVICE, "/dev/vdb");
            assert_eq!(OUTPUT_DEVICE, "/dev/vdc");
            assert_eq!(INPUT_MOUNT, "/input");
            assert_eq!(EXPECTED_INPUT_NAMES.len(), 4);
            assert_eq!(MAX_AUTHORITY_INPUT_DRIVE_BYTES_V1, 67_108_864);
            assert!(is_expected_pid1(1));
            assert!(!is_expected_pid1(2));
            assert_eq!(require_nonpromoted_authority_profile(), Ok(()));
        }

        #[test]
        fn verifier_and_second_drive_hash_precede_the_only_output_commit() {
            let run_guest_start = AUTHORITY_INIT_SOURCE
                .find("    fn run_guest()")
                .expect("run_guest start");
            let run_guest_end = AUTHORITY_INIT_SOURCE[run_guest_start..]
                .find("    fn require_nonpromoted_authority_profile()")
                .map(|offset| run_guest_start + offset)
                .expect("run_guest end");
            let run_guest_source = &AUTHORITY_INIT_SOURCE[run_guest_start..run_guest_end];
            let verify = run_guest_source
                .find("let payload = derive_governed_spot_v7_authority_payload_v1(")
                .expect("governed verifier call");
            let second_hash = run_guest_source[verify..]
                .find("if hash_bounded_input_drive(&mut input)? != input_sha256")
                .map(|offset| verify + offset)
                .expect("second drive hash");
            let commit = run_guest_source[second_hash..]
                .find("commit_data_only_output_v1(&mut output")
                .map(|offset| second_hash + offset)
                .expect("output commit");
            assert!(verify < second_hash && second_hash < commit);
            assert_eq!(
                run_guest_source
                    .matches("commit_data_only_output_v1(&mut output")
                    .count(),
                1
            );
            assert!(!run_guest_source.contains(&["spot-v7-verifier-", "output.bin",].concat()));
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
