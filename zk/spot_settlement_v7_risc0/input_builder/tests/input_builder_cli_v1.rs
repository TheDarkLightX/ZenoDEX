mod support;

use std::ffi::OsString;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(unix)]
use std::os::unix::fs::{symlink, MetadataExt};

use zenodex_zrpf_protocol_v3::MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1;
use zenodex_zrpf_risc0_spot_settlement_v7_input_builder::{
    parse_spot_settlement_v7_input_builder_args_v1, run_spot_settlement_v7_input_builder_v1,
    SpotSettlementV7InputBuilderErrorV1, SpotSettlementV7InputBuilderPathsV1,
};
use zenodex_zrpf_risc0_spot_settlement_v7_shared::decode_exact_spot_settlement_v7_guest_envelope_v1;

use support::{canonical_components, CanonicalComponentsV1};

static NEXT_TEMP_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectoryV1 {
    path: PathBuf,
}

impl TestDirectoryV1 {
    fn new(label: &str) -> Self {
        let counter = NEXT_TEMP_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "zenodex-zrpf-v7-input-builder-{label}-{}-{counter}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self { path }
    }

    fn join(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }
}

impl Drop for TestDirectoryV1 {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.path).unwrap();
    }
}

#[test]
fn strict_cli_parser_rejects_unknown_duplicate_missing_and_valueless_options() {
    assert_eq!(
        parse_spot_settlement_v7_input_builder_args_v1(["--unknown", "value"]),
        Err(SpotSettlementV7InputBuilderErrorV1::UnknownOption),
    );
    assert_eq!(
        parse_spot_settlement_v7_input_builder_args_v1([
            "--source-child-journal",
            "first",
            "--source-child-journal",
            "second",
        ]),
        Err(SpotSettlementV7InputBuilderErrorV1::DuplicateOption(
            "source child journal"
        )),
    );
    assert_eq!(
        parse_spot_settlement_v7_input_builder_args_v1(["--source-child-journal", "journal",]),
        Err(SpotSettlementV7InputBuilderErrorV1::MissingOption(
            "data availability certificate"
        )),
    );
    assert_eq!(
        parse_spot_settlement_v7_input_builder_args_v1(["--output"]),
        Err(SpotSettlementV7InputBuilderErrorV1::MissingOptionValue(
            "output"
        )),
    );
}

#[test]
fn run_builds_exact_envelope_into_one_private_create_new_output() {
    let directory = TestDirectoryV1::new("success");
    let components = canonical_components();
    let paths = write_inputs_and_parse(&directory, &components, "guest-input.bin");

    run_spot_settlement_v7_input_builder_v1(&paths).unwrap();

    let bytes = fs::read(paths.output()).unwrap();
    let envelope = decode_exact_spot_settlement_v7_guest_envelope_v1(&bytes).unwrap();
    assert_eq!(
        envelope.source_child_journal_bytes(),
        components.source_child_journal
    );
    assert_eq!(
        envelope.proposed_data_availability_certificate_bytes(),
        components.data_availability_certificate
    );
    assert_eq!(envelope.proposed_replay_bytes(), components.replay);
    assert_eq!(
        envelope.proposed_state_root_host_input_bytes(),
        components.state_root_host_input
    );
    #[cfg(unix)]
    assert_eq!(fs::metadata(paths.output()).unwrap().mode() & 0o777, 0o600);
}

#[test]
fn binary_builds_the_same_exact_envelope_with_no_success_log_channel() {
    let directory = TestDirectoryV1::new("binary-success");
    let components = canonical_components();
    let paths = write_inputs_and_parse(&directory, &components, "guest-input.bin");
    let result = Command::new(env!("CARGO_BIN_EXE_build_spot_settlement_v7_guest_input"))
        .arg("--source-child-journal")
        .arg(paths.source_child_journal())
        .arg("--data-availability-certificate")
        .arg(paths.data_availability_certificate())
        .arg("--replay")
        .arg(paths.replay())
        .arg("--state-root-host-input")
        .arg(paths.state_root_host_input())
        .arg("--output")
        .arg(paths.output())
        .output()
        .unwrap();

    assert!(result.status.success());
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
    let envelope =
        decode_exact_spot_settlement_v7_guest_envelope_v1(&fs::read(paths.output()).unwrap())
            .unwrap();
    assert_eq!(
        envelope.source_child_journal_bytes(),
        components.source_child_journal
    );
}

#[test]
fn binary_rejects_unknown_option_with_one_stable_bounded_error_line() {
    let result = Command::new(env!("CARGO_BIN_EXE_build_spot_settlement_v7_guest_input"))
        .args(["--unknown", "value"])
        .output()
        .unwrap();

    assert_eq!(result.status.code(), Some(1));
    assert!(result.stdout.is_empty());
    assert_eq!(
        result.stderr,
        b"spot settlement V7 input builder rejected: unknown_option\n"
    );
}

#[test]
fn existing_output_rejects_without_overwrite() {
    let directory = TestDirectoryV1::new("existing-output");
    let components = canonical_components();
    let paths = write_inputs_and_parse(&directory, &components, "guest-input.bin");
    fs::write(paths.output(), b"existing-output").unwrap();

    assert_eq!(
        run_spot_settlement_v7_input_builder_v1(&paths),
        Err(SpotSettlementV7InputBuilderErrorV1::OutputCreate),
    );
    assert_eq!(fs::read(paths.output()).unwrap(), b"existing-output");
}

#[test]
fn invalid_component_rejects_before_output_creation() {
    let directory = TestDirectoryV1::new("invalid-input");
    let mut components = canonical_components();
    components.source_child_journal.push(0);
    let paths = write_inputs_and_parse(&directory, &components, "guest-input.bin");

    assert_eq!(
        run_spot_settlement_v7_input_builder_v1(&paths),
        Err(SpotSettlementV7InputBuilderErrorV1::ComponentDecode(
            "source child journal"
        )),
    );
    assert!(!paths.output().exists());
}

#[cfg(unix)]
#[test]
fn symlink_input_rejects_before_output_creation() {
    let directory = TestDirectoryV1::new("symlink-input");
    let components = canonical_components();
    let paths = write_inputs_and_parse(&directory, &components, "guest-input.bin");
    let source = paths.source_child_journal().to_path_buf();
    let real = directory.join("real-journal.bin");
    fs::rename(&source, &real).unwrap();
    symlink(&real, &source).unwrap();

    assert_eq!(
        run_spot_settlement_v7_input_builder_v1(&paths),
        Err(SpotSettlementV7InputBuilderErrorV1::InputOpen(
            "source child journal"
        )),
    );
    assert!(!paths.output().exists());
}

#[cfg(unix)]
#[test]
fn hard_linked_input_rejects_before_decode() {
    let directory = TestDirectoryV1::new("hard-linked-input");
    let components = canonical_components();
    let paths = write_inputs_and_parse(&directory, &components, "guest-input.bin");
    fs::hard_link(
        paths.source_child_journal(),
        directory.join("second-journal-link.bin"),
    )
    .unwrap();

    assert_eq!(
        run_spot_settlement_v7_input_builder_v1(&paths),
        Err(SpotSettlementV7InputBuilderErrorV1::InputNotSingleLinkRegular("source child journal")),
    );
    assert!(!paths.output().exists());
}

#[test]
fn empty_and_oversized_inputs_reject_before_decode_or_output() {
    for (label, bytes) in [
        ("empty", Vec::new()),
        (
            "oversized",
            vec![0; MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1 + 1],
        ),
    ] {
        let directory = TestDirectoryV1::new(label);
        let mut components = canonical_components();
        components.source_child_journal = bytes;
        let paths = write_inputs_and_parse(&directory, &components, "guest-input.bin");

        assert_eq!(
            run_spot_settlement_v7_input_builder_v1(&paths),
            Err(SpotSettlementV7InputBuilderErrorV1::InputLength(
                "source child journal"
            )),
        );
        assert!(!paths.output().exists());
    }
}

fn write_inputs_and_parse(
    directory: &TestDirectoryV1,
    components: &CanonicalComponentsV1,
    output_name: &str,
) -> SpotSettlementV7InputBuilderPathsV1 {
    let journal = write(directory, "journal.bin", &components.source_child_journal);
    let certificate = write(
        directory,
        "certificate.bin",
        &components.data_availability_certificate,
    );
    let replay = write(directory, "replay.bin", &components.replay);
    let host = write(directory, "host.bin", &components.state_root_host_input);
    let output = directory.join(output_name);
    let args = [
        OsString::from("--source-child-journal"),
        journal.into_os_string(),
        OsString::from("--data-availability-certificate"),
        certificate.into_os_string(),
        OsString::from("--replay"),
        replay.into_os_string(),
        OsString::from("--state-root-host-input"),
        host.into_os_string(),
        OsString::from("--output"),
        output.into_os_string(),
    ];
    parse_spot_settlement_v7_input_builder_args_v1(args).unwrap()
}

fn write(directory: &TestDirectoryV1, name: &str, bytes: &[u8]) -> PathBuf {
    let path = directory.join(name);
    fs::write(&path, bytes).unwrap();
    path
}
